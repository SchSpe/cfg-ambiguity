import argparse
import errno
from http.server import ThreadingHTTPServer
import json
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import threading
from urllib.parse import parse_qs, urlsplit
import webbrowser

from ui_server import Handler, ROOT, Workspace


def dot_label(value):
    return json.dumps(str(value), ensure_ascii=False)


def token_text(tokens):
    return " ".join(map(str, tokens)) if tokens else "ε"


def diagram_dot(proof):
    if proof.get("verified") is not True:
        raise ValueError("This finding has no verified proof")
    owner = proof["owner"]
    witness = proof["witness"]
    if not isinstance(witness, list):
        raise ValueError("The proof has no terminal witness")
    kind = proof["kind"]
    if kind not in ("union", "concatenation"):
        raise ValueError("Unsupported ambiguity kind")
    color = "#c43664" if kind == "union" else "#207bb4"
    pale = "#fff0f4" if kind == "union" else "#eaf5fd"
    lines = [
        "digraph proof {",
        'graph [rankdir=TB, bgcolor="transparent", pad="0.3", nodesep="0.6", ranksep="0.65"];',
        'node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=13, margin="0.18,0.12"];',
        f'edge [color="{color}", arrowsize=0.7, penwidth=1.7];',
    ]
    if kind == "union":
        alternatives = proof.get("alternatives") or []
        identifiers = proof.get("production_ids") or []
        if len(alternatives) < 2 or len(set(identifiers)) < 2:
            raise ValueError("A union diagram needs two distinct production alternatives")
        selected = alternatives[:2]
        selected_ids = [alternative["production_id"] for alternative in selected]
        if len(set(selected_ids)) != 2 or not set(selected_ids).issubset(identifiers):
            raise ValueError("The union alternatives do not match the verified production IDs")
        lines.append(f'owner [label={dot_label(owner)}, fillcolor="#f7f8fc", color="#77839a"];')
        for index, alternative in enumerate(selected):
            label = f'{alternative["production_id"]}\n{alternative["expression"]}'
            lines.append(f'branch{index} [label={dot_label(label)}, fillcolor="{pale}", color="{color}"];')
            lines.append(f'owner -> branch{index};')
        lines.append("{rank=same; branch0; branch1;}")
        for index in range(2):
            lines.append(f'branch{index} -> witness;')
    else:
        identifiers = proof.get("production_ids") or []
        factorizations = proof.get("factorizations") or []
        if not identifiers or len(factorizations) < 2:
            raise ValueError("A concatenation diagram needs one production and two factorizations")
        selected = factorizations[:2]
        cuts = [factor["cut"] for factor in selected]
        if cuts[0] == cuts[1]:
            raise ValueError("The concatenation factorizations must have distinct splits")
        label = f'{", ".join(identifiers)}\n{owner} → {proof["expression"]}'
        lines.append(f'owner [label={dot_label(label)}, fillcolor="{pale}", color="{color}"];')
        for index, factor in enumerate(selected):
            if factor["left"] + factor["right"] != witness or len(factor["left"]) != factor["cut"]:
                raise ValueError("A factorization does not match the verified witness")
            label = f'{token_text(factor["left"])}  │  {token_text(factor["right"])}'
            lines.append(f'split{index} [label={dot_label(label)}, fillcolor="#f7f8fc", color="{color}"];')
            lines.append(f'owner -> split{index};')
        lines.append("{rank=same; split0; split1;}")
        for index in range(2):
            lines.append(f'split{index} -> witness;')
    lines.append(f'witness [label={dot_label(token_text(witness))}, fillcolor="{pale}", color="{color}", penwidth=2.2];')
    lines.append("}")
    return "\n".join(lines)


def render_svg(proof, dot_executable="dot"):
    result = subprocess.run(
        [dot_executable, "-Tsvg"], input=diagram_dot(proof).encode("utf-8"),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10, check=False,
    )
    if result.returncode or not result.stdout.lstrip().startswith(b"<?xml"):
        raise RuntimeError("Graphviz could not render this proof")
    return result.stdout


class DiagramHandler(Handler):
    def do_GET(self):
        parsed = urlsplit(self.path)
        if parsed.path != "/api/graphviz":
            return super().do_GET()
        if not self.allowed_origin():
            return self.send_json({"error": "This workbench is local to this computer"}, 403)
        query = parse_qs(parsed.query, keep_blank_values=True)
        identifiers = query.get("id", [])
        if set(query) != {"id"} or len(identifiers) != 1 or not re.fullmatch(r"[0-9a-f]{20}", identifiers[0]):
            return self.send_json({"error": "Specify one valid finding ID"}, 400)
        try:
            proof = self.server.workspace.proof(identifiers[0])
            svg = render_svg(proof, self.server.dot_executable)
            self.send_response(200)
            self.send_header("Content-Type", "image/svg+xml; charset=utf-8")
            self.send_header("Content-Length", str(len(svg)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("Content-Security-Policy", "default-src 'none'; style-src 'unsafe-inline'; sandbox")
            self.end_headers()
            self.wfile.write(svg)
        except KeyError:
            self.send_json({"error": "Unknown ambiguity witness"}, 404)
        except ValueError as error:
            self.send_json({"error": str(error)}, 400)
        except (OSError, subprocess.TimeoutExpired, RuntimeError):
            self.send_json({"error": "Graphviz could not render this proof"}, 503)
        except BrokenPipeError:
            pass


def port_number(value):
    try:
        port = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("Port must be an integer") from error
    if not 0 <= port <= 65535:
        raise argparse.ArgumentTypeError("Port must be between 0 and 65535")
    return port


def bind_server(port, explicit):
    try:
        return ThreadingHTTPServer(("127.0.0.1", port), DiagramHandler)
    except OSError as error:
        if error.errno != errno.EADDRINUSE:
            raise
        if explicit:
            raise OSError(f"Port {port} is already in use; choose another with --port") from error
        server = ThreadingHTTPServer(("127.0.0.1", 0), DiagramHandler)
        print(f"Port {port} is busy; using {server.server_port} instead.", flush=True)
        return server


def main(argv=None):
    parser = argparse.ArgumentParser(description="Open the grammar UI with Graphviz proof diagrams")
    parser.add_argument("--port", type=port_number)
    parser.add_argument("--cache", type=Path, default=ROOT / ".ui_cache")
    parser.add_argument("--no-browser", action="store_true")
    args = parser.parse_args(argv)
    dot_executable = shutil.which("dot")
    if dot_executable is None:
        parser.error("Graphviz 'dot' was not found; install Graphviz and try again")
    try:
        server = bind_server(8765 if args.port is None else args.port, args.port is not None)
    except OSError as error:
        parser.error(str(error))
    workspace = None
    thread = None
    old_sigterm = None
    try:
        workspace = Workspace(args.cache.expanduser().resolve())
        server.workspace = workspace
        server.dot_executable = dot_executable
        server.daemon_threads = True
        url = f"http://127.0.0.1:{server.server_port}/?graphviz=1"
        thread = threading.Thread(target=server.serve_forever, name="grammar-ui", daemon=True)
        thread.start()
        print(f"Grammar UI: {url}", flush=True)
        if not args.no_browser and not webbrowser.open(url, new=2):
            print("The browser did not open automatically; use the URL above.", flush=True)
        if threading.current_thread() is threading.main_thread():
            stop = threading.Event()
            old_sigterm = signal.getsignal(signal.SIGTERM)
            signal.signal(signal.SIGTERM, lambda *_: stop.set())
            while thread.is_alive() and not stop.wait(0.5):
                pass
        else:
            thread.join()
    except KeyboardInterrupt:
        pass
    finally:
        if old_sigterm is not None:
            signal.signal(signal.SIGTERM, old_sigterm)
        if thread is not None:
            server.shutdown()
            thread.join()
        if workspace is not None:
            workspace.cancel()
        server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
