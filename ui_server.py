import argparse
from collections import Counter, deque
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import mimetypes
import os
from pathlib import Path
import selectors
import subprocess
import sys
import threading
import time
from urllib.parse import parse_qs, urlparse

import grammar_engine as ENGINE
from grammar_io import load_grammar
from ui_proofs import build_grammar, serialize_finding, summarize_finding
from ui_storage import get_finding, list_findings, load_languages, page_sentences, read_summary, save_snapshot


ROOT = Path(__file__).resolve().parent
STATIC = ROOT / "ui"


def grammar_ids():
    # Cfront is not distributed; it is listed once fetched and converted (see README.md).
    return [name for name in ("roskind", "expression", "cfront")
            if name != "cfront" or (ROOT / "cfront" / "grammar.json").exists()]


def dataset(name):
    if name in ("roskind", "cfront"):
        path = ROOT / name / "grammar.json"
        if not path.exists():
            raise ValueError(f"{name}/grammar.json is missing; see README.md")
        return load_grammar(path)
    if name == "expression":
        return {
            "name": "Expression grammar", "start": "E", "format": "cfg-productions-v1",
            "terminals": ["+", "*", "(", ")", "n"], "nonterminals": ["E", "F"],
            "source": {"file": "NSF report, expression grammar G1"},
            "productions": [
                {"lhs": "E", "rhs": ["E", "+", "E"]},
                {"lhs": "E", "rhs": ["E", "*", "F"]},
                {"lhs": "E", "rhs": ["F"]},
                {"lhs": "F", "rhs": ["(", "E", ")"]},
                {"lhs": "F", "rhs": ["n"]},
            ],
            "translation_notice": "The paper's expression grammar, with union and concatenation witnesses at level 4.",
        }
    raise ValueError("Unknown grammar")


def describe(name, data):
    return {"id": name, "name": data["name"], "start": data["start"],
            "description": data.get("translation_notice", ""),
            "rule_count": len(data["productions"]), "nonterminal_count": len(data["nonterminals"])}


def memory_reader():
    if sys.platform == "darwin":
        from benchmark_roskind import memory_reader as mac_reader
        reader = mac_reader()

        def read(pid):
            values = reader(pid)
            return max(values.values()) if values else None

        return read
    if sys.platform.startswith("linux"):
        def read(pid):
            try:
                fields = Path(f"/proc/{pid}/statm").read_text().split()
                return int(fields[1]) * os.sysconf("SC_PAGE_SIZE")
            except (FileNotFoundError, PermissionError, IndexError):
                return None
        return read
    raise RuntimeError("Memory monitoring currently supports macOS and Linux")


def summary(grammar, seconds, memory, findings):
    return {"level": grammar.iteration, "seconds": seconds,
            "counts": {nt.name: str(nt.next.trie.root.size) for nt in grammar.nonterminals},
            "findings_count": len(findings),
            "findings_by_nonterminal": dict(Counter(item["owner"] for item in findings)),
            "memory_bytes": memory, "created_at": time.time()}


def worker(args):
    catalog = build_grammar(dataset(args.dataset))
    grammar = catalog.grammar
    read_memory = memory_reader()

    def phase(name):
        print(json.dumps({"phase": name}), flush=True)

    phase("loading")
    load_languages(args.previous, grammar)
    phase("computing")
    started = time.monotonic()
    findings = grammar.step()
    seconds = time.monotonic() - started
    phase("saving")
    records = []
    for finding in findings:
        record = summarize_finding(finding, catalog)
        record["raw_factorizations"] = [
            [left.symbols, right.symbols] for left, right in finding.factorizations
        ] if finding.factorizations else None
        records.append(record)
    details = summary(grammar, seconds, read_memory(os.getpid()) or 0, records)
    save_snapshot(args.snapshot, grammar, records, details)
    print(json.dumps({"saved": True, "level": grammar.iteration}), flush=True)


class Workspace:
    def __init__(self, cache):
        self.cache = Path(cache)
        self.cache.mkdir(parents=True, exist_ok=True)
        self.lock = threading.RLock()
        self.read_memory = memory_reader()
        self.process = None
        self.monitor = None
        self.generation = 0
        self.revision = 0
        self.memory_limit = 2048 * 1024 ** 2
        self.memory_history = deque(maxlen=180)
        self.used_memory = 0
        self.peak_memory = 0
        self.status = "idle"
        self.phase = None
        self.error = None
        self.target = None
        self.levels = []
        self.catalog = None
        self.grammar_description = None
        self.proof_cache = {}
        self.open("roskind")

    def file(self, level):
        return self.directory / f"level-{level}.sqlite"

    def open(self, name, memory_limit_mb=None):
        data = dataset(name)
        catalog = build_grammar(data)
        fingerprint = hashlib.sha256(json.dumps(data, sort_keys=True).encode())
        for filename in ("grammar_engine.py", "ui_proofs.py", "ui_storage.py", "ui_server.py"):
            fingerprint.update((ROOT / filename).read_bytes())
        with self.lock:
            if memory_limit_mb is not None:
                self.settings(memory_limit_mb)
            self._stop()
            self.generation += 1
            self.catalog = catalog
            self.data = data
            self.grammar_description = describe(name, data)
            self.directory = self.cache / f"{name}-{fingerprint.hexdigest()[:16]}"
            self.directory.mkdir(exist_ok=True)
            if not self.file(0).exists():
                save_snapshot(self.file(0), catalog.grammar, [], summary(catalog.grammar, 0, 0, []))
            self.levels = []
            index = 0
            while self.file(index).exists():
                self.levels.append(read_summary(self.file(index)))
                index += 1
            self.status = "idle"
            self.phase = None
            self.error = None
            self.target = None
            self.used_memory = 0
            self.peak_memory = 0
            self.memory_history.clear()
            self.proof_cache.clear()
            self.revision += 1
            return self.state()

    def settings(self, limit_mb):
        if isinstance(limit_mb, bool) or not isinstance(limit_mb, (int, float)) or not 64 <= limit_mb <= 4096:
            raise ValueError("Choose a memory limit between 64 and 4096 MiB")
        with self.lock:
            self.memory_limit = int(limit_mb * 1024 ** 2)
            return self.state()

    def state(self):
        with self.lock:
            return {"grammar": self.grammar_description, "status": self.status, "phase": self.phase,
                    "completed_level": len(self.levels) - 1, "target_level": self.target,
                    "levels": list(self.levels), "error": self.error, "revision": self.revision,
                    "memory": {"used_bytes": self.used_memory, "peak_bytes": self.peak_memory,
                               "limit_bytes": self.memory_limit, "history": list(self.memory_history),
                               "worker_alive": self.process is not None and self.process.poll() is None,
                               "server_bytes": self.read_memory(os.getpid()) or 0}}

    def grammar(self):
        with self.lock:
            return {**self.grammar_description, "terminals": self.data["terminals"],
                    "nonterminals": self.data["nonterminals"], "rules": self.catalog.rules,
                    "formulas": self.catalog.formulas, "notice": self.data.get("translation_notice", ""),
                    "source_notices": self.data.get("source_notices", [])}

    def _stop(self):
        if self.process is not None and self.process.poll() is None:
            self.process.kill()
            self.process.wait()
        self.process = None

    def cancel(self):
        with self.lock:
            running = self.status == "computing"
            self.generation += 1
            self._stop()
            self.status = "idle"
            self.phase = None
            self.target = None
            self.used_memory = 0
            self.error = "Computation cancelled. Completed levels are still available." if running else None
            self.revision += 1
            return self.state()

    def advance(self, level):
        with self.lock:
            if self.status == "computing":
                raise ValueError("A level is already being computed")
            if isinstance(level, bool) or not isinstance(level, int) or level != len(self.levels):
                raise ValueError("Advance one level beyond the last completed level")
            target = self.file(level)
            if target.exists():
                self.levels.append(read_summary(target))
                self.revision += 1
                return self.state()
            command = [sys.executable, "-u", str(Path(__file__).resolve()), "--worker",
                       "--dataset", self.grammar_description["id"],
                       "--previous", str(self.file(level - 1)), "--snapshot", str(target)]
            error_path = self.directory / f"level-{level}.stderr.txt"
            errors = error_path.open("w")
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=errors,
                                       env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}, cwd=ROOT)
            errors.close()
            self.process = process
            self.status = "computing"
            self.phase = "loading"
            self.error = None
            self.target = level
            self.used_memory = 0
            self.peak_memory = 0
            self.memory_history.clear()
            self.revision += 1
            generation = self.generation
            self.monitor = threading.Thread(target=self._watch,
                                            args=(process, generation, target, error_path), daemon=True)
            self.monitor.start()
            return self.state()

    def _watch(self, process, generation, target, error_path):
        started = time.monotonic()
        sampled = started
        last_read = started
        buffered = b""
        reason = None
        selector = selectors.DefaultSelector()
        selector.register(process.stdout, selectors.EVENT_READ)
        try:
            while process.poll() is None:
                for key, _ in selector.select(0.05):
                    chunk = os.read(key.fd, 4096)
                    if chunk:
                        buffered += chunk
                        while b"\n" in buffered:
                            line, buffered = buffered.split(b"\n", 1)
                            event = json.loads(line)
                            with self.lock:
                                if generation == self.generation and "phase" in event:
                                    self.phase = event["phase"]
                    else:
                        selector.unregister(key.fileobj)
                now = time.monotonic()
                memory = self.read_memory(process.pid)
                with self.lock:
                    if generation != self.generation:
                        return
                    if memory is not None:
                        last_read = now
                        self.used_memory = memory
                        self.peak_memory = max(self.peak_memory, memory)
                        if now - sampled >= 0.5:
                            self.memory_history.append({"time": now - started, "bytes": memory})
                            sampled = now
                        if memory >= self.memory_limit:
                            reason = f"Level {self.target} stopped at the {self.memory_limit // 1024 ** 2} MiB memory limit. Completed levels are preserved."
                    elif now - last_read > 2 and process.poll() is None:
                        reason = "Memory monitoring stopped responding. Computation stopped; completed levels are preserved."
                    if now - started > 600:
                        reason = "The level exceeded 10 minutes. Completed levels are preserved."
                    if reason and process.poll() is None:
                        process.kill()
            process.wait()
            with self.lock:
                if generation != self.generation:
                    return
                if target.exists():
                    details = read_summary(target)
                    details["memory_bytes"] = max(details.get("memory_bytes", 0), self.peak_memory)
                    self.levels.append(details)
                    self.status = "idle"
                    self.error = None
                elif reason:
                    self.status = "limited"
                    self.error = reason
                else:
                    self.status = "error"
                    error = error_path.read_text()[-1500:]
                    self.error = "The level could not finish. Completed levels are preserved. " + error
                self.process = None
                self.phase = None
                self.target = None
                self.used_memory = 0
                self.revision += 1
        finally:
            if process.poll() is None:
                process.kill()
            process.wait()
            process.stdout.close()
            selector.close()
            for incomplete in target.parent.glob(target.name + f".{process.pid}.*.tmp*"):
                incomplete.unlink(missing_ok=True)

    def snapshot(self, level):
        with self.lock:
            if level < 0 or level >= len(self.levels):
                raise ValueError("That approximation level has not completed")
            return self.file(level)

    def proof(self, identifier):
        with self.lock:
            if identifier in self.proof_cache:
                return self.proof_cache[identifier]
            catalog = self.catalog
            generation = self.generation
            paths = [self.file(level) for level in range(len(self.levels) - 1, -1, -1)]
        record = None
        for path in paths:
            try:
                record = get_finding(path, identifier)
                break
            except KeyError:
                continue
        if record is None:
            raise KeyError("Unknown ambiguity witness")
        owner = catalog.nonterminals[record["owner"]]
        formula = owner.definition
        for part in record["path"]:
            formula = formula.formula if part == "inner" else getattr(formula, part)
        pairs = record.get("raw_factorizations")
        pairs = tuple((ENGINE.Sentence.from_symbols(left), ENGINE.Sentence.from_symbols(right))
                      for left, right in pairs) if pairs else None
        finding = ENGINE.AmbiguityFinding(record["kind"], ENGINE.Sentence.from_symbols(record["witness"]),
                                          owner, formula, record["level"], tuple(record["path"]), pairs)
        proof = serialize_finding(finding, catalog)
        with self.lock:
            if generation == self.generation:
                if len(self.proof_cache) >= 128:
                    self.proof_cache.pop(next(iter(self.proof_cache)))
                self.proof_cache[identifier] = proof
        return proof


class Handler(BaseHTTPRequestHandler):
    def log_message(self, pattern, *args):
        if args and str(args[1]) not in ("200", "202"):
            super().log_message(pattern, *args)

    def send_json(self, data, status=200):
        payload = json.dumps(data).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def allowed_origin(self):
        hostname = self.headers.get("Host", "").split(":")[0]
        origin = self.headers.get("Origin")
        return hostname in ("127.0.0.1", "localhost") and (
            not origin or origin in (f"http://127.0.0.1:{self.server.server_port}",
                                     f"http://localhost:{self.server.server_port}"))

    def do_GET(self):
        if not self.allowed_origin():
            return self.send_json({"error": "This workbench is local to this computer"}, 403)
        parsed = urlparse(self.path)
        query = {name: values[0] for name, values in parse_qs(parsed.query).items()}
        workspace = self.server.workspace
        try:
            if parsed.path == "/api/catalog":
                result = {"grammars": [describe(name, dataset(name)) for name in grammar_ids()],
                          "selected": "roskind"}
            elif parsed.path == "/api/state":
                result = workspace.state()
            elif parsed.path == "/api/grammar":
                result = workspace.grammar()
            elif parsed.path == "/api/approximation":
                path = workspace.snapshot(int(query.get("level", 0)))
                result = page_sentences(path, query["nonterminal"], int(query.get("offset", 0)),
                                        int(query.get("limit", 24)),
                                        json.loads(query["prefix"]) if query.get("prefix") else None)
            elif parsed.path == "/api/findings":
                path = workspace.snapshot(int(query.get("level", 0)))
                result = list_findings(path, query.get("nonterminal"), int(query.get("offset", 0)),
                                       int(query.get("limit", 25)))
            elif parsed.path == "/api/proof":
                result = workspace.proof(query["id"])
            elif parsed.path.startswith("/api/"):
                return self.send_json({"error": "Unknown request"}, 404)
            else:
                file = (STATIC / (parsed.path.lstrip("/") or "index.html")).resolve()
                if not file.is_relative_to(STATIC) or not file.is_file():
                    return self.send_json({"error": "File not found"}, 404)
                content = file.read_bytes()
                self.send_response(200)
                self.send_header("Content-Type", mimetypes.guess_type(file)[0] or "application/octet-stream")
                self.send_header("Content-Length", str(len(content)))
                self.send_header("Cache-Control", "no-cache")
                self.send_header("X-Content-Type-Options", "nosniff")
                self.end_headers()
                self.wfile.write(content)
                return
            self.send_json(result)
        except (ValueError, KeyError, TypeError) as error:
            self.send_json({"error": str(error)}, 400)
        except BrokenPipeError:
            pass
        except Exception as error:
            self.send_json({"error": f"The request could not finish: {error}"}, 500)

    def do_POST(self):
        if not self.allowed_origin():
            return self.send_json({"error": "This workbench is local to this computer"}, 403)
        try:
            length = int(self.headers.get("Content-Length", 0))
            if length > 10000:
                raise ValueError("Request too large")
            data = json.loads(self.rfile.read(length) or b"{}")
            workspace = self.server.workspace
            if self.path == "/api/session":
                result = workspace.open(data["grammar"], data.get("memory_limit_mb"))
            elif self.path == "/api/advance":
                result = workspace.advance(data["level"])
            elif self.path == "/api/cancel":
                result = workspace.cancel()
            elif self.path == "/api/settings":
                result = workspace.settings(data["memory_limit_mb"])
            else:
                return self.send_json({"error": "Unknown request"}, 404)
            self.send_json(result, 202 if self.path == "/api/advance" else 200)
        except (ValueError, KeyError, TypeError) as error:
            self.send_json({"error": str(error)}, 400)
        except BrokenPipeError:
            pass


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--cache", type=Path, default=ROOT / ".ui_cache")
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--dataset")
    parser.add_argument("--previous")
    parser.add_argument("--snapshot")
    args = parser.parse_args()
    if args.worker:
        return worker(args)
    workspace = Workspace(args.cache)
    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    server.workspace = workspace
    print(f"Grammar workbench: http://127.0.0.1:{server.server_port}", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        workspace.cancel()
        server.server_close()


if __name__ == "__main__":
    main()
