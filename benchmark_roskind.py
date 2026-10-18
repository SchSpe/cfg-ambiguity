import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import resource
import selectors
import subprocess
import sys
import time

from grammar_io import load_grammar


class ProcessUsage(ctypes.Structure):
    _fields_ = [("uuid", ctypes.c_uint8 * 16)] + [
        (name, ctypes.c_uint64) for name in (
            "user_time", "system_time", "pkg_idle_wkups", "interrupt_wkups",
            "pageins", "wired_size", "resident_size", "phys_footprint",
            "proc_start_abstime", "proc_exit_abstime",
        )
    ]


def memory_reader():
    if sys.platform != "darwin":
        raise RuntimeError("This benchmark supervisor uses macOS process memory accounting")
    library = ctypes.CDLL("/usr/lib/libproc.dylib", use_errno=True)
    library.proc_pid_rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
    library.proc_pid_rusage.restype = ctypes.c_int

    def read(pid):
        usage = ProcessUsage()
        if library.proc_pid_rusage(pid, 0, ctypes.byref(usage)) != 0:
            return None
        return {"rss_bytes": usage.resident_size, "footprint_bytes": usage.phys_footprint}

    if read(os.getpid()) is None:
        raise RuntimeError("Process memory accounting is unavailable")
    return read


def emit(record):
    print(json.dumps(record), flush=True)


def worker(args):
    import grammar_engine as module
    data = load_grammar(args.grammar)
    terminals = {symbol: module.Terminal(symbol) for symbol in data["terminals"]}
    nonterminals = {name: module.Nonterminal(name) for name in data["nonterminals"]}
    symbols = terminals | nonterminals
    alternatives = {name: [] for name in nonterminals}
    for rule in data["productions"]:
        formula = module._join((symbols[symbol] for symbol in rule["rhs"]), module.ConcatenationFormula)
        alternatives[rule["lhs"]].append(formula)
    for name, nt in nonterminals.items():
        nt.definition = module._join(alternatives[name], module.UnionFormula)
    grammar = module.Grammar(terminals.values(), nonterminals.values())
    read_memory = memory_reader()
    emit({"event": "loaded", "nonterminals": len(nonterminals), "terminals": len(terminals),
          "productions": len(data["productions"]), "start": data["start"],
          "cacc_matches": len(grammar.recognize_caccs()), **read_memory(os.getpid())})
    start = time.monotonic()
    completed = 0
    try:
        for level in range(1, args.max_levels + 1):
            emit({"event": "level_begin", "level": level})
            before = time.monotonic()
            findings = grammar.step()
            completed = level
            finding_count = len(findings)
            del findings
            sizes = {nt.name: nt.next.trie.root.size for nt in grammar.nonterminals}
            emit({"event": "level_complete", "level": level,
                  "seconds": time.monotonic() - before,
                  "elapsed_seconds": time.monotonic() - start,
                  "peak_rss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  **read_memory(os.getpid()),
                  "start_sentences": sizes[data["start"]],
                  "summed_nonterminal_sentences": sum(sizes.values()),
                  "largest_languages": sorted(sizes.items(), key=lambda item: item[1], reverse=True)[:5],
                  "new_findings": finding_count, "total_findings": len(grammar.findings)})
    except MemoryError:
        emit({"event": "memory_error", "completed_level": completed, "attempted_level": completed + 1})
        return 3
    return 0


def supervise(args):
    read_memory = memory_reader()
    limit = int(args.memory_gib * 1024 ** 3)
    if limit <= 0 or args.timeout <= 0 or args.max_levels < 1:
        raise ValueError("Memory, time, and level limits must be positive")
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x") as log:
        def record(item):
            log.write(json.dumps(item) + "\n")
            log.flush()
            emit(item)

        record({"event": "configuration", "python": sys.version, "memory_limit_bytes": limit,
                "timeout_seconds": args.timeout, "max_levels": args.max_levels,
                "grammar": str(Path(args.grammar).resolve()),
                "grammar_sha256": hashlib.sha256(Path(args.grammar).read_bytes()).hexdigest(),
                "implementation_sha256": hashlib.sha256(Path(__file__).with_name("grammar_engine.py").read_bytes()).hexdigest(),
                "memory_policy": "Supervisor stops at max(RSS, physical footprint); sampled every 50ms"})
        command = [sys.executable, "-u", str(Path(__file__).resolve()), "--worker",
                   "--grammar", str(Path(args.grammar).resolve()), "--max-levels", str(args.max_levels)]
        stderr_path = output.with_suffix(".stderr.txt")
        with stderr_path.open("x") as errors:
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=errors,
                                       env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
            selector = selectors.DefaultSelector()
            selector.register(process.stdout, selectors.EVENT_READ)
            started = time.monotonic()
            last_heartbeat = started
            last_successful_read = started
            completed = 0
            attempted = 0
            peak = 0
            buffered = b""
            stop_reason = None
            stop_sent = False
            try:
                while True:
                    for key, _ in selector.select(0.05):
                        chunk = os.read(key.fd, 65536)
                        if chunk:
                            buffered += chunk
                            while b"\n" in buffered:
                                line, buffered = buffered.split(b"\n", 1)
                                item = json.loads(line)
                                record(item)
                                if item["event"] == "level_begin":
                                    attempted = item["level"]
                                elif item["event"] == "level_complete":
                                    completed = item["level"]
                                elif item["event"] == "memory_error":
                                    stop_reason = "memory_error"
                        else:
                            selector.unregister(key.fileobj)
                    now = time.monotonic()
                    memory = read_memory(process.pid)
                    if memory is not None:
                        last_successful_read = now
                        peak = max(peak, memory["rss_bytes"], memory["footprint_bytes"])
                        if max(memory.values()) >= limit:
                            stop_reason = "memory_cap"
                    elif now - last_successful_read > 1 and process.poll() is None:
                        stop_reason = "memory_monitor_unavailable"
                    if now - started >= args.timeout:
                        stop_reason = stop_reason or "timeout"
                    if stop_reason and not stop_sent and process.poll() is None:
                        stop_sent = True
                        process.kill()
                        record({"event": "stopped", "reason": stop_reason,
                                "completed_level": completed, "attempted_level": attempted,
                                "elapsed_seconds": now - started, "memory": memory,
                                "sampled_peak_memory_bytes": peak})
                    if now - last_heartbeat >= 10 and process.poll() is None:
                        record({"event": "heartbeat", "completed_level": completed,
                                "attempted_level": attempted, "elapsed_seconds": now - started,
                                "memory": memory, "sampled_peak_memory_bytes": peak})
                        last_heartbeat = now
                    if process.poll() is not None and not selector.get_map():
                        break
            finally:
                if process.poll() is None:
                    process.kill()
                process.wait()
                process.stdout.close()
                selector.close()
            record({"event": "exit", "returncode": process.returncode,
                    "completed_level": completed, "attempted_level": attempted,
                    "reason": stop_reason or ("completed" if process.returncode == 0 else "worker_error"),
                    "elapsed_seconds": time.monotonic() - started,
                    "sampled_peak_memory_bytes": peak, "stderr": str(stderr_path)})


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--grammar", default="roskind/grammar.json")
    parser.add_argument("--memory-gib", type=float, default=2)
    parser.add_argument("--timeout", type=float, default=600)
    parser.add_argument("--max-levels", type=int, default=100)
    parser.add_argument("--output", default="benchmark_results/roskind.jsonl")
    parser.add_argument("--worker", action="store_true")
    options = parser.parse_args()
    if options.worker:
        raise SystemExit(worker(options))
    supervise(options)
