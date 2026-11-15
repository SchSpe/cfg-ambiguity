"""Run grammar analysis in a limited worker and retain each completed level."""

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import selectors
import subprocess
import sys
import tempfile
import threading
import time

from grammar_proofs import build_grammar, summarize_finding


ROOT = Path(__file__).resolve().parent
LEVEL_SECONDS = 600  # Stop a worker that spends this long on one level.


def grammar_data(cfg):
    """Prepare parsed productions for the worker, checking the engine's limits."""
    if len(cfg.productions) > 3000:
        raise ValueError("A grammar can have at most 3000 productions here")
    if max(Counter(lhs for lhs, _ in cfg.productions).values()) > 400:
        raise ValueError("A nonterminal can have at most 400 alternatives here")
    if any(len(rhs) > 200 for _, rhs in cfg.productions):
        raise ValueError("A right-hand side can have at most 200 symbols here")
    symbols = cfg.terminals + cfg.nonterminals
    if any(not 1 <= len(symbol) <= 200 for symbol in symbols):
        raise ValueError("Symbol names must be 1 to 200 characters long")
    for symbol in symbols:
        try:
            symbol.encode("utf-8")
        except UnicodeEncodeError:
            raise ValueError("Symbol names must be valid Unicode text") from None
    return {"start": cfg.start, "terminals": list(cfg.terminals),
            "nonterminals": list(cfg.nonterminals),
            "productions": [{"lhs": lhs, "rhs": list(rhs)} for lhs, rhs in cfg.productions]}


def memory_reader():
    if sys.platform == "darwin":
        return macos_memory_reader()
    if sys.platform.startswith("linux"):
        def read(pid):
            try:
                fields = Path(f"/proc/{pid}/statm").read_text().split()
                return int(fields[1]) * os.sysconf("SC_PAGE_SIZE")
            except (FileNotFoundError, PermissionError, IndexError):
                return None
        return read
    if sys.platform == "win32":
        return windows_memory_reader()
    raise RuntimeError("Memory monitoring currently supports macOS, Linux and Windows")


def macos_memory_reader():
    import ctypes

    class ProcessUsage(ctypes.Structure):
        _fields_ = [("uuid", ctypes.c_uint8 * 16)] + [
            (name, ctypes.c_uint64) for name in (
                "user_time", "system_time", "pkg_idle_wkups", "interrupt_wkups",
                "pageins", "wired_size", "resident_size", "phys_footprint",
                "proc_start_abstime", "proc_exit_abstime",
            )
        ]

    library = ctypes.CDLL("/usr/lib/libproc.dylib", use_errno=True)
    library.proc_pid_rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
    library.proc_pid_rusage.restype = ctypes.c_int

    def read(pid):
        usage = ProcessUsage()
        if library.proc_pid_rusage(pid, 0, ctypes.byref(usage)) != 0:
            return None
        return max(usage.resident_size, usage.phys_footprint)

    if read(os.getpid()) is None:
        raise RuntimeError("Process memory accounting is unavailable")
    return read


def windows_memory_reader():
    import ctypes
    from ctypes import wintypes

    class ProcessMemoryCounters(ctypes.Structure):
        _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD),
                    ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                    ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                    ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t),
                    ("PrivateUsage", ctypes.c_size_t)]

    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel32.OpenProcess.restype = wintypes.HANDLE
    kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
    kernel32.K32GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.c_void_p, wintypes.DWORD]
    kernel32.K32GetProcessMemoryInfo.restype = wintypes.BOOL
    query_limited_information = 0x1000

    # Like the macOS reader's max of resident size and footprint: the working set,
    # or the private committed bytes when Windows has trimmed pages to the page file.
    def read(pid):
        handle = kernel32.OpenProcess(query_limited_information, False, pid)
        if not handle:
            return None
        try:
            counters = ProcessMemoryCounters(cb=ctypes.sizeof(ProcessMemoryCounters))
            if not kernel32.K32GetProcessMemoryInfo(handle, ctypes.byref(counters), counters.cb):
                return None
            return max(counters.WorkingSetSize, counters.PrivateUsage)
        finally:
            kernel32.CloseHandle(handle)

    return read


class WindowsPipeSelector:
    """The part of the selectors API that the worker monitor uses, for a pipe on
    Windows, where select() accepts only sockets."""

    def __init__(self):
        import ctypes
        from ctypes import wintypes
        import msvcrt

        kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        peek = kernel32.PeekNamedPipe
        peek.argtypes = [wintypes.HANDLE, ctypes.c_void_p, wintypes.DWORD, ctypes.c_void_p,
                         ctypes.POINTER(wintypes.DWORD), ctypes.c_void_p]
        peek.restype = wintypes.BOOL

        # A failed peek means the worker closed its end, so reading returns b"".
        def readable(fd):
            available = wintypes.DWORD()
            if not peek(msvcrt.get_osfhandle(fd), None, 0, None, ctypes.byref(available), None):
                return True
            return available.value > 0

        self.readable = readable
        self.keys = {}

    def register(self, fileobj, events):
        self.keys[fileobj] = selectors.SelectorKey(fileobj, fileobj.fileno(), events, None)

    def unregister(self, fileobj):
        del self.keys[fileobj]

    def select(self, timeout):
        deadline = time.monotonic() + timeout
        while True:
            ready = [(key, selectors.EVENT_READ) for key in self.keys.values() if self.readable(key.fd)]
            if ready or time.monotonic() >= deadline:
                return ready
            time.sleep(0.005)

    def close(self):
        self.keys.clear()


def summary(grammar, findings):
    return {"level": grammar.iteration,
            "counts": {nt.name: str(nt.next.trie.root.size) for nt in grammar.nonterminals},
            "findings_count": len(findings)}


def level_file(directory, level):
    return Path(directory) / f"level-{level}.json"


def _write_json(path, data):
    """Publish a complete checkpoint atomically, so interrupted writes are ignored."""
    descriptor, temporary = tempfile.mkstemp(prefix=f"{path.name}.{os.getpid()}.", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as output:
            json.dump(data, output, separators=(",", ":"), allow_nan=False)
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def prepare_directory(directory, data):
    """Initialize an empty temporary directory for a fresh run, starting at level 0."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    if any(directory.iterdir()):
        raise ValueError("The run directory must be empty")
    details = {"level": 0, "counts": {name: "0" for name in data["nonterminals"]},
               "findings_count": 0}
    _write_json(directory / "grammar.json", data)
    _write_json(level_file(directory, 0), {"summary": details, "findings": []})
    return [details]


def read_summary(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))["summary"]


def read_findings(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))["findings"]


def worker(args):
    """Compute a fresh grammar, writing only completed summaries and findings."""
    if args.exit_with_parent:
        def exit_with_parent():
            # The parent holds the other end of stdin, which closes when it
            # exits or is killed; a worker left behind would compute on. The
            # raw read leaves sys.stdin's lock free for interpreter shutdown.
            try:
                while os.read(sys.stdin.fileno(), 4096):
                    pass
            finally:
                os._exit(1)
        threading.Thread(target=exit_with_parent, daemon=True).start()
    directory = Path(args.directory)
    catalog = build_grammar(json.loads((directory / "grammar.json").read_text(encoding="utf-8")))
    grammar = catalog.grammar
    def emit(**event):
        print(json.dumps(event), flush=True)

    for level in range(1, args.through + 1):
        emit(phase="computing", level=level)
        findings = grammar.step()
        emit(phase="saving", level=level)
        records = []
        for finding in findings:
            record = summarize_finding(finding, catalog)
            record["raw_factorizations"] = [
                [left.symbols, right.symbols] for left, right in finding.factorizations
            ] if finding.factorizations else None
            records.append(record)
        details = summary(grammar, records)
        _write_json(level_file(directory, level), {"summary": details, "findings": records})
        grammar.findings.clear()
        emit(saved=True, level=grammar.iteration)


def start_worker(directory, through):
    """Start a fresh worker; return its process and the file its errors go to."""
    # The worker runs in ROOT, so a relative directory is resolved here.
    command = [sys.executable, "-u", str(Path(__file__).resolve()), "--worker", "--exit-with-parent",
               "--directory", str(Path(directory).resolve()), "--through", str(through)]
    error_path = Path(directory) / "worker.stderr.txt"
    with error_path.open("w", encoding="utf-8") as errors:
        process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=errors,
                                   env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}, cwd=ROOT)
    return process, error_path


def follow_worker(process, read_memory, memory_limit, *, deadline=None,
                  on_event=None, cancelled=None):
    """Watch a worker until it exits, passing each JSON line it prints to
    on_event. The worker is
    killed, and the reason returned, when its memory reaches memory_limit()
    bytes ("memory"), one level takes LEVEL_SECONDS ("level time"),
    time.monotonic() passes `deadline` ("deadline"), or its memory can't be
    read for 2 seconds ("monitor"). Once cancelled() is true this returns
    "cancelled" at once, leaving the worker to the caller. None means the
    worker exited by itself."""
    last_read = level_started = time.monotonic()
    buffered = b""
    reason = None
    selector = WindowsPipeSelector() if sys.platform == "win32" else selectors.DefaultSelector()
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
                        if event.get("saved"):
                            level_started = time.monotonic()
                        if on_event is not None:
                            on_event(event)
                else:
                    selector.unregister(key.fileobj)
            if cancelled is not None and cancelled():
                return "cancelled"
            now = time.monotonic()
            memory = read_memory(process.pid)
            if memory is not None:
                last_read = now
                if memory >= memory_limit():
                    reason = reason or "memory"
            elif now - last_read > 2 and process.poll() is None:
                reason = reason or "monitor"
            if now - level_started > LEVEL_SECONDS:
                reason = reason or "level time"
            if deadline is not None and now >= deadline:
                reason = reason or "deadline"
            if reason and process.poll() is None:
                process.kill()
        return reason
    finally:
        selector.close()


def end_worker(process, directory):
    """Make sure a worker has exited, and remove any checkpoint it left half written."""
    if process.poll() is None:
        process.kill()
    process.wait()
    process.stdout.close()
    if process.stdin is not None:
        process.stdin.close()
    for incomplete in Path(directory).glob(f"level-*.json.{process.pid}.*.tmp"):
        incomplete.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", action="store_true", required=True)
    parser.add_argument("--exit-with-parent", action="store_true")
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--through", type=int, required=True)
    args = parser.parse_args()
    if args.through < 1:
        parser.error("worker level must be at least 1")
    return worker(args)


if __name__ == "__main__":
    main()
