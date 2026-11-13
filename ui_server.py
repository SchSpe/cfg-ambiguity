import argparse
from collections import Counter, deque
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import mimetypes
import os
from pathlib import Path
import selectors
import shutil
import subprocess
import sys
import threading
import time
from urllib.parse import parse_qs, urlparse

from grammar_io import load_grammar, validate_grammar
from ui_proofs import build_grammar, finding_from_record, serialize_finding, summarize_finding
from ui_storage import get_finding, list_findings, load_languages, page_sentences, read_summary, save_snapshot


ROOT = Path(__file__).resolve().parent
STATIC = ROOT / "ui"
SESSION_REQUEST_BYTES = 2_000_000   # a posted grammar; Roskind is about 60 KB
REQUEST_BYTES = 10_000              # every other request
KEPT_CUSTOM_CACHES = 16             # cache directories of posted grammars kept on disk
STALE_CACHE_SECONDS = 7 * 24 * 3600 # posted grammars' caches unused this long are removed at start-up
DRAIN_BYTES = 64_000_000            # an oversized request body is read and dropped up to this size
MAX_LEVELS_PER_RUN = 30
LEVEL_SECONDS = 600                 # a worker that spends this long on one level is stopped


class SessionChanged(Exception):
    """A request named a grammar other than the one open on the server."""


def grammar_ids():
    # Cfront is not distributed; it is listed once fetched and converted (see GRAMMAR_SOURCES.txt).
    return [name for name in ("roskind", "expression", "cfront")
            if name != "cfront" or (ROOT / "cfront" / "grammar.json").exists()]


def dataset(name):
    if name in ("roskind", "cfront"):
        path = ROOT / name / "grammar.json"
        if not path.exists():
            raise ValueError(f"{name}/grammar.json is missing; see CONVERTED_GRAMMARS.txt")
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


def custom_grammar(data):
    """A grammar posted by the workspace page, stripped to the fields the
    engine reads and checked like a grammar.json file. The caps keep the
    engine's recursive formula code well inside Python's recursion limit."""
    if not isinstance(data, dict):
        raise ValueError("Send a grammar name or cfg-productions-v1 grammar data")
    productions = data.get("productions")
    if not isinstance(productions, list) or not productions:
        raise ValueError("The grammar has no productions")
    if len(productions) > 3000:
        raise ValueError("A grammar can have at most 3000 productions here")
    if not all(isinstance(rule, dict) for rule in productions):
        raise ValueError("Each production must be an object with lhs and rhs")
    name = data.get("name")
    grammar = {
        "format": "cfg-productions-v1",
        "name": name.strip()[:200] if isinstance(name, str) and name.strip() else "Workspace grammar",
        "start": data.get("start"),
        "terminals": data.get("terminals"),
        "nonterminals": data.get("nonterminals"),
        "productions": [{"lhs": rule.get("lhs"), "rhs": rule.get("rhs")} for rule in productions],
    }
    validate_grammar(grammar)
    if max(Counter(rule["lhs"] for rule in grammar["productions"]).values()) > 400:
        raise ValueError("A nonterminal can have at most 400 alternatives here")
    if any(len(rule["rhs"]) > 200 for rule in grammar["productions"]):
        raise ValueError("A right-hand side can have at most 200 symbols here")
    if any(not 1 <= len(symbol) <= 200 for symbol in grammar["terminals"] + grammar["nonterminals"]):
        raise ValueError("Symbol names must be 1 to 200 characters long")
    for symbol in grammar["terminals"] + grammar["nonterminals"]:
        try:
            symbol.encode("utf-8")
        except UnicodeEncodeError:
            raise ValueError("Symbol names must be valid Unicode text") from None
    grammar["name"] = grammar["name"].encode("utf-8", "replace").decode("utf-8")
    return grammar


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
    if sys.platform == "win32":
        return windows_memory_reader()
    raise RuntimeError("Memory monitoring currently supports macOS, Linux and Windows")


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


def summary(grammar, seconds, memory, findings):
    return {"level": grammar.iteration, "seconds": seconds,
            "counts": {nt.name: str(nt.next.trie.root.size) for nt in grammar.nonterminals},
            "findings_count": len(findings),
            "findings_by_nonterminal": dict(Counter(item["owner"] for item in findings)),
            "memory_bytes": memory, "created_at": time.time()}


def level_file(directory, level):
    return Path(directory) / f"level-{level}.sqlite"


def cache_key(name, data):
    """The name of a grammar's cache directory. It changes with the grammar
    and with the code that computes and saves its levels, so no cache is
    read by code that would have saved something else."""
    fingerprint = hashlib.sha256(json.dumps(data, sort_keys=True).encode())
    for filename in ("grammar_engine.py", "ui_proofs.py", "ui_storage.py", "ui_server.py"):
        fingerprint.update((ROOT / filename).read_bytes())
    return f"{name}-{fingerprint.hexdigest()[:16]}"


def prepare_directory(directory, data, grammar):
    """Give a grammar's cache directory its grammar.json and level 0, where
    every language is empty, unless it has them; return the summaries of the
    levels saved there, from level 0 up."""
    directory.mkdir(exist_ok=True)
    os.utime(directory)
    grammar_file = directory / "grammar.json"
    if not grammar_file.exists():
        temporary = grammar_file.with_name(f"grammar.json.{os.getpid()}.tmp")
        temporary.write_text(json.dumps(data), encoding="utf-8")
        os.replace(temporary, grammar_file)
    if not level_file(directory, 0).exists():
        save_snapshot(level_file(directory, 0), grammar, [], summary(grammar, 0, 0, []))
    levels = []
    while level_file(directory, len(levels)).exists():
        levels.append(read_summary(level_file(directory, len(levels))))
    return levels


def prune_stale(cache, prefix):
    """Remove the cache directories named prefix-... unused for a week."""
    cutoff = time.time() - STALE_CACHE_SECONDS
    for path in Path(cache).glob(f"{prefix}-*"):
        try:
            if path.is_dir() and path.stat().st_mtime < cutoff:
                shutil.rmtree(path, ignore_errors=True)
        except OSError:
            continue


def worker(args):
    """Compute levels first..through of the grammar saved in the cache
    directory, saving each level's snapshot as soon as it is done."""
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
    read_memory = memory_reader()

    def emit(**event):
        print(json.dumps(event), flush=True)

    emit(phase="loading", level=args.first)
    load_languages(level_file(directory, args.first - 1), grammar)
    for level in range(args.first, args.through + 1):
        emit(phase="computing", level=level)
        started = time.monotonic()
        findings = grammar.step()
        seconds = time.monotonic() - started
        emit(phase="saving", level=level)
        records = []
        for finding in findings:
            record = summarize_finding(finding, catalog)
            record["raw_factorizations"] = [
                [left.symbols, right.symbols] for left, right in finding.factorizations
            ] if finding.factorizations else None
            records.append(record)
        details = summary(grammar, seconds, read_memory(os.getpid()) or 0, records)
        save_snapshot(level_file(directory, level), grammar, records, details)
        emit(saved=True, level=grammar.iteration)


def start_worker(directory, first, through):
    """Start a worker on levels first..through of the grammar cached in
    `directory`; return the process and the file its errors go to."""
    # The worker runs in ROOT, so a relative directory is resolved here.
    command = [sys.executable, "-u", str(Path(__file__).resolve()), "--worker", "--exit-with-parent",
               "--directory", str(Path(directory).resolve()), "--first", str(first), "--through", str(through)]
    error_path = Path(directory) / f"level-{first}.stderr.txt"
    errors = error_path.open("w")
    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=errors,
                               env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}, cwd=ROOT)
    errors.close()
    return process, error_path


def follow_worker(process, read_memory, memory_limit, *, deadline=None,
                  on_event=None, on_memory=None, cancelled=None):
    """Watch a worker until it exits, passing each JSON line it prints to
    on_event and each reading of its memory to on_memory. The worker is
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
                if on_memory is not None:
                    on_memory(memory)
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
    """Make sure a worker has exited, and remove any snapshot it left half written."""
    if process.poll() is None:
        process.kill()
    process.wait()
    process.stdout.close()
    if process.stdin is not None:
        process.stdin.close()
    for incomplete in Path(directory).glob(f"level-*.sqlite.{process.pid}.*.tmp*"):
        incomplete.unlink(missing_ok=True)


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
        self.through = None
        self.levels = []
        self.catalog = None
        self.grammar_description = None
        self.proof_cache = {}
        self.custom_keys = {}   # posted grammars this server opened, oldest first
        self._prune_stale_custom()
        self.open("roskind")

    def file(self, level):
        return level_file(self.directory, level)

    def open(self, grammar, memory_limit_mb=None):
        """Open a built-in grammar by name, or grammar data posted by the
        workspace page. Levels already computed for it are reloaded. Opening
        the grammar that is already open changes nothing, so a running search
        or the reason a search stopped is kept."""
        if isinstance(grammar, str):
            name, data = grammar, dataset(grammar)
        else:
            name, data = "custom", custom_grammar(grammar)
        catalog = build_grammar(data)
        key = cache_key(name, data)
        directory = self.cache / key
        with self.lock:
            if memory_limit_mb is not None:
                self.settings(memory_limit_mb)
            if self.grammar_description and self.grammar_description["key"] == key \
                    and level_file(directory, 0).exists():
                os.utime(directory)
                return self.state()
            # Prepare the new directory before switching, so a failure here
            # leaves the open grammar as it was.
            levels = prepare_directory(directory, data, catalog.grammar)
            self._stop()
            self.generation += 1
            self.catalog = catalog
            self.data = data
            self.grammar_description = {**describe(name, data), "key": key}
            self.directory = directory
            self.levels = levels
            if name == "custom":
                self._prune_custom(key)
            self.status = "idle"
            self.phase = None
            self.error = None
            self.target = None
            self.through = None
            self.used_memory = 0
            self.peak_memory = 0
            self.memory_history.clear()
            self.proof_cache.clear()
            self.revision += 1
            return self.state()

    def _prune_custom(self, key):
        """Each edit in the workspace posts a new grammar with its own cache.
        Keep the caches of the grammars this server opened most recently.
        Another server may share the cache folder, so only this server's
        own caches are removed here; old ones are cleared at start-up."""
        self.custom_keys.pop(key, None)
        self.custom_keys[key] = True
        while len(self.custom_keys) > KEPT_CUSTOM_CACHES:
            oldest = next(iter(self.custom_keys))
            del self.custom_keys[oldest]
            shutil.rmtree(self.cache / oldest, ignore_errors=True)

    def _prune_stale_custom(self):
        """Remove posted grammars' caches unused for a week."""
        prune_stale(self.cache, "custom")

    def check(self, key):
        """Refuse a request about a grammar that is no longer the open one."""
        if key is not None and key != self.grammar_description["key"]:
            raise SessionChanged("Another grammar is open on the server now")

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
                    "through_level": self.through,
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
            self.through = None
            self.used_memory = 0
            self.error = "Computation cancelled. Completed levels are still available." if running else None
            self.revision += 1
            return self.state()

    def advance(self, level, through=None, key=None):
        """Compute the next level, or every level from the next one through
        `through`, in one worker process. Levels already on disk are reused.
        With `key`, refuse unless that grammar is still the open one."""
        with self.lock:
            self.check(key)
            if self.status == "computing":
                raise ValueError("A level is already being computed")
            if isinstance(level, bool) or not isinstance(level, int) or level != len(self.levels):
                raise ValueError("Advance one level beyond the last completed level")
            through = level if through is None else through
            if isinstance(through, bool) or not isinstance(through, int) or \
                    not level <= through <= level + MAX_LEVELS_PER_RUN - 1:
                raise ValueError(f"Choose a last level from {level} to {level + MAX_LEVELS_PER_RUN - 1}")
            while level <= through and self.file(level).exists():
                self.levels.append(read_summary(self.file(level)))
                level += 1
            if level > through:
                self.revision += 1
                return self.state()
            process, error_path = start_worker(self.directory, level, through)
            self.process = process
            self.status = "computing"
            self.phase = "loading"
            self.error = None
            self.target = level
            self.through = through
            self.used_memory = 0
            self.peak_memory = 0
            self.memory_history.clear()
            self.revision += 1
            generation = self.generation
            self.monitor = threading.Thread(target=self._watch,
                                            args=(process, generation, through, error_path), daemon=True)
            self.monitor.start()
            return self.state()

    def _record_saved(self, through):
        """Add every level the worker has saved so far. Called with the lock held."""
        added = False
        while len(self.levels) <= through and self.file(len(self.levels)).exists():
            details = read_summary(self.file(len(self.levels)))
            details["memory_bytes"] = max(details.get("memory_bytes", 0), self.peak_memory)
            self.levels.append(details)
            added = True
        if added:
            # The target stays on the last level until _watch sees the worker exit.
            if len(self.levels) <= through:
                self.target = len(self.levels)
            self.revision += 1
        return added

    def _watch(self, process, generation, through, error_path):
        started = sampled = time.monotonic()

        def on_event(event):
            with self.lock:
                if generation != self.generation:
                    return
                if "phase" in event:
                    self.phase = event["phase"]
                if event.get("saved"):
                    self._record_saved(through)

        def on_memory(memory):
            nonlocal sampled
            now = time.monotonic()
            with self.lock:
                if generation != self.generation:
                    return
                self.used_memory = memory
                self.peak_memory = max(self.peak_memory, memory)
                if now - sampled >= 0.5:
                    self.memory_history.append({"time": now - started, "bytes": memory})
                    sampled = now

        try:
            reason = follow_worker(process, self.read_memory, lambda: self.memory_limit,
                                   on_event=on_event, on_memory=on_memory,
                                   cancelled=lambda: generation != self.generation)
            if reason == "cancelled":
                return
            process.wait()
            with self.lock:
                if generation != self.generation:
                    return
                limited = {
                    "memory": f"Level {self.target} stopped at the {self.memory_limit // 1024 ** 2} MiB memory limit. Completed levels are preserved.",
                    "monitor": "Memory monitoring stopped responding. Computation stopped; completed levels are preserved.",
                    "level time": "The level exceeded 10 minutes. Completed levels are preserved.",
                }.get(reason)
                # Levels saved just before the worker exited may not have been reported yet.
                self._record_saved(through)
                if len(self.levels) > through:
                    self.status = "idle"
                    self.error = None
                elif limited:
                    self.status = "limited"
                    self.error = limited
                else:
                    self.status = "error"
                    error = error_path.read_text()[-1500:]
                    self.error = "The level could not finish. Completed levels are preserved. " + error
                self.process = None
                self.phase = None
                self.target = None
                self.through = None
                self.used_memory = 0
                self.revision += 1
        finally:
            end_worker(process, error_path.parent)

    def snapshot(self, level, key=None):
        with self.lock:
            self.check(key)
            if level < 0 or level >= len(self.levels):
                raise ValueError("That approximation level has not completed")
            return self.file(level)

    def proof(self, identifier, key=None):
        with self.lock:
            self.check(key)
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
        proof = serialize_finding(finding_from_record(record, catalog), catalog)
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
                path = workspace.snapshot(int(query.get("level", 0)), query.get("key"))
                result = page_sentences(path, query["nonterminal"], int(query.get("offset", 0)),
                                        int(query.get("limit", 24)),
                                        json.loads(query["prefix"]) if query.get("prefix") else None)
            elif parsed.path == "/api/findings":
                path = workspace.snapshot(int(query.get("level", 0)), query.get("key"))
                result = list_findings(path, query.get("nonterminal"), int(query.get("offset", 0)),
                                       int(query.get("limit", 25)))
            elif parsed.path == "/api/proof":
                result = workspace.proof(query["id"], query.get("key"))
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
        except SessionChanged as error:
            self.send_json({"error": str(error), "grammar": workspace.state()["grammar"]}, 409)
        except (ValueError, KeyError, TypeError) as error:
            self.send_json({"error": str(error)}, 400)
        except BrokenPipeError:
            pass
        except Exception as error:
            self.send_json({"error": f"The request could not finish: {error}"}, 500)

    def discard_body(self, length):
        """Read and drop a request body, so the client gets the reply rather
        than a reset connection. Very large bodies just close the connection."""
        if length > DRAIN_BYTES:
            self.close_connection = True
            return
        while length > 0:
            chunk = self.rfile.read(min(length, 65536))
            if not chunk:
                break
            length -= len(chunk)

    def do_POST(self):
        if not self.allowed_origin():
            return self.send_json({"error": "This workbench is local to this computer"}, 403)
        workspace = self.server.workspace
        try:
            length = int(self.headers.get("Content-Length", 0))
            if length < 0:
                raise ValueError("Content-Length must not be negative")
            session = self.path == "/api/session"
            if length > (SESSION_REQUEST_BYTES if session else REQUEST_BYTES):
                self.discard_body(length)
                message = (f"The grammar is larger than {SESSION_REQUEST_BYTES // 1_000_000} MB, too large for the engine"
                           if session else "Request too large")
                return self.send_json({"error": message}, 413)
            data = json.loads(self.rfile.read(length) or b"{}")
            if not isinstance(data, dict):
                raise ValueError("Send a JSON object")
            if session:
                result = workspace.open(data["grammar"], data.get("memory_limit_mb"))
            elif self.path == "/api/advance":
                result = workspace.advance(data["level"], data.get("through"), data.get("key"))
            elif self.path == "/api/cancel":
                result = workspace.cancel()
            elif self.path == "/api/settings":
                result = workspace.settings(data["memory_limit_mb"])
            else:
                return self.send_json({"error": "Unknown request"}, 404)
            self.send_json(result, 202 if self.path == "/api/advance" else 200)
        except SessionChanged as error:
            self.send_json({"error": str(error), "grammar": workspace.state()["grammar"]}, 409)
        except (ValueError, KeyError, TypeError) as error:
            self.send_json({"error": str(error)}, 400)
        except RecursionError:
            self.send_json({"error": "The grammar is nested too deeply for the engine"}, 400)
        except BrokenPipeError:
            pass
        except Exception as error:
            self.send_json({"error": f"The request could not finish: {error}"}, 500)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--cache", type=Path, default=ROOT / ".ui_cache")
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--exit-with-parent", action="store_true")
    parser.add_argument("--directory")
    parser.add_argument("--first", type=int)
    parser.add_argument("--through", type=int)
    args = parser.parse_args()
    if args.worker:
        return worker(args)
    workspace = Workspace(args.cache)
    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    server.workspace = workspace
    print(f"Grammar workbench: http://127.0.0.1:{server.server_port}", flush=True)
    print(f"Grammar workspace: http://127.0.0.1:{server.server_port}/workspace.html", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        workspace.cancel()
        server.server_close()


if __name__ == "__main__":
    main()
