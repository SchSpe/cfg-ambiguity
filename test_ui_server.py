import json
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import ui_server
import ui_storage


# Cfront is not distributed with this repository; README.md says how to add it.
CFRONT = (ui_server.ROOT / "cfront" / "gram.y").exists()


class WorkspaceTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.workspace = ui_server.Workspace(self.directory.name)
        self.workspace.open("expression")

    def tearDown(self):
        self.workspace.cancel()
        if self.workspace.monitor:
            self.workspace.monitor.join(timeout=5)
        self.directory.cleanup()

    def finish(self, expected="idle"):
        monitor = self.workspace.monitor
        if monitor:
            monitor.join(timeout=15)
            self.assertFalse(monitor.is_alive(), "Worker monitor failed to finish")
        state = self.workspace.state()
        self.assertEqual(state["status"], expected, state)
        return state

    def test_real_worker_levels_proofs_and_disk_history_resume(self):
        for level in range(1, 5):
            self.workspace.advance(level)
            state = self.finish()
            self.assertEqual(state["completed_level"], level)
        records = ui_storage.list_findings(self.workspace.snapshot(4))
        self.assertGreater(records["total"], 0)
        record = records["items"][0]
        proof = self.workspace.proof(record["id"])
        self.assertEqual(proof["witness"], record["witness"])
        self.assertEqual(proof["owner"], record["owner"])
        self.assertIs(self.workspace.proof(record["id"]), proof)
        before = ui_storage.page_sentences(self.workspace.snapshot(3), "E")
        restored = ui_server.Workspace(self.directory.name)
        try:
            state = restored.open("expression")
            self.assertEqual(state["completed_level"], 4)
            self.assertEqual(ui_storage.page_sentences(restored.snapshot(3), "E"), before)
            self.assertEqual(restored.proof(record["id"])["witness"], record["witness"])
        finally:
            restored.cancel()

    def test_cancel_then_retry_preserves_completed_level(self):
        self.workspace.advance(1)
        self.finish()
        original = self.workspace.snapshot(1).read_bytes()
        self.workspace.advance(2)
        old_monitor = self.workspace.monitor
        state = self.workspace.cancel()
        self.assertFalse(state["memory"]["worker_alive"])
        self.assertEqual(state["completed_level"], 1)
        self.workspace.advance(2)
        self.finish()
        old_monitor.join(timeout=5)
        self.assertFalse(old_monitor.is_alive())
        self.assertEqual(self.workspace.snapshot(1).read_bytes(), original)
        self.assertEqual(self.workspace.state()["completed_level"], 2)
        self.assertFalse(list(self.workspace.directory.glob("*.tmp*")))

    def test_grammar_switch_does_not_accept_previous_worker_result(self):
        other = "cfront" if CFRONT else "roskind"
        self.workspace.advance(1)
        old_monitor = self.workspace.monitor
        state = self.workspace.open(other)
        old_monitor.join(timeout=5)
        self.assertEqual(state["grammar"]["id"], other)
        self.assertEqual(self.workspace.state()["completed_level"], 0)
        self.assertEqual(self.workspace.state()["grammar"]["id"], other)

    def test_invalid_and_concurrent_advance_requests_are_rejected(self):
        for level in (0, 2, True, 1.5):
            with self.subTest(level=level), self.assertRaises(ValueError):
                self.workspace.advance(level)
        with self.workspace.lock:
            self.workspace.advance(1)
            with self.assertRaises(ValueError):
                self.workspace.advance(1)
        self.finish()
        with self.assertRaises(ValueError):
            self.workspace.snapshot(2)
        with self.assertRaises(ValueError):
            self.workspace.settings(63)

    def test_memory_limit_stops_worker_and_keeps_snapshot_readable(self):
        self.workspace.advance(1)
        self.finish()
        snapshot = self.workspace.snapshot(1)
        before = snapshot.read_bytes()
        sleeper = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(10)"], stdout=subprocess.PIPE)
        try:
            self.workspace.settings(64)
            self.workspace.read_memory = lambda pid: 65 * 1024 ** 2
            with patch.object(ui_server.subprocess, "Popen", return_value=sleeper):
                self.workspace.advance(2)
            state = self.finish("limited")
            self.assertIn("memory limit", state["error"])
            self.assertEqual(state["completed_level"], 1)
            self.assertEqual(snapshot.read_bytes(), before)
            self.assertEqual(ui_storage.page_sentences(snapshot, "F")["items"][0]["tokens"], ["n"])
            self.assertIsNotNone(sleeper.poll())
        finally:
            if sleeper.poll() is None:
                sleeper.kill()
            sleeper.wait()


class HTTPTests(unittest.TestCase):
    def setUp(self):
        try:
            self.server = ui_server.ThreadingHTTPServer(("127.0.0.1", 0), ui_server.Handler)
        except PermissionError as error:
            self.skipTest(f"Localhost binding is not allowed in this sandbox: {error}")
        self.addCleanup(self.server.server_close)
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.server.workspace = ui_server.Workspace(self.directory.name)
        self.addCleanup(self.server.workspace.cancel)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        self.addCleanup(self.shutdown)
        self.base = f"http://127.0.0.1:{self.server.server_port}"

    def shutdown(self):
        self.server.shutdown()
        self.thread.join(timeout=5)
        monitor = self.server.workspace.monitor
        self.server.workspace.cancel()
        if monitor:
            monitor.join(timeout=5)

    def request(self, path, data=None, headers=None):
        body = None if data is None else json.dumps(data).encode()
        request = Request(self.base + path, data=body, headers=headers or {})
        try:
            with urlopen(request, timeout=5) as response:
                return response.status, json.loads(response.read())
        except HTTPError as error:
            return error.code, json.loads(error.read())

    def test_live_json_contract_and_input_errors(self):
        status, catalog = self.request("/api/catalog")
        self.assertEqual(status, 200)
        expected = {"roskind", "expression"} | ({"cfront"} if CFRONT else set())
        self.assertEqual({entry["id"] for entry in catalog["grammars"]}, expected)
        status, state = self.request("/api/session", {"grammar": "expression", "memory_limit_mb": 128})
        self.assertEqual(status, 200)
        self.assertEqual(state["completed_level"], 0)
        status, grammar = self.request("/api/grammar")
        self.assertEqual(status, 200)
        self.assertEqual(len(grammar["rules"]), 5)
        self.assertIn("E", grammar["formulas"])
        status, state = self.request("/api/advance", {"level": 1})
        self.assertEqual(status, 202)
        self.server.workspace.monitor.join(timeout=10)
        status, page = self.request("/api/approximation?level=1&nonterminal=F")
        self.assertEqual(status, 200)
        self.assertEqual(page["items"], [{"rank": "0", "tokens": ["n"]}])
        self.assertEqual(self.request("/api/approximation?level=5&nonterminal=F")[0], 400)
        self.assertEqual(self.request("/api/approximation?level=1&nonterminal=absent")[0], 400)
        self.assertEqual(self.request("/api/approximation?level=1&nonterminal=F&limit=100")[0], 400)
        self.assertEqual(self.request("/api/proof?id=absent")[0], 400)
        self.assertEqual(self.request("/api/settings", {"memory_limit_mb": 0})[0], 400)
        self.assertEqual(self.request("/api/missing")[0], 404)

    def test_untrusted_host_and_origin_are_rejected(self):
        self.assertEqual(self.request("/api/state", headers={"Host": "evil.example"})[0], 403)
        self.assertEqual(self.request("/api/session", {"grammar": "expression"}, {"Origin": "https://evil.example"})[0], 403)


if __name__ == "__main__":
    unittest.main()
