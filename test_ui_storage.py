from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest.mock import patch

import grammar_engine as implementation
import ui_storage


def recursive_grammar():
    terminal = implementation.Terminal("a")
    first = implementation.Nonterminal("S")
    second = implementation.Nonterminal("T")
    first.definition = implementation.UnionFormula(
        implementation.Epsilon(), implementation.ConcatenationFormula(terminal, first),
    )
    second.definition = first
    return implementation.Grammar([terminal], [first, second])


def replace_root(nonterminal, root):
    nonterminal.next._sentences = implementation.Trie._from_root(root)


class SnapshotStorageTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / "snapshot.sqlite"

    def test_round_trip_levels_and_continue_computing(self):
        original = recursive_grammar()
        for level in range(5):
            if level:
                original.step()
            metadata = {"level": level, "seconds": 0.1, "counts": {"S": str(level)}}
            self.assertEqual(ui_storage.save_snapshot(self.path, original, [], metadata), metadata)
            restored = recursive_grammar()
            self.assertEqual(ui_storage.load_languages(self.path, restored), metadata)
            self.assertEqual(ui_storage.read_summary(self.path), metadata)
            self.assertEqual(restored.iteration, level)
            self.assertEqual(restored.findings, [])
            for left, right in zip(original.nonterminals, restored.nonterminals):
                self.assertFalse(right.previous.trie)
                self.assertEqual(list(left.next.trie), list(right.next.trie))
            restored.step()
            reference = recursive_grammar()
            reference.run(level + 1)
            for left, right in zip(reference.nonterminals, restored.nonterminals):
                self.assertEqual(list(left.next.trie), list(right.next.trie))

    def test_epsilon_insertion_order_prefix_and_page_boundaries(self):
        grammar = recursive_grammar()
        expected = [[], ["z"], ["z", "b"], ["a"], [1], ["1"]]
        trie = implementation.Trie(implementation.Sentence.from_symbols(tokens) for tokens in expected)
        replace_root(grammar.nonterminals[0], trie.root)
        ui_storage.save_snapshot(self.path, grammar, [], {"level": 3})
        first = ui_storage.page_sentences(self.path, "S", limit=2)
        self.assertEqual(first["total"], "6")
        self.assertEqual([item["tokens"] for item in first["items"]], expected[:2])
        self.assertEqual([item["rank"] for item in first["items"]], ["0", "1"])
        self.assertTrue(first["has_more"])
        last = ui_storage.page_sentences(self.path, "S", offset=4, limit=2)
        self.assertEqual([item["tokens"] for item in last["items"]], expected[4:])
        self.assertFalse(last["has_more"])
        beyond = ui_storage.page_sentences(self.path, "S", offset=100)
        self.assertEqual(beyond["items"], [])
        self.assertFalse(beyond["has_more"])
        filtered = ui_storage.page_sentences(self.path, "S", prefix=["z"], offset=1)
        self.assertEqual(filtered["total"], "2")
        self.assertEqual(filtered["items"], [{"rank": "1", "tokens": ["z", "b"]}])
        self.assertEqual(filtered["prefix"], ["z"])
        missing = ui_storage.page_sentences(self.path, "S", prefix=["absent"])
        self.assertEqual(missing["total"], "0")
        self.assertEqual(missing["items"], [])
        empty = ui_storage.page_sentences(self.path, "T")
        self.assertEqual(empty["total"], "0")

    def test_huge_shared_dag_saves_without_enumeration_and_rank_selects(self):
        grammar = recursive_grammar()
        root = implementation.TrieNode(accepting=True)
        for _ in range(100):
            root = implementation.TrieNode({0: root, 1: root})
        for nonterminal in grammar.nonterminals:
            replace_root(nonterminal, root)
        with patch.object(implementation.Trie, "__iter__", side_effect=AssertionError("No enumeration")):
            ui_storage.save_snapshot(self.path, grammar, [], {"level": 100})
            page = ui_storage.page_sentences(self.path, "S", offset=2 ** 100 - 2, limit=3)
        self.assertEqual(page["total"], str(2 ** 100))
        self.assertEqual(page["offset"], str(2 ** 100 - 2))
        self.assertEqual([item["tokens"] for item in page["items"]], [[1] * 99 + [0], [1] * 100])
        self.assertFalse(page["has_more"])
        prefixed = ui_storage.page_sentences(self.path, "S", prefix=[1, 0, 1], offset=2 ** 97 - 1)
        self.assertEqual(prefixed["total"], str(2 ** 97))
        self.assertEqual(prefixed["items"][0]["tokens"], [1, 0, 1] + [1] * 97)
        connection = sqlite3.connect(self.path)
        try:
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM nodes").fetchone()[0], 101)
        finally:
            connection.close()
        restored = recursive_grammar()
        ui_storage.load_languages(self.path, restored)
        first, second = restored.nonterminals
        self.assertIs(first.next.trie.root, second.next.trie.root)
        self.assertIs(first.next.trie.root.children[0], first.next.trie.root.children[1])
        self.assertEqual(first.next.trie.root.size, 2 ** 100)
        first.next.trie.add(implementation.Sentence())
        self.assertEqual(second.next.trie.root.size, 2 ** 100)
        self.assertEqual(ui_storage.page_sentences(self.path, "S")["total"], str(2 ** 100))

    def test_deep_trie_does_not_depend_on_recursion_limit(self):
        grammar = recursive_grammar()
        root = implementation.TrieNode(accepting=True)
        for _ in range(2500):
            root = implementation.TrieNode({"a": root})
        replace_root(grammar.nonterminals[0], root)
        ui_storage.save_snapshot(self.path, grammar, [], {"level": 1})
        restored = recursive_grammar()
        ui_storage.load_languages(self.path, restored)
        self.assertEqual(restored.nonterminals[0].next.trie.root.size, 1)
        page = ui_storage.page_sentences(self.path, "S", limit=1)
        self.assertEqual(page["items"], [{"rank": "0", "tokens": ["a"] * 2500}])

    def test_findings_preserve_tokens_ids_and_filter_order(self):
        grammar = recursive_grammar()
        records = [
            {"id": "proof-a", "owner": "S", "kind": "concatenation", "tokens": [1, "1"],
             "factorizations": [[[1], ["1"]], [[], [1, "1"]]]},
            {"id": "proof-b", "owner": "T", "kind": "union", "tokens": []},
            {"id": "proof-c", "owner": "S", "kind": "union", "tokens": ["a"]},
        ]
        ui_storage.save_snapshot(self.path, grammar, records, {"level": 5})
        self.assertEqual(ui_storage.get_finding(self.path, "proof-a"), records[0])
        self.assertEqual(ui_storage.list_findings(self.path), {"total": 3, "items": records})
        self.assertEqual(ui_storage.list_findings(self.path, "S", offset=1, limit=1), {"total": 2, "items": [records[2]]})
        self.assertEqual(ui_storage.list_findings(self.path, offset=10 ** 100), {"total": 3, "items": []})

    def test_default_finding_ids_do_not_modify_caller_records(self):
        records = [{"nonterminal": "S", "kind": "union"}]
        ui_storage.save_snapshot(self.path, recursive_grammar(), records, {"level": 0})
        self.assertNotIn("id", records[0])
        expected = dict(records[0], id=0)
        self.assertEqual(ui_storage.get_finding(self.path, 0), expected)
        self.assertEqual(ui_storage.get_finding(self.path, "0"), expected)
        self.assertEqual(ui_storage.list_findings(self.path, "S")["items"], [expected])

    def test_failed_write_preserves_last_committed_snapshot_and_cleans_temporary(self):
        grammar = recursive_grammar()
        ui_storage.save_snapshot(self.path, grammar, [], {"level": 0})
        original = self.path.read_bytes()
        grammar.step()
        with self.assertRaises(TypeError):
            ui_storage.save_snapshot(self.path, grammar, [{"bad": object()}], {"level": 1})
        self.assertEqual(self.path.read_bytes(), original)
        self.assertEqual(list(Path(self.directory.name).iterdir()), [self.path])
        self.assertEqual(ui_storage.read_summary(self.path), {"level": 0})

    def test_missing_snapshot_does_not_create_a_file(self):
        with self.assertRaises(sqlite3.OperationalError):
            ui_storage.read_summary(self.path)
        self.assertFalse(self.path.exists())

    def test_bad_request_arguments_are_rejected(self):
        ui_storage.save_snapshot(self.path, recursive_grammar(), [], {"level": 0})
        with self.assertRaises(KeyError):
            ui_storage.page_sentences(self.path, "absent")
        with self.assertRaises(KeyError):
            ui_storage.get_finding(self.path, "absent")
        for offset in (-1, 0.5, "bad", True):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                ui_storage.page_sentences(self.path, "S", offset=offset)
        for limit in (0, 51, 1.5, True):
            with self.subTest(limit=limit), self.assertRaises(ValueError):
                ui_storage.page_sentences(self.path, "S", limit=limit)
        for prefix in ("a", [object()], 1):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                ui_storage.page_sentences(self.path, "S", prefix=prefix)

    def test_wrong_grammar_fails_before_changing_existing_state(self):
        original = recursive_grammar()
        ui_storage.save_snapshot(self.path, original, [], {"level": 0})
        target = recursive_grammar()
        target.run(3)
        target.nonterminals[0].name = "Other"
        old_root = target.nonterminals[0].next.trie.root
        with self.assertRaises(ValueError):
            ui_storage.load_languages(self.path, target)
        self.assertEqual(target.iteration, 3)
        self.assertIs(target.nonterminals[0].next.trie.root, old_root)


if __name__ == "__main__":
    unittest.main()
