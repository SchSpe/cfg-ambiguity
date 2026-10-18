import random
import unittest
from unittest.mock import patch

import grammar_engine as engine

Grammar = engine.Grammar


def productions(grammar):
    return list(grammar.cfg.productions)


class GrammarRandomTests(unittest.TestCase):
    def test_seed_is_reproducible_and_does_not_change_global_random_state(self):
        state = random.getstate()
        first = Grammar.random(3, 3, 1, seed=42)
        second = Grammar.random(3, 3, 1, seed=42)
        self.assertEqual(productions(first), productions(second))
        self.assertEqual(random.getstate(), state)
        others = {tuple(productions(Grammar.random(3, 3, 1, seed=seed))) for seed in range(10)}
        self.assertGreater(len(others), 1)

    def test_same_grammar_as_generate_grammar_in_the_project_root(self):
        # random_grammar.generate_grammar(3, 3, 1, seed=42), written out.
        self.assertEqual(productions(Grammar.random(3, 3, 1, seed=42)), [
            ("S", ("t2",)),
            ("N0", ("N1",)), ("N0", ("t2",)),
            ("N1", ("t2", "t1", "N0")),
            ("N2", ("N0", "N0")), ("N2", ("N1",)), ("N2", ("t1",)), ("N2", ()),
        ])

    def test_symbol_pools_alternative_bounds_and_epsilon_count(self):
        ordinary = {f"N{i}" for i in range(4)}
        terminals = {f"t{i}" for i in range(4)}
        for seed in range(20):
            with self.subTest(seed=seed):
                grammar = Grammar.random(3, 4, 2, num_symbols=4, seed=seed)
                self.assertIsInstance(grammar, Grammar)
                self.assertEqual(grammar.cfg.start, "S")
                self.assertEqual(grammar.nonterminals[0].name, "S")
                rules = productions(grammar)
                self.assertEqual({lhs for lhs, _ in rules}, ordinary | {"S"})
                empty = [lhs for lhs, rhs in rules if not rhs]
                self.assertEqual(len(empty), 2)
                self.assertEqual(len(set(empty)), 2)
                self.assertTrue(set(empty) <= ordinary)
                for name in ordinary | {"S"}:
                    nonempty = [rhs for lhs, rhs in rules if lhs == name and rhs]
                    self.assertTrue(1 <= len(nonempty) <= 3)
                    for rhs in nonempty:
                        self.assertTrue(1 <= len(rhs) <= 4)
                        self.assertTrue(set(rhs) <= ordinary | terminals)

    def test_epsilon_is_added_after_the_nonempty_alternatives(self):
        rules = productions(Grammar.random(1, 1, 3, num_symbols=3, seed=7))
        self.assertEqual(len([rhs for lhs, rhs in rules if lhs == "S"]), 1)
        for i in range(3):
            alternatives = [rhs for lhs, rhs in rules if lhs == f"N{i}"]
            self.assertEqual(len(alternatives), 2)
            self.assertEqual(len(alternatives[0]), 1)
            self.assertEqual(alternatives[1], ())

    def test_repeated_alternatives_are_kept_and_found_ambiguous(self):
        # Force S ::= t0 | t0 and N0 ::= t0 | t0.
        with patch("grammar_engine.Random") as random_class:
            rng = random_class.return_value
            rng.sample.return_value = []
            rng.randint.side_effect = [2, 1, 1, 2, 1, 1]
            rng.choice.return_value = "t0"
            grammar = Grammar.random(2, 1, 0, num_symbols=1)
        self.assertEqual(productions(grammar), [
            ("S", ("t0",)), ("S", ("t0",)), ("N0", ("t0",)), ("N0", ("t0",)),
        ])
        _, unions, _ = grammar.approximate(1)
        self.assertEqual([finding.production_indices for finding in unions], [(0, 1), (2, 3)])

    def test_random_grammars_can_be_approximated_and_displayed(self):
        for seed in range(10):
            with self.subTest(seed=seed):
                grammar = Grammar.random(3, 3, 1, seed=seed)
                languages, _, _ = grammar.approximate(3)
                self.assertEqual(set(languages), {nt.name for nt in grammar.nonterminals})
                self.assertIn("Summary at level 3", grammar.summary())

    def test_invalid_parameters(self):
        valid = dict(max_alts=2, max_tokens=2, max_epsilon=0, num_symbols=2)
        for name in valid:
            for value in (True, 1.5, "2", None):
                with self.subTest(name=name, value=value):
                    with self.assertRaises(TypeError):
                        Grammar.random(**(valid | {name: value}))
        for name, value in (
            ("max_alts", 0), ("max_tokens", 0),
            ("max_epsilon", -1), ("max_epsilon", 3), ("num_symbols", 0),
        ):
            with self.subTest(name=name, value=value):
                with self.assertRaises(ValueError):
                    Grammar.random(**(valid | {name: value}))
        with self.assertRaises(TypeError):
            Grammar.random(**valid, seed=True)


if __name__ == "__main__":
    unittest.main()
