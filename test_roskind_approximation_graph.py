"""Check the Roskind subsets used for approximation measurements."""

from collections import Counter
import json
from pathlib import Path
import unittest

from grammar_io import load_grammar
from roskind_approximation_graph import select_roskind_rules


ROSKIND = Path(__file__).resolve().parent / "roskind" / "grammar.json"


class RoskindSelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = load_grammar(ROSKIND)
        cls.original_rules = Counter(json.dumps(rule, sort_keys=True)
                                     for rule in cls.source["productions"])

    def test_rule_budgets_preserve_original_rules_and_defined_references(self):
        original_nonterminals = set(self.source["nonterminals"])
        for count in (1, 163, 642):
            with self.subTest(count=count):
                subset = select_roskind_rules(self.source, count)
                rules = subset["productions"]
                self.assertEqual(len(rules), count)
                self.assertEqual(subset["start"], self.source["start"])
                self.assertLessEqual(
                    Counter(json.dumps(rule, sort_keys=True) for rule in rules),
                    self.original_rules,
                )
                defined = {rule["lhs"] for rule in rules}
                referenced = {symbol for rule in rules for symbol in rule["rhs"]
                              if symbol in original_nonterminals}
                self.assertIn(subset["start"], defined)
                self.assertEqual(set(subset["nonterminals"]), defined)
                self.assertLessEqual(referenced, defined)

    def test_full_budget_preserves_original_production_order(self):
        subset = select_roskind_rules(self.source, 642)
        self.assertEqual(subset["productions"], self.source["productions"])

    def test_out_of_range_rule_budgets_fail(self):
        for count in (-1, 0, 643):
            with self.subTest(count=count), self.assertRaises(ValueError):
                select_roskind_rules(self.source, count)


if __name__ == "__main__":
    unittest.main()
