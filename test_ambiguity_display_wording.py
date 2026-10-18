import io
import re
import unittest
from contextlib import redirect_stdout

import grammar_engine as engine
from paper_example import EXPRESSION_RULES


def displayed_text(method):
    output = io.StringIO()
    with redirect_stdout(output):
        method()
    # Keep the content of the box, joining any lines wrapped by its border.
    rows = [line.strip("│ ") for line in output.getvalue().splitlines()
            if line.startswith("│")]
    return re.sub(r"\s+", " ", " ".join(rows))


class AmbiguityDisplayWordingTests(unittest.TestCase):
    def setUp(self):
        self.grammar = engine.parse_grammar(EXPRESSION_RULES)
        self.grammar.approximate(4)

    def test_union_display_names_the_two_source_productions(self):
        output = displayed_text(self.grammar.display_union_ambs)

        self.assertRegex(
            output,
            r"(?i)union ambiguity between E ::= E \+ E and E ::= E \* F\b",
        )
        self.assertRegex(
            output.replace("'", ""),
            r"(?i)witness:\s*n \+ n \* n\b",
        )

    def test_concatenation_display_names_one_production_and_both_splits(self):
        output = displayed_text(self.grammar.display_cat_ambs)

        self.assertRegex(
            output,
            r"(?i)concatenation ambiguity.{0,50}E ::= E \+ E\b",
        )
        unquoted = output.replace("'", "")
        self.assertRegex(unquoted, r"(?i)witness:\s*n \+ n \+ n\b")
        self.assertRegex(
            unquoted,
            r"(?i)factorization 1:\s*\(n \+\) \* \(n \+ n\)",
        )
        self.assertRegex(
            unquoted,
            r"(?i)factorization 2:\s*\(n \+ n \+\) \* \(n\)",
        )

    def test_grouped_union_attributes_b_to_the_second_and_third_rules(self):
        grammar = engine.parse_grammar(("S ::= a", "S ::= b", "S ::= b"))
        _, findings, _ = grammar.approximate(1)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].sentence.symbols, ["b"])
        self.assertEqual(findings[0].production_indices, (1, 2))

        for level in (1, 2):
            if level == 2:
                grammar.approximate(level)
                self.assertIn(findings[0], grammar.findings)
            with self.subTest(level=level):
                output = displayed_text(grammar.display_union_ambs)
                self.assertRegex(
                    output,
                    r"(?i)union ambiguity between S ::= b and S ::= b\b",
                )
                self.assertNotRegex(
                    output,
                    r"(?i)union ambiguity between S ::= (?:a|b) and S ::= a\b"
                    r"|union ambiguity between S ::= a and S ::= b\b",
                )

    def test_changed_rule_does_not_claim_old_source_productions(self):
        grammar = engine.parse_grammar(("S ::= a", "S ::= b"))
        grammar.nonterminals[0].definition.left = grammar.terminals[1]

        _, findings, _ = grammar.approximate(1)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].production_indices, ())
        self.assertNotIn("S ::= a", displayed_text(grammar.display_union_ambs))


if __name__ == "__main__":
    unittest.main()
