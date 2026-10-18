import io
import unittest
from contextlib import redirect_stdout

import grammar_engine as engine
from paper_example import EXPRESSION_RULES


def box_lines(text):
    """The content rows of a box, without borders and padding."""
    return [line.strip("│").strip() for line in text.splitlines() if line.startswith("│")]


class SummaryTests(unittest.TestCase):
    def test_counts_match_the_approximation(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)
        languages, unions, concatenations = grammar.approximate(5)
        output = io.StringIO()
        with redirect_stdout(output):
            lines = box_lines(grammar.summary())
        self.assertEqual(output.getvalue(), "")

        def distinct(findings):     # the ambiguous operations
            return {(f.nonterminal, f.path) for f in findings}

        total = sum(len(language) for language in languages.values())
        self.assertEqual(lines[0], "Summary at level 5")
        self.assertIn("Grammar: 5 productions, 2 nonterminals, 5 terminals; start symbol E", lines)
        self.assertIn(f"Sentences: {len(languages['E'])} in L_5(E), {total} over all nonterminals",
                      lines)
        def operations(count, kind):
            return f"{count} ambiguous {kind}" + ("" if count == 1 else "s")

        self.assertIn(f"Union ambiguities: {operations(len(distinct(unions)), 'union')}, "
                      f"reported {len(unions)} times", lines)
        self.assertIn(f"Concatenation ambiguities: "
                      f"{operations(len(distinct(concatenations)), 'concatenation')}, "
                      f"reported {len(concatenations)} times", lines)
        self.assertIn(f"First ambiguity at level {grammar.findings[0].iteration}", lines)
        self.assertIn("Nonterminals involved: 1 of 2", lines)
        self.assertIn("Productions involved: 2 of 5", lines)
        rows = [line.split() for line in lines if line.startswith("E ::=")]
        self.assertEqual(rows, [
            ["E", "::=", "E", "+", "E", f"{len(distinct(unions))}", "union,",
             f"{len(distinct(concatenations))}", "concatenation"],
            ["E", "::=", "E", "*", "F", f"{len(distinct(unions))}", "union"],
        ])

    def test_level_zero_and_restart_after_an_edit(self):
        grammar = engine.parse_grammar(("S ::= a", "S ::= a"))
        lines = box_lines(grammar.summary())
        self.assertIn("Sentences: 0 in L_0(S), 0 over all nonterminals", lines)
        self.assertIn("No ambiguity found through level 0", lines)
        self.assertIn("Productions involved: 0 of 2", lines)

        grammar.run(2)
        lines = box_lines(grammar.summary())
        self.assertIn("Union ambiguities: 1 ambiguous union, reported 2 times", lines)
        self.assertIn("Grammar: 2 productions, 1 nonterminal, 1 terminal; start symbol S", lines)

        grammar.nonterminals[0].definition = grammar.terminals[0]
        lines = box_lines(grammar.summary())
        self.assertEqual(lines[0], "Summary at level 0")
        self.assertIn("Productions involved: not tracked without a matching cfg", lines)

    def test_grammar_without_cfg_counts_alternatives(self):
        a = engine.Terminal("a")
        start = engine.Nonterminal("S")
        start.definition = engine.UnionFormula(engine.ConcatenationFormula(start, start),
                                               engine.UnionFormula(a, a))
        grammar = engine.Grammar([a], [start])
        grammar.run(1)
        lines = box_lines(grammar.summary())
        self.assertIn("Grammar: 3 productions, 1 nonterminal, 1 terminal; start symbol S", lines)
        self.assertIn("Union ambiguities: 1 ambiguous union, reported 1 time", lines)
        self.assertIn("Nonterminals involved: 1 of 1", lines)
        self.assertIn("Productions involved: not tracked without a matching cfg", lines)

    def test_long_production_lists_are_cut(self):
        grammar = engine.parse_grammar(["S ::= a"] * 25)
        grammar.run(1)
        lines = box_lines(grammar.summary())
        self.assertIn("Productions involved: 25 of 25", lines)
        self.assertEqual(sum(line.startswith("S ::= a") for line in lines), 20)
        self.assertEqual(lines[-1], "… and 5 more")


if __name__ == "__main__":
    unittest.main()
