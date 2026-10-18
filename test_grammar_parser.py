import unittest

import grammar_engine as engine

class GrammarParserTests(unittest.TestCase):
    def test_paper_grammar_preserves_alternatives_and_literal_operators(self):
        grammar = engine.parse_grammar("""
E ::= E + E
E ::= E * F
E ::= F
F ::= ( E )
F ::= n
""")

        self.assertIsInstance(grammar, engine.Grammar)
        self.assertEqual([nt.name for nt in grammar.nonterminals], ["E", "F"])
        self.assertEqual({terminal.symbol for terminal in grammar.terminals},
                         {"+", "*", "(", ")", "n"})
        e, f = grammar.nonterminals
        self.assertIsInstance(e.definition, engine.UnionFormula)
        self.assertIs(e.definition.right, f)
        self.assertIsInstance(e.definition.left, engine.UnionFormula)
        plus_rule = e.definition.left.left
        times_rule = e.definition.left.right
        self.assertIsInstance(plus_rule, engine.ConcatenationFormula)
        self.assertIsInstance(plus_rule.left, engine.ConcatenationFormula)
        self.assertIs(plus_rule.left.left, e)
        self.assertEqual(plus_rule.left.right.symbol, "+")
        self.assertIs(plus_rule.right, e)
        self.assertIs(times_rule.left.left, e)
        self.assertEqual(times_rule.left.right.symbol, "*")
        self.assertIs(times_rule.right, f)
        self.assertEqual(engine.format_formula(f.definition),
                         "((('(' E) ')') | 'n')")
        self.assertEqual(grammar.run(3), [])
        self.assertEqual(
            {(finding.kind, tuple(finding.sentence.symbols))
             for finding in grammar.step()},
            {("concatenation", ("n", "+", "n", "+", "n")),
             ("union", ("n", "+", "n", "*", "n"))},
        )

    def test_iterable_rules_ignore_blank_lines_and_resolve_forward_reference(self):
        grammar = engine.parse_grammar(["", "S ::= A word", "  ", "A ::= n"])
        s, a = grammar.nonterminals
        self.assertIs(s.definition.left, a)
        self.assertEqual(s.definition.right.symbol, "word")
        self.assertEqual({terminal.symbol for terminal in grammar.terminals},
                         {"word", "n"})

    def test_empty_rhs_and_epsilon_marker(self):
        for source in ("S ::=", "S ::= ε"):
            with self.subTest(source=source):
                grammar = engine.parse_grammar(source)
                self.assertIsInstance(grammar.nonterminals[0].definition,
                                      engine.Epsilon)

    def test_syntax_errors_include_source_line_number(self):
        for source, line in (
            ("S ::= n\nnot a rule", 2),
            ("S ::= n\nS ::= a ::= b", 2),
            ("two words ::= n", 1),
        ):
            with self.subTest(source=source), self.assertRaisesRegex(
                    ValueError, rf"\b{line}\b"):
                engine.parse_grammar(source)


if __name__ == "__main__":
    unittest.main()
