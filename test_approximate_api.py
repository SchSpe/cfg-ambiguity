import unittest

import grammar_engine as engine
from paper_example import EXPRESSION_RULES


def words(sentences):
    return {tuple(sentence.symbols) for sentence in sentences}


class ApproximateAPITests(unittest.TestCase):
    def test_returns_independent_level_language_snapshots(self):
        grammar = engine.parse_grammar("""
S ::= a
T ::= S b
""")

        zero, zero_unions, zero_concats = grammar.approximate(0)
        self.assertEqual(set(zero), {"S", "T"})
        self.assertTrue(all(isinstance(language, engine.Trie)
                            for language in zero.values()))
        self.assertEqual(words(zero["S"]), set())
        self.assertEqual(words(zero["T"]), set())
        self.assertEqual((zero_unions, zero_concats), ([], []))

        one, one_unions, one_concats = grammar.approximate(1)
        self.assertEqual(words(one["S"]), {("a",)})
        self.assertEqual(words(one["T"]), set())
        self.assertEqual((one_unions, one_concats), ([], []))

        two, _, _ = grammar.approximate(2)
        self.assertEqual(words(two["T"]), {("a", "b")})
        self.assertEqual(words(one["T"]), set())
        self.assertEqual(words(zero["S"]), set())

        two["S"].add(engine.Sentence("extra"))
        again, _, _ = grammar.approximate(2)
        self.assertEqual(words(again["S"]), {("a",)})

    def test_findings_accumulate_to_absolute_level_without_repeating_steps(self):
        grammar = engine.parse_grammar("""
S ::= a
S ::= a
""")

        _, unions_two, concats_two = grammar.approximate(2)
        self.assertEqual([finding.iteration for finding in unions_two], [1, 2])
        self.assertTrue(all(finding.kind == "union" for finding in unions_two))
        self.assertEqual([tuple(finding.sentence.symbols) for finding in unions_two],
                         [("a",), ("a",)])
        self.assertEqual(concats_two, [])
        self.assertEqual(grammar.iteration, 2)

        _, repeated_unions, repeated_concats = grammar.approximate(2)
        self.assertEqual(grammar.iteration, 2)
        self.assertEqual(len(grammar.findings), 2)
        self.assertEqual([finding.iteration for finding in repeated_unions], [1, 2])
        self.assertEqual(repeated_concats, [])

        _, unions_three, _ = grammar.approximate(3)
        self.assertEqual(grammar.iteration, 3)
        self.assertEqual([finding.iteration for finding in unions_three], [1, 2, 3])

        _, unions_one, _ = grammar.approximate(1)
        self.assertEqual(grammar.iteration, 1)
        self.assertEqual([finding.iteration for finding in unions_one], [1])
        self.assertEqual(len(grammar.findings), 1)

    def test_expression_grammar_separates_union_and_concatenation(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)
        _, union_three, concat_three = grammar.approximate(3)
        self.assertEqual((union_three, concat_three), ([], []))

        languages, union_four, concat_four = grammar.approximate(4)
        self.assertEqual(set(languages), {"E", "F"})
        self.assertIn(("n", "+", "n", "*", "n"), words(languages["E"]))
        self.assertEqual(len(union_four), 1)
        self.assertEqual(len(concat_four), 1)
        union = union_four[0]
        concat = concat_four[0]
        self.assertEqual((union.kind, union.iteration, union.nonterminal.name),
                         ("union", 4, "E"))
        self.assertEqual(tuple(union.sentence.symbols),
                         ("n", "+", "n", "*", "n"))
        self.assertEqual((concat.kind, concat.iteration, concat.nonterminal.name),
                         ("concatenation", 4, "E"))
        self.assertEqual(tuple(concat.sentence.symbols),
                         ("n", "+", "n", "+", "n"))
        self.assertEqual(len(concat.factorizations), 2)

        _, union_after_reset, concat_after_reset = grammar.approximate(3)
        self.assertEqual(grammar.iteration, 3)
        self.assertEqual((union_after_reset, concat_after_reset), ([], []))

    def test_rejects_invalid_level(self):
        grammar = engine.parse_grammar("S ::= a")
        for level in (-1, 1.5, "2"):
            with self.subTest(level=level), self.assertRaises(ValueError):
                grammar.approximate(level)

    def test_run_returns_new_findings_after_definition_changes(self):
        grammar = engine.parse_grammar(("S ::= a", "S ::= a", "S ::= b"))
        grammar.run(1)
        b = next(terminal for terminal in grammar.terminals if terminal.symbol == "b")
        grammar.nonterminals[0].definition = engine.UnionFormula(b, b)

        findings = grammar.run(1)
        self.assertEqual(len(findings), 1)
        self.assertEqual((findings[0].iteration, findings[0].sentence.symbols),
                         (1, ["b"]))

    def test_regrouping_alternatives_refreshes_finding_paths(self):
        grammar = engine.parse_grammar(("S ::= a", "S ::= a", "S ::= a"))
        _, old_findings, _ = grammar.approximate(1)
        a = grammar.terminals[0]
        grammar.nonterminals[0].definition = engine.UnionFormula(
            a, engine.UnionFormula(a, a)
        )

        _, new_findings, _ = grammar.approximate(1)
        self.assertEqual({finding.path for finding in old_findings},
                         {(), ("left",)})
        self.assertEqual({finding.path for finding in new_findings},
                         {(), ("right",)})


if __name__ == "__main__":
    unittest.main()
