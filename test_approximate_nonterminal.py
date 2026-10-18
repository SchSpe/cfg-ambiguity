import unittest
import weakref

import grammar_engine as engine
from paper_example import EXPRESSION_RULES


def words(sentences):
    return {tuple(sentence.symbols) for sentence in sentences}


def finding_key(finding):
    return (finding.kind, tuple(finding.sentence.symbols), finding.nonterminal.name,
            finding.path, finding.iteration, finding.production_indices,
            tuple((tuple(x.symbols), tuple(y.symbols)) for x, y in finding.factorizations or ()))


class DependenciesTests(unittest.TestCase):
    def test_a_chain_needs_one_nonterminal_per_level(self):
        grammar = engine.parse_grammar("""
S ::= T b
T ::= U c
U ::= a
X ::= X X
X ::= a
""")
        self.assertEqual(grammar.dependencies("S", 3), {1: ("U",), 2: ("T",), 3: ("S",)})
        self.assertEqual(grammar.dependencies("S", 5),
                         {1: (), 2: (), 3: ("U",), 4: ("T",), 5: ("S",)})
        self.assertEqual(grammar.dependencies("X", 2), {1: ("X",), 2: ("X",)})
        self.assertEqual(grammar.dependencies("S", 0), {})

    def test_mutual_recursion_needs_both_below_the_top(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)
        self.assertEqual(grammar.dependencies("E", 4),
                         {1: ("E", "F"), 2: ("E", "F"), 3: ("E", "F"), 4: ("E",)})
        self.assertEqual(grammar.dependencies("F", 3), {1: ("E", "F"), 2: ("E",), 3: ("F",)})

    def test_unknown_names_and_bad_levels_are_rejected(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)
        with self.assertRaises(ValueError):
            grammar.dependencies("G", 2)
        with self.assertRaises(ValueError):
            grammar.approximate_nonterminal("G", 2)
        with self.assertRaises(ValueError):
            grammar.approximate_nonterminal("E", -1)


class ApproximateNonterminalTests(unittest.TestCase):
    def assert_matches_full_run(self, grammar, name, level):
        alone, unions, concatenations = grammar.approximate_nonterminal(name, level)
        computed = {(nt, k) for k, names in grammar.dependencies(name, level).items()
                    for nt in names}
        languages, all_unions, all_concatenations = grammar.approximate(level)
        self.assertIsInstance(alone, engine.Trie)
        self.assertEqual(words(alone), words(languages[name]))
        for found, everything in ((unions, all_unions), (concatenations, all_concatenations)):
            expected = [finding for finding in everything
                        if (finding.nonterminal.name, finding.iteration) in computed]
            self.assertEqual([finding_key(f) for f in found], [finding_key(f) for f in expected])

    def test_expression_grammar_matches_the_full_run(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)
        for level in range(6):
            for name in ("E", "F"):
                with self.subTest(name=name, level=level):
                    self.assert_matches_full_run(grammar, name, level)

    def test_random_grammars_match_the_full_run(self):
        for seed in range(30):
            grammar = engine.Grammar.random(3, 3, 1, num_symbols=3, seed=seed)
            for nt in grammar.nonterminals:
                with self.subTest(seed=seed, name=nt.name):
                    self.assert_matches_full_run(grammar, nt.name, 3)

    def test_formula_grammar_without_a_cfg_matches_the_full_run(self):
        a, b = engine.Terminal("a"), engine.Terminal("b")
        s, t = engine.Nonterminal("S"), engine.Nonterminal("T")
        s.definition = engine.UnionFormula(
            engine.ConcatenationFormula(s, s),
            engine.ParenthesizedFormula(engine.UnionFormula(t, a)))
        t.definition = engine.UnionFormula(engine.ConcatenationFormula(a, t), engine.Epsilon())
        grammar = engine.Grammar([a, b], [s, t])
        for level in range(5):
            with self.subTest(level=level):
                self.assert_matches_full_run(grammar, "S", level)

    def test_only_the_listed_definitions_are_evaluated_two_levels_at_a_time(self):
        grammar = engine.parse_grammar("""
T ::= P Q
P ::= A c
Q ::= B c
A ::= a
B ::= b
X ::= X X
X ::= a
""")
        evaluate, alive, evaluated = grammar._evaluate, {}, []

        def watched(formula, nonterminal, path, languages, level, findings):
            if path == ():      # a whole definition: which earlier languages still exist?
                evaluated.append(((nonterminal.name, level),
                                  {key for key, language in alive.items() if language() is not None}))
            language = evaluate(formula, nonterminal, path, languages, level, findings)
            if path == ():
                alive[nonterminal.name, level] = weakref.ref(language)
            return language

        grammar._evaluate = watched
        language, unions, concatenations = grammar.approximate_nonterminal("T", 3)
        self.assertEqual(words(language), {("a", "c", "b", "c")})
        self.assertEqual((unions, concatenations), ([], []))    # X, whose rules are ambiguous, is never evaluated
        self.assertEqual(evaluated, [
            (("A", 1), set()),
            (("B", 1), {("A", 1)}),
            (("P", 2), {("A", 1), ("B", 1)}),
            (("Q", 2), {("A", 1), ("B", 1), ("P", 2)}),
            (("T", 3), {("P", 2), ("Q", 2)}),        # level 1 is gone
        ])

    def test_the_grammar_state_is_left_unchanged(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)
        grammar.run(2)
        state = ([(nt.previous, nt.next) for nt in grammar.nonterminals],
                 grammar.iteration, list(grammar.findings))
        grammar.approximate_nonterminal("E", 5)
        self.assertEqual(([(nt.previous, nt.next) for nt in grammar.nonterminals],
                          grammar.iteration, grammar.findings), state)

    def test_level_zero_is_empty(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)
        language, unions, concatenations = grammar.approximate_nonterminal("E", 0)
        self.assertEqual((words(language), unions, concatenations), (set(), [], []))


if __name__ == "__main__":
    unittest.main()
