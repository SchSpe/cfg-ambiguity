import io
import unittest
from contextlib import redirect_stdout

import grammar_engine as implementation
from paper_example import EXPRESSION_RULES


Terminal = implementation.Terminal
Nonterminal = implementation.Nonterminal
Epsilon = implementation.Epsilon
ParenthesizedFormula = implementation.ParenthesizedFormula
UnionFormula = implementation.UnionFormula
ConcatenationFormula = implementation.ConcatenationFormula
Grammar = implementation.Grammar


def union(*formulas):
    result = formulas[0]
    for formula in formulas[1:]:
        result = UnionFormula(result, formula)
    return result


def concatenate(*formulas):
    result = formulas[0]
    for formula in formulas[1:]:
        result = ConcatenationFormula(result, formula)
    return result


def bounded_languages(grammar, max_length):
    languages = {nt: set() for nt in grammar.nonterminals}

    def product(left, right):
        return {
            x + y for x in left for y in right
            if len(x) + len(y) <= max_length
        }

    def evaluate(formula):
        if isinstance(formula, Terminal):
            return {(formula.symbol,)} if max_length else set()
        if isinstance(formula, Epsilon):
            return {()}
        if isinstance(formula, Nonterminal):
            return languages[formula]
        if isinstance(formula, ParenthesizedFormula):
            return evaluate(formula.formula)
        if isinstance(formula, UnionFormula):
            return evaluate(formula.left) | evaluate(formula.right)
        if isinstance(formula, ConcatenationFormula):
            return product(evaluate(formula.left), evaluate(formula.right))
        raise TypeError(type(formula))

    while True:
        expanded = {nt: evaluate(nt.definition) for nt in grammar.nonterminals}
        if expanded == languages:
            return {nt.name: words for nt, words in languages.items()}
        languages = expanded


def single_definition(formula, terminals, extras=()):
    start = Nonterminal("S")
    start.definition = formula
    return Grammar(terminals, (start, *extras))


class CACCRecognitionTests(unittest.TestCase):
    def assert_rule(self, grammar, rule_id, kind=None):
        matches = [m for m in grammar.recognize_caccs() if m.rule_id == rule_id]
        self.assertTrue(matches, rule_id)
        for match in matches:
            self.assertIn(match.nonterminal, grammar.nonterminals)
            self.assertIsInstance(match.path, tuple)
            self.assertTrue(match.source)
            self.assertTrue(match.reason)
            if kind is not None:
                self.assertEqual(match.kind, kind)
        return matches[0]

    def test_mixed_recursion_records_owner_and_two_distinct_alternatives(self):
        b, c, d = (Terminal(symbol) for symbol in "bcd")
        start = Nonterminal("S")
        start.definition = union(concatenate(b, start), concatenate(start, c), d)
        grammar = Grammar([b, c, d], [start])
        match = self.assert_rule(grammar, "mixed_recursion", "union")
        self.assertIs(match.nonterminal, start)
        self.assertIs(match.formula, start.definition)
        self.assertEqual(match.path, ())

    def test_self_embedding_is_not_two_alternatives_of_mixed_recursion(self):
        a, b = Terminal("a"), Terminal("b")
        start = Nonterminal("S")
        start.definition = union(concatenate(start, b, start), a)
        grammar = Grammar([a, b], [start])
        self.assert_rule(grammar, "self_embedding", "concatenation")
        self.assertNotIn("mixed_recursion", {m.rule_id for m in grammar.recognize_caccs()})

    def test_duplicate_union_keeps_local_formula_and_path(self):
        a, b = Terminal("a"), Terminal("b")
        repeated = union(a, Terminal("a"))
        grammar = single_definition(concatenate(b, ParenthesizedFormula(repeated)), [a, b])
        match = self.assert_rule(grammar, "duplicate_union", "union")
        self.assertIs(match.formula, repeated)
        self.assertEqual(match.path, ("right", "inner"))

    def test_optional_square_accepts_both_epsilon_positions(self):
        a = Terminal("a")
        optional = concatenate(union(a, Epsilon()), union(Epsilon(), a))
        grammar = single_definition(optional, [a])
        self.assert_rule(grammar, "optional_square", "concatenation")

    def test_dead_languages_do_not_prove_ambiguity(self):
        a = Terminal("a")
        dead = Nonterminal("Dead")
        dead.definition = dead
        for formula in (
            union(dead, dead),
            concatenate(union(dead, Epsilon()), union(dead, Epsilon())),
        ):
            with self.subTest(formula=implementation.format_formula(formula)):
                grammar = single_definition(formula, [a], [dead])
                self.assertEqual(grammar.recognize_caccs(), [])

    def test_unproductive_recursive_owners_do_not_prove_ambiguity(self):
        a, b = Terminal("a"), Terminal("b")
        start = Nonterminal("S")
        for formula in (
            union(concatenate(a, start), concatenate(start, b)),
            concatenate(start, a, start),
        ):
            with self.subTest(formula=implementation.format_formula(formula)):
                start.definition = formula
                grammar = Grammar([a, b], [start])
                self.assertEqual(grammar.recognize_caccs(), [])

    def test_unproductive_contexts_do_not_prove_recursive_patterns(self):
        a = Terminal("a")
        start, dead = Nonterminal("S"), Nonterminal("Dead")
        dead.definition = dead
        for formula in (
            union(concatenate(dead, start), concatenate(start, a), a),
            union(concatenate(a, start), concatenate(start, dead), a),
            union(concatenate(start, dead, start), a),
        ):
            with self.subTest(formula=implementation.format_formula(formula)):
                start.definition = formula
                grammar = Grammar([a], [start, dead])
                self.assertEqual(grammar.recognize_caccs(), [])

    def test_epsilon_self_embedding_is_derivation_ambiguity(self):
        start = Nonterminal("S")
        start.definition = union(concatenate(start, start), Epsilon())
        grammar = Grammar([], [start])
        self.assert_rule(grammar, "self_embedding", "derivation")

    def test_dead_concatenation_context_keeps_only_real_local_matches(self):
        a = Terminal("a")
        dead = Nonterminal("Dead")
        dead.definition = dead
        left, right = union(a, Epsilon()), union(a, Epsilon())
        flattened = single_definition(concatenate(dead, left, right), [a], [dead])
        self.assertEqual(flattened.recognize_caccs(), [])
        local = concatenate(left, right)
        nested = single_definition(concatenate(dead, local), [a], [dead])
        matches = nested.recognize_caccs()
        self.assertEqual(len(matches), 1)
        self.assertEqual(matches[0].rule_id, "optional_square")
        self.assertEqual(matches[0].path, ("right",))
        self.assertIs(matches[0].formula, local)

    def test_structurally_different_languages_are_not_assumed_equal(self):
        a, b = Terminal("a"), Terminal("b")
        formulas = (
            union(a, b),
            concatenate(union(a, Epsilon()), union(b, Epsilon())),
        )
        for formula in formulas:
            with self.subTest(formula=implementation.format_formula(formula)):
                grammar = single_definition(formula, [a, b])
                self.assertEqual(grammar.recognize_caccs(), [])

    def test_productivity_uses_fixed_point_without_running_approximations(self):
        a = Terminal("a")
        chain = [Nonterminal(f"N{i}") for i in range(70)]
        for current, following in zip(chain, chain[1:]):
            current.definition = following
        chain[-1].definition = a
        grammar = single_definition(union(chain[0], chain[0]), [a], chain)
        self.assert_rule(grammar, "duplicate_union")
        self.assertEqual(grammar.iteration, 0)
        self.assertTrue(all(not nt.next.sentences for nt in grammar.nonterminals))


class CACCTransformationTests(unittest.TestCase):
    def assert_preserved(self, grammar, max_length=5, **kwargs):
        expected = bounded_languages(grammar, max_length)
        result = grammar.transform_caccs(**kwargs)
        actual = bounded_languages(result.grammar, max_length)
        for name, words in expected.items():
            self.assertEqual(actual[name], words, str(name))
        return result

    def test_report_expression_grammar_uses_both_corollaries(self):
        plus, star, opening, closing, number = [Terminal(s) for s in ("+", "*", "(", ")", "n")]
        expr, factor = Nonterminal("E"), Nonterminal("F")
        expr.definition = union(concatenate(expr, plus, expr), concatenate(expr, star, factor), factor)
        factor.definition = union(concatenate(opening, expr, closing), number)
        grammar = Grammar([plus, star, opening, closing, number], [expr, factor])
        result = self.assert_preserved(grammar, 7)
        self.assertEqual([change.rule_id for change in result.changes[:2]], ["mixed_recursion", "self_embedding"])
        self.assertTrue(result.changes[0].introduced)
        self.assertFalse(result.remaining)
        self.assertFalse(result.limit_reached)
        self.assertEqual(result.grammar.run(4), [])

    def test_repair_cacc_returns_the_papers_final_grammar(self):
        grammar = implementation.parse_grammar(EXPRESSION_RULES)
        expected = implementation.parse_grammar((
            "E ::= E + T", "E ::= T",
            "T ::= T * F", "T ::= F",
            "F ::= ( E )", "F ::= n",
        ))

        repair_output = io.StringIO()
        with redirect_stdout(repair_output):
            first = grammar.repair_cacc(grammar.recognize_caccs()[0])
            repaired = grammar.repair_cacc()

        self.assertIsInstance(first, Grammar)
        self.assertIsInstance(repaired, Grammar)
        self.assertEqual(repair_output.getvalue().splitlines(),
                         ["Repaired 1 CACC match.", "Repaired 2 CACC matches."])
        incomplete_output = io.StringIO()
        with redirect_stdout(incomplete_output):
            with self.assertRaisesRegex(RuntimeError, "step limit reached"):
                grammar.repair_cacc(max_steps=0)
        self.assertEqual(incomplete_output.getvalue(), "")
        self.assertEqual([nt.name for nt in repaired.nonterminals], ["E", "T", "F"])
        self.assertEqual(implementation._grammar_key(repaired),
                         implementation._grammar_key(expected))
        self.assertEqual(bounded_languages(grammar, 7),
                         {name: words for name, words in bounded_languages(repaired, 7).items()
                          if name in ("E", "F")})

        output = io.StringIO()
        with redirect_stdout(output):
            repaired.display()
        for rule in ("E ::= E + T | T", "T ::= T * F | F", "F ::= ( E ) | n"):
            self.assertIn(rule, output.getvalue())

    def test_optional_square_and_duplicate_union_preserve_language(self):
        a, b = Terminal("a"), Terminal("b")
        base = union(a, concatenate(b, b))
        for formula, rule_id in (
            (union(base, base), "duplicate_union"),
            (concatenate(union(base, Epsilon()), union(base, Epsilon())), "optional_square"),
        ):
            with self.subTest(rule_id=rule_id):
                grammar = single_definition(formula, [a, b])
                result = self.assert_preserved(grammar)
                self.assertIn(rule_id, [change.rule_id for change in result.changes])

    def test_epsilon_self_embedding_preserves_only_empty_sentence(self):
        start = Nonterminal("S")
        start.definition = union(concatenate(start, start), Epsilon())
        result = self.assert_preserved(Grammar([], [start]))
        self.assertEqual(bounded_languages(result.grammar, 1)["S"], {()})
        self.assertFalse(result.remaining)

    def test_mixed_recursion_preserves_other_alternatives(self):
        a, b, c, d = [Terminal(s) for s in "abcd"]
        start = Nonterminal("S")
        start.definition = union(concatenate(a, start), concatenate(start, b), c, d)
        result = self.assert_preserved(Grammar([a, b, c, d], [start]), 5)
        self.assertTrue(result.changes)
        self.assertFalse(result.remaining)

    def test_scan_and_transform_preserve_original_objects_and_state(self):
        a = Terminal("a")
        grammar = single_definition(union(a, a), [a])
        grammar.run(2)
        start = grammar.nonterminals[0]
        definition, previous, following = start.definition, start.previous, start.next
        findings = tuple(grammar.findings)
        matches = grammar.recognize_caccs()
        result = grammar.transform_caccs()
        self.assertEqual(len(matches), 1)
        self.assertIs(start.definition, definition)
        self.assertIs(start.previous, previous)
        self.assertIs(start.next, following)
        self.assertEqual(tuple(grammar.findings), findings)
        self.assertEqual(grammar.iteration, 2)
        self.assertIsNot(result.grammar, grammar)
        self.assertIsNot(result.grammar.nonterminals[0], start)
        self.assertEqual(result.grammar.iteration, 0)
        self.assertEqual(result.grammar.findings, [])
        self.assertTrue(all(not nt.next.sentences for nt in result.grammar.nonterminals))
        change = result.changes[0]
        self.assertIsInstance(change.before, str)
        self.assertIsInstance(change.after, str)
        self.assertNotEqual(change.before, change.after)
        self.assertTrue(change.source)

    def test_transformation_limit_reports_unfinished_patterns(self):
        a = Terminal("a")
        grammar = single_definition(concatenate(union(a, a), union(a, a)), [a])
        untouched = self.assert_preserved(grammar, max_steps=0)
        self.assertEqual(untouched.changes, [])
        self.assertTrue(untouched.remaining)
        self.assertTrue(untouched.limit_reached)
        once = self.assert_preserved(grammar, max_steps=1)
        self.assertEqual(len(once.changes), 1)
        self.assertTrue(once.remaining)
        self.assertTrue(once.limit_reached)
        finished = self.assert_preserved(grammar, max_steps=5)
        self.assertFalse(finished.remaining)
        self.assertFalse(finished.limit_reached)

    def test_apply_one_match_preserves_language(self):
        a = Terminal("a")
        grammar = single_definition(union(a, a), [a])
        result = grammar.apply_cacc(grammar.recognize_caccs()[0])
        self.assertEqual(len(result.changes), 1)
        self.assertEqual(bounded_languages(grammar, 3), bounded_languages(result.grammar, 3))

    def test_apply_rejects_match_from_another_grammar(self):
        a = Terminal("a")
        grammar = single_definition(union(a, a), [a])
        other = single_definition(union(a, a), [a])
        foreign = other.recognize_caccs()[0]
        with self.assertRaisesRegex(ValueError, "does not belong|stale"):
            grammar.apply_cacc(foreign)
        self.assertEqual(len(grammar.recognize_caccs()), 1)
        self.assertEqual(grammar.iteration, 0)

    def test_apply_rejects_stale_match_after_definition_changes(self):
        a, b = Terminal("a"), Terminal("b")
        for mutate_in_place in (False, True):
            with self.subTest(mutate_in_place=mutate_in_place):
                grammar = single_definition(union(a, a), [a, b])
                start = grammar.nonterminals[0]
                old_match = grammar.recognize_caccs()[0]
                if mutate_in_place:
                    start.definition.left = b
                    start.definition.right = b
                else:
                    start.definition = union(b, b)
                current_definition = start.definition
                with self.assertRaisesRegex(ValueError, "does not belong|stale"):
                    grammar.apply_cacc(old_match)
                self.assertIs(start.definition, current_definition)
                self.assertEqual(bounded_languages(grammar, 1)["S"], {("b",)})
                self.assertEqual(len(grammar.recognize_caccs()), 1)

    def test_recursive_alias_cycles_do_not_block_other_changes(self):
        a = Terminal("a")
        left, right, duplicate = [Nonterminal(name) for name in ("A", "B", "C")]
        left.definition = union(concatenate(right, left), Epsilon())
        right.definition = union(concatenate(left, right), Epsilon())
        duplicate.definition = union(a, a)
        grammar = Grammar([a], [left, right, duplicate])
        grammar.run(3)
        definitions = tuple(nt.definition for nt in grammar.nonterminals)
        languages = tuple((nt.previous, nt.next) for nt in grammar.nonterminals)
        findings = tuple(grammar.findings)
        result = self.assert_preserved(grammar, 3, max_steps=20)
        self.assertFalse(result.stalled)
        self.assertFalse(result.remaining)
        self.assertFalse(result.limit_reached)
        self.assertLess(len(result.changes), 20)
        self.assertIn("duplicate_union", [change.rule_id for change in result.changes])
        simplified = next(nt for nt in result.grammar.nonterminals if nt.name == "C")
        self.assertIsInstance(simplified.definition, Terminal)
        self.assertEqual(simplified.definition.symbol, "a")
        self.assertEqual(tuple(nt.definition for nt in grammar.nonterminals), definitions)
        self.assertEqual(tuple((nt.previous, nt.next) for nt in grammar.nonterminals), languages)
        self.assertEqual(tuple(grammar.findings), findings)
        self.assertEqual(grammar.iteration, 3)

    def test_fresh_helpers_avoid_terminal_and_nonterminal_names(self):
        a, b, c, reserved = [Terminal(s) for s in ("a", "b", "c", "S_tail")]
        start, occupied = Nonterminal("S"), Nonterminal("S_tail_1")
        start.definition = union(concatenate(a, start), concatenate(start, b), c)
        occupied.definition = a
        grammar = Grammar([a, b, c, reserved], [start, occupied])
        result = self.assert_preserved(grammar)
        names = [nt.name for nt in result.grammar.nonterminals]
        self.assertEqual(len(names), len(set(names)))
        self.assertTrue(set(names).isdisjoint(t.symbol for t in result.grammar.terminals))
        self.assertTrue(result.changes[0].introduced)


if __name__ == "__main__":
    unittest.main()
