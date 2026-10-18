import unittest

import grammar_engine as implementation

Sentence = implementation.Sentence
Language = implementation.Language
Nonterminal = implementation.Nonterminal
Terminal = implementation.Terminal
Epsilon = implementation.Epsilon
ParenthesizedFormula = implementation.ParenthesizedFormula
UnionFormula = implementation.UnionFormula
ConcatenationFormula = implementation.ConcatenationFormula
Grammar = implementation.Grammar


def sentence(*symbols):
    result = Sentence()
    for symbol in symbols:
        result = result * Sentence(symbol)
    return result


def language(*sentences):
    result = Language()
    result.sentences = set(sentences)
    return result


def concatenate(*formulas):
    result = formulas[0]
    for formula in formulas[1:]:
        result = ConcatenationFormula(result, formula)
    return result


def union(*formulas):
    result = formulas[0]
    for formula in formulas[1:]:
        result = UnionFormula(result, formula)
    return result


class SentenceAndLanguageTests(unittest.TestCase):
    def test_sentence_equality_order_and_concatenation(self):
        left = Sentence(3)
        right = Sentence(4)
        result = left * right
        self.assertEqual(result.symbols, [3, 4])
        self.assertEqual(result.length, 2)
        self.assertEqual(left.symbols, [3])
        self.assertEqual(right.symbols, [4])
        self.assertNotEqual(result, right * left)
        self.assertEqual(Sentence() * left, left)
        self.assertEqual(left * Sentence(), left)
        self.assertEqual(len({Sentence(3), Sentence(3), Sentence(4)}), 2)

    def test_union_records_local_overlap_and_preserves_operands(self):
        left = language(sentence("a"), sentence("b"))
        right = language(sentence("b"), sentence("c"))
        result = left | right
        self.assertEqual(result.sentences, {sentence("a"), sentence("b"), sentence("c")})
        self.assertEqual(result.union_witnesses, {sentence("b")})
        self.assertEqual(left.sentences, {sentence("a"), sentence("b")})
        self.assertEqual(right.sentences, {sentence("b"), sentence("c")})
        self.assertFalse((result | Language()).union_witnesses)

    def test_empty_language_and_epsilon_have_different_products(self):
        operand = language(sentence("a"), sentence("b"))
        self.assertFalse((Language() * operand).sentences)
        self.assertFalse((operand * Language()).sentences)
        self.assertEqual((Language(Sentence()) * operand).sentences, operand.sentences)
        self.assertEqual((operand * Language(Sentence())).sentences, operand.sentences)

    def test_concatenation_retains_distinct_nonempty_factorizations(self):
        operand = language(sentence("a"), sentence("a", "a"))
        result = operand * operand
        witness = sentence("a", "a", "a")
        self.assertEqual(
            result.sentences,
            {sentence("a", "a"), witness, sentence("a", "a", "a", "a")},
        )
        self.assertEqual(set(result.concatenation_witnesses), {witness})
        self.assertEqual(
            set(result.concatenation_witnesses[witness]),
            {(sentence("a"), sentence("a", "a")), (sentence("a", "a"), sentence("a"))},
        )
        self.assertFalse((result * Language(Sentence())).concatenation_witnesses)

    def test_concatenation_retains_epsilon_factorizations(self):
        operand = language(Sentence(), sentence("a"))
        result = operand * operand
        self.assertEqual(set(result.concatenation_witnesses), {sentence("a")})
        self.assertEqual(
            set(result.concatenation_witnesses[sentence("a")]),
            {(Sentence(), sentence("a")), (sentence("a"), Sentence())},
        )


class GrammarTests(unittest.TestCase):
    def test_iteration_is_synchronous_in_both_definition_orders(self):
        for reverse in (False, True):
            with self.subTest(reverse=reverse):
                terminal = Terminal("a")
                start = Nonterminal("S")
                other = Nonterminal("A")
                start.definition = other
                other.definition = terminal
                declarations = [other, start] if reverse else [start, other]
                grammar = Grammar([terminal], declarations)
                self.assertEqual(grammar.step(), [])
                self.assertFalse(start.next.sentences)
                self.assertEqual(other.next.sentences, {sentence("a")})
                self.assertEqual(grammar.step(), [])
                self.assertEqual(start.next.sentences, {sentence("a")})
                self.assertEqual(grammar.iteration, 2)

    def test_recursive_union_first_appears_in_round_two(self):
        terminal = Terminal("a")
        start = Nonterminal("S")
        start.definition = UnionFormula(terminal, start)
        grammar = Grammar([terminal], [start])
        self.assertEqual(grammar.step(), [])
        findings = grammar.step()
        self.assertEqual(len(findings), 1)
        finding = findings[0]
        self.assertEqual(finding.kind, "union")
        self.assertEqual(finding.sentence, sentence("a"))
        self.assertEqual(finding.iteration, 2)
        self.assertIs(finding.nonterminal, start)
        self.assertIs(finding.formula, start.definition)
        self.assertEqual(finding.path, ())
        self.assertIsNone(finding.factorizations)
        later = grammar.step()
        self.assertEqual(len(later), 1)
        self.assertEqual(later[0].iteration, 3)

    def test_nested_finding_keeps_exact_site_without_propagating_overlap(self):
        a = Terminal("a")
        b = Terminal("b")
        inner = UnionFormula(a, a)
        start = Nonterminal("S")
        start.definition = UnionFormula(ParenthesizedFormula(inner), b)
        grammar = Grammar([a, b], [start])
        findings = grammar.step()
        self.assertEqual(len(findings), 1)
        self.assertIs(findings[0].formula, inner)
        self.assertEqual(findings[0].path, ("left", "inner"))
        self.assertFalse(start.next.union_witnesses)
        self.assertEqual(start.next.sentences, {sentence("a"), sentence("b")})

    def test_nonterminal_reference_does_not_inherit_old_operation_findings(self):
        a = Terminal("a")
        b = Terminal("b")
        start = Nonterminal("S")
        other = Nonterminal("A")
        start.definition = UnionFormula(other, b)
        other.definition = UnionFormula(a, a)
        grammar = Grammar([a, b], [start, other])
        findings = grammar.run(2)
        self.assertEqual(len(findings), 2)
        self.assertTrue(all(finding.nonterminal is other for finding in findings))
        self.assertEqual([finding.iteration for finding in findings], [1, 2])
        self.assertFalse(start.next.union_witnesses)

    def test_concatenation_finding_keeps_both_splits(self):
        a = Terminal("a")
        left = UnionFormula(Epsilon(), a)
        right = UnionFormula(Epsilon(), a)
        start = Nonterminal("S")
        start.definition = ConcatenationFormula(left, right)
        grammar = Grammar([a], [start])
        findings = grammar.step()
        self.assertEqual(len(findings), 1)
        finding = findings[0]
        self.assertEqual(finding.kind, "concatenation")
        self.assertIs(finding.formula, start.definition)
        self.assertEqual(finding.sentence, sentence("a"))
        self.assertEqual(
            set(finding.factorizations),
            {(Sentence(), sentence("a")), (sentence("a"), Sentence())},
        )

    def test_run_is_bounded_and_reset_restores_initial_state(self):
        a = Terminal("a")
        start = Nonterminal("S")
        start.definition = UnionFormula(Epsilon(), ConcatenationFormula(a, start))
        grammar = Grammar([a], [start])
        self.assertEqual(grammar.run(0), [])
        self.assertEqual(grammar.iteration, 0)
        self.assertEqual(grammar.run(3), [])
        self.assertEqual(grammar.iteration, 3)
        self.assertEqual(start.next.sentences, {Sentence(), sentence("a"), sentence("a", "a")})
        grammar.reset()
        self.assertEqual(grammar.iteration, 0)
        self.assertEqual(grammar.findings, [])
        self.assertFalse(start.previous.sentences)
        self.assertFalse(start.next.sentences)
        grammar.run(1)
        self.assertEqual(start.next.sentences, {Sentence()})

    def test_reset_allows_findings_to_be_discovered_again(self):
        a = Terminal("a")
        start = Nonterminal("S")
        start.definition = UnionFormula(a, a)
        grammar = Grammar([a], [start])
        self.assertEqual(len(grammar.run(2)), 2)
        grammar.reset()
        self.assertEqual(grammar.findings, [])
        self.assertEqual(len(grammar.step()), 1)

    def test_validation_rejects_missing_definitions_and_undeclared_symbols(self):
        a = Terminal("a")
        start = Nonterminal("S")
        with self.assertRaises(ValueError):
            Grammar([a], [start])
        start.definition = Terminal("b")
        with self.assertRaises(ValueError):
            Grammar([a], [start])
        start.definition = Nonterminal("S")
        with self.assertRaises(ValueError):
            Grammar([a], [start])

    def test_terminal_symbols_are_registered_by_value(self):
        start = Nonterminal("S")
        start.definition = Terminal("a")
        grammar = Grammar([Terminal("a")], [start])
        grammar.step()
        self.assertEqual(start.next.sentences, {sentence("a")})

    def test_validation_rejects_conflicting_declarations(self):
        a = Terminal("a")
        start = Nonterminal("S")
        start.definition = a
        with self.assertRaises(ValueError):
            Grammar([a, Terminal("a")], [start])
        duplicate = Nonterminal("S")
        duplicate.definition = a
        with self.assertRaises(ValueError):
            Grammar([a], [start, duplicate])
        with self.assertRaises(ValueError):
            Grammar([a, Terminal("S")], [start])

    def test_report_example_first_witness_is_in_round_four(self):
        terminals = {name: Terminal(name) for name in ("ID", "LP", "RP", "PLUS", "MINUS", "STAR", "SLASH")}
        expr = Nonterminal("expr")
        term = Nonterminal("term")
        prim = Nonterminal("prim")
        expr.definition = union(
            concatenate(expr, terminals["PLUS"], term),
            concatenate(expr, terminals["MINUS"], term),
            term,
        )
        term.definition = union(
            concatenate(term, terminals["STAR"], prim),
            concatenate(prim, terminals["SLASH"], term),
            prim,
        )
        prim.definition = union(
            concatenate(terminals["LP"], expr, terminals["RP"]),
            terminals["ID"],
        )
        grammar = Grammar(terminals.values(), [expr, term, prim])
        self.assertEqual(grammar.run(3), [])
        findings = grammar.step()
        self.assertEqual(len(findings), 1)
        finding = findings[0]
        self.assertEqual(finding.kind, "union")
        self.assertIs(finding.nonterminal, term)
        self.assertIs(finding.formula, term.definition.left)
        self.assertEqual(finding.path, ("left",))
        self.assertEqual(finding.iteration, 4)
        self.assertEqual(finding.sentence, sentence("ID", "SLASH", "ID", "STAR", "ID"))


if __name__ == "__main__":
    unittest.main()
