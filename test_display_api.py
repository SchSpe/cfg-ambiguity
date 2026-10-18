import io
import re
import unittest
from contextlib import redirect_stdout

import grammar_engine as engine
from paper_example import EXPRESSION_RULES


def printed_by(method):
    output = io.StringIO()
    with redirect_stdout(output):
        method()
    return output.getvalue()


def without_box_decoration(output):
    border_characters = set("│┃║|┌┐└┘├┤╔╗╚╝╠╣─━═+-=")
    lines = [line for line in output.splitlines()
             if not (len(line.strip()) >= 3
                     and set(line.strip()) <= border_characters)]
    text = "\n".join(lines)
    text = re.sub(r"(?m)^\s*[│┃║|]\s*|\s*[│┃║|]\s*$", " ", text)
    return re.sub(r"[┌┐└┘├┤╔╗╚╝╠╣─━═]", " ", text)


class DisplayAPITests(unittest.TestCase):
    def assert_boxed_section(self, output, heading):
        self.assertRegex(output, rf"(?i)\b{heading}\b")
        border_characters = set("│┃║|┌┐└┘├┤╔╗╚╝╠╣─━═+-=")
        borders = [line.strip() for line in output.splitlines()
                   if len(line.strip()) >= 3
                   and set(line.strip()) <= border_characters]
        self.assertGreaterEqual(len(borders), 2, output)

    def test_display_preserves_original_rule_order_and_repeated_lhs(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)

        self.assertIsInstance(grammar.cfg, engine.CFG)
        self.assertEqual(getattr(grammar.cfg.start, "name", grammar.cfg.start), "E")
        self.assertEqual(len(grammar.cfg.productions), 5)

        output = printed_by(grammar.display)
        self.assert_boxed_section(output, "Grammar")

        positions = []
        for rule in EXPRESSION_RULES:
            self.assertEqual(output.count(rule), 1, rule)
            positions.append(output.index(rule))
        self.assertEqual(positions, sorted(positions))

    def test_display_and_approximation_follow_changed_definition(self):
        grammar = engine.parse_grammar("S ::= a\nS ::= b")
        grammar.approximate(1)
        grammar.nonterminals[0].definition = grammar.terminals[1]

        languages, unions, concats = grammar.approximate(1)
        self.assertEqual([sentence.symbols for sentence in languages["S"]], [["b"]])
        self.assertEqual((unions, concats), ([], []))
        output = printed_by(grammar.display)
        self.assertIn("S ::= b", output)
        self.assertNotIn("S ::= a", output)

    def test_level_zero_display_shows_empty_languages(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)

        output = printed_by(grammar.display_langs)
        self.assert_boxed_section(output, "Languages")
        content = without_box_decoration(output)

        self.assertRegex(content, r"(?m)^\s*L_0\(E\)\s*=")
        self.assertRegex(content, r"(?m)^\s*L_0\(F\)\s*=")
        self.assertTrue(any(marker in output.lower()
                            for marker in ("∅", "{}", "[]", "empty", "set()")))

    def test_display_langs_shows_level_four_languages(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)
        grammar.approximate(4)

        output = printed_by(grammar.display_langs)
        self.assert_boxed_section(output, "Languages")
        content = without_box_decoration(output)

        self.assertRegex(content, r"(?m)^\s*L_4\(E\)\s*=")
        self.assertRegex(content, r"(?m)^\s*L_4\(F\)\s*=")
        # Allow quoted terminals or list punctuation without requiring one layout.
        normalized = re.sub(r"[\[\]',]", " ", content)
        self.assertRegex(normalized, r"\bn\s+\+\s+n\s+\*\s+n\b")
        self.assertRegex(normalized, r"\bn\s+\+\s+n\s+\+\s+n\b")

    def test_ambiguity_displays_show_level_four_witnesses_and_factorizations(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)
        grammar.approximate(4)

        union_output = printed_by(grammar.display_union_ambs)
        cat_output = printed_by(grammar.display_cat_ambs)

        self.assert_boxed_section(union_output, "Union ambiguities")
        self.assert_boxed_section(cat_output, "Concatenation ambiguities")
        union_text = re.sub(r"['\"(),]", " ", without_box_decoration(union_output))
        cat_text = re.sub(r"['\"(),]", " ", without_box_decoration(cat_output))
        self.assertRegex(union_text, r"(?is)\bwitness\s*:\s*n\s*\+\s*n\s*\*\s*n\b")
        self.assertRegex(cat_text, r"(?is)\bwitness\s*:\s*n\s*\+\s*n\s*\+\s*n\b")
        self.assertRegex(cat_text, r"(?i)\bfactorization\s*1\b")
        self.assertRegex(cat_text, r"(?i)\bfactorization\s*2\b")
        self.assertRegex(cat_text, r"(?is)\bfactorization\s*1\s*:\s*n\s*\+\s*\*\s*n\s*\+\s*n\b")
        self.assertRegex(cat_text, r"(?is)\bfactorization\s*2\s*:\s*n\s*\+\s*n\s*\+\s*\*\s*n\b")

    def test_ambiguity_displays_report_no_findings_at_level_zero(self):
        grammar = engine.parse_grammar(EXPRESSION_RULES)

        for method, heading in ((grammar.display_union_ambs, "Union ambiguities"),
                                (grammar.display_cat_ambs, "Concatenation ambiguities")):
            with self.subTest(heading=heading):
                output = printed_by(method)
                self.assert_boxed_section(output, heading)
                self.assertRegex(output, r"(?is)\bno\b.{0,80}\b(?:ambiguity|ambiguities|findings)\b")

    def test_display_methods_work_for_manually_built_grammar(self):
        terminal = engine.Terminal("a")
        start = engine.Nonterminal("S")
        start.definition = terminal
        grammar = engine.Grammar([terminal], [start])

        self.assertIn("S", printed_by(grammar.display))
        grammar.approximate(1)
        output = printed_by(grammar.display_langs)
        self.assertIn("S", output)
        self.assertIn("a", output)


if __name__ == "__main__":
    unittest.main()
