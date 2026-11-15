"""Behavioral checks for parse -> NSF repair -> approximation -> report.

The small set-based oracle below bounds token length, not parse-tree height:
a language-preserving rewrite may change the height of its derivations.
"""

from contextlib import redirect_stderr
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import check_grammar
from approximate_and_detect import approximate_and_detect
from repair import repair_caccs, transform_caccs
from parse import parse_grammar
from report import build_report, prove_finding, render_text


ROOT = Path(__file__).resolve().parent
PAPER_GRAMMAR = """\
E ::= E + E
E ::= E * F
E ::= F
F ::= ( E )
F ::= n
"""
DANGLING_GRAMMAR = "S ::= i S\nS ::= i S e S\nS ::= x\n"
NSF_FAMILIES = {"mixed_recursion", "self_embedding", "duplicate_union", "optional_square"}


def bounded_languages(cfg, length):
    """Independent least fixed point using ordinary sets of token tuples."""
    languages = {name: set() for name in cfg.nonterminals}
    while True:
        previous = {name: set(words) for name, words in languages.items()}
        for lhs, rhs in cfg.productions:
            words = {()}
            for symbol in rhs:
                factors = previous[symbol] if symbol in previous else {(symbol,)}
                words = {left + right for left in words for right in factors
                         if len(left) + len(right) <= length}
            languages[lhs].update(words)
        if languages == previous:
            return languages


def leaves(tree):
    if isinstance(tree, str):
        return (tree,)
    return tuple(token for child in tree["children"] for token in leaves(child))


def report_for(text, level=4, max_repairs=100):
    original = parse_grammar(text)
    repairs = repair_caccs(original, max_steps=max_repairs)
    approximation = approximate_and_detect(repairs.grammar, level)
    return build_report("example.bnf", original, repairs, approximation)


class NSFRepairTests(unittest.TestCase):
    def assert_language_preserved(self, text, required_family, length=6):
        original = parse_grammar(text)
        productions, lines = original.productions, original.production_lines
        repaired = repair_caccs(original)
        self.assertIn(required_family, {change.rule_id for change in repaired.changes})
        self.assertTrue(all(change.rule_id in NSF_FAMILIES for change in repaired.changes))
        before = bounded_languages(original, length)
        after = bounded_languages(repaired.grammar, length)
        for name in original.nonterminals:
            self.assertEqual(before[name], after[name], name)
        self.assertEqual(original.productions, productions)
        self.assertEqual(original.production_lines, lines)
        self.assertIsNot(repaired.grammar, original)
        return repaired

    def test_mixed_recursion_preserves_both_recursive_directions(self):
        self.assert_language_preserved("A ::= b A\nA ::= A c\nA ::= d", "mixed_recursion")

    def test_self_embedding_preserves_alternative_base_sentences(self):
        self.assert_language_preserved("E ::= E + E\nE ::= n\nE ::= m", "self_embedding")

    def test_duplicate_alternatives_preserve_empty_and_nonempty_sentences(self):
        self.assert_language_preserved("S ::=\nS ::=\nS ::= a\nS ::= a", "duplicate_union")

    def test_optional_square_follows_nullable_aliases(self):
        repaired = self.assert_language_preserved(
            "S ::= N N\nN ::= M\nM ::= a\nM ::=", "optional_square")
        self.assertEqual(bounded_languages(repaired.grammar, 3)["S"], {(), ("a",), ("a", "a")})

    def test_optional_square_preserves_surrounding_tokens(self):
        self.assert_language_preserved(
            'S ::= "left side" N N "|"\nN ::= a\nN ::= b\nN ::=', "optional_square")

    def test_paper_example_reaches_the_reports_replacement_rules(self):
        repaired = self.assert_language_preserved(PAPER_GRAMMAR, "mixed_recursion", length=7)
        self.assertEqual([change.rule_id for change in repaired.changes],
                         ["mixed_recursion", "self_embedding"])
        self.assertEqual(set(repaired.grammar.productions), {
            ("E", ("E", "+", "T")), ("E", ("T",)),
            ("T", ("T", "*", "F")), ("T", ("F",)),
            ("F", ("(", "E", ")")), ("F", ("n",)),
        })

    def test_non_nsf_extensions_are_detected_but_not_automatically_rewritten(self):
        examples = {
            "transparent_cycle": "S ::= S\nS ::= a",
            "subsumed_alternative": "S ::= A\nS ::= x\nA ::= x",
            "dangling_suffix": DANGLING_GRAMMAR,
        }
        for family, text in examples.items():
            with self.subTest(family=family):
                original = parse_grammar(text)
                repaired = repair_caccs(original)
                self.assertEqual(repaired.grammar.productions, original.productions)
                self.assertFalse(repaired.changes)
                self.assertIn(family, {match.rule_id for match in repaired.remaining})
                self.assertFalse(repaired.limit_reached)
                self.assertFalse(repaired.stalled)

    def test_existing_explicit_extended_rewrite_api_is_still_available(self):
        original = parse_grammar("S ::= S\nS ::= a")
        explicit = transform_caccs(original)
        self.assertTrue(explicit.changes)
        self.assertEqual(bounded_languages(original, 3)["S"],
                         bounded_languages(explicit.grammar, 3)["S"])

    def test_repair_limit_preserves_unfinished_work_and_remaining_evidence(self):
        original = parse_grammar("E ::= E + E\nE ::= n")
        result = repair_caccs(original, max_steps=0)
        self.assertEqual(result.grammar.productions, original.productions)
        self.assertFalse(result.changes)
        self.assertTrue(result.limit_reached)
        self.assertIn("self_embedding", {match.rule_id for match in result.remaining})

    def test_recognition_extensions_do_not_exhaust_a_zero_repair_budget(self):
        result = repair_caccs(parse_grammar(DANGLING_GRAMMAR), max_steps=0)
        self.assertTrue(result.remaining)
        self.assertFalse(result.limit_reached)
        self.assertFalse(result.stalled)

    def test_last_allowed_repair_can_finish_with_only_extensions_remaining(self):
        result = repair_caccs(parse_grammar("S ::= a\nS ::= a\nU ::= U\nU ::= b"), max_steps=1)
        self.assertEqual([change.rule_id for change in result.changes], ["duplicate_union"])
        self.assertTrue(result.remaining)
        self.assertFalse(result.limit_reached)
        self.assertFalse(result.stalled)

    def test_repair_limit_reports_newly_exposed_nsf_work(self):
        result = repair_caccs(parse_grammar(PAPER_GRAMMAR), max_steps=1)
        self.assertEqual([change.rule_id for change in result.changes], ["mixed_recursion"])
        self.assertIn("self_embedding", {match.rule_id for match in result.remaining})
        self.assertTrue(result.limit_reached)
        self.assertEqual(bounded_languages(parse_grammar(PAPER_GRAMMAR), 7)["E"],
                         bounded_languages(result.grammar, 7)["E"])

    def test_changed_rules_have_generated_locations_and_original_lines_survive(self):
        original = parse_grammar(PAPER_GRAMMAR)
        repaired = repair_caccs(original).grammar
        lines = dict(zip(repaired.productions, repaired.production_lines))
        self.assertEqual(lines["F", ("(", "E", ")")], 4)
        self.assertEqual(lines["F", ("n",)], 5)
        self.assertEqual(lines["E", ("E", "+", "T")], 0)


class ApproximationTests(unittest.TestCase):
    def test_union_finding_keeps_distinct_rules_and_two_valid_trees(self):
        cfg = parse_grammar("S ::= A\nS ::= B\nA ::= x\nB ::= x")
        result = approximate_and_detect(cfg, 5)
        sites = [site for site in result.sites if site.finding.kind == "union"]
        self.assertEqual(len(sites), 1)
        site = sites[0]
        self.assertEqual(site.first_level, 2)
        self.assertEqual(site.rule_indices, (0, 1))
        self.assertEqual(site.finding.sentence, ("x",))
        trees = prove_finding(site.finding, result.catalog, site.finding.iteration)
        self.assertEqual([leaves(tree) for tree in trees], [("x",), ("x",)])
        self.assertNotEqual(trees[0]["rule"], trees[1]["rule"])

    def test_concatenation_finding_keeps_both_empty_boundary_choices(self):
        cfg = parse_grammar("S ::= A A\nA ::=\nA ::= a")
        result = approximate_and_detect(cfg, 5)
        sites = [site for site in result.sites if site.finding.kind == "concatenation"]
        self.assertEqual(len(sites), 1)
        site = sites[0]
        self.assertEqual(site.first_level, 2)
        self.assertEqual(site.finding.sentence, ("a",))
        self.assertEqual({len(left) for left, right in site.finding.factorizations}, {0, 1})
        trees = prove_finding(site.finding, result.catalog, site.finding.iteration)
        self.assertEqual([leaves(tree) for tree in trees], [("a",), ("a",)])
        self.assertNotEqual(trees[0], trees[1])

    def test_start_language_cannot_stop_search_while_dependencies_are_growing(self):
        cfg = parse_grammar("S ::= A\nA ::= B\nB ::= x")
        result = approximate_and_detect(cfg, 6)
        self.assertEqual(result.level_reached, 4)
        self.assertTrue(result.saturated)
        self.assertEqual(result.start_sentences, 1)

    def test_infinite_unambiguous_language_is_only_checked_to_the_requested_level(self):
        cfg = parse_grammar("S ::= a S\nS ::= b")
        result = approximate_and_detect(cfg, 4)
        self.assertEqual(result.level_reached, 4)
        self.assertFalse(result.saturated)
        self.assertEqual(result.start_sentences, 4)
        self.assertFalse(result.sites)


class ReportTests(unittest.TestCase):
    def test_verdict_describes_repaired_grammar_even_before_original_witness_depth(self):
        report = report_for("E ::= E + E\nE ::= n", level=1)
        self.assertTrue(report["repairs"].changes)
        self.assertEqual(report["verdict"], "none_found")
        self.assertEqual(report["exit_code"], 0)
        self.assertFalse(report["sites"])

    def test_removed_duplicate_ambiguity_can_be_proved_unambiguous(self):
        report = report_for("S ::= a\nS ::= a", level=5)
        self.assertEqual(report["verdict"], "unambiguous")
        self.assertEqual(report["exit_code"], 0)
        self.assertFalse(report["sites"])

    def test_report_contains_repairs_and_complete_analyzed_grammar(self):
        report = report_for(PAPER_GRAMMAR, level=5)
        text = render_text(report)
        self.assertEqual(report["verdict"], "none_found")
        self.assertIn("E ::= E + E", text)
        for lhs, rhs in report["cfg"].productions:
            self.assertIn(f"{lhs} ::= {' '.join(rhs)}", text)
        for family in ("mixed recursion", "self embedding"):
            self.assertIn(family, text.lower().replace("_", " "))
        self.assertIn("generated", text.lower())
        self.assertNotIn("line 0", text.lower())

    def test_remaining_structural_ambiguity_is_reported_at_shallow_depth(self):
        report = report_for(DANGLING_GRAMMAR, level=1)
        self.assertFalse(report["repairs"].changes)
        self.assertEqual(report["verdict"], "ambiguous")
        self.assertEqual(report["exit_code"], 1)
        self.assertIn("dangling", render_text(report).lower())

    def test_remaining_witnesses_use_repaired_rules_including_generated_helpers(self):
        report = report_for("S ::= E\nE ::= E + E\nE ::= A\nE ::= B\nA ::= x\nB ::= x", level=5)
        self.assertEqual(report["verdict"], "ambiguous")
        self.assertTrue(report["repairs"].changes)
        self.assertIn("E_part", {site["nonterminal"] for site in report["sites"]})
        self.assertTrue(any(all(report["cfg"].production_lines[rule] == 0 for rule in site["rules"])
                            for site in report["sites"]))
        for site in report["sites"]:
            self.assertEqual([leaves(tree) for tree in site["trees"]], [site["witness"]] * 2)
            for tree in site["trees"]:
                self.assertIn(tree["rule"], site["rules"])
                self.assertEqual(report["cfg"].productions[tree["rule"]][0], site["nonterminal"])

    def test_unreachable_construct_does_not_change_start_verdict(self):
        report = report_for("S ::= x\nU ::= U\nU ::= a", level=4)
        self.assertEqual(report["verdict"], "unambiguous")
        self.assertEqual(report["exit_code"], 0)
        self.assertTrue(report["repairs"].remaining)
        self.assertTrue(all(not site["reachable"] for site in report["sites"]))

    def test_ambiguous_prefix_with_dead_suffix_does_not_change_verdict(self):
        report = report_for("S ::= x\nS ::= A A D\nA ::=\nA ::= a\nD ::= D", level=4)
        self.assertEqual(report["verdict"], "unambiguous")
        self.assertEqual(report["exit_code"], 0)
        self.assertFalse(report["sites"])

    def test_unproductive_cycle_has_no_terminal_sentence_ambiguity(self):
        report = report_for("S ::= S", level=4)
        self.assertEqual(report["verdict"], "unambiguous")
        self.assertEqual(report["start_sentences"], 0)
        self.assertFalse(report["repairs"].changes)
        self.assertFalse(report["sites"])
        self.assertTrue(report["warnings"])

    def test_unfinished_repairs_are_reported_without_losing_ambiguity_evidence(self):
        report = report_for("E ::= E + E\nE ::= n", level=1, max_repairs=0)
        self.assertEqual(report["verdict"], "ambiguous")
        self.assertTrue(report["repairs"].limit_reached)
        self.assertIn("limit", render_text(report).lower())


class CommandTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="cfg-pipeline-test-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.source = self.directory / "grammar.bnf"
        self.output = self.directory / "grammar.ambiguity.txt"

    def run_command(self, *arguments):
        return subprocess.run([sys.executable, str(ROOT / "check_grammar.py"),
                               str(self.source), *map(str, arguments)],
                              cwd=self.directory, capture_output=True, text=True,
                              encoding="utf-8", timeout=30)

    def test_cli_repairs_before_search_and_leaves_input_untouched(self):
        self.source.write_text(PAPER_GRAMMAR, encoding="utf-8")
        before = self.source.read_bytes()
        result = self.run_command("--level", 4)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.source.read_bytes(), before)
        text = self.output.read_text(encoding="utf-8")
        self.assertIn("E ::= E + T", text)
        self.assertIn("T ::= T * F", text)
        self.assertNotIn("AMBIGUOUS:", text)
        self.assertEqual(result.stdout, "")

    def test_repeated_runs_write_identical_reports(self):
        self.source.write_text(PAPER_GRAMMAR, encoding="utf-8")
        first = self.run_command("--level", 4)
        self.assertEqual(first.returncode, 0, first.stderr)
        content = self.output.read_bytes()
        second = self.run_command("--level", 4)
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertEqual(self.output.read_bytes(), content)

    def test_utf8_bom_input_and_custom_report_destination(self):
        self.source.write_text('<S> ::= "café"\n', encoding="utf-8-sig")
        destination = self.directory / "custom.txt"
        result = self.run_command("--output", destination)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('"café"', destination.read_text(encoding="utf-8"))
        self.assertFalse(self.output.exists())

    def test_bad_input_preserves_previous_report(self):
        for source in (b"S -> x", b"\xff"):
            with self.subTest(source=source):
                self.source.write_bytes(source)
                self.output.write_bytes(b"previous report\n")
                result = self.run_command()
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertEqual(self.output.read_bytes(), b"previous report\n")

    def test_output_cannot_replace_input(self):
        self.source.write_text("S ::= x\n", encoding="utf-8")
        before = self.source.read_bytes()
        result = self.run_command("--output", self.source)
        self.assertEqual(result.returncode, 4, result.stderr)
        self.assertEqual(self.source.read_bytes(), before)

    def test_invalid_depth_does_not_write_report(self):
        self.source.write_text("S ::= x\n", encoding="utf-8")
        result = self.run_command("--level", 0)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertFalse(self.output.exists())

    def test_cancellation_preserves_previous_report(self):
        self.source.write_text("S ::= x\n", encoding="utf-8")
        self.output.write_bytes(b"previous report\n")
        with patch.object(check_grammar, "repair_caccs", side_effect=KeyboardInterrupt), redirect_stderr(io.StringIO()):
            status = check_grammar.main([str(self.source)])
        self.assertEqual(status, 130)
        self.assertEqual(self.output.read_bytes(), b"previous report\n")


if __name__ == "__main__":
    unittest.main()
