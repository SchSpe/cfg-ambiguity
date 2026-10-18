"""Check extraction edge cases and compare both complete grammars with Bison."""

import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

from convert_yacc import parse_yacc
from grammar_io import load_grammar


ROOT = Path(__file__).resolve().parent
# Cfront is not distributed with this repository; README.md says how to add it.
CFRONT = (ROOT / "cfront" / "gram.y").exists()
CFRONT_MISSING = "cfront/gram.y is not included; see README.md to fetch it"


def bison_productions(report):
    """Independent oracle: parse Bison's production listing, not the Yacc input."""
    section = report.split("\nGrammar\n", 1)[1].split("\nTerminals", 1)[0]
    rules = []
    lhs = None
    for line in section.splitlines():
        match = re.match(r"\s*\d+\s+(.*)", line)
        if not match:
            continue
        content = match[1]
        if content.startswith("|"):
            rhs_text = content[1:].strip()
        else:
            lhs, rhs_text = content.split(":", 1)
            rhs_text = rhs_text.strip()
        rhs_text = rhs_text.replace("/* empty */", "").replace("%empty", "").replace("ε", "")
        tokens = re.findall(r"'(?:\\.|[^'\\])*'|\S+", rhs_text)
        rhs = [ast.literal_eval(t) if t.startswith("'") else t for t in tokens]
        rules.append((lhs, tuple(rhs)))
    helpers = {lhs for lhs, rhs in rules if re.fullmatch(r"\$?@\d+", lhs)}
    if any(rhs for lhs, rhs in rules if lhs in helpers):
        raise AssertionError("Expected only empty action-helper productions")
    return [(lhs, tuple(s for s in rhs if s not in helpers))
            for lhs, rhs in rules if lhs != "$accept" and lhs not in helpers]


class ConversionTests(unittest.TestCase):
    def test_actions_literals_precedence_epsilon_and_omitted_semicolon(self):
        source = r'''%{
            const char *ignored = "%% }";
        %}
        %token ID END 0 LOW
        %left LOW
        %start start
        %%
        start: '{' { if (x) { f("}"); } /* } */ } item '}' %prec LOW
             | END
             | /* empty */ ;
        item: ID { /* nested-looking comment /* is not nested */ }
        other: '|' | ';' | '\'' | '{' | '}' ;
        %%
        trailing C code is not grammar syntax
        '''
        data = parse_yacc(source)
        self.assertEqual(data["start"], "start")
        self.assertEqual([(r["lhs"], r["rhs"]) for r in data["productions"]], [
            ("start", ["{", "item", "}"]), ("start", ["END"]), ("start", []),
            ("item", ["ID"]), ("other", ["|"]), ("other", [";"]),
            ("other", ["'"]), ("other", ["{"]), ("other", ["}"]),
        ])
        self.assertEqual(data["productions"][0]["yacc_precedence"], "LOW")
        self.assertEqual(data["productions"][0]["omitted_actions"][0]["after_symbols"], 1)
        self.assertEqual(data["yacc"]["explicit_eof_tokens"], ["END"])

    def test_duplicate_alternatives_are_not_deduplicated(self):
        data = parse_yacc("%token X\n%%\ns: X | X;\n%%")
        self.assertEqual([r["rhs"] for r in data["productions"]], [["X"], ["X"]])

    def test_undeclared_symbols_and_unsupported_directives_fail(self):
        with self.assertRaises(ValueError):
            parse_yacc("%%\ns: unknown;\n%%")
        with self.assertRaises(ValueError):
            parse_yacc("%glr-parser\n%%\ns: ;\n%%")

    def test_loader_rejects_unknown_rhs(self):
        data = {"format": "cfg-productions-v1", "start": "s", "terminals": [],
                "nonterminals": ["s"], "productions": [{"lhs": "s", "rhs": ["missing"]}]}
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "bad.json"
            path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):
                load_grammar(path)

    def test_original_hashes_and_corpus_structure(self):
        cases = [
            ("cfront", "gram.y", "43183a06e283bdc56132e444191f73cd4d148f6179f8b6c33b9a769a6ef16acd", "ext_def", 389, 91, 79, 20),
            ("roskind", "cpp5.y", "3274a15770415e8d8a2be58466a6f949ba1af1c737382da941ee510885b53f71", "translation_unit", 642, 163, 101, 15),
        ]
        for folder, source, digest, start, nr, nn, nt, empty in cases:
            with self.subTest(grammar=folder):
                if folder == "cfront" and not CFRONT:
                    self.skipTest(CFRONT_MISSING)
                self.assertEqual(hashlib.sha256((ROOT / folder / source).read_bytes()).hexdigest(), digest)
                data = load_grammar(ROOT / folder / "grammar.json")
                self.assertEqual(data["source"]["sha256"], digest)
                self.assertEqual(data["start"], start)
                self.assertEqual((len(data["productions"]), len(data["nonterminals"]), len(data["terminals"])), (nr, nn, nt))
                self.assertEqual(sum(not r["rhs"] for r in data["productions"]), empty)

    @unittest.skipUnless(shutil.which("bison"), "Bison is optional; needed only for the independent oracle")
    def test_every_production_matches_bison(self):
        for folder, filename in [("cfront", "gram.y"), ("roskind", "cpp5.y")]:
            with self.subTest(grammar=folder), tempfile.TemporaryDirectory() as tmp:
                if folder == "cfront" and not CFRONT:
                    self.skipTest(CFRONT_MISSING)
                output = Path(tmp) / "parser.c"
                run = subprocess.run([shutil.which("bison"), "-v", "-o", str(output),
                                      str(ROOT / folder / filename)], capture_output=True, text=True)
                self.assertEqual(run.returncode, 0, run.stderr)
                expected = bison_productions(output.with_suffix(".output").read_text())
                data = load_grammar(ROOT / folder / "grammar.json")
                actual = [(r["lhs"], tuple(r["rhs"])) for r in data["productions"]]
                self.assertEqual(actual, expected)


if __name__ == "__main__":
    unittest.main()
