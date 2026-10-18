import copy
import json
import unittest

from ui_proofs import ProofLimitExceeded, build_grammar, implementation, serialize_finding, summarize_finding


def catalog_from(rules, start="S"):
    nonterminals = list(dict.fromkeys(lhs for lhs, rhs in rules))
    terminals = list(dict.fromkeys(symbol for lhs, rhs in rules for symbol in rhs
                                   if symbol not in nonterminals))
    return build_grammar({"format": "cfg-productions-v1", "name": "Proof test", "start": start,
                          "terminals": terminals, "nonterminals": nonterminals,
                          "source": {"file": "test.y", "url": "https://example.org/test.y"},
                          "productions": [{"lhs": lhs, "rhs": rhs, "source_line": index + 10}
                                          for index, (lhs, rhs) in enumerate(rules)]})


class ProofTests(unittest.TestCase):
    def assert_derivation(self, tree, catalog):
        kind = tree["kind"]
        if kind == "terminal":
            self.assertEqual(tree["tokens"], [tree["symbol"]])
            self.assertIn(tree["symbol"], catalog.terminals)
            return
        if kind == "epsilon":
            self.assertEqual(tree["tokens"], [])
            return
        children = tree["children"]
        for child in children:
            self.assert_derivation(child, catalog)
        if kind == "concatenation":
            self.assertEqual(tree["tokens"], children[0]["tokens"] + children[1]["tokens"])
            self.assertEqual(tree["cut"], len(children[0]["tokens"]))
        elif kind in ("union", "parentheses"):
            self.assertEqual(tree["tokens"], children[0]["tokens"])
        elif kind in ("nonterminal", "production"):
            rule = catalog.rules_by_id[tree["production_id"]]
            self.assertEqual(tree["symbol"], rule["lhs"])
            self.assertEqual(tree["tokens"], children[0]["tokens"])

            def frontier(node):
                if node["kind"] in ("nonterminal", "terminal"):
                    if node["kind"] == "nonterminal":
                        self.assertEqual(node["level"], tree["level"] - 1)
                    return [node["symbol"]]
                if node["kind"] == "epsilon":
                    return []
                return [symbol for child in node["children"] for symbol in frontier(child)]

            self.assertEqual(frontier(children[0]), rule["rhs"])
        else:
            self.fail(f"Unknown derivation node: {kind}")

    def assert_valid_proof(self, proof, catalog):
        self.assertTrue(proof["verified"])
        self.assertEqual(len(proof["derivations"]), 2)
        for tree in proof["derivations"]:
            self.assertEqual(tree["tokens"], proof["witness"])
            self.assert_derivation(tree, catalog)
        self.assertEqual(proof["scope"], "local")
        self.assertIn("start symbol", proof["scope_note"])
        json.dumps(proof)

    def test_catalog_preserves_global_production_order_and_source(self):
        catalog = catalog_from([("S", ["A"]), ("A", ["TOKEN"]), ("S", [])])
        self.assertEqual([rule["id"] for rule in catalog.rules], ["P001", "P002", "P003"])
        self.assertEqual(catalog.rules[1]["source_line"], 11)
        self.assertEqual(catalog.rules[1]["source"]["file"], "test.y")
        self.assertEqual(catalog.rules[1]["rhs"], ["TOKEN"])
        self.assertEqual(catalog.site_rules["S", ()], ("P001", "P003"))

    def test_union_chooses_actual_productions_inside_flattened_left_branch(self):
        catalog = catalog_from([("S", ["a"]), ("S", ["A"]), ("S", ["B"]),
                                ("A", ["b"]), ("B", ["b"])])
        finding = catalog.grammar.run(2)[0]
        summary = summarize_finding(finding, catalog)
        self.assertEqual(summary["candidate_production_ids"], ["P001", "P002", "P003"])
        proof = serialize_finding(finding, catalog)
        self.assertEqual(proof["production_ids"], ["P002", "P003"])
        self.assertEqual(proof["supporting_production_ids"], ["P002", "P003", "P004", "P005"])
        self.assertEqual(proof["witness"], ["b"])
        self.assert_valid_proof(proof, catalog)

    def test_duplicate_alternatives_keep_distinct_occurrence_ids(self):
        catalog = catalog_from([("S", ["TOKEN"]), ("S", ["TOKEN"])])
        proof = serialize_finding(catalog.grammar.step()[0], catalog)
        self.assertEqual(proof["production_ids"], ["P001", "P002"])
        self.assertEqual(proof["witness"], ["TOKEN"])
        self.assert_valid_proof(proof, catalog)

    def test_epsilon_union_and_nullable_derivations(self):
        catalog = catalog_from([("S", ["A"]), ("S", ["B"]), ("A", []), ("B", [])])
        proof = serialize_finding(catalog.grammar.run(2)[0], catalog)
        self.assertEqual(proof["witness"], [])
        self.assert_valid_proof(proof, catalog)

    def test_product_proof_has_distinct_cuts_of_one_production(self):
        catalog = catalog_from([("S", ["A", "A"]), ("A", []), ("A", ["a"])])
        proof = serialize_finding(catalog.grammar.run(2)[0], catalog)
        self.assertEqual(proof["production_ids"], ["P001"])
        self.assertEqual(proof["supporting_production_ids"], ["P001", "P002", "P003"])
        self.assertEqual({item["cut"] for item in proof["factorizations"]}, {0, 1})
        self.assert_valid_proof(proof, catalog)

    def test_nested_product_proves_local_site_even_with_dead_suffix(self):
        catalog = catalog_from([("S", ["A", "A", "D"]), ("A", []), ("A", ["a"]), ("D", ["D"])])
        finding = catalog.grammar.run(2)[0]
        self.assertEqual(finding.path, ("left",))
        self.assertFalse(catalog.nonterminals["S"].next.sentences)
        proof = serialize_finding(finding, catalog)
        self.assertEqual(proof["path"], ["left"])
        self.assertEqual(proof["production_ids"], ["P001"])
        self.assertEqual(proof["expression"], "(A A)")
        self.assertNotIn("P004", proof["supporting_production_ids"])
        self.assert_valid_proof(proof, catalog)

    def test_nonempty_product_factors_and_multi_token_witness(self):
        catalog = catalog_from([("S", ["A", "A"]), ("A", ["a"]), ("A", ["a", "a"])])
        proof = serialize_finding(catalog.grammar.run(2)[0], catalog)
        self.assertEqual(proof["witness"], ["a", "a", "a"])
        self.assertEqual({item["cut"] for item in proof["factorizations"]}, {1, 2})
        self.assert_valid_proof(proof, catalog)

    def test_report_expression_example_proves_every_level_four_finding(self):
        catalog = catalog_from([("E", ["E", "+", "E"]), ("E", ["E", "*", "F"]),
                                ("E", ["F"]), ("F", ["(", "E", ")"]), ("F", ["n"])], start="E")
        findings = catalog.grammar.run(4)
        self.assertEqual(len(findings), 2)
        self.assertEqual({finding.kind for finding in findings}, {"union", "concatenation"})
        for finding in findings:
            self.assert_valid_proof(serialize_finding(finding, catalog), catalog)

    def test_recursive_union_uses_recorded_level(self):
        catalog = catalog_from([("S", ["S"]), ("S", ["a"])])
        finding = catalog.grammar.run(2)[0]
        proof = serialize_finding(finding, catalog)
        self.assert_valid_proof(proof, catalog)
        finding.iteration = 1
        with self.assertRaisesRegex(ValueError, "recorded approximation level"):
            serialize_finding(finding, catalog)

    def test_historical_proof_does_not_use_current_approximation_or_samples(self):
        catalog = catalog_from([("S", ["S"]), ("S", ["TOKEN"])])
        finding = catalog.grammar.run(2)[0]
        expected = serialize_finding(finding, catalog)
        catalog.grammar.run(3)
        catalog.grammar.reset()
        self.assertEqual(serialize_finding(finding, catalog), expected)
        self.assertEqual(catalog.grammar.iteration, 0)
        self.assertEqual(catalog.grammar.findings, [])

    def test_invalid_witness_is_rejected(self):
        catalog = catalog_from([("S", ["TOKEN"]), ("S", ["TOKEN"])])
        finding = copy.copy(catalog.grammar.step()[0])
        finding.sentence = implementation.Sentence("T")
        with self.assertRaisesRegex(ValueError, "cannot be derived"):
            serialize_finding(finding, catalog)

    def test_invalid_product_boundary_is_rejected(self):
        catalog = catalog_from([("S", ["A", "A"]), ("A", []), ("A", ["a"])])
        finding = copy.copy(catalog.grammar.run(2)[0])
        finding.factorizations = (finding.factorizations[0], finding.factorizations[0])
        with self.assertRaisesRegex(ValueError, "two distinct"):
            serialize_finding(finding, catalog)

    def test_changed_grammar_or_foreign_finding_is_rejected(self):
        catalog = catalog_from([("S", ["TOKEN"]), ("S", ["TOKEN"])])
        other = catalog_from([("S", ["TOKEN"]), ("S", ["TOKEN"])])
        finding = catalog.grammar.step()[0]
        with self.assertRaisesRegex(ValueError, "does not belong"):
            serialize_finding(finding, other)
        catalog.nonterminals["S"].definition = implementation.Epsilon()
        with self.assertRaisesRegex(ValueError, "definitions changed"):
            serialize_finding(finding, catalog)

    def test_resource_limit_returns_no_incomplete_certificate(self):
        catalog = catalog_from([("S", ["S"]), ("S", ["TOKEN"])])
        finding = catalog.grammar.run(2)[0]
        with self.assertRaisesRegex(ProofLimitExceeded, "has not been fully verified"):
            serialize_finding(finding, catalog, max_states=1)
        self.assert_valid_proof(serialize_finding(finding, catalog, max_states=100), catalog)
        self.assert_valid_proof(serialize_finding(finding, catalog, max_states=None), catalog)

    def test_invalid_state_budget_is_rejected(self):
        catalog = catalog_from([("S", ["TOKEN"]), ("S", ["TOKEN"])])
        finding = catalog.grammar.step()[0]
        for limit in (0, -1, True, 1.5):
            with self.subTest(limit=limit), self.assertRaisesRegex(ValueError, "positive integer"):
                serialize_finding(finding, catalog, max_states=limit)


if __name__ == "__main__":
    unittest.main()
