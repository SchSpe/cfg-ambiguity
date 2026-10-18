import hashlib
import json
from functools import lru_cache

import grammar_engine as implementation



class ProofLimitExceeded(RuntimeError):
    pass


class GrammarCatalog:
    def __init__(self, data):
        self.data = data
        self.terminals = {name: implementation.Terminal(name) for name in data["terminals"]}
        self.nonterminals = {name: implementation.Nonterminal(name) for name in data["nonterminals"]}
        self.start = data["start"]
        symbols = self.terminals | self.nonterminals
        self.rules = []
        self.rules_by_lhs = {name: [] for name in self.nonterminals}
        self.rule_formulas = {}
        self.site_rules = {}
        self.site_formulas = {}
        self.rule_paths = {}
        width = max(3, len(str(len(data["productions"]))))
        for index, original in enumerate(data["productions"], 1):
            rule_id = f"P{index:0{width}d}"
            rhs = list(original["rhs"])
            formula = _join([symbols[name] for name in rhs], implementation.ConcatenationFormula)
            rule = dict(original)
            rule.update(id=rule_id, rhs=rhs, source=dict(data.get("source", {})),
                        text=f"{original['lhs']} → {' '.join(map(str, rhs)) if rhs else 'ε'}",
                        algebraic=implementation.format_formula(formula))
            self.rules.append(rule)
            self.rules_by_lhs[original["lhs"]].append(rule)
            self.rule_formulas[rule_id] = formula
        self.rules_by_id = {rule["id"]: rule for rule in self.rules}
        for name, nonterminal in self.nonterminals.items():
            rules = self.rules_by_lhs[name]
            if not rules:
                raise ValueError(f"No productions for {name}")
            nonterminal.definition = _join(
                [self.rule_formulas[rule["id"]] for rule in rules], implementation.UnionFormula)
            self._index_definition(name, nonterminal.definition, rules, ())
        self.grammar = implementation.Grammar(self.terminals.values(), self.nonterminals.values())
        self.formulas = {name: implementation.format_formula(nt.definition)
                         for name, nt in self.nonterminals.items()}
        self._definitions = {name: nt.definition for name, nt in self.nonterminals.items()}

    def _index_definition(self, owner, formula, rules, path):
        self.site_rules[owner, path] = tuple(rule["id"] for rule in rules)
        self.site_formulas[owner, path] = formula
        if len(rules) > 1:
            self._index_definition(owner, formula.left, rules[:-1], path + ("left",))
            self._index_definition(owner, formula.right, rules[-1:], path + ("right",))
        else:
            rule_id = rules[0]["id"]
            self.rule_paths[rule_id] = path
            self._index_rhs(owner, formula, rule_id, path)

    def _index_rhs(self, owner, formula, rule_id, path):
        self.site_rules[owner, path] = (rule_id,)
        self.site_formulas[owner, path] = formula
        if isinstance(formula, implementation.ConcatenationFormula):
            self._index_rhs(owner, formula.left, rule_id, path + ("left",))
            self._index_rhs(owner, formula.right, rule_id, path + ("right",))

    def check_finding(self, finding):
        owner = finding.nonterminal.name
        if self.nonterminals.get(owner) is not finding.nonterminal:
            raise ValueError("Finding does not belong to this grammar")
        if any(nt.definition is not self._definitions[name] for name, nt in self.nonterminals.items()):
            raise ValueError("Grammar definitions changed after the production catalog was built")
        if self.site_formulas.get((owner, tuple(finding.path))) is not finding.formula:
            raise ValueError("Finding does not match its recorded formula location")
        if finding.iteration < 1:
            raise ValueError("A finite ambiguity finding must have a positive level")


def _join(items, operator):
    if not items:
        return implementation.Epsilon()
    result = items[0]
    for item in items[1:]:
        result = operator(result, item)
    return result


def build_grammar(data):
    return GrammarCatalog(data)


def summarize_finding(finding, catalog):
    catalog.check_finding(finding)
    witness = list(finding.sentence.symbols)
    key = [finding.kind, finding.nonterminal.name, finding.iteration, list(finding.path), witness]
    if finding.factorizations is not None:
        key.append(sorted(len(left.symbols) for left, _ in finding.factorizations))
    identifier = hashlib.sha256(json.dumps(key, ensure_ascii=False, separators=(",", ":")).encode()).hexdigest()[:20]
    return {
        "id": identifier,
        "kind": finding.kind,
        "owner": finding.nonterminal.name,
        "level": finding.iteration,
        "path": list(finding.path),
        "expression": implementation.format_formula(finding.formula),
        "witness": witness,
        "candidate_production_ids": list(catalog.site_rules[finding.nonterminal.name, tuple(finding.path)]),
        "scope": "local",
        "scope_note": "This proves ambiguity at the marked formula in this nonterminal's definition; it does not by itself prove ambiguity of the start symbol.",
    }


class WitnessParser:
    def __init__(self, catalog, tokens, level, max_states=100000):
        if max_states is not None and (not isinstance(max_states, int)
                                       or isinstance(max_states, bool) or max_states < 1):
            raise ValueError("max_states must be a positive integer or None")
        self.catalog = catalog
        self.tokens = tuple(tokens)
        self.level = level
        self.max_states = max_states
        self.states = 0
        self.minimum = [{name: float("inf") for name in catalog.nonterminals}]
        self.maximum = [{name: -1 for name in catalog.nonterminals}]
        self.bounds = lru_cache(maxsize=None)(self._bounds)
        try:
            for budget in range(1, level + 1):
                minimum = {}
                maximum = {}
                for name, nt in catalog.nonterminals.items():
                    minimum[name], maximum[name] = self.bounds(nt.definition, budget - 1)
                self.minimum.append(minimum)
                self.maximum.append(maximum)
        except BaseException:
            self.bounds.cache_clear()
            raise
        self.parse = lru_cache(maxsize=None)(self._parse)

    def _consume_state(self):
        self.states += 1
        if self.max_states is not None and self.states > self.max_states:
            raise ProofLimitExceeded(
                f"Proof verification exceeded the {self.max_states:,}-state work limit. "
                "This witness has not been fully verified; increase max_states to retry.")

    def _bounds(self, formula, budget):
        self._consume_state()
        if isinstance(formula, implementation.Terminal):
            return 1, 1
        if isinstance(formula, implementation.Epsilon):
            return 0, 0
        if isinstance(formula, implementation.Nonterminal):
            return self.minimum[budget][formula.name], self.maximum[budget][formula.name]
        if isinstance(formula, implementation.ParenthesizedFormula):
            return self.bounds(formula.formula, budget)
        left_min, left_max = self.bounds(formula.left, budget)
        right_min, right_max = self.bounds(formula.right, budget)
        if isinstance(formula, implementation.UnionFormula):
            return min(left_min, right_min), max(left_max, right_max)
        if left_max < 0 or right_max < 0:
            return float("inf"), -1
        return left_min + right_min, left_max + right_max

    def _parse(self, formula, budget, begin, end):
        self._consume_state()
        minimum, maximum = self.bounds(formula, budget)
        if end - begin < minimum or end - begin > maximum:
            return None
        tokens = list(self.tokens[begin:end])
        if isinstance(formula, implementation.Terminal):
            if self.tokens[begin:end] == (formula.symbol,):
                return {"kind": "terminal", "symbol": formula.symbol, "tokens": tokens, "children": []}
            return None
        if isinstance(formula, implementation.Epsilon):
            return {"kind": "epsilon", "tokens": [], "children": []} if begin == end else None
        if isinstance(formula, implementation.Nonterminal):
            if budget <= 0:
                return None
            for rule in self.catalog.rules_by_lhs[formula.name]:
                child = self.parse(self.catalog.rule_formulas[rule["id"]], budget - 1, begin, end)
                if child is not None:
                    return {"kind": "nonterminal", "symbol": formula.name, "level": budget,
                            "production_id": rule["id"], "tokens": tokens, "children": [child]}
            return None
        if isinstance(formula, implementation.ParenthesizedFormula):
            child = self.parse(formula.formula, budget, begin, end)
            return None if child is None else {"kind": "parentheses", "tokens": tokens, "children": [child]}
        if isinstance(formula, implementation.UnionFormula):
            for side in ("left", "right"):
                child = self.parse(getattr(formula, side), budget, begin, end)
                if child is not None:
                    return {"kind": "union", "branch": side, "tokens": tokens, "children": [child]}
            return None
        left_min, left_max = self.bounds(formula.left, budget)
        right_min, right_max = self.bounds(formula.right, budget)
        if left_max < 0 or right_max < 0:
            return None
        first = max(begin + left_min, end - right_max)
        last = min(begin + left_max, end - right_min)
        for cut in range(int(first), int(last) + 1):
            left = self.parse(formula.left, budget, begin, cut)
            if left is None:
                continue
            right = self.parse(formula.right, budget, cut, end)
            if right is not None:
                return {"kind": "concatenation", "cut": cut - begin,
                        "tokens": tokens, "children": [left, right]}
        return None

    def require(self, formula, budget, begin, end):
        tree = self.parse(formula, budget, begin, end)
        if tree is None:
            raise ValueError("The recorded witness cannot be derived at its recorded approximation level")
        return tree


def _selected_production(catalog, owner, path, tree):
    while len(catalog.site_rules[owner, path]) > 1:
        if tree["kind"] != "union":
            raise ValueError("Production provenance does not match the derivation")
        path += (tree["branch"],)
        tree = tree["children"][0]
    return catalog.site_rules[owner, path][0], tree


def _production_tree(catalog, rule_id, tree, level):
    return {"kind": "production", "production_id": rule_id,
            "symbol": catalog.rules_by_id[rule_id]["lhs"], "level": level,
            "tokens": tree["tokens"], "children": [tree]}


def _supporting_rules(trees):
    found = set()
    pending = list(trees)
    while pending:
        tree = pending.pop()
        if "production_id" in tree:
            found.add(tree["production_id"])
        pending.extend(tree.get("children", []))
    return found


def serialize_finding(finding, catalog, max_states=100000):
    result = summarize_finding(finding, catalog)
    parser = WitnessParser(catalog, result["witness"], finding.iteration - 1, max_states=max_states)
    try:
        return _prove_finding(finding, catalog, result, parser)
    finally:
        parser.parse.cache_clear()
        parser.bounds.cache_clear()


def _prove_finding(finding, catalog, result, parser):
    owner = result["owner"]
    path = tuple(finding.path)
    word = tuple(result["witness"])
    budget = finding.iteration - 1
    derivations = []
    production_ids = set()
    if finding.kind == "union":
        if not isinstance(finding.formula, implementation.UnionFormula):
            raise ValueError("A union finding must refer to a union formula")
        alternatives = []
        for side in ("left", "right"):
            formula = getattr(finding.formula, side)
            tree = parser.require(formula, budget, 0, len(word))
            rule_id, selected = _selected_production(catalog, owner, path + (side,), tree)
            derivation = _production_tree(catalog, rule_id, selected, finding.iteration)
            alternatives.append({"side": side, "expression": implementation.format_formula(catalog.rule_formulas[rule_id]),
                                 "operand_expression": implementation.format_formula(formula),
                                 "production_id": rule_id, "derivation": derivation})
            derivations.append(derivation)
            production_ids.add(rule_id)
        if alternatives[0]["production_id"] == alternatives[1]["production_id"]:
            raise ValueError("The union proof must use two distinct production occurrences")
        result["alternatives"] = alternatives
        result["proof_statement"] = "The same terminal sequence is derived by both highlighted production alternatives."
    elif finding.kind == "concatenation":
        if not isinstance(finding.formula, implementation.ConcatenationFormula):
            raise ValueError("A concatenation finding must refer to a product formula")
        factorizations = []
        cuts = set()
        for left_sentence, right_sentence in finding.factorizations or ():
            left_tokens = tuple(left_sentence.symbols)
            right_tokens = tuple(right_sentence.symbols)
            if left_tokens + right_tokens != word:
                raise ValueError("The recorded factors do not concatenate to the witness")
            cut = len(left_tokens)
            left_tree = parser.require(finding.formula.left, budget, 0, cut)
            right_tree = parser.require(finding.formula.right, budget, cut, len(word))
            tree = {"kind": "concatenation", "cut": cut, "tokens": list(word),
                    "children": [left_tree, right_tree]}
            factorizations.append({"cut": cut, "left": list(left_tokens), "right": list(right_tokens),
                                   "left_derivation": left_tree, "right_derivation": right_tree,
                                   "derivation": tree})
            derivations.append(tree)
            cuts.add(cut)
        if len(cuts) < 2:
            raise ValueError("A concatenation proof requires two distinct token boundaries")
        production_ids.update(catalog.site_rules[owner, path])
        result["factorizations"] = factorizations
        result["left_expression"] = implementation.format_formula(finding.formula.left)
        result["right_expression"] = implementation.format_formula(finding.formula.right)
        result["proof_statement"] = "The same terminal sequence admits two different boundaries between the highlighted product's left and right factors."
    else:
        raise ValueError(f"Unsupported ambiguity finding: {finding.kind}")
    result["production_ids"] = [rule["id"] for rule in catalog.rules if rule["id"] in production_ids]
    supporting = _supporting_rules(derivations) | production_ids
    result["supporting_production_ids"] = [rule["id"] for rule in catalog.rules if rule["id"] in supporting]
    result["derivations"] = derivations
    result["verified"] = True
    result["verification"] = "Both derivations were independently checked against the original productions at this finite level; displayed approximation samples are not used."
    return result
