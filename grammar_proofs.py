"""Reconstruct two valid parse trees for an engine ambiguity finding."""

from functools import lru_cache

import grammar_engine as engine


class GrammarCatalog:
    """Build the engine formulas once and tie their paths to BNF productions."""

    def __init__(self, cfg):
        self.rules = cfg.productions
        self.nonterminals = {name: engine.Nonterminal(name) for name in cfg.nonterminals}
        symbols = {name: engine.Terminal(name) for name in cfg.terminals} | self.nonterminals
        self.rules_by_lhs = {name: [] for name in self.nonterminals}
        self.rule_formulas = []
        self.rule_paths = [None] * len(self.rules)
        self.site_rules = {}
        for index, (lhs, rhs) in enumerate(self.rules):
            self.rules_by_lhs[lhs].append(index)
            self.rule_formulas.append(_join([symbols[name] for name in rhs], engine.ConcatenationFormula))
        for name, nonterminal in self.nonterminals.items():
            rules = self.rules_by_lhs[name]
            nonterminal.definition = _join([self.rule_formulas[index] for index in rules], engine.UnionFormula)
            self._index_definition(name, nonterminal.definition, rules, ())
        self.grammar = engine.Grammar(self.nonterminals.values())

    def _index_definition(self, owner, formula, rules, path):
        # Definitions and right sides are left-associated chains built by _join.
        for rule in reversed(rules[1:]):
            self.rule_paths[rule] = path + ("right",)
            self._index_rhs(owner, formula.right, rule, path + ("right",))
            formula, path = formula.left, path + ("left",)
        self.rule_paths[rules[0]] = path
        self._index_rhs(owner, formula, rules[0], path)

    def _index_rhs(self, owner, formula, rule, path):
        while True:
            self.site_rules[owner, path] = (rule,)
            if not isinstance(formula, engine.ConcatenationFormula):
                break
            formula, path = formula.left, path + ("left",)


def _join(items, operator):
    if not items:
        return engine.Epsilon()
    result = items[0]
    for item in items[1:]:
        result = operator(result, item)
    return result


class WitnessParser:
    def __init__(self, catalog, tokens, level):
        self.catalog = catalog
        self.tokens = tokens
        self.minimum = [{name: float("inf") for name in catalog.nonterminals}]
        self.maximum = [{name: -1 for name in catalog.nonterminals}]
        self.bounds = lru_cache(maxsize=None)(self._bounds)
        try:
            for budget in range(1, level + 1):
                minimum, maximum = {}, {}
                for name, nt in catalog.nonterminals.items():
                    minimum[name], maximum[name] = self.bounds(nt.definition, budget - 1)
                self.minimum.append(minimum)
                self.maximum.append(maximum)
        except BaseException:
            self.bounds.cache_clear()
            raise
        self.parse = lru_cache(maxsize=None)(self._parse)

    def _bounds(self, formula, budget):
        if isinstance(formula, engine.Terminal):
            return 1, 1
        if isinstance(formula, engine.Epsilon):
            return 0, 0
        if isinstance(formula, engine.Nonterminal):
            return self.minimum[budget][formula.name], self.maximum[budget][formula.name]
        left_min, left_max = self.bounds(formula.left, budget)
        right_min, right_max = self.bounds(formula.right, budget)
        if isinstance(formula, engine.UnionFormula):
            return min(left_min, right_min), max(left_max, right_max)
        if left_max < 0 or right_max < 0:
            return float("inf"), -1
        return left_min + right_min, left_max + right_max

    def _parse(self, formula, budget, begin, end):
        minimum, maximum = self.bounds(formula, budget)
        if end - begin < minimum or end - begin > maximum:
            return None
        if isinstance(formula, engine.Terminal):
            return [formula.symbol] if self.tokens[begin:end] == (formula.symbol,) else None
        if isinstance(formula, engine.Epsilon):
            return [] if begin == end else None
        if isinstance(formula, engine.Nonterminal):
            for rule in self.catalog.rules_by_lhs[formula.name]:
                children = self.parse(self.catalog.rule_formulas[rule], budget - 1, begin, end)
                if children is not None:
                    return [{"symbol": formula.name, "rule": rule, "children": children}]
            return None
        left_min, left_max = self.bounds(formula.left, budget)
        right_min, right_max = self.bounds(formula.right, budget)
        first = max(begin + left_min, end - right_max)
        last = min(begin + left_max, end - right_min)
        for cut in range(int(first), int(last) + 1):
            left = self.parse(formula.left, budget, begin, cut)
            if left is None:
                continue
            right = self.parse(formula.right, budget, cut, end)
            if right is not None:
                return left + right
        return None

    def require(self, formula, budget, begin, end):
        children = self.parse(formula, budget, begin, end)
        if children is None:
            raise ValueError("The witness cannot be derived at this approximation level")
        return children


def _alternative_rule(catalog, owner, path, side, alternative):
    rules = catalog.site_rules.get((owner, alternative), ())
    if (alternative[:len(path) + 1] != path + (side,) or len(rules) != 1
            or catalog.rule_paths[rules[0]] != alternative):
        raise ValueError("The union alternatives do not match the finding's formula location")
    return rules[0]


def prove_finding(finding, catalog, level):
    """Return two checked trees, using at most `level` nonterminal expansions."""
    owner, path = finding.nonterminal.name, finding.path
    formula = catalog.nonterminals[owner].definition
    for part in path:
        formula = getattr(formula, part)
    if formula is not finding.formula or level < 1:
        raise ValueError("The finding does not match its formula location or approximation level")
    parser = WitnessParser(catalog, finding.sentence, level - 1)
    try:
        return _prove_finding(finding, catalog, parser, level - 1)
    finally:
        parser.parse.cache_clear()
        parser.bounds.cache_clear()


def _prove_finding(finding, catalog, parser, budget):
    owner, path, word = finding.nonterminal.name, finding.path, finding.sentence
    trees = []
    if finding.kind == "union":
        if not isinstance(finding.formula, engine.UnionFormula) or len(finding.alternatives) != 2:
            raise ValueError("A union finding must name two alternatives of a union formula")
        rules = [_alternative_rule(catalog, owner, path, side, alternative)
                 for side, alternative in zip(("left", "right"), finding.alternatives)]
        if rules[0] == rules[1]:
            raise ValueError("The union proof must use two distinct production occurrences")
        for rule in rules:
            children = parser.require(catalog.rule_formulas[rule], budget, 0, len(word))
            trees.append({"symbol": owner, "rule": rule, "children": children})
    elif finding.kind == "concatenation":
        if not isinstance(finding.formula, engine.ConcatenationFormula):
            raise ValueError("A concatenation finding must refer to a product formula")
        if len(finding.factorizations or ()) != 2:
            raise ValueError("A concatenation proof requires two factorizations")
        rule, = catalog.site_rules[owner, path]
        cuts = set()
        for left, right in finding.factorizations:
            if left + right != word:
                raise ValueError("The factors do not concatenate to the witness")
            cut = len(left)
            children = (parser.require(finding.formula.left, budget, 0, cut)
                        + parser.require(finding.formula.right, budget, cut, len(word)))
            tree = {"symbol": owner, "rule": rule, "children": children}
            if len(children) < len(catalog.rules[rule][1]):
                tree["rhs_prefix"] = len(children)
            trees.append(tree)
            cuts.add(cut)
        if len(cuts) != 2:
            raise ValueError("A concatenation proof requires two distinct token boundaries")
    else:
        raise ValueError(f"Unsupported ambiguity finding: {finding.kind}")
    return trees
