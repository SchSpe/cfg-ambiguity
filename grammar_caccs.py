"""Recognize and rewrite certain ambiguity-causing constructs in parsed BNF.

The four NSF patterns and the three later structural patterns are kept here,
independent of the finite-language checker. Rewrites return new CFG objects;
input productions are never changed. Unchanged rules keep their source line,
while generated rules use line 0. Structural recognition does not depend on
an approximation level and is not a proof that all ambiguity has been removed.
"""

from collections import defaultdict, deque
from dataclasses import dataclass, field, replace
from typing import NamedTuple

from grammar_engine import CFG, Epsilon, UnionFormula, ConcatenationFormula


@dataclass(eq=False)
class Terminal:
    symbol: str


@dataclass(eq=False)
class Nonterminal:
    name: str
    definition: object = None


@dataclass(frozen=True)
class CACCMatch:
    rule_id: str
    kind: str
    nonterminal: str
    path: tuple
    alternatives: tuple
    source: str
    reason: str
    rewrite_available: bool
    rewrite_reason: str
    _productions: tuple = field(repr=False, compare=False)


@dataclass(frozen=True)
class CACCRewrite:
    rule_id: str
    nonterminal: str
    before: str
    after: str
    introduced: tuple


@dataclass
class CACCResult:
    grammar: CFG
    changes: list
    remaining: list
    limit_reached: bool = False
    stalled: bool = False


@dataclass
class _Graph:
    terminals: tuple
    nonterminals: tuple


@dataclass
class _Match:
    rule_id: str
    kind: str
    nonterminal: Nonterminal
    path: tuple
    formula: object
    replacement: object
    source: str
    reason: str
    details: object = None
    alternatives: tuple = ()


def _join(formulas, operator):
    formulas = list(formulas)
    if operator is ConcatenationFormula:
        formulas = [formula for formula in formulas if not isinstance(formula, Epsilon)]
    if not formulas:
        return Epsilon()
    result = formulas[0]
    for formula in formulas[1:]:
        result = operator(result, formula)
    return result


def _flatten(formula, operator, path=()):
    if isinstance(formula, operator):
        return (_flatten(formula.left, operator, path + ("left",))
                + _flatten(formula.right, operator, path + ("right",)))
    return [(formula, path)]


def _walk_formula(formula, path=()):
    yield formula, path
    if isinstance(formula, (UnionFormula, ConcatenationFormula)):
        yield from _walk_formula(formula.left, path + ("left",))
        yield from _walk_formula(formula.right, path + ("right",))


def _formula_at(formula, path):
    for side in path:
        formula = getattr(formula, side)
    return formula


def _format_formula(formula):
    if isinstance(formula, Terminal):
        return formula.symbol
    if isinstance(formula, Nonterminal):
        return formula.name
    if isinstance(formula, Epsilon):
        return "ε"
    separator = " | " if isinstance(formula, UnionFormula) else " "
    return "(" + separator.join(_format_formula(item) for item, _ in _flatten(formula, type(formula))) + ")"


def _definition_text(nt):
    return nt.name + " ::= " + " | ".join(_format_formula(item) for item, _ in _flatten(nt.definition, UnionFormula))


def _build_graph(cfg):
    terminals = {name: Terminal(name) for name in cfg.terminals}
    nonterminals = {name: Nonterminal(name) for name in cfg.nonterminals}
    symbols = terminals | nonterminals
    alternatives = {name: [] for name in cfg.nonterminals}
    for lhs, rhs in cfg.productions:
        alternatives[lhs].append(_join((symbols[name] for name in rhs), ConcatenationFormula))
    for name, nt in nonterminals.items():
        nt.definition = _join(alternatives[name], UnionFormula)
    return _Graph(tuple(terminals.values()), tuple(nonterminals.values()))


def _to_cfg(graph, original):
    """Name nested choices rather than distributing them into large products."""
    nonterminals = list(graph.nonterminals)
    nested = {}
    productions = []
    index = 0
    while index < len(nonterminals):
        owner = nonterminals[index]
        index += 1
        for alternative, _ in _flatten(owner.definition, UnionFormula):
            rhs = []
            for factor, _ in _flatten(alternative, ConcatenationFormula):
                if isinstance(factor, Epsilon):
                    continue
                if isinstance(factor, UnionFormula):
                    if factor not in nested:
                        helper = Nonterminal(_fresh_name(graph, owner.name + "_part", nonterminals))
                        helper.definition = factor
                        nested[factor] = helper
                        nonterminals.append(helper)
                    factor = nested[factor]
                rhs.append(factor.symbol if isinstance(factor, Terminal) else factor.name)
            productions.append((owner.name, tuple(rhs)))
    sources = defaultdict(deque)
    for rule, line in zip(original.productions, original.production_lines):
        sources[rule].append(line)
    lines = [sources[rule].popleft() if sources[rule] else 0 for rule in productions]
    return CFG(productions, lines)


def _selection(match):
    owner = match.nonterminal.name if isinstance(match, _Match) else match.nonterminal
    return match.rule_id, owner, match.path, match.alternatives


def _available(graph, match):
    if match.rule_id != "dangling_suffix":
        return True
    return bool(_dangling_group(_Productions(graph.nonterminals), match.nonterminal, match.details[-1]))


def _public_match(cfg, graph, match):
    available = _available(graph, match)
    return CACCMatch(match.rule_id, match.kind, match.nonterminal.name, match.path,
                     match.alternatives, match.source, match.reason, available,
                     "" if available else "The nearest-binding rewrite does not support this recursive or nullable context.",
                     cfg.productions)


def recognize_caccs(cfg):
    """Return structural matches, including matches whose rewrite is unsupported."""
    graph = _build_graph(cfg)
    return [_public_match(cfg, graph, match) for match in _recognize_caccs(graph)]


def apply_cacc(cfg, match):
    """Apply one recognized match to a copy, or return stalled when unsupported.

    A match from a different or edited grammar raises ValueError. Unsupported
    rewrites leave every production and source line unchanged.
    """
    if not isinstance(match, CACCMatch) or match._productions != cfg.productions:
        raise ValueError("The CACC match belongs to a different or edited grammar")
    graph = _build_graph(cfg)
    selected = next((item for item in _recognize_caccs(graph) if _selection(item) == _selection(match)), None)
    if selected is None:
        raise ValueError("The CACC match is no longer present in this grammar")
    if not _available(graph, selected):
        result = CFG(cfg.productions, cfg.production_lines)
        return CACCResult(result, [], recognize_caccs(result), stalled=True)
    rewritten, change = _apply_cacc(graph, selected)
    stalled = _grammar_key(rewritten) == _grammar_key(graph)
    result = CFG(cfg.productions, cfg.production_lines) if stalled else _to_cfg(rewritten, cfg)
    change = replace(change, introduced=tuple(name for name in result.nonterminals if name not in cfg.nonterminals))
    return CACCResult(result, [] if stalled else [change], recognize_caccs(result), stalled=stalled)


def transform_caccs(cfg, max_steps=100):
    """Apply supported rewrites until none remain, no progress is possible, or the limit is reached."""
    if type(max_steps) is not int or max_steps < 0:
        raise ValueError("max_steps must be a nonnegative integer")
    result = CFG(cfg.productions, cfg.production_lines)
    seen = {result.productions}
    changes = []
    stalled = False
    while len(changes) < max_steps:
        graph = _build_graph(result)
        matches = _recognize_caccs(graph)
        if not matches:
            break
        for match in matches:
            if not _available(graph, match):
                continue
            candidate, change = _apply_cacc(graph, match)
            if _grammar_key(candidate) == _grammar_key(graph):
                continue
            candidate = _to_cfg(candidate, result)
            key = candidate.productions
            if key not in seen:
                break
        else:
            stalled = True
            break
        change = replace(change, introduced=tuple(name for name in candidate.nonterminals if name not in result.nonterminals))
        result = candidate
        seen.add(key)
        changes.append(change)
    remaining = recognize_caccs(result)
    return CACCResult(result, changes, remaining, bool(remaining) and len(changes) == max_steps, stalled)


def _formula_key(formula, names=False):
    """A key that is equal for formulas differing only in grouping.

    Nonterminals compare by identity, or by name when `names` is set, which
    allows two grammars to be compared.
    """
    if isinstance(formula, Terminal):
        return ("terminal", formula.symbol)
    if isinstance(formula, Nonterminal):
        return ("nonterminal", formula.name if names else formula)
    if isinstance(formula, Epsilon):
        return ("epsilon",)
    operator = type(formula)
    return (operator.__name__, tuple(_formula_key(item, names) for item, _ in _flatten(formula, operator)))


def _grammar_key(grammar):
    return tuple((nt.name, _formula_key(nt.definition, names=True)) for nt in grammar.nonterminals)


class _Derives(NamedTuple):
    """What a formula can derive."""
    any_sentence: bool          # at least one sentence
    nonempty_sentence: bool     # at least one sentence other than ε


def _derives(formula, known):
    """What `formula` derives, given what each nonterminal is `known` to derive."""
    if isinstance(formula, Terminal):
        return _Derives(True, True)
    if isinstance(formula, Epsilon):
        return _Derives(True, False)
    if isinstance(formula, Nonterminal):
        return known[formula]
    left = _derives(formula.left, known)
    right = _derives(formula.right, known)
    if isinstance(formula, UnionFormula):
        return _Derives(left.any_sentence or right.any_sentence,
                        left.nonempty_sentence or right.nonempty_sentence)
    return _Derives(left.any_sentence and right.any_sentence,
                    (left.nonempty_sentence and right.any_sentence)
                    or (left.any_sentence and right.nonempty_sentence))


def _nonterminal_derives(grammar):
    """What each nonterminal derives: the least fixed point of _derives."""
    known = {nt: _Derives(False, False) for nt in grammar.nonterminals}
    while True:
        updated = {nt: _derives(nt.definition, known) for nt in grammar.nonterminals}
        if updated == known:
            return known
        known = updated


_CACC_SOURCE = "NSF report, Section 6, "


def _recognize_caccs(grammar):
    """All matches, in the order their rewrites are to run: transparent
    cycles first, which the other union rewrites assume gone; subsumed
    alternatives; dangling suffixes, which have to be rewritten before a
    mixed recursion they hold; then mixed recursions, self embeddings and
    the rest."""
    known = _nonterminal_derives(grammar)
    productions = _Productions(grammar.nonterminals)
    mixed, embedded, local = [], [], []
    for nt in grammar.nonterminals:
        alternatives = [    # (alternative, its path, its factors)
            (alternative, path, [factor for factor, _ in _flatten(alternative, ConcatenationFormula)])
            for alternative, path in _flatten(nt.definition, UnionFormula)
        ]
        if known[nt].any_sentence and len(alternatives) >= 2:
            mixed += _mixed_recursions(nt, alternatives, known)
            embedded += _self_embeddings(nt, alternatives, known)
        for formula, path in _walk_formula(nt.definition):
            if not _productive_context(nt.definition, path, known):
                continue
            if isinstance(formula, UnionFormula):
                local += _duplicate_union(nt, formula, path, known)
            elif isinstance(formula, ConcatenationFormula):
                local += _optional_squares(nt, formula, path, known, productions)
    return (_transparent_cycles(productions) + _subsumed_alternatives(productions)
            + _dangling_suffixes(productions) + mixed + embedded + local)


def _productive_context(formula, path, known):
    """A local ambiguity matters only if its surrounding product can derive a sentence."""
    for side in path:
        if isinstance(formula, ConcatenationFormula):
            sibling = formula.right if side == "left" else formula.left
            if not _derives(sibling, known).any_sentence:
                return False
        formula = getattr(formula, side)
    return True


def _mixed_recursions(nt, alternatives, known):
    """A ::= β A | A γ | δ, where δ stands for all the other alternatives."""
    matches = []
    for _, beta_path, beta_factors in alternatives:         # β A
        if beta_factors[-1] is not nt:
            continue
        beta = _join(beta_factors[:-1], ConcatenationFormula)
        if not _derives(beta, known).any_sentence:
            continue
        for _, gamma_path, gamma_factors in alternatives:   # A γ
            if gamma_path == beta_path or gamma_factors[0] is not nt:
                continue
            gamma = _join(gamma_factors[1:], ConcatenationFormula)
            rest = [alternative for alternative, path, _ in alternatives
                    if path not in (beta_path, gamma_path)]
            if not rest or not _derives(gamma, known).any_sentence:
                continue
            matches.append(_Match(
                "mixed_recursion", "union", nt, (), nt.definition, None,
                _CACC_SOURCE + "Corollary 1 (p. 6)",
                "Distinct productive prefix and suffix recursive alternatives overlap.",
                (beta, gamma, _join(rest, UnionFormula)), (beta_path, gamma_path)))
    return matches


def _self_embeddings(nt, alternatives, known):
    """A ::= A β A | γ, where γ stands for all the other alternatives."""
    matches = []
    for _, path, factors in alternatives:
        if len(factors) < 2 or factors[0] is not nt or factors[-1] is not nt:
            continue
        beta = _join(factors[1:-1], ConcatenationFormula)
        beta_derives = _derives(beta, known)
        if not beta_derives.any_sentence:
            continue
        gamma = _join((alternative for alternative, other_path, _ in alternatives
                       if other_path != path), UnionFormula)
        replacement = UnionFormula(_join((nt, beta, gamma), ConcatenationFormula), gamma)
        nonempty = known[nt].nonempty_sentence or beta_derives.nonempty_sentence
        matches.append(_Match(
            "self_embedding", "concatenation" if nonempty else "derivation",
            nt, (), nt.definition, replacement,
            _CACC_SOURCE + "Corollary 2 (p. 6)",
            "A productive A beta A alternative permits distinct recursive associations.",
            alternatives=(path,)))
    return matches


def _duplicate_union(nt, formula, path, known):
    """X | X: an alternative that repeats an earlier one of the same union."""
    first_seen = {}
    retained = []
    repeated = []
    for alternative, alternative_path in _flatten(formula, UnionFormula, path):
        key = _formula_key(alternative)
        if key in first_seen and _derives(alternative, known).any_sentence:
            repeated.append((first_seen[key], alternative_path))
        else:
            retained.append(alternative)
            first_seen[key] = alternative_path
    if not repeated:
        return []
    return [_Match(
        "duplicate_union", "union", nt, path, formula, _join(retained, UnionFormula),
        _CACC_SOURCE + "union idempotency (p. 6)",
        "The same productive alternative occurs more than once.",
        alternatives=repeated)]


def _optional_squares(nt, formula, path, known, productions):
    """(X | ε) (X | ε): two neighbouring factors that are the same optional X."""
    factors = _flatten(formula, ConcatenationFormula, path)
    if not all(_derives(factor, known).any_sentence for factor, _ in factors):
        return []
    matches = []
    for i in range(len(factors) - 1):
        (left, left_path), (right, right_path) = factors[i], factors[i + 1]
        if (left is right and isinstance(left, Nonterminal)
                and left in productions.nullable and left in productions.nonempty):
            matches.append(_Match(
                "optional_square", "concatenation", nt, path, formula, None,
                _CACC_SOURCE + "optional-expression square (p. 6)",
                "Either occurrence of the nullable nonterminal can supply the same nonempty block.",
                details=(path, i), alternatives=(left_path, right_path)))
            continue
        body, other_body = _optional_body(left), _optional_body(right)
        if (body is None or other_body is None
                or _formula_key(body) != _formula_key(other_body)
                or not _derives(body, known).any_sentence):
            continue
        square = _join((ConcatenationFormula(body, body), body, Epsilon()), UnionFormula)
        rebuilt = [factor for factor, _ in factors[:i]] + [square] + [factor for factor, _ in factors[i + 2:]]
        matches.append(_Match(
            "optional_square", "concatenation" if _derives(body, known).nonempty_sentence else "derivation",
            nt, path, formula, _join(rebuilt, ConcatenationFormula),
            _CACC_SOURCE + "optional-expression square (p. 6)",
            "Either optional factor can supply the same productive block.",
            alternatives=(left_path, right_path)))
    return matches


def _optional_body(formula):
    """The union of the other alternatives when one alternative of `formula`
    is ε (X for X | ε), otherwise None."""
    alternatives = _flatten(formula, UnionFormula)
    if len(alternatives) >= 2:
        for i, (alternative, _) in enumerate(alternatives):
            if isinstance(alternative, Epsilon):
                return _join((item for j, (item, _) in enumerate(alternatives) if i != j), UnionFormula)
    return None


# The three newer constructs work on productions: what a sequence of symbols
# derives, which symbols derive ε, which can end a derivation.

class _Productions:
    """The definitions of `nonterminals` read as productions.

    Every union of a definition is a symbol: the definition of each
    nonterminal, and each union that is a factor of an alternative, a
    nonterminal without a name. Each alternative is a production, its
    right-hand side a tuple of symbols with the ε factors left out: a
    terminal's symbol, a Nonterminal, or such a nested UnionFormula.

    rules        {symbol: [(rhs, alternative, path)]}, the symbols in grammar
                 order, a nested union after the nonterminal that holds it
    owner, path  the nonterminal whose definition holds a symbol, and the
                 symbol's path there (() for the nonterminal itself)
    nullable, productive, nonempty
                 the symbols that derive ε, some sentence, and some sentence
                 other than ε; a terminal is productive and nonempty
    """

    def __init__(self, nonterminals):
        self.rules, self.owner, self.path = {}, {}, {}
        for nt in nonterminals:
            self._read(nt, nt.definition, nt, ())
        self.order = {symbol: index for index, symbol in enumerate(self.rules)}
        self.nullable = self._least(lambda rhs, found: all(symbol in found for symbol in rhs))
        self.productive = self._least(lambda rhs, found: all(
            self.is_terminal(symbol) or symbol in found for symbol in rhs))
        self.nonempty = self._least(lambda rhs, found: self.derives_sentence(rhs) and any(
            self.is_terminal(symbol) or symbol in found for symbol in rhs))
        self._steps, self._corners, self._ends = {}, {}, {}

    def _read(self, symbol, formula, owner, path):
        rules = self.rules[symbol] = []
        self.owner[symbol], self.path[symbol] = owner, path
        for alternative, alternative_path in _flatten(formula, UnionFormula, path):
            rhs = []
            for factor, factor_path in _flatten(alternative, ConcatenationFormula, alternative_path):
                if not isinstance(factor, Epsilon):
                    rhs.append(_symbol(factor))
                if isinstance(factor, UnionFormula):
                    self._read(factor, factor, owner, factor_path)
            rules.append((tuple(rhs), alternative, alternative_path))

    def _least(self, holds):
        """The least set of symbols with a production whose rhs `holds`, given the set."""
        found = set()
        changed = True
        while changed:
            changed = False
            for symbol, rules in self.rules.items():
                if symbol not in found and any(holds(rhs, found) for rhs, _, _ in rules):
                    found.add(symbol)
                    changed = True
        return found

    def is_terminal(self, symbol):
        return symbol not in self.rules

    def derives_sentence(self, symbols):
        return all(self.is_terminal(symbol) or symbol in self.productive for symbol in symbols)

    def derives_epsilon(self, symbols):
        return all(symbol in self.nullable for symbol in symbols)

    def derives_nonempty(self, symbols):
        return self.derives_sentence(symbols) and any(
            self.is_terminal(symbol) or symbol in self.nonempty for symbol in symbols)

    def useful(self, symbol):
        """The productions of `symbol` whose symbols all derive some sentence."""
        return [rule for rule in self.rules[symbol] if self.derives_sentence(rule[0])]

    def steps(self, symbol, side):
        """The symbols Y with a useful production `symbol` ::= σ Y τ where τ
        is nullable (side "right"), σ is ("left"), or both are ("transparent")."""
        if side not in self._steps:
            self._steps[side] = {
                lhs: [target for rhs, _, _ in self.useful(lhs) for i, target in enumerate(rhs)
                      if not self.is_terminal(target)
                      and (side == "left" or self.derives_epsilon(rhs[i + 1:]))
                      and (side == "right" or self.derives_epsilon(rhs[:i]))]
                for lhs in self.rules}
        return self._steps[side].get(symbol, [])

    def corners(self, symbol, side):
        """The symbols that `symbol` reaches by steps(), itself included; for
        side "right", the symbols at the right end of its derivations."""
        key = (symbol, side)
        if key not in self._corners:
            reached, stack = {symbol}, [symbol]
            while stack:
                for target in self.steps(stack.pop(), side):
                    if target not in reached:
                        reached.add(target)
                        stack.append(target)
            self._corners[key] = reached
        return self._corners[key]

    def ends(self, side):
        """{symbol: the symbols with a derivation whose first ("left") or last
        ("right") symbol it is}, over all productions, unproductive ones too."""
        if side not in self._ends:
            first = {}
            for lhs, rules in self.rules.items():
                first[lhs] = set()
                for rhs, _, _ in rules:
                    for symbol in (rhs if side == "left" else reversed(rhs)):
                        first[lhs].add(symbol)
                        if symbol not in self.nullable:
                            break
            hosts = defaultdict(set)
            for lhs in self.rules:
                reached, stack = {lhs}, [lhs]
                while stack:
                    for symbol in first.get(stack.pop(), ()):
                        if symbol not in reached:
                            reached.add(symbol)
                            stack.append(symbol)
                for symbol in reached:
                    hosts[symbol].add(lhs)
            self._ends[side] = hosts
        return self._ends[side]


class _Derivations:
    """Exact tests source ⇒* target between sequences of symbols, with the
    productions of `productions` except `excluded` (a symbol and the index
    of one of its productions), and the nullable symbols found again
    without it.

    For each target, the symbols that derive each of its spans are found
    shortest span first, as in the CYK algorithm, and within a span by a
    fixed point, for the productions that cover the span with one symbol and
    nullable ones around it."""

    def __init__(self, productions, excluded=None):
        self.productions = productions
        self.rules = {symbol: [rhs for index, (rhs, _, _) in enumerate(rules) if (symbol, index) != excluded]
                      for symbol, rules in productions.rules.items()}
        removed = productions.rules[excluded[0]][excluded[1]][0] if excluded else None
        self.nullable = productions.nullable
        if removed is not None and productions.derives_epsilon(removed):     # perhaps the only way to ε
            self.nullable = set()
            changed = True
            while changed:
                changed = False
                for symbol, alternatives in self.rules.items():
                    if symbol not in self.nullable and any(
                            all(item in self.nullable for item in rhs) for rhs in alternatives):
                        self.nullable.add(symbol)
                        changed = True
        self._charts = {}

    def derives(self, source, target):
        if not target:
            return all(symbol in self.nullable for symbol in source)
        if not self._ends_fit(source, target):
            return False
        chart = self._chart(target)
        return self._covers(source, 0, len(target), target, chart, chart[0, len(target)])

    def _ends_fit(self, source, target):
        """A quick necessary condition: some derivation of `source` begins
        with the first symbol of `target`, and some ends with its last."""
        for side, end, sequence in (("left", target[0], source), ("right", target[-1], source[::-1])):
            hosts = self.productions.ends(side).get(end, ())
            for symbol in sequence:
                if symbol == end or symbol in hosts:
                    break
                if symbol not in self.productions.nullable:
                    return False
            else:
                return False
        return True

    def _chart(self, target):
        """{(i, j): the symbols that derive target[i:j]}"""
        if target not in self._charts:
            starts, finals = self.productions.ends("left"), self.productions.ends("right")
            chart = {}
            for length in range(1, len(target) + 1):
                for i in range(len(target) - length + 1):
                    j = i + length
                    candidates = starts.get(target[i], set()) & finals.get(target[j - 1], set())
                    found = {target[i]} if length == 1 and target[i] in self.rules else set()
                    changed = True
                    while changed:
                        changed = False
                        for symbol in candidates - found:
                            if any(self._covers(rhs, i, j, target, chart, found)
                                   for rhs in self.rules[symbol]):
                                found.add(symbol)
                                changed = True
                    chart[i, j] = found
            self._charts[target] = chart
        return self._charts[target]

    def _covers(self, rhs, i, j, target, chart, found):
        """Whether `rhs` derives target[i:j], where `found` holds the symbols
        known so far to derive that span."""
        reached = {i}
        for symbol in rhs:
            following = set()
            for p in reached:
                if symbol in self.rules:
                    if symbol in self.nullable:
                        following.add(p)
                    following.update(q for q in range(p + 1, j + 1)
                                     if symbol in (found if (p, q) == (i, j) else chart[p, q]))
                elif p < j and target[p] == symbol:
                    following.add(p + 1)
            reached = following
            if not reached:
                return False
        return j in reached


def _symbol(factor):
    """The symbol of _Productions that a factor of an alternative stands for."""
    return factor.symbol if isinstance(factor, Terminal) else factor


def _factors(alternative):
    """The factors of an alternative without its ε ones, one per symbol of its production."""
    return [factor for factor, _ in _flatten(alternative, ConcatenationFormula)
            if not isinstance(factor, Epsilon)]


def _component(productions, symbol):
    """The symbols that `symbol` reaches by transparent steps and that reach
    it back, its strongly connected component, in grammar order."""
    return sorted((other for other in productions.corners(symbol, "transparent")
                   if symbol in productions.corners(other, "transparent")), key=productions.order.get)


def _step_positions(productions, rhs, members):
    """The positions of `members` in `rhs` whose context is nullable."""
    return [i for i, symbol in enumerate(rhs)
            if symbol in members and productions.derives_epsilon(rhs[:i] + rhs[i + 1:])]


def _cycle_parts(productions, component):
    """What rewriting a component of transparent steps needs: the symbols of
    the steps' left and right contexts that lie outside it and derive a
    nonempty sentence, as {"left": {symbol: a factor for it}, "right": …};
    the alternatives that are not steps, the exits, as {key: (rhs,
    alternative)}; and whether a context holds a member."""
    members = set(component)
    contexts = {"left": {}, "right": {}}
    exits = {}
    nested = False
    for member in component:
        for rhs, alternative, _ in productions.rules[member]:
            factors = _factors(alternative)
            positions = _step_positions(productions, rhs, members)
            for i in positions:
                for side, symbols, items in (("left", rhs[:i], factors[:i]),
                                             ("right", rhs[i + 1:], factors[i + 1:])):
                    for symbol, factor in zip(symbols, items):
                        nested = nested or symbol in members
                        if symbol not in members and symbol in productions.nonempty:
                            contexts[side].setdefault(symbol, factor)
            if not positions:
                exits.setdefault(_formula_key(alternative), (rhs, alternative))
    return contexts, exits, nested


def _transparent_cycles(productions):
    """X ::= σ Y τ with σ and τ nullable is a transparent step: every
    sentence of Y is one of X. When such steps form a cycle, the symbols on
    it share one language, so every sentence of an alternative δ of X that
    is not a step is also one of each step α of X: X ::= δ | α is a union
    ambiguity, as in A ::= A | d, or A ::= P A Q | d with P and Q nullable.
    One match per strongly connected component of the steps, at its first
    such pair; the rewrite rebuilds the whole component.

    A cycle comes after the cycles that the nonempty versions of its
    symbols would copy: with B ::= B C | ε and C ::= C C | c | ε, a C' made
    while C ::= C C stands would be C' ::= C' C | C' | c, a cycle again."""
    found, seen = [], set()
    for symbol in productions.rules:
        if symbol in seen:
            continue
        component = _component(productions, symbol)
        seen.update(component)
        if len(component) == 1 and symbol not in productions.steps(symbol, "transparent"):
            continue
        members = set(component)
        for member in component:
            useful = productions.useful(member)
            steps = [path for rhs, _, path in useful if _step_positions(productions, rhs, members)]
            exits = [path for rhs, _, path in useful if not _step_positions(productions, rhs, members)]
            if steps and exits:
                owner = productions.owner[member]
                found.append((component, _Match(
                    "transparent_cycle", "union", owner, productions.path[member],
                    owner.definition if member is owner else member, None,
                    "the cycles A ⇒+ A that grammars usually exclude, through nullable contexts",
                    "The members of a cycle with nullable contexts derive each other's sentences, "
                    "so a sentence of an exit is also one of a cycle step.",
                    details=tuple(component), alternatives=(exits[0], steps[0]))))
                break
    cycle_of = {member: index for index, (component, _) in enumerate(found) for member in component}
    ordered, visited = [], set()

    def visit(index):
        if index in visited:
            return
        visited.add(index)
        contexts, exits, nested = _cycle_parts(productions, found[index][0])
        versioned = [*contexts["left"], *contexts["right"]]
        if nested:
            versioned += [symbol for rhs, _ in exits.values() if productions.derives_epsilon(rhs)
                          for symbol in rhs]
        for symbol in versioned:
            for reached in productions.corners(symbol, "left"):
                if cycle_of.get(reached, index) != index:
                    visit(cycle_of[reached])
        ordered.append(found[index][1])

    for index in range(len(found)):
        visit(index)
    return ordered


def _subsumed_alternatives(productions):
    """A ::= α | α' | γ, where α derives α' without the rule A ::= α'. Every
    sentence of α' is then one of α too, and deleting A ::= α' keeps every
    language, as α still derives α'. The test is exact, with the nullable
    symbols found again without A ::= α': in A ::= ε | B, B ::= A, the ε of
    B comes from A ::= ε, which must stay. A union nested in a definition
    counts as well, as for a duplicate union, whose pairs of equal
    alternatives are left to it."""
    matches = []
    for symbol, rules in productions.rules.items():
        if len(rules) < 2:
            continue
        owner = productions.owner[symbol]
        keys = [_formula_key(alternative) for _, alternative, _ in rules]
        for index, (target, _, target_path) in enumerate(rules):
            if not productions.derives_sentence(target):
                continue
            derivations = None
            for other, (source, _, source_path) in enumerate(rules):
                if keys[other] == keys[index]:
                    continue
                derivations = derivations or _Derivations(productions, (symbol, index))
                if derivations.derives(source, target):
                    kept = [alternative for i, (_, alternative, _) in enumerate(rules) if i != index]
                    matches.append(_Match(
                        "subsumed_alternative", "union", owner, productions.path[symbol],
                        owner.definition if symbol is owner else symbol, _join(kept, UnionFormula),
                        _CACC_SOURCE + "union idempotency (p. 6), extended to derivations",
                        "One alternative derives another, so each sentence of the second is one of both.",
                        alternatives=(source_path, target_path)))
    return matches


def _dangling_roles(productions, owner, mirrored):
    """The alternatives of `owner` read from the right end (from the left
    when `mirrored`), and {index of one: its roles}, each (role, (μ, X)):
    "open" for μ X, "closed" for μ X γ, "option" for μ A ν, where A is the
    owner. Only prefixes that something closes count: i S e S is closed
    after i, and open after i S e for nothing."""
    side = "left" if mirrored else "right"
    alternatives = [rhs[::-1] if mirrored else rhs for rhs, _, _ in productions.rules[owner]]
    useful = [productions.derives_sentence(rhs) for rhs in alternatives]
    kinds = {}      # (μ, X) of each open alternative μ X, in order
    for rhs, ok in zip(alternatives, useful):
        if (ok and len(rhs) >= 2 and isinstance(rhs[-1], Nonterminal)
                and owner in productions.corners(rhs[-1], side)):
            kinds[rhs[:-1], rhs[-1]] = None
    found = {}
    for index, rhs in enumerate(alternatives):
        if not useful[index]:
            continue
        found[index] = []
        for mu, corner in kinds:
            head = mu + (corner,)
            if rhs == head:
                found[index].append(("open", (mu, corner)))
            elif rhs[:len(head)] == head and not productions.derives_epsilon(rhs[len(head):]):
                found[index].append(("closed", (mu, corner)))
        if owner in rhs:
            at = len(rhs) - 1 - rhs[::-1].index(owner)
            nu = rhs[at + 1:]
            if (nu and productions.derives_epsilon(nu) and productions.derives_nonempty(nu)
                    and not productions.derives_epsilon(rhs[:at])):
                found[index].append(("option", (rhs[:at], owner)))
    closing = {kind for candidates in found.values() for role, kind in candidates if role != "open"}
    found = {index: [(role, kind) for role, kind in candidates if kind in closing]
             for index, candidates in found.items()}
    return alternatives, {index: candidates for index, candidates in found.items() if candidates}


def _dangling_group(productions, owner, mirrored):
    """The dangling suffixes of `owner` as {index of an alternative: (role,
    (μ, X))}, read as _dangling_roles does, or None when there are none or
    the rewrite does not accept them:

    - an alternative has two roles, or the other end has dangling suffixes
      too (rewriting one end would copy the other's into M, unseen);
    - some μ derives ε, so that γ can close an empty μ as well;
    - some μ can begin with A, some γ begins with A while A is nullable, or
      some ν holds A;
    - another alternative can begin with A, unless it is A c and every X is
      A (see below);
    - a symbol that ends in A is followed, at the end of an alternative, by
      nullable symbols one of which derives a nonempty sentence: it is at
      the end only when they derive ε, so its copy would be too narrow.
    """
    alternatives, found = _dangling_roles(productions, owner, mirrored)
    if (not found or any(len(candidates) > 1 for candidates in found.values())
            or _dangling_roles(productions, owner, not mirrored)[1]):
        return None
    roles = {index: candidates[0] for index, candidates in found.items()}
    # A generalized rewrite with several prefixes and nullable suffix parts
    # has a known language-preservation counterexample. Keep reporting the
    # construct, but leave this family unchanged until its rewrite is proved.
    if len({kind for _, kind in roles.values()}) > 1 and any(role == "option" for role, _ in roles.values()):
        return None

    def begins_with_owner(rhs):
        for symbol in rhs:
            if not productions.is_terminal(symbol) and owner in productions.corners(
                    symbol, "right" if mirrored else "left"):
                return True
            if symbol not in productions.nullable:
                return False
        return False

    def ends_in_owner(symbol):
        return not productions.is_terminal(symbol) and owner in productions.corners(
            symbol, "left" if mirrored else "right")

    for index, (role, (mu, _)) in roles.items():
        rest = alternatives[index][len(mu) + 1:]
        if (productions.derives_epsilon(mu) or begins_with_owner(mu) or role == "option" and owner in rest
                or role == "closed" and rest[0] is owner and owner in productions.nullable):
            return None
    for symbol in productions.rules:
        if not ends_in_owner(symbol):
            continue
        for index, (rhs, _, _) in enumerate(productions.rules[symbol]):
            if (not productions.derives_sentence(rhs)
                    or symbol is owner and roles.get(index, (None,))[0] == "option"):    # split first
                continue
            rhs = rhs[::-1] if mirrored else rhs
            for i in reversed(range(len(rhs) - 1)):
                after = rhs[i + 1:]
                if not productions.derives_epsilon(after):
                    break
                if ends_in_owner(rhs[i]) and any(item in productions.nonempty for item in after):
                    return None
    # The rewrite makes M c of A c, which is right when X is A. Through a copy
    # of X it loses sentences, and keeping A c keeps the ambiguity: in
    # A ::= b C | b C g | A c | x, C ::= p A | y, b p b y c g needs the open
    # b C inside A c.
    if any(index not in roles and productions.derives_sentence(rhs) and begins_with_owner(rhs)
           and (rhs[0] is not owner or any(corner is not owner for _, (_, corner) in roles.values()))
           for index, rhs in enumerate(alternatives)):
        return None
    return roles


def _dangling_suffixes(productions):
    """A ::= μ X | μ X γ | δ: an open alternative and a closed one with the
    same prefix μ and nonterminal X, where X is A or ends in A (X ⇒* ξ A), and
    γ is not nullable. With m from μ, a from A and g from γ, the sentence
    m m a g is then in both, as m (m a g) and as m (m a) g: g can close
    either μ, as the else of nested if statements can. The mirror image,
    A ::= X μ | γ X μ | δ, counts too, and so does μ A ν with a nullable ν
    that derives a nonempty sentence, the option of μ A | μ A ν written as
    one rule: m (m a g) ε and m (m a) g are two cuts before ν.

    Recognition is independent of the nearest-binding rewrite's safety
    restrictions. Prefixes must be equal: commuting ones, as in
    A ::= b A | b b A m | d, are ambiguous too, but not matched."""
    matches = []
    for owner in productions.rules:
        if not isinstance(owner, Nonterminal) or owner not in productions.productive:
            continue
        rules = productions.rules[owner]
        for mirrored in (False, True):
            _, candidates = _dangling_roles(productions, owner, mirrored)
            roles = [(index, role, kind) for index, values in candidates.items() for role, kind in values]
            orient = (lambda items: items[::-1]) if mirrored else (lambda items: items)
            for index, role, (mu, corner) in roles:
                if role == "open":
                    continue
                factors = orient(_factors(rules[index][1]))
                details = (_join(orient(factors[:len(mu)]), ConcatenationFormula), corner,
                           _join(orient(factors[len(mu) + 1:]), ConcatenationFormula), mirrored)
                if role == "option":
                    sites, kind = [(rules[index][2],)], "concatenation"
                else:
                    sites = [(rules[other][2], rules[index][2]) for other, other_role, other_kind
                             in roles if other_role == "open" and other_kind == (mu, corner)]
                    kind = "union"
                for alternatives in sites:
                    matches.append(_Match(
                        "dangling_suffix", kind, owner, (), owner.definition, None,
                        "the dangling else, extended to corner chains",
                        "A closing suffix after a repeated prefix can close either occurrence of the prefix.",
                        details, alternatives))
    return matches


def _clone_formula(formula, terminals, nonterminals):
    if isinstance(formula, Terminal):
        return terminals[formula.symbol]
    if isinstance(formula, Nonterminal):
        return nonterminals[formula]
    if isinstance(formula, Epsilon):
        return Epsilon()
    return type(formula)(_clone_formula(formula.left, terminals, nonterminals),
                         _clone_formula(formula.right, terminals, nonterminals))


def _clone_grammar(grammar):
    """A copy at level 0 and without cfg, with the maps {symbol: new Terminal}
    and {nonterminal: its copy} that _clone_formula needs."""
    terminals = {terminal.symbol: Terminal(terminal.symbol) for terminal in grammar.terminals}
    nonterminals = {nt: Nonterminal(nt.name) for nt in grammar.nonterminals}
    for old, new in nonterminals.items():
        new.definition = _clone_formula(old.definition, terminals, nonterminals)
    return _Graph(tuple(terminals.values()), tuple(nonterminals.values())), terminals, nonterminals


def _fresh_name(grammar, base, introduced=()):
    """`base`, or `base` with a number, unused by `grammar` and by the
    nonterminals `introduced` so far."""
    used = ({nt.name for nt in grammar.nonterminals} | {terminal.symbol for terminal in grammar.terminals}
            | {nt.name for nt in introduced})
    if base.startswith("<") and ">" in base:
        base = base.replace(">", "", 1) + ">"
    name = base
    index = 1
    while name in used:
        name = f"{base[:-1]}_{index}>" if base.startswith("<") else f"{base}_{index}"
        index += 1
    return name


def _replace_formula(formula, path, replacement):
    if not path:
        return replacement
    step, *rest = path
    if step == "left":
        formula.left = _replace_formula(formula.left, rest, replacement)
    else:
        formula.right = _replace_formula(formula.right, rest, replacement)
    return formula


def _nonempty_forms(productions, rhs, factors, nonempty):
    """The ways the factors of `rhs` derive a nonempty sentence, by
    ε-elimination: for each i where rhs[:i] is nullable and rhs[i] derives a
    nonempty sentence, `nonempty`(factor i) followed by the factors after it."""
    forms = []
    for i, symbol in enumerate(rhs):
        if productions.is_terminal(symbol) or symbol in productions.nonempty:
            forms.append([nonempty(factors[i])] + list(factors[i + 1:]))
        if symbol not in productions.nullable:
            break
    return forms


class _NonemptyVersions:
    """New nonterminals for the nonempty sentences of nullable symbols.

    Called on a factor, it returns the factor itself when its symbol is not
    nullable, and otherwise a new nonterminal X' for X, which define() gives
    the forms of _nonempty_forms for each useful alternative of X. These
    are read from the first of `views` that has X; there the new
    nonterminals count as terminals, which is what they are: not nullable,
    and nonempty."""

    def __init__(self, grammar, views, introduced):
        self.grammar, self.views, self.introduced = grammar, views, introduced
        self.versions = {}
        self.pending = []

    def _view(self, symbol):
        return next((view for view in self.views if symbol in view.rules), self.views[-1])

    def __call__(self, factor):
        symbol = _symbol(factor)
        view = self._view(symbol)
        if symbol not in view.nullable:
            return factor
        if symbol not in self.versions:
            base = symbol.name if isinstance(symbol, Nonterminal) else f"{view.owner[symbol].name}_part"
            name = _fresh_name(self.grammar, f"{base}_nonempty", self.introduced)
            self.versions[symbol] = Nonterminal(name)
            self.introduced.append(self.versions[symbol])
            self.pending.append(symbol)
        return self.versions[symbol]

    def define(self):
        while self.pending:
            symbol = self.pending.pop(0)
            view = self._view(symbol)
            forms = {}
            for rhs, alternative, _ in view.useful(symbol):
                for form in _nonempty_forms(view, rhs, _factors(alternative), self):
                    formula = _join(form, ConcatenationFormula)
                    forms.setdefault(_formula_key(formula), formula)
            self.versions[symbol].definition = _join(forms.values(), UnionFormula)


def _rebuild_cycle(grammar, owner, introduced):
    """Rewrite the strongly connected component of transparent steps that
    holds `owner` (in `grammar`) as a whole; return its nonterminals.

    Its first nonterminal H takes the language they all share, and the
    others become H. With E the alternatives that are not steps, S and T the
    symbols of the steps' left and right contexts that derive a nonempty
    sentence, and X' for the nonempty sentences of X:

        H ::= s' H | H_tail (s in S),   H_tail ::= H_tail t' | δ (t in T, δ in E)

    which is H ::= s' H | δ without T, H ::= H t' | δ without S, and H ::= δ
    without either. When a context holds a member, the language L is
    nullable and holds L L, so it is the star of its generators g: each
    context symbol outside the component, each alternative in E that is not
    nullable, and each symbol of one that is; then H ::= H g' | ε. The X'
    are made from the rewritten definitions, so that they cannot form a
    cycle again."""
    productions = _Productions(grammar.nonterminals)
    component = _component(productions, owner)
    named = [member for member in component if isinstance(member, Nonterminal)]
    head = named[0]
    contexts, exits, nested = _cycle_parts(productions, component)
    nonempty = _NonemptyVersions(grammar, [productions], introduced)
    if nested:
        generators = {**contexts["left"], **contexts["right"]}
        for rhs, alternative in exits.values():
            if not productions.derives_epsilon(rhs):
                generators[_formula_key(alternative)] = alternative
                continue
            for symbol, factor in zip(rhs, _factors(alternative)):
                if symbol in productions.nonempty:
                    generators.setdefault(symbol, factor)
        head.definition = _join([ConcatenationFormula(head, nonempty(generator))
                                 for generator in generators.values()] + [Epsilon()], UnionFormula)
    else:
        core = head
        if contexts["left"] and contexts["right"]:
            core = Nonterminal(_fresh_name(grammar, f"{head.name}_tail", introduced))
            introduced.append(core)
        lefts = [ConcatenationFormula(nonempty(factor), head) for factor in contexts["left"].values()]
        rights = [ConcatenationFormula(core, nonempty(factor)) for factor in contexts["right"].values()]
        alternatives = [alternative for _, alternative in exits.values()]
        if core is head:
            head.definition = _join(lefts + rights + alternatives, UnionFormula)
        else:
            head.definition = _join(lefts + [core], UnionFormula)
            core.definition = _join(rights + alternatives, UnionFormula)
    for member in named[1:]:
        member.definition = head
    rewritten = [*grammar.nonterminals, *(nt for nt in introduced if nt.definition is not None)]
    nonempty.views = [_Productions(rewritten), productions]
    nonempty.define()
    return named


def _nearest_binding(grammar, owner, mirrored, introduced):
    """Rewrite the dangling suffixes of `owner` (in `grammar`), all its
    prefixes μ at once, so that each γ closes the nearest μ:

        A ::= μ X | μ X γ | δ    becomes    A ::= μ X | μ X' γ | δ
                                            M ::= μ X' γ' | δ'

    M, new, is A without the open alternatives μ X, so it never leaves a μ
    open at its right end, and the γ after it closes the μ before it. X' is
    M when X is A, and otherwise a copy of X; γ' and δ' are γ and δ with
    the symbols at their right end that end in A replaced by such copies,
    each copy holding the alternatives of the original redirected the same
    way, until A becomes M. δ' also has an A at its left end replaced by M:
    a left-recursive alternative A c, whose mixed recursion is rewritten
    after this, must not open a μ either (_dangling_group allows one only
    when every X is A). An option μ A ν is first split into μ A and one
    μ A ν' for each nonempty form ν' of ν. With several prefixes, each has
    its own M, which keeps the open alternatives of the others. When
    `mirrored`, all of this is read from the left end."""
    productions = _Productions(grammar.nonterminals)
    roles = _dangling_group(productions, owner, mirrored)
    side = "left" if mirrored else "right"
    orient = (lambda items: items[::-1]) if mirrored else list
    nonempty = _NonemptyVersions(grammar, [productions], introduced)
    kinds = list(dict.fromkeys(kind for _, kind in roles.values()))
    copies = {kind: {} for kind in kinds}      # kind -> {nonterminal: its copy}
    pending = []

    def copy(kind, nt):
        if nt not in copies[kind]:
            copies[kind][nt] = Nonterminal(_fresh_name(grammar, f"{nt.name}_closed", introduced))
            introduced.append(copies[kind][nt])
            if nt is not owner:
                pending.append((kind, nt))
        return copies[kind][nt]

    def build(factors):
        return _join(orient(factors), ConcatenationFormula)

    def redirect(kind, factors):
        """`factors`, in reading order, with the symbols at their end that end in A replaced."""
        factors = list(factors)
        for i in reversed(range(len(factors))):
            symbol = _symbol(factors[i])
            if not productions.is_terminal(symbol) and owner in productions.corners(symbol, side):
                if isinstance(symbol, Nonterminal):
                    factors[i] = copy(kind, symbol)
                else:
                    factors[i] = _join([build(redirect(kind, orient(_factors(alternative))))
                                        for _, alternative, _ in productions.rules[symbol]], UnionFormula)
            if symbol not in productions.nullable:
                break
        return factors

    def closed(kind, factors, closing=None):
        """μ X' γ, with γ redirected for `closing` when given."""
        mu, corner = kind
        gamma = factors[len(mu) + 1:]
        return build(factors[:len(mu)] + [copy(kind, corner)]
                     + (redirect(closing, gamma) if closing else gamma))

    for kind in kinds:
        copy(kind, owner)
    entries = []        # (role, kind, factors in reading order, the alternative if kept as it is)
    opened = {kind for role, kind in roles.values() if role == "open"}
    for index, (rhs, alternative, _) in enumerate(productions.rules[owner]):
        role, kind = roles.get(index, (None, None))
        if role != "option":
            entries.append((role, kind, orient(_factors(alternative)), alternative))
            continue
        split = len(kind[0]) + 1
        factors, symbols = orient(_factors(alternative)), orient(rhs)
        if kind not in opened:
            opened.add(kind)
            entries.append(("open", kind, factors[:split], None))
        for form in _nonempty_forms(productions, symbols[split:], factors[split:], nonempty):
            entries.append(("closed", kind, factors[:split] + form, None))
    # The X' in the forms ν' can end in A too (E' ::= g A for E ::= g A | ε), so
    # redirect() must see their productions: define them, and read them with
    # those of the grammar before A is rewritten.
    nonempty.define()
    productions = _Productions([*grammar.nonterminals, *nonempty.versions.values()])
    owner.definition = _join([closed(kind, factors) if role == "closed" else alternative or build(factors)
                              for role, kind, factors, alternative in entries], UnionFormula)
    for current in kinds:
        alternatives = []
        for role, kind, factors, _ in entries:
            if role == "closed":
                alternatives.append(closed(kind, factors, current))
            elif not (role == "open" and kind == current):
                if role is None and factors and factors[0] is owner:
                    factors = [copy(current, owner)] + factors[1:]
                alternatives.append(build(redirect(current, factors)))
        copies[current][owner].definition = _join(alternatives, UnionFormula)
    while pending:
        kind, nt = pending.pop(0)
        copies[kind][nt].definition = _join([build(redirect(kind, orient(_factors(alternative))))
                                             for _, alternative, _ in productions.rules[nt]], UnionFormula)


def _apply_cacc(grammar, match):
    """Rewrite `match` in a copy of `grammar`; return (copy, CACCRewrite).

    A transparent cycle rebuilds the definitions of its component, and a
    dangling suffix that of its owner, both from the copy itself; the other
    rewrites are built from the match. New nonterminals follow the first
    definition changed."""
    result, terminals, nonterminals = _clone_grammar(grammar)
    owner = nonterminals[match.nonterminal]
    changed, introduced = [owner], []
    if match.rule_id == "mixed_recursion":
        beta, gamma, delta = [_clone_formula(item, terminals, nonterminals) for item in match.details]
        helper_base = "T" if owner.name == "E" else f"{owner.name}_tail"
        helper = Nonterminal(_fresh_name(result, helper_base))
        owner.definition = UnionFormula(_join((beta, owner), ConcatenationFormula), helper)
        helper.definition = UnionFormula(_join((helper, gamma), ConcatenationFormula), delta)
        introduced.append(helper)
    elif match.rule_id == "transparent_cycle":
        changed = _rebuild_cycle(result, owner, introduced)
    elif match.rule_id == "dangling_suffix":
        if _dangling_group(_Productions(result.nonterminals), owner, match.details[-1]):
            _nearest_binding(result, owner, match.details[-1], introduced)
    elif match.rule_id == "optional_square" and match.details is not None:
        _split_square(result, owner, *match.details, introduced)
    else:
        replacement = _clone_formula(match.replacement, terminals, nonterminals)
        owner.definition = _replace_formula(owner.definition, match.path, replacement)
    position = result.nonterminals.index(changed[0]) + 1
    result.nonterminals = result.nonterminals[:position] + tuple(introduced) + result.nonterminals[position:]
    originals = {new: old for old, new in nonterminals.items()}
    before = "\n".join(_definition_text(originals[nt]) for nt in changed)
    after = "\n".join(_definition_text(nt) for nt in changed + introduced)
    return result, CACCRewrite(match.rule_id, match.nonterminal.name, before, after,
                               tuple(nt.name for nt in introduced))


def _split_square(grammar, owner, path, start, introduced):
    """Rewrite the alternative μ N N ν at `path` in the definition of `owner`,
    where N derives ε and N N begins at factor `start`, as
    μ N' N' ν | μ N' ν | μ ν, with N' for the nonempty sentences of N."""
    factors = _factors(_formula_at(owner.definition, path))
    nonempty = _NonemptyVersions(grammar, [_Productions(grammar.nonterminals)], introduced)
    part = nonempty(factors[start])
    mu, nu = factors[:start], factors[start + 2:]
    forms = (mu + [part, part] + nu, mu + [part] + nu, mu + nu)
    owner.definition = _replace_formula(owner.definition, path, _join(
        [_join(form, ConcatenationFormula) for form in forms], UnionFormula))
    nonempty.define()
