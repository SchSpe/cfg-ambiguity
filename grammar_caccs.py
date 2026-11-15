"""Recognize and rewrite seven certain ambiguity-causing constructs in BNF.

Rules stay (lhs, rhs) tuples throughout. Matches identify zero-based production
occurrences and half-open RHS spans. Rewrites return new CFG objects; unchanged
occurrences keep their source lines and generated productions use line 0.
"""

from collections import defaultdict, deque
from dataclasses import dataclass, field

from grammar_parser import CFG


# The automatic stage follows the four directly implemented transformations
# in Section 6. The other recognized constructs remain available to explicit
# callers of apply_cacc() and transform_caccs().
NSF_REPAIR_IDS = frozenset({
    "mixed_recursion",       # Corollary 1
    "self_embedding",        # Corollary 2
    "duplicate_union",       # union idempotency
    "optional_square",       # Example 7
})


@dataclass(frozen=True)
class CACCMatch:
    rule_id: str
    kind: str
    nonterminal: str
    production_indices: tuple
    rhs_spans: tuple
    source: str
    reason: str
    rewrite_available: bool
    rewrite_reason: str
    _productions: tuple = field(repr=False, compare=False)
    _details: tuple = field(default=(), repr=False)


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


class _Facts:
    """Shared nullable, productive, nonempty and corner facts for one rule set."""

    def __init__(self, productions):
        self.productions = tuple(productions)
        self.rules = {}
        for index, (lhs, rhs) in enumerate(self.productions):
            self.rules.setdefault(lhs, []).append((index, rhs))
        self.order = {name: index for index, name in enumerate(self.rules)}
        self.nullable = self._least(lambda rhs, found: all(symbol in found for symbol in rhs))
        self.productive = self._least(lambda rhs, found: all(self.is_terminal(s) or s in found for s in rhs))
        self.nonempty = self._least(lambda rhs, found: self.derives_sentence(rhs) and any(self.is_terminal(s) or s in found for s in rhs))
        self._steps, self._corners, self._ends = {}, {}, {}

    def _least(self, holds):
        found = set()
        while True:
            before = len(found)
            for lhs, rules in self.rules.items():
                if any(holds(rhs, found) for _, rhs in rules):
                    found.add(lhs)
            if len(found) == before:
                return found

    def is_terminal(self, symbol):
        return symbol not in self.rules

    def derives_sentence(self, rhs):
        return all(self.is_terminal(s) or s in self.productive for s in rhs)

    def derives_epsilon(self, rhs):
        return all(s in self.nullable for s in rhs)

    def derives_nonempty(self, rhs):
        return self.derives_sentence(rhs) and any(self.is_terminal(s) or s in self.nonempty for s in rhs)

    def useful(self, lhs):
        return [(index, rhs) for index, rhs in self.rules[lhs] if self.derives_sentence(rhs)]

    def steps(self, symbol, side):
        """Useful X -> prefix Y suffix steps, with the indicated contexts nullable."""
        if side not in self._steps:
            self._steps[side] = {
                lhs: [target for _, rhs in self.useful(lhs) for i, target in enumerate(rhs)
                      if target in self.rules
                      and (side == "left" or self.derives_epsilon(rhs[i + 1:]))
                      and (side == "right" or self.derives_epsilon(rhs[:i]))]
                for lhs in self.rules}
        return self._steps[side].get(symbol, ())

    def corners(self, symbol, side):
        key = symbol, side
        if key not in self._corners:
            reached, pending = {symbol}, [symbol]
            while pending:
                for target in self.steps(pending.pop(), side):
                    if target not in reached:
                        reached.add(target)
                        pending.append(target)
            self._corners[key] = reached
        return self._corners[key]

    def ends(self, side):
        """Reverse corner reachability, including unproductive rules, for chart pruning."""
        if side not in self._ends:
            first = {}
            for lhs, rules in self.rules.items():
                first[lhs] = set()
                for _, rhs in rules:
                    for symbol in (rhs if side == "left" else reversed(rhs)):
                        first[lhs].add(symbol)
                        if symbol not in self.nullable:
                            break
            hosts = defaultdict(set)
            for lhs in self.rules:
                reached, pending = {lhs}, [lhs]
                while pending:
                    for symbol in first.get(pending.pop(), ()):
                        if symbol not in reached:
                            reached.add(symbol)
                            pending.append(symbol)
                for symbol in reached:
                    hosts[symbol].add(lhs)
            self._ends[side] = hosts
        return self._ends[side]


class _Derivations:
    """Exact tests source ⇒* target between sequences of symbols, with the
    productions except the occurrence `excluded`, and the nullable symbols found again
    without it.

    For each target, the symbols that derive each of its spans are found
    shortest span first, as in the CYK algorithm, and within a span by a
    fixed point, for the productions that cover the span with one symbol and
    nullable ones around it."""

    def __init__(self, productions, excluded=None):
        self.productions = productions
        self.rules = {symbol: [rhs for index, rhs in rules if index != excluded]
                      for symbol, rules in productions.rules.items()}
        removed = productions.productions[excluded][1] if excluded is not None else None
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


def _dangling_roles(productions, owner, mirrored):
    """The alternatives of `owner` read from the right end (from the left
    when `mirrored`), and {index of one: its roles}, each (role, (μ, X)):
    "open" for μ X, "closed" for μ X γ, "option" for μ A ν, where A is the
    owner. Only prefixes that something closes count: i S e S is closed
    after i, and open after i S e for nothing."""
    side = "left" if mirrored else "right"
    alternatives = [rhs[::-1] if mirrored else rhs for _, rhs in productions.rules[owner]]
    useful = [productions.derives_sentence(rhs) for rhs in alternatives]
    kinds = {}      # (μ, X) of each open alternative μ X, in order
    for rhs, ok in zip(alternatives, useful):
        if (ok and len(rhs) >= 2 and rhs[-1] in productions.rules
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
                or role == "closed" and rest[0] == owner and owner in productions.nullable):
            return None
    for symbol in productions.rules:
        if not ends_in_owner(symbol):
            continue
        for index, (_, rhs) in enumerate(productions.rules[symbol]):
            if (not productions.derives_sentence(rhs)
                    or symbol == owner and roles.get(index, (None,))[0] == "option"):    # split first
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
           and (rhs[0] != owner or any(corner != owner for _, (_, corner) in roles.values()))
           for index, rhs in enumerate(alternatives)):
        return None
    return roles

_NSF = "NSF report, Section 6, "


def _match(facts, rule_id, owner, indices, kind, reason, source, spans=(), details=(), available=True):
    return CACCMatch(rule_id, kind, owner, tuple(indices), tuple(spans), source, reason, available,
                     "" if available else "The nearest-binding rewrite does not support this recursive or nullable context.",
                     facts.productions, tuple(details))


def _component(facts, symbol):
    return tuple(sorted((other for other in facts.corners(symbol, "transparent")
                         if symbol in facts.corners(other, "transparent")), key=facts.order.get))


def _step_positions(facts, rhs, members):
    return [i for i, symbol in enumerate(rhs)
            if symbol in members and facts.derives_epsilon(rhs[:i] + rhs[i + 1:])]


def _cycle_parts(facts, component):
    contexts = {"left": {}, "right": {}}
    exits = {}
    nested = False
    for member in component:
        for _, rhs in facts.rules[member]:
            positions = _step_positions(facts, rhs, component)
            for i in positions:
                for side, symbols in (("left", rhs[:i]), ("right", rhs[i + 1:])):
                    for symbol in symbols:
                        nested |= symbol in component
                        if symbol not in component and symbol in facts.nonempty:
                            contexts[side][symbol] = None
            if not positions:
                exits[rhs] = None
    return contexts, exits, nested


def _transparent_cycles(facts):
    """Find productive transparent SCCs; order dependencies before their copies."""
    found, seen = [], set()
    for symbol in facts.rules:
        if symbol in seen:
            continue
        component = _component(facts, symbol)
        seen.update(component)
        if len(component) == 1 and symbol not in facts.steps(symbol, "transparent"):
            continue
        for owner in component:
            steps, exits = [], []
            for index, rhs in facts.useful(owner):
                (steps if _step_positions(facts, rhs, component) else exits).append(index)
            if steps and exits:
                found.append((component, _match(facts, "transparent_cycle", owner, (exits[0], steps[0]), "union",
                    "A productive cycle with nullable contexts derives each exit in two ways.",
                    "transparent derivation cycles", details=component)))
                break
    cycle_of = {member: index for index, (component, _) in enumerate(found) for member in component}
    ordered, visited = [], set()

    def visit(index):
        if index in visited:
            return
        visited.add(index)
        contexts, exits, nested = _cycle_parts(facts, found[index][0])
        copied = [*contexts["left"], *contexts["right"]]
        if nested:
            copied.extend(symbol for rhs in exits if facts.derives_epsilon(rhs) for symbol in rhs)
        for symbol in copied:
            for reached in facts.corners(symbol, "left"):
                if cycle_of.get(reached, index) != index:
                    visit(cycle_of[reached])
        ordered.append(found[index][1])

    for index in range(len(found)):
        visit(index)
    return ordered


def _subsumed(facts):
    matches = []
    for owner, rules in facts.rules.items():
        for target_index, target in facts.useful(owner):
            derivations = None
            for source_index, source in rules:
                if source == target:
                    continue
                derivations = derivations or _Derivations(facts, target_index)
                if derivations.derives(source, target):
                    matches.append(_match(facts, "subsumed_alternative", owner, (source_index, target_index), "union",
                        "One alternative derives another without using the alternative to be removed.",
                        _NSF + "union idempotency, extended to derivations"))
    return matches


def _dangling(facts):
    matches = []
    for owner in facts.rules:
        if owner not in facts.productive:
            continue
        for mirrored in (False, True):
            _, candidates = _dangling_roles(facts, owner, mirrored)
            roles = [(index, role, kind) for index, values in candidates.items() for role, kind in values]
            if not roles:
                continue
            available = bool(_dangling_group(facts, owner, mirrored))
            for index, role, kind in roles:
                if role == "open":
                    continue
                own = facts.rules[owner][index][0]
                occurrences = [(own,)] if role == "option" else [
                    (facts.rules[owner][other][0], own) for other, other_role, other_kind in roles
                    if other_role == "open" and other_kind == kind]
                for indices in occurrences:
                    matches.append(_match(facts, "dangling_suffix", owner, indices,
                        "concatenation" if role == "option" else "union",
                        "A closing suffix after a repeated prefix can close either occurrence of the prefix.",
                        "the dangling else, extended to corner chains", details=(mirrored,), available=available))
    return matches


def _recognize(facts):
    mixed, embedded, local = [], [], []
    for owner, rules in facts.rules.items():
        if owner not in facts.productive:
            continue
        for first, prefix in rules:
            if prefix and prefix[-1] == owner and facts.derives_sentence(prefix[:-1]):
                for second, suffix in rules:
                    if (first != second and suffix and suffix[0] == owner
                            and facts.derives_sentence(suffix[1:]) and len(rules) > 2):
                        mixed.append(_match(facts, "mixed_recursion", owner, (first, second), "union",
                            "Distinct productive prefix and suffix recursive alternatives overlap.",
                            _NSF + "Corollary 1"))
            if len(prefix) >= 2 and prefix[0] == prefix[-1] == owner and facts.derives_sentence(prefix[1:-1]):
                embedded.append(_match(facts, "self_embedding", owner, (first,),
                    "concatenation" if owner in facts.nonempty or facts.derives_nonempty(prefix[1:-1]) else "derivation",
                    "A productive A beta A alternative permits distinct recursive associations.",
                    _NSF + "Corollary 2"))
        duplicates, optional = {}, []
        for index, rhs in facts.useful(owner):
            duplicates.setdefault(rhs, []).append(index)
            for offset, (left, right) in enumerate(zip(rhs, rhs[1:])):
                if left == right and left in facts.nullable and left in facts.nonempty:
                    optional.append(_match(facts, "optional_square", owner, (index,), "concatenation",
                        "Either occurrence of the nullable nonterminal can supply the same nonempty block.",
                        _NSF + "optional-expression square", spans=((index, offset, offset + 2),)))
        for indices in duplicates.values():
            if len(indices) > 1:
                local.append(_match(facts, "duplicate_union", owner, indices, "union",
                    "The same productive alternative occurs more than once.", _NSF + "union idempotency"))
        local.extend(optional)
    return _transparent_cycles(facts) + _subsumed(facts) + _dangling(facts) + mixed + embedded + local


class _Edit:
    """Construct productions while retaining the source of each unchanged occurrence."""

    def __init__(self, cfg):
        self.cfg = cfg
        self.rules = {name: [] for name in cfg.nonterminals}
        self.indices = {name: [] for name in cfg.nonterminals}
        for index, ((lhs, rhs), line) in enumerate(zip(cfg.productions, cfg.production_lines)):
            self.rules[lhs].append((rhs, line))
            self.indices[lhs].append(index)
        self.used = set(cfg.nonterminals) | set(cfg.terminals)
        self.introduced = []
        self.changed = set()

    def fresh(self, base):
        if base.startswith("<") and ">" in base:
            base = base.replace(">", "", 1) + ">"
        name, number = base, 1
        while name in self.used:
            name = f"{base[:-1]}_{number}>" if base.startswith("<") else f"{base}_{number}"
            number += 1
        self.used.add(name)
        self.introduced.append(name)
        self.rules[name] = None      # A queued nonempty/closed helper is defined later.
        return name

    def set(self, name, alternatives):
        alternatives = list(alternatives)
        if not alternatives:
            raise ValueError(f"A rewrite would leave {name} without any productions")
        sources = defaultdict(deque)
        for rhs, line in self.rules.get(name) or ():
            sources[rhs].append(line)
        self.rules[name] = [(rhs, sources[rhs].popleft() if sources[rhs] else 0) for rhs in alternatives]
        self.changed.add(name)

    def replace_rule(self, index, alternatives):
        owner, original = self.cfg.productions[index]
        position = self.indices[owner].index(index)
        line = self.cfg.production_lines[index]
        self.rules[owner][position:position + 1] = [(rhs, line if rhs == original else 0) for rhs in alternatives]
        self.changed.add(owner)

    def remove(self, indices):
        excluded = set(indices)
        owner = self.cfg.productions[indices[0]][0]
        self.rules[owner] = [entry for index, entry in zip(self.indices[owner], self.rules[owner]) if index not in excluded]
        self.changed.add(owner)

    def facts(self):
        return _Facts((name, rhs) for name, entries in self.rules.items() if entries is not None for rhs, _ in entries)

    def finish(self):
        productions, lines, emitted = [], [], set()
        for (lhs, rhs), line in zip(self.cfg.productions, self.cfg.production_lines):
            if lhs not in self.changed:
                productions.append((lhs, rhs))
                lines.append(line)
            elif lhs not in emitted:
                emitted.add(lhs)
                for body, source in self.rules[lhs]:
                    productions.append((lhs, body))
                    lines.append(source)
        for lhs in self.introduced:
            for rhs, line in self.rules[lhs]:
                productions.append((lhs, rhs))
                lines.append(line)
        return CFG(productions, lines)


class _Nonempty:
    """Queued helper rules for L(X) minus epsilon, including recursive X.

    New helper names count as nonnullable symbols while their definitions
    are being built. Each view describes a complete earlier grammar version.
    """

    def __init__(self, edit, views):
        self.edit, self.views = edit, views
        self.versions = {}
        self.pending = deque()

    def symbol(self, name):
        facts = next((view for view in self.views if name in view.rules), self.views[-1])
        if name not in facts.nullable:
            return name
        if name not in self.versions:
            self.versions[name] = self.edit.fresh(name + "_nonempty")
            self.pending.append(name)
        return self.versions[name]

    def forms(self, rhs, facts):
        """Choose the first nonempty symbol after a nullable prefix."""
        result = []
        for index, symbol in enumerate(rhs):
            if facts.is_terminal(symbol) or symbol in facts.nonempty:
                result.append((self.symbol(symbol),) + rhs[index + 1:])
            if symbol not in facts.nullable:
                break
        return result

    def define(self):
        while self.pending:
            name = self.pending.popleft()
            facts = next(view for view in self.views if name in view.rules)
            forms = dict.fromkeys(form for _, rhs in facts.useful(name) for form in self.forms(rhs, facts))
            self.edit.set(self.versions[name], forms)


def _rewrite_cycle(edit, facts, component):
    """Collapse a transparent SCC into its shared language, retaining aliases.

    Without nested members, nullable left/right contexts become nonempty
    prefix/suffix generators around the exits. With nested members the common
    language is the star of its generators. Nonempty copies use the rewritten
    definitions so they cannot recreate the removed transparent cycle.
    """
    head = component[0]
    contexts, exits, nested = _cycle_parts(facts, component)
    nonempty = _Nonempty(edit, [facts])
    if nested:
        generators = dict.fromkeys((nonempty.symbol(s),) for s in (*contexts["left"], *contexts["right"]))
        for rhs in exits:
            if not facts.derives_epsilon(rhs):
                generators[rhs] = None
            else:
                for symbol in rhs:
                    if symbol in facts.nonempty:
                        generators[(nonempty.symbol(symbol),)] = None
        edit.set(head, [(head,) + rhs for rhs in generators] + [()])
    else:
        core = edit.fresh(head + "_tail") if contexts["left"] and contexts["right"] else head
        lefts = [(nonempty.symbol(symbol), head) for symbol in contexts["left"]]
        rights = [(core, nonempty.symbol(symbol)) for symbol in contexts["right"]]
        if core == head:
            edit.set(head, lefts + rights + list(exits))
        else:
            edit.set(head, lefts + [(core,)])
            edit.set(core, rights + list(exits))
    for member in component[1:]:
        edit.set(member, [(head,)])
    nonempty.views = [edit.facts(), facts]
    nonempty.define()


def _rewrite_dangling(edit, facts, owner, mirrored):
    """Close each suffix at the nearest matching prefix, within the guarded shapes.

    Closed copies redirect the relevant end through corner chains. Nullable
    suffixes are split first, and their nonempty helpers must be visible to
    corner analysis before the closed copies are defined.
    """
    roles = _dangling_group(facts, owner, mirrored)
    side = "left" if mirrored else "right"
    orient = (lambda rhs: rhs[::-1]) if mirrored else (lambda rhs: rhs)
    nonempty = _Nonempty(edit, [facts])
    kinds = list(dict.fromkeys(kind for _, kind in roles.values()))
    copies = {kind: {} for kind in kinds}
    pending = deque()

    def closed_copy(kind, name):
        if name not in copies[kind]:
            copies[kind][name] = edit.fresh(name + "_closed")
            if name != owner:
                pending.append((kind, name))
        return copies[kind][name]

    def redirect(kind, rhs):
        rhs = list(rhs)
        for index in reversed(range(len(rhs))):
            symbol = rhs[index]
            if symbol in facts.rules and owner in facts.corners(symbol, side):
                rhs[index] = closed_copy(kind, symbol)
            if symbol not in facts.nullable:
                break
        return tuple(rhs)

    def closed(kind, rhs, closing=None):
        mu, corner = kind
        suffix = rhs[len(mu) + 1:]
        return orient(rhs[:len(mu)] + (closed_copy(kind, corner),)
                      + (redirect(closing, suffix) if closing else suffix))

    for kind in kinds:
        closed_copy(kind, owner)
    entries = []
    opened = {kind for role, kind in roles.values() if role == "open"}
    for index, (_, original) in enumerate(facts.rules[owner]):
        role, kind = roles.get(index, (None, None))
        rhs = orient(original)
        if role != "option":
            entries.append((role, kind, rhs))
            continue
        split = len(kind[0]) + 1
        if kind not in opened:
            opened.add(kind)
            entries.append(("open", kind, rhs[:split]))
        for form in nonempty.forms(rhs[split:], facts):
            entries.append(("closed", kind, rhs[:split] + form))
    nonempty.define()
    facts = edit.facts()
    edit.set(owner, [closed(kind, rhs) if role == "closed" else orient(rhs) for role, kind, rhs in entries])
    for current in kinds:
        alternatives = []
        for role, kind, rhs in entries:
            if role == "closed":
                alternatives.append(closed(kind, rhs, current))
            elif not (role == "open" and kind == current):
                if role is None and rhs and rhs[0] == owner:
                    rhs = (closed_copy(current, owner),) + rhs[1:]
                alternatives.append(orient(redirect(current, rhs)))
        edit.set(copies[current][owner], alternatives)
    while pending:
        kind, name = pending.popleft()
        edit.set(copies[kind][name], [orient(redirect(kind, orient(rhs))) for _, rhs in facts.rules[name]])


def _rewrite(cfg, facts, match):
    edit = _Edit(cfg)
    owner = match.nonterminal
    indices = match.production_indices
    if match.rule_id == "duplicate_union":
        edit.remove(indices[1:])
    elif match.rule_id == "subsumed_alternative":
        edit.remove((indices[1],))
    elif match.rule_id == "mixed_recursion":
        prefix, suffix = (cfg.productions[index][1] for index in indices)
        helper = edit.fresh("T" if owner == "E" else owner + "_tail")
        edit.set(owner, [prefix, (helper,)])
        edit.set(helper, [(helper,) + suffix[1:]] + [rhs for index, rhs in facts.rules[owner] if index not in indices])
    elif match.rule_id == "self_embedding":
        recursive = cfg.productions[indices[0]][1]
        rest = [rhs for index, rhs in facts.rules[owner] if index != indices[0]]
        # A choice inside A beta gamma gets its own BNF nonterminal instead
        # of distributing a Cartesian product of alternatives.
        if len(rest) == 1:
            gamma = rest[0]
        else:
            helper = edit.fresh(owner + "_part")
            edit.set(helper, rest)
            gamma = (helper,)
        edit.set(owner, [(owner,) + recursive[1:-1] + gamma] + rest)
    elif match.rule_id == "optional_square":
        index, start, end = match.rhs_spans[0]
        rhs = cfg.productions[index][1]
        nonempty = _Nonempty(edit, [facts])
        part = nonempty.symbol(rhs[start])
        alternatives = [(part, part), (part,), ()]
        if start == 0 and end == len(rhs):
            edit.replace_rule(index, alternatives)
        else:
            # Factor the choice so independent optional pairs do not multiply
            # all surrounding alternatives during repeated rewrites.
            helper = edit.fresh(owner + "_optional")
            edit.set(helper, alternatives)
            edit.replace_rule(index, [rhs[:start] + (helper,) + rhs[end:]])
        nonempty.define()
    elif match.rule_id == "transparent_cycle":
        _rewrite_cycle(edit, facts, match._details)
    elif match.rule_id == "dangling_suffix":
        _rewrite_dangling(edit, facts, owner, match._details[0])
    result = edit.finish()
    changed = [name for name in cfg.nonterminals if name in edit.changed]
    def definitions(grammar, names):
        return "\n".join(lhs + " ::= " + (" ".join(rhs) or "ε")
                         for lhs, rhs in grammar.productions if lhs in names)
    change = CACCRewrite(match.rule_id, owner, definitions(cfg, changed),
                         definitions(result, changed + edit.introduced), tuple(edit.introduced))
    return result, change


def recognize_caccs(cfg):
    """Find structural ambiguity patterns, independent of the finite search level."""
    return _recognize(_Facts(cfg.productions))


def apply_cacc(cfg, match):
    """Apply one match to a copy; unsupported rewrites return unchanged and stalled."""
    if not isinstance(match, CACCMatch) or match._productions != cfg.productions:
        raise ValueError("The CACC match belongs to a different or edited grammar")
    facts = _Facts(cfg.productions)
    selected = next((item for item in _recognize(facts) if item == match), None)
    if selected is None:
        raise ValueError("The CACC match is no longer present in this grammar")
    if not selected.rewrite_available:
        result = CFG(cfg.productions, cfg.production_lines)
        return CACCResult(result, [], _recognize(facts), stalled=True)
    result, change = _rewrite(cfg, facts, selected)
    stalled = result.productions == cfg.productions
    return CACCResult(result, [] if stalled else [change], recognize_caccs(result), stalled=stalled)


def repair_caccs(cfg, max_steps=100):
    """Apply the NSF Section 6 repairs to a copy before approximation.

    Recognition extensions are retained in `remaining`, but are not rewritten
    by this stage. They do not count as stalled repairs or an exhausted limit.
    """
    return _transform_caccs(cfg, max_steps, NSF_REPAIR_IDS)


def transform_caccs(cfg, max_steps=100):
    """Explicitly apply all supported rewrites, including recognition extensions."""
    return _transform_caccs(cfg, max_steps, None)


def _transform_caccs(cfg, max_steps, rule_ids):
    """Re-recognize after each rewrite; never revisit a previous rule set."""
    if type(max_steps) is not int or max_steps < 0:
        raise ValueError("max_steps must be a nonnegative integer")
    result = CFG(cfg.productions, cfg.production_lines)
    seen, changes, stalled = {result.productions}, [], False
    facts = _Facts(result.productions)
    matches = _recognize(facts)
    eligible = [match for match in matches if rule_ids is None or match.rule_id in rule_ids]
    while eligible and len(changes) < max_steps:
        for match in eligible:
            if not match.rewrite_available:
                continue
            candidate, change = _rewrite(result, facts, match)
            if candidate.productions not in seen:
                break
        else:
            stalled = True
            break
        result = candidate
        seen.add(result.productions)
        changes.append(change)
        facts = _Facts(result.productions)
        matches = _recognize(facts)
        eligible = [match for match in matches if rule_ids is None or match.rule_id in rule_ids]
    return CACCResult(result, changes, matches, bool(eligible) and len(changes) == max_steps, stalled)
