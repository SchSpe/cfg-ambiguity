"""Approximate a CFG level by level, detecting ambiguity during evaluation.

The caller supplies the grammar to check, after any repairs. This stage builds
the engine formulas, runs synchronous language approximation, and keeps one
finding per ambiguity site. Parse-tree reconstruction and text belong to the
report stage.
"""

from dataclasses import dataclass

from grammar_engine import AmbiguityFinding, GrammarCatalog, format_formula
from grammar_parser import CFG


@dataclass
class AmbiguitySite:
    """One expression location, its first discovery, and its latest witness."""

    finding: AmbiguityFinding
    rule_indices: tuple[int, ...]
    first_level: int


@dataclass
class ApproximationResult:
    """The completed search and the catalog needed to prove its witnesses."""

    cfg: CFG
    catalog: GrammarCatalog
    requested_level: int
    level_reached: int
    saturated: bool
    sites: list[AmbiguitySite]
    reachable: set[str]
    unproductive: list[str]
    start_sentences: int


def analyse_dependencies(cfg):
    """Return productive reachability, all start dependencies, and dead symbols.

    A local ambiguity affects the start symbol only through productions that
    can finish. Stabilization, however, must check every dependency's language.
    """
    nonterminals = set(cfg.nonterminals)
    rules = {name: [] for name in cfg.nonterminals}
    for lhs, rhs in cfg.productions:
        rules[lhs].append([symbol for symbol in rhs if symbol in nonterminals])

    productive = set()
    while True:
        before = len(productive)
        for name, alternatives in rules.items():
            if any(all(symbol in productive for symbol in rhs) for rhs in alternatives):
                productive.add(name)
        if len(productive) == before:
            break

    def reachable_through(allow):
        reached, pending = set(), [cfg.start]
        while pending:
            name = pending.pop()
            if name not in reached:
                reached.add(name)
                pending.extend(symbol for rhs in rules[name] if allow(rhs) for symbol in rhs)
        return reached

    reachable = (reachable_through(lambda rhs: all(symbol in productive for symbol in rhs))
                 if cfg.start in productive else set())
    used = reachable_through(lambda rhs: True)
    unproductive = [name for name in cfg.nonterminals if name not in productive]
    return reachable, used, unproductive


def approximate_and_detect(cfg, level):
    """Search through `level`, or stop when the start dependencies stabilize.

    Union overlap and competing concatenation cuts are detected by step(),
    during the same evaluation that constructs each level's finite languages.
    The input productions are never changed.
    """
    if type(level) is not int or level < 1:
        raise ValueError("level must be a positive integer")
    catalog = GrammarCatalog(cfg)
    reachable, used, unproductive = analyse_dependencies(cfg)
    dependencies = [catalog.nonterminals[name] for name in cfg.nonterminals if name in used]
    previous_counts = [nt.next.root.size for nt in dependencies]
    sites = {}
    saturated = False

    for _ in range(level):
        for finding in catalog.grammar.step():
            owner = finding.nonterminal.name
            paths = finding.alternatives or (finding.path,)
            rules = tuple(rule for path in paths for rule in catalog.site_rules[owner, tuple(path)])
            key = (finding.kind, owner, rules, tuple(finding.path))
            if key not in sites:
                sites[key] = AmbiguitySite(finding, rules, finding.iteration)
            else:
                sites[key].finding = finding

        counts = [nt.next.root.size for nt in dependencies]
        # Languages only grow: equal finite counts imply equal sets.
        saturated = counts == previous_counts
        if saturated:
            break
        previous_counts = counts

    # An ambiguous prefix cannot finish a production with an unproductive factor.
    dead = set(unproductive)
    findings = [site for site in sites.values() if all(symbol not in dead
                for rule in site.rule_indices for symbol in cfg.productions[rule][1])]
    findings.sort(key=lambda site: (
        site.first_level, min(site.rule_indices), site.finding.kind,
        site.finding.nonterminal.name, site.rule_indices,
        format_formula(site.finding.formula) if site.finding.kind == "concatenation" else ""))

    return ApproximationResult(
        cfg, catalog, level, catalog.grammar.iteration, saturated, findings,
        reachable, unproductive, catalog.nonterminals[cfg.start].next.root.size)
