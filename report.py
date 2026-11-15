"""Build verified evidence and format the result of the four-stage checker.

All findings and rule numbers refer to the grammar after NSF repairs. The
report presents the input grammar, the repaired grammar, and the ambiguity
witnesses with their parse trees. This module never repairs or approximates a grammar.
"""

from functools import lru_cache
from itertools import zip_longest
import textwrap

import approximate_and_detect as engine


def build_report(path, original, repairs, approximation):
    """Assemble a verdict and checked trees for the grammar that was searched."""
    cfg = approximation.cfg
    reached = approximation.reachable
    sites = []
    for site in approximation.sites:
        finding = site.finding
        sites.append({
            "kind": finding.kind, "nonterminal": finding.nonterminal.name,
            "first_level": site.first_level, "reachable": finding.nonterminal.name in reached,
            "rules": site.rule_indices, "witness": finding.sentence,
            "trees": _derivations(finding, site.first_level, approximation.catalog),
        })

    # Remaining constructs belong to the repaired grammar. A removed construct
    # describes the input and must not determine the repaired grammar's verdict.
    ambiguous = (any(site["reachable"] for site in sites)
                 or any(match.nonterminal in reached for match in repairs.remaining))
    verdict = "ambiguous" if ambiguous else "unambiguous" if approximation.saturated else "none_found"
    warnings = []
    if not approximation.start_sentences:
        extent = "at all" if approximation.saturated else f"through level {approximation.level_reached}"
        warnings.append(f"{cfg.start} derives no sentence {extent}.")
    if approximation.unproductive:
        warnings.append(f"No sentence can be derived from {_names(approximation.unproductive)}.")
    unreached = [name for name in cfg.nonterminals
                if name not in reached and name not in approximation.unproductive]
    if unreached and cfg.start not in approximation.unproductive:
        warnings.append(f"No sentence of {cfg.start} is derived through {_names(unreached)}, "
                        "so an ambiguity there does not make the checked grammar ambiguous.")

    return {
        "file": str(path), "original": original, "repairs": repairs, "cfg": cfg,
        "requested_level": approximation.requested_level, "level_reached": approximation.level_reached,
        "saturated": approximation.saturated, "start_sentences": approximation.start_sentences,
        "verdict": verdict, "exit_code": 1 if ambiguous else 0,
        "sites": sites, "caccs": repairs.remaining, "reachable": reached, "warnings": warnings,
    }


def _derivations(finding, first_level, catalog):
    """Try earlier levels for the latest witness so its displayed trees stay short."""
    for level in range(first_level, finding.iteration):
        try:
            return prove_finding(finding, catalog, level)
        except ValueError:
            continue
    return prove_finding(finding, catalog, finding.iteration)


def _rule_text(rule):
    lhs, rhs = rule
    return f"{lhs} ::= {' '.join(rhs) if rhs else EMPTY}"


def _rule_location(cfg, index):
    """Number the checked rules without inventing source lines for generated ones."""
    line = cfg.production_lines[index]
    origin = f"source line {line}" if line else "generated"
    return f"rule {index + 1}, {origin}"


def _names(names):
    shown = ", ".join(names[:10])
    return shown + (f" and {len(names) - 10} more" if len(names) > 10 else "")


EMPTY = "(empty)"
TEXT_WIDTH = 79


def _sentence(tokens):
    return " ".join(tokens) if tokens else EMPTY


def _leaves(item):
    """The terminals of a parse-tree item, left to right."""
    if isinstance(item, str):
        return [item]
    return [leaf for child in item["children"] for leaf in _leaves(child)]


def _drawing(item):
    """A parse-tree item as lines, one node to a line, each under its parent."""
    if isinstance(item, str):
        return [item]
    children = [_drawing(child) for child in item["children"]] or [[EMPTY]]
    if "rhs_prefix" in item:
        children.append(["(rest of the rule)"])
    lines = [item["symbol"]]
    for number, child in enumerate(children, 1):
        last = number == len(children)
        lines.append(("`-- " if last else "|-- ") + child[0])
        lines.extend(("    " if last else "|   ") + line for line in child[1:])
    return lines


def _beside(left, right):
    """Draw the two trees side by side when they fit, otherwise vertically."""
    width = max(map(len, left)) + 4
    if 3 + width + max(map(len, right)) <= TEXT_WIDTH:
        return [("   " + first.ljust(width) + second).rstrip()
                for first, second in zip_longest(left, right, fillvalue="")]
    return ["   " + line for line in left] + [""] + ["   " + line for line in right]


def _wrapped(text, first, rest):
    return textwrap.wrap(text, TEXT_WIDTH, initial_indent=first, subsequent_indent=rest,
                         break_long_words=False, break_on_hyphens=False)


def _site_lines(number, site, cfg):
    union = site["kind"] == "union"
    rules = [_rule_text(cfg.productions[index]) for index in site["rules"]]
    places = [_rule_location(cfg, index) for index in site["rules"]]
    width = max(map(len, rules))
    trees = site["trees"]
    lines = [f"{number}. {site['kind'].capitalize()} ambiguity in {site['nonterminal']}, "
             f"first seen at level {site['first_level']}"]
    if not site["reachable"]:
        lines += _wrapped(f"No sentence of {cfg.start} is derived through {site['nonterminal']}, "
                          f"so this doesn't make the grammar ambiguous.", "   ", "   ")
    lines += ["", "   Two rules derive the same sentence:" if union
              else "   One rule divides the same sentence in two ways:"]
    lines += [f"     {rule.ljust(width)}    ({place})" for rule, place in zip(rules, places)]
    witness = f"   Witness: {_sentence(site['witness'])}"
    if "rhs_prefix" in trees[0]:
        witness += f", from the rule's first {trees[0]['rhs_prefix']} symbols"
    lines.append(witness)
    if union:
        same = rules[0] == rules[1]
        captions = [_rule_text(cfg.productions[tree["rule"]]) + (f" ({place})" if same else "")
                    for tree, place in zip(trees, places)]
    else:
        captions = [f"{_sentence([leaf for child in tree['children'][:-1] for leaf in _leaves(child)])} | "
                    f"{_sentence(_leaves(tree['children'][-1]))}" for tree in trees]
    blocks = [[f"Parse tree {index}: {caption}", *_drawing(tree)]
              for index, (caption, tree) in enumerate(zip(captions, trees), 1)]
    return lines + [""] + _beside(*blocks)


def render_text(report):
    """Show the input grammar, repaired grammar, and ambiguities with trees."""
    original, cfg = report["original"], report["cfg"]
    repairs = report["repairs"]
    level = report["level_reached"]

    lines = ["Input grammar:", f"  File: {report['file']}", f"  Start symbol: {original.start}", ""]
    for index, rule in enumerate(original.productions):
        lines.append(f"  {_rule_text(rule)}    ({_rule_location(original, index)})")

    lines += ["", "Repaired grammar:", f"  Start symbol: {cfg.start}"]
    if not repairs.changes:
        lines.append("  Unchanged.")
    if repairs.limit_reached:
        lines.append("  The repair limit was reached; some NSF constructs remain.")
    if repairs.stalled:
        lines.append("  Repairs stopped because no further supported rewrite made progress.")
    lines.append("")
    for index, rule in enumerate(cfg.productions):
        lines.append(f"  {_rule_text(rule)}    ({_rule_location(cfg, index)})")

    lines += ["", "Ambiguities:"]
    verdict = report["verdict"]
    if verdict == "ambiguous":
        lines.append("  AMBIGUOUS: the repaired grammar has ambiguity reachable from its start symbol.")
    elif verdict == "unambiguous":
        lines.append("  UNAMBIGUOUS: the repaired grammar is proved unambiguous.")
    else:
        lines.append(f"  NO AMBIGUITY FOUND through level {level}.")
        lines.append("  Deeper parse trees were not checked; a higher --level looks further.")
    checked = f"Checked through level {level} (requested {report['requested_level']})."
    if report["saturated"]:
        checked += " The start-symbol dependencies stopped growing."
    lines += _wrapped(checked, "  ", "  ")

    if verdict == "ambiguous" and not any(site["reachable"] for site in report["sites"]):
        lines += _wrapped(
            "A structural check establishes ambiguity, but no witness trees reachable from the "
            "start symbol were found through this level. Increase --level to search for its trees.",
            "  ", "  ")
    elif not report["sites"]:
        lines.append(f"  No witness found through level {level}.")
    for number, site in enumerate(report["sites"], 1):
        lines += ["", *_site_lines(number, site, cfg)]

    for match in report["caccs"]:
        title = match.rule_id.replace("_", " ").capitalize()
        locations = "; ".join(_rule_location(cfg, index) for index in match.production_indices)
        lines += ["", *_wrapped(f"Structural finding: {title} in {match.nonterminal} ({locations})", "  ", "  ")]
        lines += _wrapped(match.reason, "    ", "    ")
        if match.nonterminal not in report["reachable"]:
            lines += _wrapped(f"No sentence of {cfg.start} is derived through {match.nonterminal}, "
                              "so this does not make the checked grammar ambiguous.", "    ", "    ")
    for warning in report["warnings"]:
        lines += ["", *_wrapped(warning, "  Note: ", "        ")]
    return "\n".join(lines) + "\n"


# ----- Witness reconstruction -----------------------------------------------


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
