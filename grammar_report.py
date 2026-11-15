"""Build verified evidence and format the result of the four-stage checker.

All findings and rule numbers refer to the grammar after NSF repairs. The
report retains the input grammar and the rewrite history so those rules can
be read in context. This module never repairs or approximates a grammar.
"""

from itertools import zip_longest
import textwrap

from grammar_proofs import prove_finding


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


def _plural(number, singular, plural=None):
    return f"{number:,} {singular if number == 1 else plural or singular + 's'}"


def _amount(count):
    """Keep very large sentence counts readable."""
    digits = str(count)
    return f"{count:,}" if len(digits) <= 15 else f"about {digits[0]}.{digits[1:3]} x 10^{len(digits) - 1}"


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
    """Present the repair history, checked grammar, search, and remaining evidence."""
    cfg, name = report["cfg"], report["file"]
    repairs = report["repairs"]
    target = f"the repaired grammar from {name}" if repairs.changes else name
    verdict, level = report["verdict"], report["level_reached"]
    reachable_sites = [site for site in report["sites"] if site["reachable"]]
    if verdict == "ambiguous":
        lines = [f"AMBIGUOUS: {target}"]
        if not reachable_sites:
            lines += _wrapped(
                "A remaining certain ambiguity-causing construct establishes ambiguity. "
                "The depth-limited search has not found a witness reachable from the start symbol; "
                "increase --level to search for its parse trees.", "", "")
    elif verdict == "unambiguous":
        lines = [f"UNAMBIGUOUS: {target} is proved unambiguous"]
    else:
        lines = [f"NO AMBIGUITY FOUND in {target} through level {level}",
                 "Deeper parse trees were not checked; a higher --level looks further."]

    original = report["original"]
    lines += ["", f"Input: {name}",
              f"       {_plural(len(original.productions), 'rule')}, start symbol {original.start}",
              "", *_repair_lines(repairs), "", "Grammar checked:"]
    if repairs.changes:
        lines.append("  The verdict, witnesses, and rule numbers below refer to this repaired grammar.")
    else:
        lines.append("  The input grammar was unchanged.")
    for index, rule in enumerate(cfg.productions):
        lines.append(f"  {_rule_text(rule)}    ({_rule_location(cfg, index)})")

    lines += ["", "Approximation and ambiguity detection:",
              f"  {_plural(len(cfg.productions), 'rule')}, "
              f"{_plural(len(cfg.nonterminals), 'nonterminal')}, "
              f"{_plural(len(cfg.terminals), 'terminal')}, start symbol {cfg.start}"]
    checked = f"Checked through level {level} (requested {report['requested_level']})."
    if report["saturated"]:
        checked += " The start-symbol dependencies stopped growing; no later level adds sentences."
    else:
        checked += f" This covers parse trees of height {level} or less."
    lines += _wrapped(checked, "  ", "  ")
    lines.append(f"  Sentences: {_amount(report['start_sentences'])} of {cfg.start} at level {level}")

    lines += ["", "Ambiguity witnesses:"]
    if not report["sites"]:
        lines.append("  None found through the checked level.")
    for number, site in enumerate(report["sites"], 1):
        lines += ["", *_site_lines(number, site, cfg)]

    lines += ["", "Remaining recognized CACCs:"]
    if not report["caccs"]:
        lines.append("  None recognized. This alone does not prove unambiguity.")
    for match in report["caccs"]:
        title = match.rule_id.replace("_", " ").capitalize()
        locations = "; ".join(_rule_location(cfg, index) for index in match.production_indices)
        lines += ["", *_wrapped(f"{title} in {match.nonterminal} ({locations})", "  ", "  ")]
        lines += _wrapped(match.reason, "    ", "    ")
        lines += _wrapped(f"Source: {match.source}.", "    ", "    ")
        if match.nonterminal not in report["reachable"]:
            lines += _wrapped(f"No sentence of {cfg.start} is derived through {match.nonterminal}, "
                              "so this does not make the checked grammar ambiguous.", "    ", "    ")
    if report["warnings"]:
        lines += ["", "Notes:"]
        for warning in report["warnings"]:
            lines += _wrapped(warning, "- ", "  ")
    return "\n".join(lines) + "\n"


def _repair_lines(repairs):
    lines = ["NSF CACC repairs:"]
    if not repairs.changes:
        lines.append("  No NSF repair was applied.")
    for number, change in enumerate(repairs.changes, 1):
        title = change.rule_id.replace("_", " ").capitalize()
        lines += [f"  {number}. {title} in {change.nonterminal}", "     Before:"]
        lines += [f"       {rule}" for rule in change.before.splitlines()]
        lines.append("     After:")
        lines += [f"       {rule}" for rule in change.after.splitlines()]
    if repairs.limit_reached:
        lines.append("  The repair limit was reached; some NSF constructs remain.")
    if repairs.stalled:
        lines.append("  Repairs stopped because no further supported rewrite made progress.")
    return lines
