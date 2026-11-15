"""Read BNF, find ambiguity witnesses, and write a text report with parse trees."""

import argparse
from itertools import zip_longest
import os
from pathlib import Path
import sys
import tempfile
import textwrap

from grammar_engine import format_formula, parse_grammar
from grammar_proofs import GrammarCatalog, prove_finding


DEFAULT_LEVEL = 6
NONE_FOUND, AMBIGUOUS, UNREADABLE, FAILED = 0, 1, 2, 4

class InputError(Exception):
    """The BNF file cannot be read or parsed."""


def read_grammar(path):
    try:
        return parse_grammar(Path(path).read_text(encoding="utf-8-sig"))
    except OSError as error:
        raise InputError(f"Can't read {path}: {error.strerror or error}") from None
    except UnicodeDecodeError:
        raise InputError(f"{path} isn't UTF-8 text") from None
    except ValueError as error:
        raise InputError(str(error)) from None


def analyse(cfg):
    """Return (reached, used, unproductive): the nonterminals the start
    symbol reaches through rules whose symbols all derive sentences, so that
    a witness of theirs extends to a sentence of the whole grammar; every
    nonterminal the start symbol's language is built from; and those that
    derive no sentence at all, in grammar order."""
    nonterminals = set(cfg.nonterminals)
    rules = {name: [] for name in cfg.nonterminals}
    for lhs, rhs in cfg.productions:
        rules[lhs].append([symbol for symbol in rhs if symbol in nonterminals])
    productive = set()
    grown = True
    while grown:
        grown = False
        for name, alternatives in rules.items():
            if name not in productive and any(all(symbol in productive for symbol in rhs) for rhs in alternatives):
                productive.add(name)
                grown = True

    def closure(follows):
        seen, pending = set(), [cfg.start]
        while pending:
            name = pending.pop()
            if name not in seen:
                seen.add(name)
                pending.extend(symbol for rhs in rules[name] if follows(rhs) for symbol in rhs)
        return seen

    reached = closure(lambda rhs: all(symbol in productive for symbol in rhs)) if cfg.start in productive else set()
    used = closure(lambda rhs: True)
    unproductive = [name for name in cfg.nonterminals if name not in productive]
    return reached, used, unproductive


def compute(catalog, level, used):
    """Run the engine directly, retaining the latest witness for each site."""
    grammar = catalog.grammar
    relevant = [catalog.nonterminals[name] for name in used]
    previous = [nt.next.root.size for nt in relevant]
    sites = {}
    final = False
    for _ in range(level):
        for finding in grammar.step():
            owner = finding.nonterminal.name
            paths = finding.alternatives or (finding.path,)
            rules = tuple(rule_id for path in paths for rule_id in catalog.site_rules[owner, tuple(path)])
            key = (finding.kind, owner, rules, tuple(finding.path))
            sites.setdefault(key, {"first_level": finding.iteration, "rules": rules})["finding"] = finding
        counts = [nt.next.root.size for nt in relevant]
        final = counts == previous
        if final:
            break
        previous = counts
    return list(sites.values()), final


def _rule_text(rule):
    lhs, rhs = rule
    return f"{lhs} ::= {' '.join(rhs) if rhs else EMPTY}"


def _names(names):
    shown = ", ".join(names[:10])
    return shown + (f" and {len(names) - 10} more" if len(names) > 10 else "")


def _derivations(finding, first_level, catalog):
    """Use the earliest level that proves the witness, to keep its trees short."""
    for level in range(first_level, finding.iteration):
        try:
            return prove_finding(finding, catalog, level)
        except ValueError:
            continue
    return prove_finding(finding, catalog, finding.iteration)


def build_report(path, cfg, level):
    catalog = GrammarCatalog(cfg)
    reached, used, unproductive = analyse(cfg)
    sites, final = compute(catalog, level, used)
    sites.sort(key=lambda site: (
        site["first_level"], min(site["rules"]), site["finding"].kind,
        site["finding"].nonterminal.name, site["rules"],
        format_formula(site["finding"].formula) if site["finding"].kind == "concatenation" else ""))
    entries = []
    for site in sites:
        finding = site["finding"]
        entries.append({"kind": finding.kind, "nonterminal": finding.nonterminal.name,
                        "first_level": site["first_level"], "reachable": finding.nonterminal.name in reached,
                        "rules": site["rules"], "witness": finding.sentence,
                        "trees": _derivations(finding, site["first_level"], catalog)})
    ambiguous = any(entry["reachable"] for entry in entries)
    verdict = "ambiguous" if ambiguous else "unambiguous" if final else "none_found"
    level_reached = catalog.grammar.iteration
    count = catalog.nonterminals[cfg.start].next.root.size
    warnings = []
    if not count:
        warnings.append(f"{cfg.start} derives no sentence {'at all' if final else f'through level {level_reached}'}.")
    if unproductive:
        warnings.append(f"No sentence can be derived from {_names(unproductive)}.")
    unreached = [name for name in cfg.nonterminals if name not in reached and name not in unproductive]
    if unreached and cfg.start not in unproductive:
        warnings.append(f"No sentence of {cfg.start} is derived through {_names(unreached)}, "
                        f"so an ambiguity there doesn't make the grammar ambiguous.")
    return {"file": path, "cfg": cfg, "exit_code": AMBIGUOUS if ambiguous else NONE_FOUND,
            "requested_level": level, "level_reached": level_reached, "start_sentences": count,
            "verdict": verdict, "sites": entries, "warnings": warnings}


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
    places = [f"line {cfg.production_lines[index]}" for index in site["rules"]]
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
    cfg, name = report["cfg"], report["file"]
    start, level, asked = cfg.start, report["level_reached"], report["requested_level"]
    count, verdict = len(report["sites"]), report["verdict"]
    found = _plural(count, "ambiguity", "ambiguities")
    if verdict == "ambiguous":
        lines = [f"AMBIGUOUS: {found} found in {name}"]
    elif verdict == "unambiguous":
        lines = [f"UNAMBIGUOUS: {name} is proved unambiguous"]
    else:
        lines = [f"NO AMBIGUITY FOUND in {name} through level {level}",
                 "Deeper parse trees were not checked; a higher --level looks further."]
    if count and verdict != "ambiguous":
        lines += _wrapped(f"Listed below: {found} in rules that no sentence of {start} is derived through.", "", "")
    checked = (f"through level {level}, which added nothing to the languages {start} is built from, "
               f"so no later level can" if level < asked
               else f"through level {level} (parse trees of height {level} or less)")
    lines += ["", f"Grammar:    {_plural(len(cfg.productions), 'rule')}, "
              f"{_plural(len(cfg.nonterminals), 'nonterminal')}, "
              f"{_plural(len(cfg.terminals), 'terminal')}, start symbol {start}"]
    lines += _wrapped(checked, "Checked:    ", "            ")
    lines.append(f"Sentences:  {_amount(report['start_sentences'])} of {start} at level {level}")
    for number, site in enumerate(report["sites"], 1):
        lines += ["", *_site_lines(number, site, cfg)]
    if report["warnings"]:
        lines += ["", "Notes:"]
        for warning in report["warnings"]:
            lines += _wrapped(warning, "- ", "  ")
    return "\n".join(lines) + "\n"


def check_output_path(path, source):
    """Keep a report from replacing its grammar input."""
    if path.resolve() == source.resolve() or (path.exists() and source.exists() and path.samefile(source)):
        raise ValueError(f"the report would overwrite input file {source}")


def save_report(path, text, source):
    """Write UTF-8 beside the destination and replace it only after success."""
    check_output_path(path, source)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n",
                                         prefix=f".{path.name}.", suffix=".tmp",
                                         dir=path.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        check_output_path(path, source)
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def positive_level(text):
    try:
        level = int(text)
    except ValueError:
        raise argparse.ArgumentTypeError(f"not an integer: {text}") from None
    if level < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return level


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="check_grammar.py",
        description="Read a BNF text file and write an ambiguity report with parse trees.")
    parser.add_argument("grammar", metavar="FILE", help="BNF grammar text file")
    parser.add_argument("-o", "--output", metavar="FILE",
                        help="report file (default: <stem>.ambiguity.txt beside the grammar)")
    parser.add_argument("--level", type=positive_level, default=DEFAULT_LEVEL,
                        help=f"check parse trees up to this height (default {DEFAULT_LEVEL})")
    args = parser.parse_args(argv)
    if args.grammar == "-" or args.output == "-":
        parser.error("name input and output files; '-' streams are not supported")

    def say(message):
        print(f"check_grammar: {message}", file=sys.stderr, flush=True)

    try:
        source = Path(args.grammar)
        try:
            output = Path(args.output) if args.output is not None else source.with_suffix(".ambiguity.txt")
            check_output_path(output, source)
        except (OSError, ValueError) as error:
            say(f"Can't choose report output: {error}")
            return FAILED
        try:
            cfg = read_grammar(args.grammar)
        except InputError as error:
            say(str(error))
            return UNREADABLE
        try:
            report = build_report(args.grammar, cfg, args.level)
            text = render_text(report)
        except (RuntimeError, ValueError, MemoryError) as error:
            say(f"The run failed: {error}")
            return FAILED
        try:
            save_report(output, text, source)
        except (OSError, ValueError) as error:
            say(f"Can't write report to {output}: {error}")
            return FAILED
    except KeyboardInterrupt:
        say("Interrupted; no partial report was written.")
        return 130
    say(f"report saved to {output}")
    return report["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
