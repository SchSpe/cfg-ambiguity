"""Read a BNF text file and write an ambiguity report with two parse trees
for each witness:

    python check_grammar.py grammar.txt
    python check_grammar.py grammar.txt -o report.txt --level 8

The default report is <stem>.ambiguity.txt beside the grammar. The engine
checks parse trees through the requested height, stopping earlier if the
languages stop growing. Errors and the saved report path go to standard error.

Exit status: 0 means no ambiguity found (or proved unambiguous), 1 means
ambiguous, 2 means unreadable input, 4 means the run or report write failed,
and 130 means interrupted.
"""

import argparse
from copy import copy
from itertools import zip_longest
import os
from pathlib import Path
import sys
import tempfile
import textwrap

from grammar_engine import ConcatenationFormula, format_formula, parse_grammar
from grammar_proofs import build_grammar, prove_finding


DEFAULT_LEVEL = 6
NONE_FOUND, AMBIGUOUS, UNREADABLE, FAILED = 0, 1, 2, 4

EPILOG = """\
examples:
  python check_grammar.py grammar.txt
  python check_grammar.py grammar.txt -o report.txt
  python check_grammar.py grammar.txt --level 8

BNF rules use A ::= x y | z, with more alternatives on lines beginning
with | or repeated left sides. Nonterminals may use <name> notation.
An empty alternative denotes the empty string. Quote a token such as '|'
or 'x*' that would otherwise read as notation.

exit status:
  0  no ambiguity found through the level, or proved unambiguous
  1  ambiguous
  2  the grammar or command line cannot be read
  4  the run or report write failed
  130  interrupted
"""


class InputError(Exception):
    """The grammar, or a file the command names, can't be read."""


def read_grammar(path):
    """Read BNF and retain the source line of each expanded production."""
    try:
        text = Path(path).read_bytes().decode("utf-8-sig")
    except OSError as error:
        raise InputError(f"Can't read {path}: {error.strerror or error}") from None
    except UnicodeDecodeError:
        raise InputError(f"{path} isn't UTF-8 text") from None
    try:
        cfg = parse_grammar(text).cfg
        data = {"start": cfg.start, "terminals": list(cfg.terminals),
                "nonterminals": list(cfg.nonterminals),
                "productions": [{"lhs": lhs, "rhs": list(rhs)} for lhs, rhs in cfg.productions]}
    except (ValueError, TypeError) as error:
        raise InputError(str(error)) from None
    except RecursionError:
        raise InputError("The grammar is nested too deeply for the engine") from None
    return data, [f"{path}:{number}" for number in cfg.production_lines]


def analyse(data):
    """Return (reached, used, unproductive): the nonterminals the start
    symbol reaches through rules whose symbols all derive sentences, so that
    a witness of theirs extends to a sentence of the whole grammar; every
    nonterminal the start symbol's language is built from; and those that
    derive no sentence at all, in grammar order."""
    nonterminals = set(data["nonterminals"])
    rules = {name: [] for name in data["nonterminals"]}
    for rule in data["productions"]:
        rules[rule["lhs"]].append([symbol for symbol in rule["rhs"] if symbol in nonterminals])
    productive = set()
    grown = True
    while grown:
        grown = False
        for name, alternatives in rules.items():
            if name not in productive and any(all(symbol in productive for symbol in rhs) for rhs in alternatives):
                productive.add(name)
                grown = True

    def closure(follows):
        seen, pending = set(), [data["start"]]
        while pending:
            name = pending.pop()
            if name not in seen:
                seen.add(name)
                pending.extend(symbol for rhs in rules[name] if follows(rhs) for symbol in rhs)
        return seen

    reached = closure(lambda rhs: all(symbol in productive for symbol in rhs)) if data["start"] in productive else set()
    used = closure(lambda rhs: True)
    unproductive = [name for name in data["nonterminals"] if name not in productive]
    return reached, used, unproductive


def compute(catalog, level, used):
    """Run the engine directly, retaining the latest witness for each site."""
    grammar = catalog.grammar
    previous = {name: nt.next.trie.root.size for name, nt in catalog.nonterminals.items()}
    sites = {}
    final = False
    for _ in range(level):
        for finding in grammar.step():
            owner = finding.nonterminal.name
            paths = finding.alternatives or (finding.path,)
            rules = tuple(rule_id for path in paths for rule_id in catalog.site_rules[owner, tuple(path)])
            key = (finding.kind, owner, rules, tuple(finding.path))
            sites.setdefault(key, {"first_level": finding.iteration, "rules": rules})["finding"] = finding
        grammar.findings.clear()
        counts = {name: nt.next.trie.root.size for name, nt in catalog.nonterminals.items()}
        final = all(counts[name] == previous[name] for name in used)
        if final:
            break
        previous = counts
    return list(sites.values()), final


def _rule_text(rule):
    return f"{rule['lhs']} ::= {' '.join(rule['rhs']) if rule['rhs'] else 'ε'}"


def _symbol_count(formula):
    if isinstance(formula, ConcatenationFormula):
        return _symbol_count(formula.left) + _symbol_count(formula.right)
    return 1


def _names(names):
    shown = ", ".join(names[:10])
    return shown + (f" and {len(names) - 10} more" if len(names) > 10 else "")


def _derivations(finding, first_level, catalog):
    """Verify the latest witness at the earliest level that derives it both
    ways, keeping its trees no taller than the ambiguity needs."""
    for level in range(first_level, finding.iteration):
        earlier = copy(finding)
        earlier.iteration = level
        try:
            return prove_finding(earlier, catalog)
        except ValueError:
            continue
    return prove_finding(finding, catalog)


def build_report(path, data, places, level, catalog, sites, final):
    position = {rule["id"]: index for index, rule in enumerate(catalog.rules)}
    texts = [_rule_text(rule) for rule in catalog.rules]
    reached, _, unproductive = analyse(data)

    entries = []
    for site in sites:
        finding = site["finding"]
        rules = tuple(position[rule_id] for rule_id in site["rules"])
        owner = finding.nonterminal.name
        entry = {"kind": finding.kind, "nonterminal": owner,
                 "first_level": site["first_level"], "reachable": owner in reached,
                 "rules": [{"text": texts[rule], "source": places[rule]} for rule in rules],
                 "witness": list(finding.sentence.symbols)}
        order = (site["first_level"], min(rules), finding.kind, owner, rules,
                 format_formula(finding.formula) if finding.kind == "concatenation" else "")
        entries.append((order, entry, finding, rules))
    entries.sort(key=lambda item: item[0])

    def parse_tree(node):
        """Turn a verified derivation into the nodes drawn in the report."""
        if node["kind"] == "terminal":
            return [node["symbol"]]
        children = [item for child in node["children"] for item in parse_tree(child)]
        if node["kind"] in ("nonterminal", "production"):
            return [{"symbol": node["symbol"], "rule": texts[position[node["production_id"]]], "children": children}]
        return children

    for _, entry, finding, rules in entries:
        derivations = _derivations(finding, entry["first_level"], catalog)
        if finding.kind == "union":
            entry["trees"] = [parse_tree(derivation)[0] for derivation in derivations]
            continue
        rule = catalog.rules[rules[0]]
        root = {"symbol": finding.nonterminal.name, "rule": _rule_text(rule)}
        if _symbol_count(finding.formula) < len(rule["rhs"]):
            root["rhs_prefix"] = _symbol_count(finding.formula)
        entry["trees"] = [{**root, "children": parse_tree(derivation)} for derivation in derivations]

    if any(entry["reachable"] for _, entry, _, _ in entries):
        verdict, code = "ambiguous", AMBIGUOUS
    else:
        verdict, code = ("unambiguous" if final else "none_found"), NONE_FOUND

    start = data["start"]
    reached_level = catalog.grammar.iteration
    start_sentences = catalog.nonterminals[start].next.trie.root.size
    warnings = []
    if not start_sentences:
        warnings.append(f"{start} derives no sentence {'at all' if final else f'through level {reached_level}'}.")
    if unproductive:
        warnings.append(f"No sentence can be derived from {_names(unproductive)}.")
    unreached = [name for name in data["nonterminals"] if name not in reached and name not in unproductive]
    if unreached and start not in unproductive:
        warnings.append(f"No sentence of {start} is derived through {_names(unreached)}, "
                        f"so an ambiguity there doesn't make the grammar ambiguous.")

    return {
        "exit_code": code,
        "grammar": {"file": path, "start": start, "rules": len(data["productions"]),
                    "nonterminals": len(data["nonterminals"]), "terminals": len(data["terminals"])},
        "requested_level": level,
        "level_reached": reached_level,
        "start_sentences": str(start_sentences),
        "verdict": verdict,
        "site_count": len(entries),
        "sites": [entry for _, entry, _, _ in entries],
        "warnings": warnings,
    }


EMPTY = "(empty)"
TEXT_WIDTH = 79


def _plural(number, singular, plural=None):
    return f"{number:,} {singular if number == 1 else plural or singular + 's'}"


def _amount(digits):
    """A count given in decimal: in full up to 15 digits, then to three figures."""
    return f"{int(digits):,}" if len(digits) <= 15 else f"about {digits[0]}.{digits[1:3]} x 10^{len(digits) - 1}"


def _sentence(tokens):
    return " ".join(tokens) if tokens else EMPTY


def _shown_rule(text):
    return text[:-1] + EMPTY if text.endswith("::= ε") else text


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


def _beside(blocks, indent):
    """Blocks of lines side by side when there are two that fit the width
    together, else one under the other."""
    if len(blocks) == 2:
        left, right = blocks
        width = max(map(len, left)) + 4
        if len(indent) + width + max(map(len, right)) <= TEXT_WIDTH:
            return [(indent + first.ljust(width) + second).rstrip()
                    for first, second in zip_longest(left, right, fillvalue="")]
    lines = []
    for block in blocks:
        lines += [""] * bool(lines) + [indent + line for line in block]
    return lines


def _wrapped(text, first, rest):
    return textwrap.wrap(text, TEXT_WIDTH, initial_indent=first, subsequent_indent=rest,
                         break_long_words=False, break_on_hyphens=False)


def _site_lines(number, site, grammar):
    """One site of the report: its kind and nonterminal, its rules and where
    they are, its witness and the witness's two parse trees."""
    union = site["kind"] == "union"
    # A rule read from the grammar file itself is named by its line there.
    file = grammar["file"] + ":"
    rules = [_shown_rule(rule["text"]) for rule in site["rules"]]
    places = [rule.get("source", "") for rule in site["rules"]]
    places = [f"line {place[len(file):]}" if place.startswith(file) else place for place in places]
    width = max(map(len, rules))
    trees = site["trees"]

    lines = [f"{number}. {site['kind'].capitalize()} ambiguity in {site['nonterminal']}, "
             f"first seen at level {site['first_level']}"]
    if not site["reachable"]:
        lines += _wrapped(f"No sentence of {grammar['start']} is derived through {site['nonterminal']}, "
                          f"so this doesn't make the grammar ambiguous.", "   ", "   ")
    lines += ["", "   Two rules derive the same sentence:" if union
              else "   One rule divides the same sentence in two ways:"]
    lines += [f"     {rule.ljust(width)}    ({place})" if place else f"     {rule}"
              for rule, place in zip(rules, places)]
    witness = f"   Witness: {_sentence(site['witness'])}"
    if "rhs_prefix" in trees[0]:
        witness += f", from the rule's first {trees[0]['rhs_prefix']} symbols"
    lines.append(witness)

    if union:
        # A union site's trees are in the order of its rules; two rules with
        # the same text are told apart by their places.
        same = rules[0] == rules[1]
        captions = [_shown_rule(tree["rule"]) + (f" ({place})" if same and place else "")
                    for tree, place in zip(trees, places)]
    else:
        # A product is its first symbols times its last one, so the tree's
        # last child is the right factor.
        captions = [f"{_sentence([leaf for child in tree['children'][:-1] for leaf in _leaves(child)])} | "
                    f"{_sentence(_leaves(tree['children'][-1]))}" for tree in trees]
    blocks = [[f"Parse tree {index}: {caption}", *_drawing(tree)]
              for index, (caption, tree) in enumerate(zip(captions, trees), 1)]
    return lines + [""] + _beside(blocks, "   ")


def render_text(report):
    """The verdict, search depth, ambiguity witnesses and their parse trees."""
    grammar = report["grammar"]
    name = grammar["file"]
    start, level, asked = grammar["start"], report["level_reached"], report["requested_level"]
    count, verdict = report["site_count"], report["verdict"]
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

    if level < asked:
        checked = (f"through level {level}, which added nothing to the languages {start} is built from, "
                   f"so no later level can")
    else:
        checked = f"through level {level} (parse trees of height {level} or less)"
    lines += ["",
              f"Grammar:    {_plural(grammar['rules'], 'rule')}, {_plural(grammar['nonterminals'], 'nonterminal')}, "
              f"{_plural(grammar['terminals'], 'terminal')}, start symbol {start}"]
    lines += _wrapped(checked, "Checked:    ", "            ")
    lines.append(f"Sentences:  {_amount(report['start_sentences'])} of {start} at level {level}")

    for number, site in enumerate(report["sites"], 1):
        lines += ["", *_site_lines(number, site, grammar)]
    if report["warnings"]:
        lines += ["", "Notes:"]
        for warning in report["warnings"]:
            lines += _wrapped(warning, "- ", "  ")
    return "\n".join(lines) + "\n"


def check_output_path(path, protected):
    """Keep a report from replacing its grammar input."""
    resolved = path.resolve()
    for source in protected:
        if resolved == source.resolve() or (path.exists() and source.exists() and path.samefile(source)):
            raise ValueError(f"the report would overwrite input file {source}")


def save_report(path, text, protected):
    """Write UTF-8 beside the destination and replace it only after success."""
    check_output_path(path, protected)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n",
                                         prefix=f".{path.name}.", suffix=".tmp",
                                         dir=path.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        check_output_path(path, protected)
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
        prog="check_grammar.py", epilog=EPILOG, formatter_class=argparse.RawDescriptionHelpFormatter,
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
        protected = [Path(args.grammar)]
        try:
            output = Path(args.output) if args.output is not None else Path(args.grammar).with_suffix(".ambiguity.txt")
            check_output_path(output, protected)
        except (OSError, ValueError) as error:
            say(f"Can't choose report output: {error}")
            return FAILED
        try:
            data, places = read_grammar(args.grammar)
            catalog = build_grammar(data)
        except RecursionError:
            say("The grammar is nested too deeply for the engine")
            return UNREADABLE
        except (InputError, ValueError) as error:
            say(str(error))
            return UNREADABLE
        try:
            _, used, _ = analyse(data)
            sites, final = compute(catalog, args.level, used)
            report = build_report(args.grammar, data, places, args.level, catalog, sites, final)
            text = render_text(report)
        except (RuntimeError, ValueError, MemoryError) as error:
            say(f"The run failed: {error}")
            return FAILED
        try:
            save_report(output, text, protected)
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
