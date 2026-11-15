"""Read a BNF text file and write an ambiguity report with two parse trees
for each witness:

    python check_grammar.py grammar.txt
    python check_grammar.py grammar.txt -o report.txt --level 8

The default report is <stem>.ambiguity.txt beside the grammar. Each run
checks parse trees through the requested height under time and memory
limits. Progress and errors go to standard error.

Exit status: 0 means no ambiguity found (or proved unambiguous), 1 means
ambiguous, 2 means unreadable input, 3 means a limit stopped the search,
and 4 means the run or report write failed.
"""

import argparse
from itertools import zip_longest
import math
import os
from pathlib import Path
import sys
import tempfile
import textwrap
import time

from grammar_engine import ConcatenationFormula, parse_grammar
import analysis_runtime
from grammar_proofs import ProofLimitExceeded, build_grammar, finding_from_record, prove_finding


DEFAULT_LEVEL = 6
DEFAULT_SECONDS = 90
DEFAULT_MEMORY_MB = 2048
NONE_FOUND, AMBIGUOUS, UNREADABLE, LIMITED, FAILED = range(5)

EPILOG = """\
examples:
  python check_grammar.py grammar.txt
  python check_grammar.py grammar.txt -o report.txt
  python check_grammar.py grammar.txt --level 8 --max-seconds 60

BNF rules use A ::= x y | z, with more alternatives on lines beginning
with | or repeated left sides. Nonterminals may use <name> notation.
An empty alternative denotes the empty string. Quote a token such as '|'
or 'x*' that would otherwise read as notation.

exit status:
  0  no ambiguity found through the level, or proved unambiguous
  1  ambiguous
  2  the grammar or command line cannot be read
  3  a time or memory limit stopped the search
  4  the run or report write failed
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
        data = analysis_runtime.grammar_data(cfg)
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


def saturated(levels, used):
    """Whether the languages the start symbol is built from stopped growing at
    the last level: then no later level adds a sentence or an ambiguity."""
    return len(levels) > 1 and all(levels[-1]["counts"][name] == levels[-2]["counts"][name] for name in used)


def settled(levels, used):
    """The levels up to the first one at which saturated() holds, so that a
    report doesn't depend on how many more a worker saved before it was stopped."""
    for number in range(2, len(levels) + 1):
        if saturated(levels[:number], used):
            return levels[:number]
    return levels


def compute(data, level, directory, seconds, memory_mb, used, say):
    """Compute levels within the limits, returning completed summaries and
    the reason for stopping before the requested level, if any."""
    started = time.monotonic()
    start = data["start"]
    levels = analysis_runtime.prepare_directory(directory, data)

    def record_saved():
        while len(levels) <= level and analysis_runtime.level_file(directory, len(levels)).exists():
            levels.append(analysis_runtime.read_summary(analysis_runtime.level_file(directory, len(levels))))
            details = levels[-1]
            say(f"level {details['level']}: {details['counts'][start]} sentences of {start}, "
                f"{details['findings_count']} ambiguous site(s), {time.monotonic() - started:.1f} s")

    def on_event(event):
        if event.get("saved"):
            record_saved()

    process, error_path = analysis_runtime.start_worker(directory, level)
    try:
        reason = analysis_runtime.follow_worker(
            process, analysis_runtime.memory_reader(), lambda: memory_mb * 1024 ** 2,
            deadline=started + seconds, on_event=on_event,
            cancelled=lambda: saturated(levels, used))
    finally:
        analysis_runtime.end_worker(process, directory)
    # Include levels saved just before the worker exited.
    record_saved()
    levels = settled(levels, used)
    if len(levels) > level or saturated(levels, used):
        return levels, None
    failed = len(levels)
    if reason == "memory":
        return levels, {"reason": "memory",
                        "message": f"Level {failed} stopped at the {memory_mb} MiB memory limit."}
    if reason in ("deadline", "level time"):
        limit = seconds if reason == "deadline" else analysis_runtime.LEVEL_SECONDS
        return levels, {"reason": "time",
                        "message": f"Level {failed} stopped at the {limit:g}-second time limit."}
    if reason == "monitor":
        return levels, {"reason": "monitor",
                        "message": f"Level {failed} stopped because the worker's memory couldn't be read."}
    error = error_path.read_text(errors="replace").strip()[-1500:]
    return levels, {"reason": "error",
                    "message": f"Level {failed} failed: {error or 'the worker exited without saving it'}"}


def _rule_text(rule):
    return f"{rule['lhs']} ::= {' '.join(rule['rhs']) if rule['rhs'] else 'ε'}"


def _symbol_count(formula):
    if isinstance(formula, ConcatenationFormula):
        return _symbol_count(formula.left) + _symbol_count(formula.right)
    return 1


def _names(names):
    shown = ", ".join(names[:10])
    return shown + (f" and {len(names) - 10} more" if len(names) > 10 else "")


def _derivations(record, first_level, catalog):
    """A record's finding and the two derivations of its witness, taken at
    the earliest level that has both. The proof checker returns the first
    derivation it meets within a level, which at a late level can run through
    a chain of empty rules; at the earliest level the trees are no taller
    than the ambiguity needs."""
    for level in range(first_level, record["level"]):
        finding = finding_from_record({**record, "level": level}, catalog)
        try:
            return finding, prove_finding(finding, catalog)
        except (ProofLimitExceeded, ValueError):
            continue        # the witness isn't derived both ways this early, or it takes too much work to tell
    finding = finding_from_record(record, catalog)
    return finding, prove_finding(finding, catalog)


def build_report(path, data, places, level, levels, stopped, directory):
    catalog = build_grammar(data)
    position = {rule["id"]: index for index, rule in enumerate(catalog.rules)}
    texts = [_rule_text(rule) for rule in catalog.rules]
    reached, used, unproductive = analyse(data)

    sites = {}
    for number in range(1, len(levels)):
        for record in analysis_runtime.read_findings(analysis_runtime.level_file(directory, number)):
            rules = tuple(position[rule_id] for rule_id in record["candidate_production_ids"])
            key = (record["kind"], record["owner"], rules,
                   record["expression"] if record["kind"] == "concatenation" else None)
            sites.setdefault(key, {"first_level": number, "rules": rules})["record"] = record

    entries = []
    for key, site in sites.items():
        record = site["record"]
        entry = {"kind": record["kind"], "nonterminal": record["owner"],
                 "first_level": site["first_level"], "reachable": record["owner"] in reached,
                 "rules": [{"text": texts[rule], "source": places[rule]} for rule in site["rules"]],
                 "witness": record["witness"]}
        if record["kind"] == "concatenation":
            entry["expression"] = record["expression"]
            entry["cuts"] = sorted(len(left) for left, _ in record["raw_factorizations"])
        entries.append(((site["first_level"], min(site["rules"]), record["kind"], key), entry, record))
    entries.sort(key=lambda item: item[0])

    def parse_tree(node):
        """Turn a verified derivation into the nodes drawn in the report."""
        if node["kind"] == "terminal":
            return [node["symbol"]]
        children = [item for child in node["children"] for item in parse_tree(child)]
        if node["kind"] in ("nonterminal", "production"):
            return [{"symbol": node["symbol"], "rule": texts[position[node["production_id"]]], "children": children}]
        return children

    for _, entry, record in entries:
        try:
            finding, derivations = _derivations(record, entry["first_level"], catalog)
        except (ProofLimitExceeded, ValueError) as error:
            entry["trees_error"] = str(error)
            continue
        if record["kind"] == "union":
            entry["trees"] = [parse_tree(derivation)[0] for derivation in derivations]
            continue
        rule = catalog.rules[position[record["candidate_production_ids"][0]]]
        root = {"symbol": record["owner"], "rule": _rule_text(rule)}
        if _symbol_count(finding.formula) < len(rule["rhs"]):
            root["rhs_prefix"] = _symbol_count(finding.formula)
        entry["trees"] = [{**root, "children": parse_tree(derivation)} for derivation in derivations]

    final = saturated(levels, used)
    if any(entry["reachable"] for _, entry, _ in entries):
        verdict, code = "ambiguous", AMBIGUOUS
    else:
        verdict = "unambiguous" if final else "none_found"
        code = (FAILED if stopped["reason"] == "error" else LIMITED) if stopped and not final else NONE_FOUND

    start = data["start"]
    reached_level = len(levels) - 1
    warnings = []
    if reached_level and levels[-1]["counts"][start] == "0":
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
        "start_sentences": levels[-1]["counts"][start],
        "verdict": verdict,
        "stopped": stopped,
        "site_count": len(entries),
        "sites": [entry for _, entry, _ in entries],
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
    trees = site.get("trees")

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
    if trees and "rhs_prefix" in trees[0]:
        witness += f", from the rule's first {trees[0]['rhs_prefix']} symbols"
    lines.append(witness)

    if trees is None:
        if not union:
            first, second = (f"{_sentence(site['witness'][:cut])} | {_sentence(site['witness'][cut:])}"
                             for cut in site["cuts"])
            lines += [f"   Divided as: {first}", f"          and: {second}",
                      f"   The ambiguous product, in the engine's notation: {site['expression']}"]
        reason = site.get("trees_error", "The proof could not be reconstructed.")
        return lines + [""] + _wrapped(f"Parse trees: not drawn. {reason}", "   ", "   ")

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
    """A report as plain text: the verdict, what was checked, then each listed
    site and the report's warnings."""
    grammar = report["grammar"]
    name = grammar["file"]
    start, level, asked = grammar["start"], report["level_reached"], report["requested_level"]
    count, verdict, stopped = report["site_count"], report["verdict"], report["stopped"]
    found = _plural(count, "ambiguity", "ambiguities")

    if verdict == "ambiguous":
        lines = [f"AMBIGUOUS: {found} found in {name}"]
    elif verdict == "unambiguous":
        lines = [f"UNAMBIGUOUS: {name} is proved unambiguous"]
    elif not level:
        lines = [f"NOT CHECKED: no level of {name} finished"]
    elif stopped:
        lines = [f"NO AMBIGUITY FOUND in {name} through level {level}",
                 f"The run stopped there, so levels {level + 1} to {asked} were not checked."]
    else:
        lines = [f"NO AMBIGUITY FOUND in {name} through level {level}",
                 "Deeper parse trees were not checked; a higher --level looks further."]
    if count and verdict != "ambiguous":
        lines += _wrapped(f"Listed below: {found} in rules that no sentence of {start} is derived through.", "", "")

    if not level:
        checked = "no level finished"
    elif stopped:
        checked = f"through level {level} of the {asked} asked for"
    elif level < asked:
        # The run ended early without a limit: the languages stopped growing.
        checked = (f"through level {level}, which added nothing to the languages {start} is built from, "
                   f"so no later level can")
    else:
        checked = f"through level {level} (parse trees of height {level} or less)"
    lines += ["",
              f"Grammar:    {_plural(grammar['rules'], 'rule')}, {_plural(grammar['nonterminals'], 'nonterminal')}, "
              f"{_plural(grammar['terminals'], 'terminal')}, start symbol {start}"]
    lines += _wrapped(checked, "Checked:    ", "            ")
    if stopped:
        lines += _wrapped(stopped["message"], "Stopped:    ", "            ")
    if level:
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


def _count(minimum, kind=int):
    def read(text):
        try:
            value = kind(text)
        except ValueError:
            raise argparse.ArgumentTypeError(f"not a number: {text}") from None
        if kind is float and not math.isfinite(value):
            raise argparse.ArgumentTypeError("must be a finite number")
        if value < minimum:
            raise argparse.ArgumentTypeError(f"must be at least {minimum}")
        return value
    return read


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="check_grammar.py", epilog=EPILOG, formatter_class=argparse.RawDescriptionHelpFormatter,
        description="Read a BNF text file and write an ambiguity report with parse trees.")
    parser.add_argument("grammar", metavar="FILE", help="BNF grammar text file")
    parser.add_argument("-o", "--output", metavar="FILE",
                        help="report file (default: <stem>.ambiguity.txt beside the grammar)")
    parser.add_argument("--level", type=_count(1), default=DEFAULT_LEVEL,
                        help=f"check parse trees up to this height (default {DEFAULT_LEVEL})")
    parser.add_argument("--max-seconds", type=_count(0.001, float), default=DEFAULT_SECONDS,
                        help=f"stop computing after this many seconds (default {DEFAULT_SECONDS})")
    parser.add_argument("--max-memory-mb", type=_count(64), default=DEFAULT_MEMORY_MB,
                        help=f"stop the worker at this many MiB (default {DEFAULT_MEMORY_MB})")
    args = parser.parse_args(argv)
    if args.grammar == "-" or args.output == "-":
        parser.error("name input and output files; '-' streams are not supported")

    def say(message):
        print(f"check_grammar: {message}", file=sys.stderr, flush=True)

    protected = [Path(args.grammar)]
    try:
        output = Path(args.output) if args.output is not None else Path(args.grammar).with_suffix(".ambiguity.txt")
        check_output_path(output, protected)
    except (OSError, ValueError) as error:
        say(f"Can't choose report output: {error}")
        return FAILED
    try:
        data, places = read_grammar(args.grammar)
    except InputError as error:
        say(str(error))
        return UNREADABLE
    _, used, _ = analyse(data)

    try:
        with tempfile.TemporaryDirectory(prefix="ambiguity-") as temporary:
            directory = Path(temporary)
            levels, stopped = compute(data, args.level, directory, args.max_seconds, args.max_memory_mb, used, say)
            report = build_report(args.grammar, data, places, args.level, levels, stopped, directory)
    except (OSError, RuntimeError) as error:
        say(f"The run failed: {error}")
        return FAILED
    try:
        save_report(output, render_text(report), protected)
    except (OSError, ValueError) as error:
        say(f"Can't write report to {output}: {error}")
        return FAILED
    say(f"report saved to {output}")
    return report["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
