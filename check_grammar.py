"""Check a grammar for ambiguity from the command line, in a form that
scripts, CI jobs and coding agents can use as well as people:

    python check_grammar.py grammar.txt --level 8
    python check_grammar.py grammar.txt -o report.txt

The grammar is BNF text (E ::= E + E | id, or <expr> ::= <expr> + <expr> | id)
or cfg-productions-v1 JSON (grammar_io.py); - reads standard input.
Alternatives may continue on lines beginning with |. Levels run under a
time and a memory limit, and cached per grammar, so a later call with a
higher --level carries on from the last level done. A text report is saved
beside the grammar as <stem>.ambiguity.txt, with the verdict and each
ambiguity's kind, rules, witness sentence and two parse trees. --output
chooses another file; --output - writes to standard output. JSON reports
(--json) and reports for standard input go to standard output by default.
--schema describes the JSON format. Progress goes to standard error, and
the exit status is the verdict:

    0  no ambiguity found through the requested level, or the grammar is
       proved unambiguous (its languages stopped growing, with none found)
    1  ambiguous: a site the start symbol reaches, not listed in --accept
    2  the grammar, the accept file or the command line can't be read
    3  a time or memory limit stopped the run before the requested level
    4  the run failed
"""

import argparse
import hashlib
from itertools import zip_longest
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import textwrap
import time

from grammar_engine import ConcatenationFormula, parse_grammar
import analysis_runtime
from grammar_proofs import ProofLimitExceeded, build_grammar, finding_from_record, serialize_finding
from grammar_storage import read_findings, read_summary


FORMAT = "ambiguity-report-v1"
DEFAULT_LEVEL = 6           # a higher --level resumes from the cache
DEFAULT_SECONDS = 90        # inside the 2-minute default timeout of an agent's shell command
DEFAULT_MEMORY_MB = 2048
DEFAULT_FINDINGS = 50
NONE_FOUND, AMBIGUOUS, UNREADABLE, LIMITED, FAILED = range(5)      # exit statuses
SCOPE = ("Each site is an ambiguity in one nonterminal's rules, shown by its witness: a sentence of "
         "that nonterminal with two parse trees. A site the start symbol reaches makes the whole "
         "grammar ambiguous. Finding nothing through a level covers parse trees of that height or "
         "less; it proves the grammar unambiguous only when proves_unambiguous is true.")

EPILOG = """\
exit status:
  0  no ambiguity found through the level, or the grammar is proved unambiguous
  1  ambiguous: a site the start symbol reaches, not listed in --accept
  2  the grammar, the accept file or the command line can't be read
  3  a time or memory limit stopped the run before the level
  4  the run failed

examples:
  python check_grammar.py g1.txt --level 6
  python check_grammar.py g1.txt --level 6 -o report.txt
  python check_grammar.py g1.txt -o -
  python check_grammar.py g1.txt --level 10 --max-seconds 60 --json --trees
  python check_grammar.py g1.txt --json --max-findings 0 > accepted.json
  python check_grammar.py g1.txt --accept accepted.json
  python check_grammar.py --schema

BNF rules use A ::= x y | z, with more alternatives on lines beginning
with | or repeated left sides. Nonterminals may use <name> notation.
An empty alternative denotes the empty string. Quote a token such as '|'
or 'x*' that would otherwise read as notation. Levels are
cached per grammar, so a later run with a higher --level continues where
this one stopped.
"""


# ----- The report's JSON Schema ----------------------------------------------

TREE = {"anyOf": [
    {"type": "string", "description": "A terminal."},
    {"type": "object", "additionalProperties": False, "required": ["symbol", "rule", "children"],
     "properties": {
         "symbol": {"type": "string", "description": "The nonterminal at this node."},
         "rule": {"type": "string", "description": "The rule used at this node, as A ::= x y."},
         "rhs_prefix": {"type": "integer", "minimum": 2,
                        "description": "At the root of a concatenation site's tree, when the ambiguous "
                                       "product is only the rule's first rhs_prefix symbols: the tree "
                                       "covers those symbols."},
         "children": {"type": "array", "items": {"$ref": "#/$defs/tree"}}}}]}

SITE = {
    "type": "object", "additionalProperties": False,
    "required": ["id", "kind", "nonterminal", "first_level", "reachable", "accepted", "rules", "witness"],
    "properties": {
        "id": {"type": "string",
               "description": "The site's name, made from its kind, nonterminal, rules and (for a "
                              "concatenation) product, so it survives edits elsewhere in the grammar. "
                              "List it in an --accept file to stop it counting."},
        "kind": {"enum": ["union", "concatenation"],
                 "description": "union: two rules of the nonterminal derive the witness. concatenation: "
                                "the factors of one rule's product can meet at two places in it."},
        "nonterminal": {"type": "string"},
        "first_level": {"type": "integer", "minimum": 1, "description": "The first level that showed the site."},
        "reachable": {"type": "boolean",
                      "description": "Whether the start symbol reaches the nonterminal through rules whose "
                                     "symbols all derive sentences, so that the witness extends to an "
                                     "ambiguous sentence of the whole grammar."},
        "accepted": {"type": "boolean", "description": "Listed in the --accept file, so it can't make the exit status 1."},
        "rules": {"type": "array", "minItems": 1, "maxItems": 2,
                  "description": "The two rules of a union site, earlier first, or the rule of a concatenation site.",
                  "items": {"type": "object", "additionalProperties": False, "required": ["text"],
                            "properties": {"text": {"type": "string"},
                                           "source": {"type": "string", "description": "file:line of the rule, when known."}}}},
        "witness": {"type": "array", "items": {"type": "string"},
                    "description": "The shortest sentence found with two parse trees, as terminals."},
        "expression": {"type": "string",
                       "description": "Concatenation sites: the ambiguous product in the rule, in the engine's notation."},
        "cuts": {"type": "array", "minItems": 2, "maxItems": 2, "items": {"type": "integer", "minimum": 0},
                 "description": "Concatenation sites: two places in the witness, counted in tokens, where "
                                "the product's factors can meet."},
        "trees": {"type": "array", "minItems": 2, "maxItems": 2, "items": {"$ref": "#/$defs/tree"},
                  "description": "With --trees: two different parse trees of the witness."},
        "trees_error": {"type": "string",
                        "description": "With --trees: why the trees couldn't be rebuilt, such as the proof checker's work limit."}}}

SCHEMA = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "title": "check_grammar.py report",
    "description": "The one JSON object check_grammar.py prints with --json. An unreadable grammar or command "
                   "gives only format, exit_code and error.",
    "type": "object", "additionalProperties": False, "required": ["format", "exit_code"],
    "$defs": {"tree": TREE, "site": SITE},
    "properties": {
        "format": {"const": FORMAT},
        "exit_code": {"enum": [0, 1, 2, 3, 4],
                      "description": "The command's exit status. 0: nothing found through the requested level, "
                                     "or proved unambiguous. 1: ambiguous. 2: unreadable input. 3: a limit "
                                     "stopped the run first. 4: the run failed."},
        "error": {"type": "object", "additionalProperties": False, "required": ["message"],
                  "properties": {"message": {"type": "string", "description": "What is wrong, and what to write instead."},
                                 "line": {"type": "integer", "minimum": 1, "description": "The grammar line at fault, when there is one."}}},
        "grammar": {"type": "object", "additionalProperties": False,
                    "required": ["file", "start", "rules", "nonterminals", "terminals"],
                    "properties": {"file": {"type": "string", "description": "As named on the command line; - is standard input."},
                                   "start": {"type": "string"},
                                   "rules": {"type": "integer", "minimum": 1},
                                   "nonterminals": {"type": "integer", "minimum": 1},
                                   "terminals": {"type": "array", "items": {"type": "string"},
                                                 "description": "Every terminal the rules use. A misspelt nonterminal shows up here."}}},
        "requested_level": {"type": "integer", "minimum": 1},
        "level_reached": {"type": "integer", "minimum": 0,
                          "description": "Every parse tree of height up to this level was checked. It is below "
                                         "requested_level when a limit stopped the run (see stopped) or when "
                                         "the languages stopped growing (verdict unambiguous)."},
        "start_sentences": {"type": "string", "pattern": "^[0-9]+$",
                            "description": "How many sentences the start symbol derives at level_reached, in "
                                           "decimal, since it can pass 2^64."},
        "verdict": {"enum": ["ambiguous", "unambiguous", "none_found"],
                    "description": "ambiguous: some reachable site, accepted or not. unambiguous: proved, as the "
                                   "languages stopped growing with no reachable site. none_found: no reachable "
                                   "site through level_reached, which says nothing about deeper levels."},
        "proves_unambiguous": {"type": "boolean"},
        "stopped": {"type": ["object", "null"], "additionalProperties": False,
                    "required": ["reason", "level", "message"],
                    "description": "Why the run ended before requested_level, or null.",
                    "properties": {"reason": {"enum": ["time", "memory", "monitor", "error"]},
                                   "level": {"type": "integer", "minimum": 1, "description": "The level that didn't finish."},
                                   "message": {"type": "string"},
                                   "limit_seconds": {"type": "number"},
                                   "limit_mb": {"type": "integer"}}},
        "scope": {"type": "string", "description": "What a site proves, and what finding none means."},
        "site_count": {"type": "integer", "minimum": 0,
                       "description": "Every site found, reachable or not; sites lists the first --max-findings."},
        "sites": {"type": "array", "items": {"$ref": "#/$defs/site"},
                  "description": "In order of first_level, then of the rules."},
        "warnings": {"type": "array", "items": {"type": "string"}},
        "timings": {"type": "array", "description": "With --timings: each level's time and its worker's memory.",
                    "items": {"type": "object", "additionalProperties": False,
                              "required": ["level", "seconds", "memory_mb"],
                              "properties": {"level": {"type": "integer"}, "seconds": {"type": "number"},
                                             "memory_mb": {"type": "number"}}}}}}


# ----- Reading the grammar ---------------------------------------------------

class InputError(Exception):
    """The grammar, or a file the command names, can't be read."""


def read_text(path):
    try:
        raw = sys.stdin.buffer.read() if path == "-" else Path(path).read_bytes()
        return raw.decode("utf-8-sig")
    except OSError as error:
        raise InputError(f"Can't read {path}: {error.strerror or error}") from None
    except UnicodeDecodeError:
        raise InputError(f"{path} isn't UTF-8 text") from None


def read_grammar(path):
    """Return the grammar as cfg-productions-v1 data, holding only what the
    engine reads, and each production's place: "file:line", or None."""
    text = read_text(path)
    try:
        if text.lstrip().startswith("{"):
            original = json.loads(text)
            data = analysis_runtime.custom_grammar({**original, "name": "check_grammar"})
            source = original.get("source") if isinstance(original.get("source"), dict) else {}
            file = source.get("file")
            places = [f"{file}:{rule['source_line']}" if file and isinstance(rule.get("source_line"), int) else None
                      for rule in original["productions"]]
        else:
            cfg = parse_grammar(text).cfg
            data = analysis_runtime.custom_grammar({
                "name": "check_grammar", "start": cfg.start, "terminals": list(cfg.terminals),
                "nonterminals": list(cfg.nonterminals),
                "productions": [{"lhs": lhs, "rhs": list(rhs)} for lhs, rhs in cfg.productions]})
            name = "stdin" if path == "-" else str(path)
            places = [f"{name}:{number}" for number in cfg.production_lines]
    except json.JSONDecodeError as error:
        raise InputError(f"Line {error.lineno}: {error.msg} (the text starts with {{, so it is read as JSON)") from None
    except (ValueError, TypeError) as error:
        raise InputError(str(error)) from None
    except RecursionError:
        raise InputError("The grammar is nested too deeply for the engine") from None
    return data, places


def read_accepted(path):
    """The site ids in an --accept file: a report from this command, or a
    JSON list of ids or of sites."""
    try:
        data = json.loads(read_text(path))
    except json.JSONDecodeError as error:
        raise InputError(f"{path} isn't JSON: {error.msg} at line {error.lineno} "
                         f"(an --accept file is a report made with --json, or a JSON list of site ids)") from None
    items = data.get("sites") if isinstance(data, dict) else data
    if not isinstance(items, list):
        raise InputError(f"{path} must hold a report from check_grammar.py or a list of site ids")
    ids = set()
    for item in items:
        site_id = item.get("id") if isinstance(item, dict) else item
        if not isinstance(site_id, str):
            raise InputError(f"{path} lists a site without a string id")
        ids.add(site_id)
    return ids


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


# ----- Computing the levels --------------------------------------------------

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


def claim(directory, seconds):
    """Mark a cache directory as this run's until it ends, unless another run
    that hasn't timed out holds it; return whether this run has it."""
    lock = directory / "check.lock"
    for _ in range(2):
        try:
            descriptor = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        except FileExistsError:
            try:
                until = json.loads(lock.read_text())["until"]
            except (OSError, ValueError, KeyError, TypeError):
                until = 0       # unreadable: left by a run that was killed
            if until > time.time():
                return False
            lock.unlink(missing_ok=True)
            continue
        with os.fdopen(descriptor, "w") as file:
            json.dump({"until": time.time() + seconds + 60}, file)
        return True
    return False


def compute(data, level, directory, seconds, memory_mb, used, say):
    """Bring the levels cached in `directory` up to `level` within the limits.
    Return the summaries of levels 0 to the last one done, and why the run
    stopped before `level`, or None."""
    started = time.monotonic()
    start = data["start"]
    levels = settled(analysis_runtime.prepare_directory(directory, data, build_grammar(data).grammar)[:level + 1], used)
    if len(levels) > 1:
        say(f"levels 1-{len(levels) - 1} from the cache")
    if len(levels) > level or saturated(levels, used):
        return levels, None

    def record_saved():
        while len(levels) <= level and analysis_runtime.level_file(directory, len(levels)).exists():
            levels.append(read_summary(analysis_runtime.level_file(directory, len(levels))))
            details = levels[-1]
            say(f"level {details['level']}: {details['counts'][start]} sentences of {start}, "
                f"{details['findings_count']} ambiguous site(s), {time.monotonic() - started:.1f} s")

    def on_event(event):
        if event.get("saved"):
            record_saved()

    process, error_path = analysis_runtime.start_worker(directory, len(levels), level)
    try:
        reason = analysis_runtime.follow_worker(
            process, analysis_runtime.memory_reader(), lambda: memory_mb * 1024 ** 2, deadline=started + seconds,
            on_event=on_event, cancelled=lambda: saturated(levels, used))
    finally:
        analysis_runtime.end_worker(process, directory)
    # Levels saved just before the worker exited may not have been read yet.
    record_saved()
    levels = settled(levels, used)
    if len(levels) > level or saturated(levels, used):
        return levels, None
    failed = len(levels)
    if reason == "memory":
        return levels, {"reason": "memory", "level": failed, "limit_mb": memory_mb,
                        "message": f"Level {failed} stopped at the {memory_mb} MiB memory limit."}
    if reason in ("deadline", "level time"):
        limit = seconds if reason == "deadline" else analysis_runtime.LEVEL_SECONDS
        return levels, {"reason": "time", "level": failed, "limit_seconds": limit,
                        "message": f"Level {failed} stopped at the {limit:g}-second time limit."}
    if reason == "monitor":
        return levels, {"reason": "monitor", "level": failed,
                        "message": f"Level {failed} stopped because the worker's memory couldn't be read."}
    error = error_path.read_text(errors="replace").strip()[-1500:]
    return levels, {"reason": "error", "level": failed,
                    "message": f"Level {failed} failed: {error or 'the worker exited without saving it'}"}


# ----- The report ------------------------------------------------------------

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
            return finding, serialize_finding(finding, catalog)["derivations"]
        except (ProofLimitExceeded, ValueError):
            continue        # the witness isn't derived both ways this early, or it takes too much work to tell
    finding = finding_from_record(record, catalog)
    return finding, serialize_finding(finding, catalog)["derivations"]


def build_report(path, data, places, level, levels, stopped, directory, accepted, max_findings, trees, timings):
    catalog = build_grammar(data)
    position = {rule["id"]: index for index, rule in enumerate(catalog.rules)}
    texts = [_rule_text(rule) for rule in catalog.rules]
    # A rule's key is its text and which copy of that text it is.
    copies = {}
    rule_keys = []
    for text in texts:
        copies[text] = copies.get(text, 0) + 1
        rule_keys.append([text, copies[text]])
    reached, used, unproductive = analyse(data)

    sites = {}      # key -> {"first_level", and the record from the last level}
    for number in range(1, len(levels)):
        for record in read_findings(analysis_runtime.level_file(directory, number)):
            rules = [position[rule_id] for rule_id in record["candidate_production_ids"]]
            key = json.dumps([record["kind"], record["owner"], [rule_keys[rule] for rule in rules],
                              record["expression"] if record["kind"] == "concatenation" else None])
            sites.setdefault(key, {"first_level": number, "rules": rules})["record"] = record

    entries = []
    for key, site in sites.items():
        record = site["record"]
        site_id = hashlib.sha256(key.encode()).hexdigest()[:12]
        entry = {"id": site_id, "kind": record["kind"], "nonterminal": record["owner"],
                 "first_level": site["first_level"], "reachable": record["owner"] in reached,
                 "accepted": site_id in accepted,
                 "rules": [{"text": texts[rule], **({"source": places[rule]} if places[rule] else {})}
                           for rule in site["rules"]],
                 "witness": record["witness"]}
        if record["kind"] == "concatenation":
            entry["expression"] = record["expression"]
            entry["cuts"] = sorted(len(left) for left, _ in record["raw_factorizations"])
        entries.append(((site["first_level"], min(site["rules"]), record["kind"], key), entry, record))
    entries.sort(key=lambda item: item[0])
    shown = entries[:max_findings] if max_findings else entries

    def parse_tree(node):
        """A proof's derivation as parse-tree items: an object for each
        nonterminal, a string for each terminal."""
        if node["kind"] == "terminal":
            return [node["symbol"]]
        children = [item for child in node["children"] for item in parse_tree(child)]
        if node["kind"] in ("nonterminal", "production"):
            return [{"symbol": node["symbol"], "rule": texts[position[node["production_id"]]], "children": children}]
        return children     # ε, or a step inside one rule

    if trees:
        for _, entry, record in shown:
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

    counted = [entry for _, entry, _ in entries if entry["reachable"] and not entry["accepted"]]
    final = saturated(levels, used)
    if any(entry["reachable"] for _, entry, _ in entries):
        verdict = "ambiguous"
    else:
        verdict = "unambiguous" if final else "none_found"
    if counted:
        code = AMBIGUOUS
    elif stopped and verdict != "unambiguous":
        code = FAILED if stopped["reason"] == "error" else LIMITED
    else:
        code = NONE_FOUND

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
    if len(shown) < len(entries):
        warnings.append(f"Showing {len(shown)} of {len(entries)} sites; raise --max-findings to see more (0 shows all).")
    missing = accepted - {entry["id"] for _, entry, _ in entries}
    if missing:
        warnings.append(f"{len(missing)} accepted site(s) weren't found through level {reached_level}.")

    report = {
        "format": FORMAT,
        "exit_code": code,
        "grammar": {"file": path, "start": start, "rules": len(data["productions"]),
                    "nonterminals": len(data["nonterminals"]), "terminals": data["terminals"]},
        "requested_level": level,
        "level_reached": reached_level,
        "start_sentences": levels[-1]["counts"][start],
        "verdict": verdict,
        "proves_unambiguous": verdict == "unambiguous",
        "stopped": stopped,
        "scope": SCOPE,
        "site_count": len(entries),
        "sites": [entry for _, entry, _ in shown],
        "warnings": warnings,
    }
    if timings:
        report["timings"] = [{"level": details["level"], "seconds": round(details["seconds"], 3),
                              "memory_mb": round(details["memory_bytes"] / 1024 ** 2, 1)}
                             for details in levels[1:]]
    return report


# ----- The report as text ----------------------------------------------------

EMPTY = "(empty)"       # the empty string: as a sentence, as a right side and as a leaf
TEXT_WIDTH = 79         # a site's two parse trees are drawn side by side when they fit in this


def _plural(number, singular, plural=None):
    return f"{number:,} {singular if number == 1 else plural or singular + 's'}"


def _amount(digits):
    """A count given in decimal: in full up to 15 digits, then to three figures."""
    return f"{int(digits):,}" if len(digits) <= 15 else f"about {digits[0]}.{digits[1:3]} x 10^{len(digits) - 1}"


def _sentence(tokens):
    return " ".join(tokens) if tokens else EMPTY


def _shown_rule(text):
    # The text report's own words are ASCII, so that a pipe in any code page carries them.
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
    file = ("stdin" if grammar["file"] == "-" else grammar["file"]) + ":"
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
    if site["accepted"]:
        lines.append("   Accepted: it is listed in the --accept file.")
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
        reason = site.get("trees_error", "The report was made without them.")
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
    name = "standard input" if grammar["file"] == "-" else grammar["file"]
    start, level, asked = grammar["start"], report["level_reached"], report["requested_level"]
    count, verdict, stopped = report["site_count"], report["verdict"], report["stopped"]
    found = _plural(count, "ambiguity", "ambiguities")

    if verdict == "ambiguous":
        lines = [f"AMBIGUOUS: {found} found in {name}"]
        if report["exit_code"] != AMBIGUOUS:
            lines.append(f"Each one that {start} reaches is in the --accept file, so none counts toward the exit status.")
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
              f"{_plural(len(grammar['terminals']), 'terminal')}, start symbol {start}"]
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
    if "timings" in report:
        lines += ["", "Level   Seconds   Memory (MiB)"]
        lines += [f"{timing['level']:5}   {timing['seconds']:7.3f}   {timing['memory_mb']:12.1f}"
                  for timing in report["timings"]]
    return "\n".join(lines) + "\n"


# ----- The command -----------------------------------------------------------

def write(text):
    """Send text to standard output, with any character its encoding can't
    carry escaped (a pipe on Windows is in the system's code page)."""
    encoding = getattr(sys.stdout, "encoding", None) or "utf-8"
    try:
        text.encode(encoding)
    except UnicodeEncodeError:
        text = text.encode(encoding, "backslashreplace").decode(encoding)
    try:
        sys.stdout.write(text)
        sys.stdout.flush()
    except OSError:
        # The reader closed the pipe early, as head does; Windows reports
        # that as EINVAL rather than EPIPE. Keep the exit status regardless.
        os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())


def emit(value):
    # ASCII only, so that a pipe in any code page carries it; indented for a
    # person at a terminal, compact for a program reading a pipe.
    if sys.stdout.isatty():
        write(json.dumps(value, indent=2, ensure_ascii=True) + "\n")
    else:
        write(json.dumps(value, ensure_ascii=True, separators=(",", ":")) + "\n")


def fail(message, code, as_json):
    if not as_json:
        print(f"check_grammar: {message}", file=sys.stderr, flush=True)
        return code
    error = {"message": message}
    line = re.match(r"Line (\d+): ", message)
    if line:
        error["line"] = int(line.group(1))
    emit({"format": FORMAT, "exit_code": code, "error": error})
    return code


def check_output_path(path, protected):
    """Keep a report from replacing its grammar or acceptance input."""
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
        if value < minimum:
            raise argparse.ArgumentTypeError(f"must be at least {minimum}")
        return value
    return read


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="check_grammar.py", epilog=EPILOG, formatter_class=argparse.RawDescriptionHelpFormatter,
        description="Check a context-free grammar for ambiguity and write a report with parse trees.")
    parser.add_argument("grammar", nargs="?",
                        help="BNF text (E ::= E + E | id, with optional <name> nonterminals) "
                             "or cfg-productions-v1 JSON; - reads standard input")
    parser.add_argument("--level", type=_count(1), default=DEFAULT_LEVEL,
                        help=f"check parse trees up to this height (default {DEFAULT_LEVEL})")
    parser.add_argument("--max-seconds", type=_count(0.001, float), default=DEFAULT_SECONDS,
                        help=f"stop computing after this long, keeping the levels done (default {DEFAULT_SECONDS})")
    parser.add_argument("--max-memory-mb", type=_count(64), default=DEFAULT_MEMORY_MB,
                        help=f"stop the worker at this much memory (default {DEFAULT_MEMORY_MB})")
    parser.add_argument("--max-findings", type=_count(0), default=DEFAULT_FINDINGS,
                        help=f"list at most this many sites; 0 lists all (default {DEFAULT_FINDINGS})")
    parser.add_argument("--json", action="store_true",
                        help="write the report as one JSON object instead of text (default: standard output)")
    parser.add_argument("-o", "--output", metavar="PATH",
                        help="report destination; - writes to standard output (default: <stem>.ambiguity.txt "
                             "beside the grammar, or standard output for --json or standard input)")
    parser.add_argument("--trees", action="store_true",
                        help="with --json, add two parse trees of each listed site's witness "
                             "(the text report always draws them)")
    parser.add_argument("--accept", metavar="FILE",
                        help="sites that don't count toward exit status 1: an earlier report (made with "
                             "--json --max-findings 0) or a JSON list of site ids")
    parser.add_argument("--timings", action="store_true", help="add each level's time and memory")
    parser.add_argument("--cache", type=Path, default=analysis_runtime.ROOT / ".ambiguity_cache",
                        help="where computed levels are kept (default: .ambiguity_cache beside this file)")
    parser.add_argument("--quiet", action="store_true", help="print no progress on standard error")
    parser.add_argument("--schema", action="store_true", help="print the JSON Schema of the --json report and exit")
    args = parser.parse_args(argv)
    if args.schema:
        if args.output not in (None, "-"):
            parser.error("--schema writes to standard output; omit --output or use --output -")
        emit(SCHEMA)
        return NONE_FOUND
    if args.grammar is None:
        parser.error("name a grammar file, or - for standard input")
    say = (lambda message: None) if args.quiet else (
        lambda message: print(f"check_grammar: {message}", file=sys.stderr, flush=True))
    output = None
    protected = [Path(path) for path in (args.grammar, args.accept) if path not in (None, "-")]
    try:
        if args.output not in (None, "-"):
            output = Path(args.output)
        elif args.output is None and not args.json and args.grammar != "-":
            output = Path(args.grammar).with_suffix(".ambiguity.txt")
        if output is not None:
            check_output_path(output, protected)
    except (OSError, ValueError) as error:
        return fail(f"Can't choose report output: {error}", FAILED, False)

    try:
        data, places = read_grammar(args.grammar)
        accepted = read_accepted(args.accept) if args.accept else set()
    except InputError as error:
        return fail(str(error), UNREADABLE, args.json and output is None)
    _, used, _ = analyse(data)

    lock = temporary = None
    try:
        args.cache.mkdir(parents=True, exist_ok=True)
        analysis_runtime.prune_stale(args.cache, "check")
        directory = args.cache / analysis_runtime.cache_key("check", data)
        directory.mkdir(exist_ok=True)
        if claim(directory, args.max_seconds):
            lock = directory / "check.lock"
        else:
            say("another run is using this grammar's cache, so this one works in a temporary folder")
            temporary = tempfile.TemporaryDirectory(prefix="check-")
            directory = Path(temporary.name)
        levels, stopped = compute(data, args.level, directory, args.max_seconds, args.max_memory_mb, used, say)
        report = build_report(args.grammar, data, places, args.level, levels, stopped, directory,
                              accepted, args.max_findings, args.trees or not args.json, args.timings)
    except (OSError, RuntimeError) as error:
        return fail(f"The run failed: {error}", FAILED, args.json and output is None)
    finally:
        if lock is not None:
            lock.unlink(missing_ok=True)
        if temporary is not None:
            temporary.cleanup()
    if output is not None:
        try:
            text = (json.dumps(report, indent=2, ensure_ascii=False) + "\n"
                    if args.json else render_text(report))
            save_report(output, text, protected)
        except (OSError, ValueError) as error:
            return fail(f"Can't write report to {output}: {error}", FAILED, False)
        say(f"report saved to {output}")
    elif args.json:
        emit(report)
    else:
        write(render_text(report))
    return report["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
