"""Read the converted C++ grammars using only the Python standard library.

Example (from the implementation folder):
    grammar = load_grammar("roskind/grammar.json")
    for rule in grammar["productions"]:
        print(rule["lhs"], rule["rhs"])

RHS symbols are token names or nonterminal names; [] means epsilon.
Membership in grammar["nonterminals"] distinguishes the two kinds.
This reader loads grammar data; grammar_engine.py implements the ambiguity algorithm.
"""

import json
from pathlib import Path


def load_grammar(path):
    """Return validated grammar data, retaining source and Yacc metadata."""
    with Path(path).open(encoding="utf-8") as source:
        grammar = json.load(source)
    if grammar.get("format") != "cfg-productions-v1":
        raise ValueError("Unsupported grammar format")
    for key in ("terminals", "nonterminals"):
        names = grammar[key]
        if not isinstance(names, list) or not all(isinstance(s, str) for s in names):
            raise ValueError(f"{key} must be a list of symbol names")
        if len(names) != len(set(names)):
            raise ValueError(f"Duplicate names in {key}")
    terminals = set(grammar["terminals"])
    nonterminals = set(grammar["nonterminals"])
    if terminals & nonterminals:
        raise ValueError("Terminal and nonterminal names overlap")
    if grammar["start"] not in nonterminals:
        raise ValueError("Start symbol is not a nonterminal")
    if not isinstance(grammar["productions"], list) or not grammar["productions"]:
        raise ValueError("No productions")
    defined = set()
    for rule in grammar["productions"]:
        if rule["lhs"] not in nonterminals:
            raise ValueError(f"Unknown left-hand side: {rule['lhs']}")
        defined.add(rule["lhs"])
        rhs = rule["rhs"]
        if not isinstance(rhs, list) or not all(isinstance(s, str) for s in rhs):
            raise ValueError("Each RHS must be a list of symbol names")
        unknown = set(rhs) - terminals - nonterminals
        if unknown:
            raise ValueError(f"Undefined RHS symbols: {sorted(unknown)}")
    if defined != nonterminals:
        raise ValueError("Some nonterminals have no productions")
    return grammar


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path)
    args = parser.parse_args()
    data = load_grammar(args.path)
    print(f"{data['name']}: start={data['start']}; "
          f"{len(data['productions'])} productions; "
          f"{len(data['nonterminals'])} nonterminals; "
          f"{len(data['terminals'])} used terminals")
