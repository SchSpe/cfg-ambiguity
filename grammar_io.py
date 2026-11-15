"""Validate grammar data in the cfg-productions-v1 format."""


def validate_grammar(grammar):
    """Check grammar data in the cfg-productions-v1 format and return it."""
    if not isinstance(grammar, dict):
        raise ValueError("Grammar data must be an object")
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
        if not isinstance(rule, dict):
            raise ValueError("Each production must be an object with lhs and rhs")
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
