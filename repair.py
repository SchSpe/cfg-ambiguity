"""Match and rewrite literal BNF templates using regular expressions.

These syntactic matches do not establish ambiguity. Indirect derivations,
nullable chains, and general recursive contexts are deliberately not analyzed.
"""

import re

from parse import CFG, parse_grammar


NSF_REPAIR_IDS = frozenset({"mixed_recursion", "self_embedding", "duplicate_union", "optional_square"})


_REASONS = {
    "duplicate_union": "The same alternative is written more than once.",
    "transparent_cycle": "A direct self-rule appears beside another alternative.",
    "mixed_recursion": "The three alternatives have the literal forms beta A, A gamma, and delta.",
    "self_embedding": "The two alternatives have the literal forms A beta A and gamma.",
    "optional_square": "A repeated symbol has an empty and one explicitly written alternative.",
    "subsumed_alternative": "A unit alternative directly expands to another written alternative.",
    "dangling_suffix": "Three alternatives match a canonical dangling-suffix template.",
}


def _line(owner, rhs):
    return owner + " ::= " + rhs


def _lines(cfg):
    return [_line(owner, " ".join(rhs)) for owner, rhs in cfg.productions]


def _fresh(cfg, owner):
    base = "T" if owner == "E" else owner[:-1] + "_cacc>" if owner.startswith("<") else owner + "_cacc"
    used = set(cfg.nonterminals) | set(cfg.terminals)
    name, number = base, 1
    while name in used:
        name = f"{base[:-1]}_{number}>" if base.startswith("<") else f"{base}_{number}"
        number += 1
    return name


def recognize_caccs(cfg):
    """Return literal matches with rule indices and private replacement recipes."""
    bodies = [" ".join(rhs) for _, rhs in cfg.productions]
    rules = {owner: [] for owner in cfg.nonterminals}
    for index, (owner, _) in enumerate(cfg.productions):
        rules[owner].append(index)
    # Full escaped spellings keep quoted spaces and backslashes in one token.
    atom = "(?:" + "|".join(re.escape(token) for token in sorted(cfg.terminals, key=len, reverse=True)) + ")" if cfg.terminals else "(?!)"
    words = atom + "(?: " + atom + ")*"
    optional_words = "(?:" + words + ")?"
    token = "(?:" + "|".join(re.escape(symbol) for symbol in sorted((*cfg.terminals, *cfg.nonterminals), key=len, reverse=True)) + ")"
    sequence = token + "(?: " + token + ")*"
    optional_sequence = "(?:" + sequence + ")?"
    matches = []

    def add(kind, owner, indices, replacements, extra=()):
        matches.append({"rule_id": kind, "nonterminal": owner,
                        "production_indices": tuple(indices), "reason": _REASONS[kind],
                        "_replace": replacements, "_append": tuple(extra),
                        "_productions": cfg.productions})

    for owner, indices in rules.items():
        own = re.escape(owner)
        seen = {}
        for index in indices:
            body = bodies[index]
            if body in seen:
                add("duplicate_union", owner, (seen[body], index), {index: ()})
            else:
                seen[body] = index
            if re.fullmatch(own, body) and any(bodies[other] != owner for other in indices):
                add("transparent_cycle", owner, (index,), {index: ()})

        # One-step inlining only: A -> B | beta, B -> beta, and B != A.
        for source in indices:
            other = bodies[source]
            if other == owner or other not in rules:
                continue
            for expansion in rules[other]:
                beta = bodies[expansion]
                if not re.fullmatch(optional_words, beta):
                    continue
                target = next((i for i in indices if i != source and re.fullmatch(re.escape(beta), bodies[i])), None)
                if target is not None:
                    add("subsumed_alternative", owner, (source, target, expansion), {target: ()})

        for index in indices:
            for other, alternatives in rules.items():
                if other == owner or len(alternatives) != 2 or not re.fullmatch(re.escape(other) + " " + re.escape(other), bodies[index]):
                    continue
                empty = [i for i in alternatives if not bodies[i]]
                filled = [i for i in alternatives if re.fullmatch(sequence, bodies[i])]
                if empty and filled:
                    beta = bodies[filled[0]]
                    add("optional_square", owner, (index, *alternatives),
                        {index: tuple(_line(owner, body) for body in (beta + " " + beta, beta, ""))})

        if len(indices) == 2:
            for recursive in indices:
                pattern = own + "(?P<beta>(?: " + token + ")*) " + own
                if not re.fullmatch(pattern, bodies[recursive]):
                    continue
                base = next(i for i in indices if i != recursive)
                gamma = bodies[base]
                if re.fullmatch(optional_sequence, gamma):
                    body = re.sub(pattern, lambda match: (owner + match["beta"] + " " + gamma).strip(), bodies[recursive])
                    add("self_embedding", owner, (recursive, base), {recursive: (_line(owner, body),)})

        if len(indices) != 3:
            continue
        for prefix in indices:
            left = re.fullmatch("(?P<beta>" + sequence + ") " + own, bodies[prefix])
            if not left:
                continue
            for suffix in indices:
                if suffix == prefix:
                    continue
                right = re.fullmatch(own + " (?P<gamma>" + sequence + ")", bodies[suffix])
                base = next(i for i in indices if i not in (prefix, suffix))
                if right and re.fullmatch(optional_sequence, bodies[base]):
                    helper = _fresh(cfg, owner)
                    tail = re.sub(own + " (?P<gamma>" + sequence + ")", lambda match: helper + " " + match["gamma"], bodies[suffix])
                    add("mixed_recursion", owner, (prefix, suffix, base),
                        {suffix: (_line(owner, helper),), base: ()},
                        (_line(helper, tail), _line(helper, bodies[base])))

            # Only p A | p A q [A] | r, with distinct single terminals p,q,r.
            opened = re.fullmatch("(?P<p>" + atom + ") " + own, bodies[prefix])
            if not opened:
                continue
            for closed in indices:
                if closed == prefix:
                    continue
                pattern = re.escape(opened["p"]) + " " + own + " (?P<q>" + atom + ")(?P<tail> " + own + ")?"
                closing = re.fullmatch(pattern, bodies[closed])
                base = next(i for i in indices if i not in (prefix, closed))
                if not closing or not re.fullmatch(atom, bodies[base]):
                    continue
                p, q, r = opened["p"], closing["q"], bodies[base]
                if len({p, q, r}) != 3:
                    continue
                helper = _fresh(cfg, owner)
                changed = re.sub(pattern, lambda match: p + " " + helper + " " + match["q"] + (match["tail"] or ""), bodies[closed])
                matched = p + " " + helper + " " + q + (" " + helper if closing["tail"] else "")
                add("dangling_suffix", owner, (prefix, closed, base),
                    {closed: (_line(owner, changed),)},
                    (_line(helper, matched), _line(helper, r)))
    return matches


def apply_cacc(cfg, match):
    """Apply a returned match to a new CFG, preserving untouched source lines."""
    if match["_productions"] != cfg.productions:
        raise ValueError("The template match belongs to a different or edited grammar")
    rows = []
    for index, text in enumerate(_lines(cfg)):
        for replacement in match["_replace"].get(index, (text,)):
            rows.append((replacement, cfg.production_lines[index] if replacement == text else 0))
    rows.extend((text, 0) for text in match["_append"])
    # The first surviving production still needs to name the original start.
    start = cfg.start + " ::= "
    if not rows[0][0].startswith(start):
        first = next(i for i, (text, _) in enumerate(rows) if text.startswith(start))
        rows.insert(0, rows.pop(first))
    parsed = parse_grammar("\n".join(text for text, _ in rows))
    return CFG(parsed.productions, [rows[line - 1][1] for line in parsed.production_lines])


def repair_caccs(cfg, max_steps=100):
    """Apply only the four NSF templates before approximation."""
    return _transform(cfg, max_steps, NSF_REPAIR_IDS)


def transform_caccs(cfg, max_steps=100):
    """Explicitly apply any of the seven literal templates."""
    return _transform(cfg, max_steps, None)


def _transform(cfg, max_steps, allowed):
    if type(max_steps) is not int or max_steps < 0:
        raise ValueError("max_steps must be a nonnegative integer")
    result = CFG(cfg.productions, cfg.production_lines)
    changes, seen, stalled = [], {result.productions}, False
    while True:
        matches = recognize_caccs(result)
        eligible = [m for m in matches if allowed is None or m["rule_id"] in allowed]
        if not eligible or len(changes) == max_steps:
            break
        for match in eligible:
            candidate = apply_cacc(result, match)
            if candidate.productions not in seen:
                break
        else:
            stalled = True
            break
        result = candidate
        seen.add(result.productions)
        changes.append({"rule_id": match["rule_id"], "nonterminal": match["nonterminal"]})
    return {"grammar": result, "changes": changes, "remaining": matches,
            "limit_reached": bool(eligible) and len(changes) == max_steps, "stalled": stalled}
