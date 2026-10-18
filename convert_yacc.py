"""Extract the syntactic productions of the two bundled historical grammars.

Run this file to regenerate grammar.json and grammar.cfg beside each original.
Original Yacc files are never modified. This is a deliberately restricted Yacc
reader: unsupported syntax fails instead of silently dropping grammar symbols.
Actions are recorded by position but not executed; precedence is metadata only.
"""

import ast
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re

from grammar_io import load_grammar


@dataclass(frozen=True)
class Token:
    kind: str
    value: str
    line: int
    begin: int
    end: int


def _quote_end(text, pos):
    quote = text[pos]
    i = pos + 1
    while i < len(text):
        if text[i] == "\\":
            i += 2
        elif text[i] == quote:
            return i + 1
        else:
            i += 1
    raise ValueError(f"Unterminated quoted string at offset {pos}")


def _comment_end(text, pos):
    if text.startswith("//", pos):
        end = text.find("\n", pos + 2)
        return len(text) if end < 0 else end
    end = text.find("*/", pos + 2)
    if end < 0:
        raise ValueError(f"Unterminated comment at offset {pos}")
    return end + 2


def _code_end(text, pos, prologue=False):
    """Skip C/C++ code, respecting nested braces, quotes, and comments."""
    i = pos + (2 if prologue else 1)
    depth = 1
    while i < len(text):
        if text.startswith(("/*", "//"), i):
            i = _comment_end(text, i)
        elif text[i] in "\"'":
            i = _quote_end(text, i)
        elif prologue and text.startswith("%}", i):
            return i + 2
        elif not prologue and text[i] == "{":
            depth += 1
            i += 1
        elif not prologue and text[i] == "}":
            depth -= 1
            i += 1
            if depth == 0:
                return i
        else:
            i += 1
    raise ValueError(f"Unterminated code block at offset {pos}")


def tokenize(text):
    result = []
    i = 0
    line = 1
    sections = 0
    while i < len(text):
        begin, begin_line = i, line
        kind = None
        if text[i].isspace():
            i += 1
        elif text.startswith(("/*", "//"), i):
            i = _comment_end(text, i)
        elif text.startswith("%{", i):
            i = _code_end(text, i, prologue=True)
        elif text.startswith("%%", i):
            kind = "section"
            i += 2
            sections += 1
        elif text[i] == "{":
            kind = "action"
            i = _code_end(text, i)
        elif text[i] in "\"'":
            kind = "literal"
            i = _quote_end(text, i)
        elif match := re.match(r"%[a-zA-Z_][a-zA-Z_0-9-]*", text[i:]):
            kind = "directive"
            i += len(match[0])
        elif match := re.match(r"[a-zA-Z_$][a-zA-Z_0-9.$]*", text[i:]):
            kind = "symbol"
            i += len(match[0])
        elif match := re.match(r"[0-9]+", text[i:]):
            kind = "number"
            i += len(match[0])
        elif text[i] in ":|;<>":
            kind = text[i]
            i += 1
        else:
            raise ValueError(f"Unsupported character {text[i]!r} on line {line}")
        if kind:
            result.append(Token(kind, text[begin:i], begin_line, begin, i))
        line += text[begin:i].count("\n")
        if sections == 2:
            break  # The trailing C/C++ program is not grammar input.
    if sections != 2:
        raise ValueError("Expected two Yacc %% section delimiters")
    return result


def _symbol(token):
    if token.kind == "symbol":
        return token.value
    if token.kind == "literal":
        value = ast.literal_eval(token.value)
        if not isinstance(value, str) or len(value) != 1:
            raise ValueError("Only single-character Yacc literals are supported")
        return value
    raise ValueError(f"Expected a symbol on line {token.line}")


def parse_yacc(text):
    tokens = tokenize(text)
    split = next(i for i, token in enumerate(tokens) if token.kind == "section")
    header, body = tokens[:split], tokens[split + 1:-1]
    declared, numbers, precedence = [], {}, []
    start = None
    i = 0
    while i < len(header):
        directive = header[i]
        if directive.kind != "directive":
            raise ValueError(f"Expected declaration on line {directive.line}")
        i += 1
        end = i
        while end < len(header) and header[end].kind != "directive":
            end += 1
        args = header[i:end]
        i = end
        if directive.value == "%start":
            if len(args) != 1 or args[0].kind != "symbol":
                raise ValueError("Invalid %start")
            start = args[0].value
        elif directive.value in ("%token", "%left", "%right", "%nonassoc"):
            symbols = []
            j = 0
            if args and args[0].kind == "<":
                if len(args) < 3 or args[1].kind != "symbol" or args[2].kind != ">":
                    raise ValueError("Invalid token type tag")
                j = 3
            while j < len(args):
                symbol = _symbol(args[j])
                symbols.append(symbol)
                if symbol not in declared:
                    declared.append(symbol)
                j += 1
                if j < len(args) and args[j].kind == "number":
                    numbers[symbol] = int(args[j].value)
                    j += 1
            if directive.value != "%token":
                precedence.append({"associativity": directive.value[1:], "symbols": symbols})
        elif directive.value not in ("%type", "%union"):
            raise ValueError(f"Unsupported declaration {directive.value}")

    rules = []
    i = 0
    while i < len(body):
        if body[i].kind != "symbol" or i + 1 >= len(body) or body[i + 1].kind != ":":
            raise ValueError(f"Expected a rule on line {body[i].line}")
        lhs = body[i].value
        rule_line = body[i].line
        i += 2
        while True:
            rhs, actions = [], []
            override = None
            line = body[i].line if i < len(body) else rule_line
            while i < len(body):
                token = body[i]
                # Traditional Yacc permits an omitted semicolon before a new LHS.
                if token.kind in ("|", ";") or (
                    token.kind == "symbol" and i + 1 < len(body) and body[i + 1].kind == ":"
                ):
                    break
                if token.kind == "action":
                    actions.append({"after_symbols": len(rhs), "source_line": token.line,
                                    "source_end_line": token.line + token.value.count("\n")})
                elif token.kind == "directive" and token.value == "%prec":
                    if override is not None or i + 1 >= len(body):
                        raise ValueError(f"Invalid %prec on line {token.line}")
                    i += 1
                    override = _symbol(body[i])
                elif token.kind in ("symbol", "literal"):
                    rhs.append(_symbol(token))
                else:
                    raise ValueError(f"Unexpected {token.value!r} on line {token.line}")
                i += 1
            rule = {"lhs": lhs, "rhs": rhs, "source_line": line}
            if override is not None:
                rule["yacc_precedence"] = override
            if actions:
                rule["omitted_actions"] = actions
            rules.append(rule)
            if i < len(body) and body[i].kind == "|":
                i += 1
                continue
            if i < len(body) and body[i].kind == ";":
                i += 1
            break

    nonterminals = list(dict.fromkeys(rule["lhs"] for rule in rules))
    if set(nonterminals) & set(declared):
        raise ValueError("Terminal/nonterminal name collision")
    terminals = list(dict.fromkeys(s for r in rules for s in r["rhs"] if s not in nonterminals))
    literal_symbols = {_symbol(t) for t in body if t.kind == "literal"}
    unknown = set(terminals) - set(declared) - literal_symbols - {"error"}
    if unknown:
        raise ValueError(f"Undeclared symbols: {sorted(unknown)}")
    for rule in rules:
        if "yacc_precedence" in rule and rule["yacc_precedence"] not in declared:
            raise ValueError("Undeclared precedence symbol")
    return {
        "format": "cfg-productions-v1",
        "start": start or nonterminals[0],
        "terminals": terminals,
        "nonterminals": nonterminals,
        "productions": rules,
        "yacc": {
            "declared_tokens": declared,
            "token_numbers": numbers,
            "precedence_low_to_high": precedence,
            "explicit_eof_tokens": [s for s, n in numbers.items() if n == 0],
            "error_token_used": "error" in terminals,
        },
    }


def render_cfg(data):
    """A human-readable view of exactly the same ordered production list."""
    lines = ["# " + data["name"], "# " + data["translation_notice"],
             "# Source: " + data["source"]["file"],
             "# Quoted symbols are terminals; unquoted symbols are nonterminals.",
             "# epsilon means the empty string. Repeated LHS lines are alternatives.",
             "# Compiler actions and precedence are not applied; see grammar.json."]
    lines.extend(data["source_notices"])
    lines.extend(["", "%start " + data["start"], ""])
    terminals = set(data["terminals"])
    for rule in data["productions"]:
        rhs = " ".join(json.dumps(s, ensure_ascii=False) if s in terminals else s
                       for s in rule["rhs"]) or "epsilon"
        lines.append(f"{rule['lhs']} ::= {rhs}")
    return "\n".join(lines) + "\n"


def convert(source, name, url):
    raw = source.read_bytes()
    text = raw.decode("utf-8")
    data = parse_yacc(text)
    if source.name == "cpp5.y":
        begin = text.index("/* Copyright")
        end = text.index("*/", begin) + 2
        notices = [text[begin:end], "Portions Copyright (c) 1989, 1990 James A. Roskind"]
        notes = [
            "Start translation_unit describes a complete translation unit, including an empty one.",
            "IDENTIFIER and TYPEDEFname remain distinct preclassified tokens; no lexer or symbol table is implemented here.",
            "This historical grammar omits templates and exception handling.",
        ]
    else:
        begin = text.index("/*******************************************************************************")
        notices = [text[begin:text.index("*/", begin) + 2]]
        notes = [
            "Start ext_def describes one external definition, not an entire C++ source file.",
            "EOFTOK is the original explicit end-of-input token (code 0); it is retained, not replaced by epsilon.",
            "The error recovery symbol error is retained as a distinguished terminal, not ordinary source text.",
            "Actions that change lexer state, scope, lookahead, or control flow are not executed.",
            "Precedence and associativity are retained only as metadata; all syntactic alternatives remain.",
            "The source archive makes this code available for historical research purposes only.",
        ]
    metadata = {
        "name": name,
        "translation_notice": "Translation of the original Yacc syntactic productions; not the executable compiler's full behavior.",
        "source": {"file": source.name, "url": url, "sha256": hashlib.sha256(raw).hexdigest()},
        "source_notices": notices,
        "notes": notes,
    }
    data = {**metadata, **data}
    json_path = source.with_name("grammar.json")
    json_path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    source.with_name("grammar.cfg").write_text(render_cfg(data), encoding="utf-8")
    loaded = load_grammar(json_path)
    assert loaded == data
    assert source.read_bytes() == raw
    duplicates = sum(n - 1 for n in Counter((r["lhs"], tuple(r["rhs"])) for r in data["productions"]).values())
    print(f"{name}: {len(data['productions'])} rules, {len(data['nonterminals'])} nonterminals, "
          f"{len(data['terminals'])} used terminals, {duplicates} duplicate alternatives retained")


if __name__ == "__main__":
    root = Path(__file__).resolve().parent
    if (root / "cfront/gram.y").exists():
        convert(root / "cfront/gram.y", "Cfront 3.0.3",
                "https://softwarepreservation.computerhistory.org/c_plus_plus/cfront/release_3.0.3/source/src/gram.y")
    else:
        print("Cfront 3.0.3: cfront/gram.y not found, skipped (see README.md)")
    convert(root / "roskind/cpp5.y", "Roskind grammar release 2.0",
            "https://blog.robertelder.org/jim-roskind-grammar/c%2B%2Bgrammar2.0.tar.Z")
