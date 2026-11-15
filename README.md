# CFG ambiguity checker

Read a BNF text file and save an ambiguity report with the rules involved,
witness sentences, two parse trees per witness, and recognized ambiguity-causing
constructs.

Requires Python 3.11 or later. It uses only the standard library.

## Run

Save your BNF grammar as `grammar.txt`:

```text
<expr> ::= <expr> "+" <expr>
         | "n"
```

```sh
python check_grammar.py grammar.txt
```

This writes `grammar.ambiguity.txt` beside the input file. The report includes
the verdict, search depth, source line numbers, witness sentences, two drawn
parse trees for each witness, and certain ambiguity-causing constructs (CACCs).

Choose a different report filename or search depth:

```sh
python check_grammar.py grammar.txt --output report.txt --level 8
```

Reports are UTF-8 text. Running again replaces the previous report. The command
refuses to overwrite the input grammar.

## BNF input

Use `::=` for a production and `|` between alternatives. An alternative can
continue on the next line if it starts with `|`. Repeating the left-hand side
also works. The first left-hand side is the start symbol.

Use `<name>` for a nonterminal and single or double quotes for literal terminals.
An undefined `<name>` is an error. Quotes remain in terminal labels in the
report, and a quoted string is one token even if it contains spaces or `|`.
An empty alternative or unquoted `ε` means the empty string. Comments start
with `#` or `//` outside quotes. EBNF repetition and optional-group notation
are not supported; write them as BNF productions instead.

Bare-symbol rules also work, for example `E ::= E + E` and
`E ::= n`. In that format, symbols on a left-hand side are nonterminals and
other symbols are terminals.

## Search depth and results

The engine runs directly, checking parse trees up to height 6 by default.
Use `--level` to change the depth. Each run analyzes the input afresh and
writes the report when it finishes. Press Ctrl+C to cancel a run.

A witness or a reachable CACC proves ambiguity. Finding no witness covers only
the levels checked; the grammar is proved unambiguous only when the relevant
languages stop growing.
The report states whether ambiguity was found, the grammar was proved
unambiguous, or only the requested depth was checked.

| Exit status | Meaning |
| --- | --- |
| 0 | No ambiguity found through the checked depth, or proved unambiguous |
| 1 | An ambiguity reachable from the start symbol was found |
| 2 | Invalid input or command line |
| 4 | The run failed |
| 130 | The run was cancelled |

Each witness includes two verified parse trees. All ambiguity sites found
within the checked depth are reported. A CACC can establish ambiguity before
the witness search reaches it; the report then suggests increasing `--level`
to find parse trees. Use `--help` for the available options.

## CACC recognition and rewrites

`grammar_caccs.py` recognizes seven constructs: mixed recursion, self-embedding,
duplicate alternatives, repeated optional expressions, transparent cycles,
subsumed alternatives, and dangling suffixes. The report lists each match with
its nonterminal, source lines, and an explanation. These structural checks are
independent of `--level`; a construct in an unreachable definition does not
change the verdict.

Rewrites are explicit Python calls using the same `CFG` returned by
`grammar_engine.parse_grammar(text)`:

- `recognize_caccs(cfg)` returns the matches.
- `apply_cacc(cfg, match)` applies one supported rewrite to a copy.
- `transform_caccs(cfg, max_steps=100)` applies supported rewrites repeatedly.

Matches identify rules by zero-based `production_indices`. For matches within
a rule, `rhs_spans` contains `(production_index, start, end)` with an exclusive
end position. Both refer directly to `cfg.productions`.

The rewrite result contains `grammar`, `changes`, `remaining`, `limit_reached`,
and `stalled`. A recognized construct can remain when its rewrite's conditions
are not met. Inspect the result before using the rewritten grammar; removing
these patterns does not establish unambiguity. Changed and generated rules have
source line 0; unchanged rules retain their input line numbers.

## License

MIT; see [LICENSE](LICENSE).
