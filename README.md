# CFG ambiguity checker

Read a BNF text file and save an ambiguity report with the rules involved,
witness sentences, and two parse trees for each reported ambiguity.

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
the verdict, search depth, source line numbers, witness sentences, and two
drawn parse trees for each listed ambiguity. It also explains any limit that
stopped the search or prevented a tree from being reconstructed.

Choose a different report filename or search depth:

```sh
python check_grammar.py grammar.txt --output report.txt --level 8
```

Reports are UTF-8 text. Running again replaces the previous report. The command
refuses to overwrite the input grammar or an acceptance file.

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

The earlier bare-symbol format still works, for example `E ::= E + E` and
`E ::= n`. In that format, symbols on a left-hand side are nonterminals and
other symbols are terminals.

Use `--output -` to print the report instead of saving it. The command also
accepts `cfg-productions-v1` JSON and `-` as the input filename for standard
input. Standard-input and JSON reports go to standard output unless you give
an output filename. To save a JSON report with parse trees:

```sh
python check_grammar.py grammar.txt --json --trees --output report.json
```

Use `--help` for all options or `--schema` for the JSON report schema.

## Limits and results

The default search level is 6, with a 90-second computation limit and a 2048 MiB
worker memory limit. Change these with `--level`, `--max-seconds`, and
`--max-memory-mb`.

Completed levels are cached in `.ambiguity_cache/` beside the program. A later
run at a higher level resumes from the cache. Use `--cache PATH` to choose a
different location. The cache can be deleted and regenerated.

A witness proves ambiguity. Finding no witness covers only the levels checked;
the grammar is proved unambiguous only when the relevant languages stop growing.
The JSON report distinguishes `ambiguous`, `none_found`, and `unambiguous`.

| Exit status | Meaning |
| --- | --- |
| 0 | No new ambiguity found, or proved unambiguous |
| 1 | An ambiguity reachable from the start symbol is not in the acceptance file |
| 2 | Invalid input or command line |
| 3 | A limit stopped the search |
| 4 | The run failed |

Save a baseline before editing the grammar, then compare the edited grammar
against it to flag only new ambiguities:

```sh
python check_grammar.py grammar.txt --json --max-findings 0 > accepted.json
# Edit grammar.txt, then:
python check_grammar.py grammar.txt --json --accept accepted.json
```

Acceptance changes the exit status, not the reported verdict. Progress goes to
standard error; `--quiet` suppresses it.

## License

MIT; see [LICENSE](LICENSE).
