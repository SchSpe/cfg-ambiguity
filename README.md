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

## Limits and results

The default search level is 6, with a 90-second computation limit and a 2048 MiB
worker memory limit. Change these with `--level`, `--max-seconds`, and
`--max-memory-mb`.

Each run analyzes the input afresh. If a limit stops the search, the report
includes the completed levels and findings. Temporary computation files are
removed when the run ends.

A witness proves ambiguity. Finding no witness covers only the levels checked;
the grammar is proved unambiguous only when the relevant languages stop growing.
The report states whether ambiguity was found, the grammar was proved
unambiguous, or only the requested depth was checked.

| Exit status | Meaning |
| --- | --- |
| 0 | No ambiguity found through the checked depth, or proved unambiguous |
| 1 | An ambiguity reachable from the start symbol was found |
| 2 | Invalid input or command line |
| 3 | A limit stopped the search |
| 4 | The run failed |

Parse trees are always included when reconstruction succeeds. All ambiguity
sites found within the checked depth are reported. Use `--help` for the
available options.

## License

MIT; see [LICENSE](LICENSE).
