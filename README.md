# Ambiguity detection for context-free grammars

Implementation of the algebraic ambiguity detector from Altman and Logothetis
[1, 2], with a browser UI for exploring approximation levels.

- `grammar_engine.py` — the detector
- `run_ui.py` — browser UI (see `UI_README.txt`)
- `report/report.tex` — project report
- `test_*.py` — tests (`python3 -m unittest discover -s . -p "test_*.py"`)

The UI and tests use the Roskind C++ grammar (in `roskind/`, see
`THIRD_PARTY_NOTICES`) and the expression grammar G1 from the NSF report [3].

## Optional: the Cfront grammar

The converter, tests and UI server can also use the grammar of AT&T Cfront
3.0.3. Its `gram.y` is AT&T proprietary source that the Computer History
Museum posts for historical research purposes only, so it is not included
here. Without it the Cfront tests are skipped. To add it locally, from this
folder:

```bash
mkdir -p cfront
curl -fL -o cfront/gram.y https://softwarepreservation.computerhistory.org/c_plus_plus/cfront/release_3.0.3/source/src/gram.y
echo "43183a06e283bdc56132e444191f73cd4d148f6179f8b6c33b9a769a6ef16acd  cfront/gram.y" | sha256sum -c -
python3 convert_yacc.py
```

On macOS use `shasum -a 256 -c -` in place of `sha256sum -c -`. In
PowerShell, compare `(Get-FileHash cfront\gram.y).Hash` with the checksum
above. If the checksum does not match, do not continue: the conversion and
tests expect exactly this file.

`convert_yacc.py` writes `cfront/grammar.json` and `cfront/grammar.cfg`, and
regenerates the Roskind files unchanged. `cfront/` is in `.gitignore`. After
this, `/api/catalog` lists Cfront and the Cfront tests in
`test_grammar_io.py` and `test_ui_server.py` run. `GRAMMAR_SOURCES.txt` and
`CONVERTED_GRAMMARS.txt` describe both grammars.

## References

1. T. Altman and G. Logothetis. A note on ambiguity in context-free grammars.
   *Information Processing Letters* 35(3):111–114, 1990.
2. T. Altman and G. Logothetis. An algebraic view of ambiguity in
   context-free grammars and language expressions. Preprint, 2011.
3. T. Altman. Final report on National Science Foundation grant
   CCR-9215731. Cited in the code as "the NSF report".

## License

MIT (see `LICENSE`). The Roskind grammar files keep their own terms; see
`THIRD_PARTY_NOTICES`.
