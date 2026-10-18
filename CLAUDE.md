# Altman ambiguity project

Class project for Tom Altman's automata course (due December 2026): implement
the algebraic ambiguity detector from Altman and Logothetis, then produce less
ambiguous, language-preserving grammars.

## Working

- When a piece of work is finished and tests pass, commit and push to
  `origin`. Ask before force-pushing or rewriting history.
- Python 3.11+ standard library only; no venv needed. Tests:
  `python3 -m unittest discover -s . -p "test_*.py"` (about 3 s; pytest is
  not used). The UI needs Graphviz `dot`; `matplotlib` only for plots.
- This repo is meant to be public. Never commit papers (PDFs), `cfront/` or other
  third-party material; `.gitignore` covers them. The Cfront tests skip
  when `cfront/gram.y` is absent (see `README.md`).

## Layout

`grammar_engine.py` (detector), `run_ui.py` (browser UI, see
`UI_README.txt`), `report/report.tex` (the report), `test_*.py`.
