import argparse
from importlib.util import find_spec
import json
import math
import os
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

from grammar_io import load_grammar


ROOT = Path(__file__).resolve().parent
ROSKIND = ROOT / "roskind" / "grammar.json"


def select_roskind_rules(data, count):
    """Keep exactly count original rules with all referenced nonterminals defined."""
    rules = data["productions"]
    if not isinstance(count, int) or isinstance(count, bool) or not 1 <= count <= len(rules):
        raise ValueError(f"rules must be between 1 and {len(rules)}")

    names = set(data["nonterminals"])
    start = data["start"]
    first = next((index for index, rule in enumerate(rules)
                  if rule["lhs"] == start and not names.intersection(rule["rhs"])), None)
    if first is None:
        raise ValueError("The start symbol has no base production")

    base = [first]
    defined = {start}
    while len(defined) < len(names):
        for index, rule in enumerate(rules):
            if rule["lhs"] not in defined and names.intersection(rule["rhs"]) <= defined:
                base.append(index)
                defined.add(rule["lhs"])
                break
        else:
            raise ValueError("Cannot select one dependency-closed rule per nonterminal")

    selected = base[:count]
    if count > len(base):
        base_set = set(base)
        selected += [index for index in range(len(rules)) if index not in base_set][
            :count - len(base)
        ]
    indices = set(selected)
    productions = [rule for index, rule in enumerate(rules) if index in indices]
    selected_names = {rule["lhs"] for rule in productions}
    used_symbols = {symbol for rule in productions for symbol in rule["rhs"]}
    return {
        **data,
        "productions": productions,
        "nonterminals": [name for name in data["nonterminals"] if name in selected_names],
        "terminals": [name for name in data["terminals"] if name in used_symbols],
        "selection": {
            "kind": "production-deletion subgrammar",
            "policy": "start base rule; one dependency-ready rule per nonterminal; then source order",
            "source_production_numbers": [index + 1 for index in sorted(indices)],
        },
    }


def plot_approximation_size(records, rule_count, requested_levels, output):
    loaded = next((record for record in records if record.get("event") == "loaded"), None)
    finished = [record for record in records if record.get("event") == "level_complete"]
    exit_record = next((record for record in reversed(records)
                        if record.get("event") == "exit"), {})
    if loaded is None or "start" not in loaded:
        raise RuntimeError("The benchmark did not report the grammar start symbol")

    os.environ.setdefault("MPLCONFIGDIR", str(output.parent / ".matplotlib"))
    os.environ.setdefault("XDG_CACHE_HOME", str(output.parent / ".cache"))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import StrMethodFormatter

    levels = [0] + [record["level"] for record in finished]
    start_sizes = [0] + [record["start_sentences"] for record in finished]
    total_sizes = [0] + [record["summed_nonterminal_sentences"] for record in finished]
    completed = levels[-1]
    status = exit_record.get("reason", "unknown")
    scope = "Full grammar" if rule_count == 642 else "Production-deletion subgrammar"
    fig, (start_ax, total_ax) = plt.subplots(
        2, 1, sharex=True, figsize=(9, 7), layout="constrained"
    )
    start_ax.plot(levels, start_sizes, marker="o", color="#2164ba", linewidth=2.2)
    start_ax.set_ylabel(f"|L_k({loaded['start']})|")
    start_ax.set_ylim(0, max(start_sizes) * 1.25 + 1)
    total_ax.plot(levels, total_sizes, marker="o", color="#b04e2d", linewidth=2.2)
    total_ax.set_ylim(0, max(max(total_sizes), 1) * 1.18)
    total_ax.yaxis.set_major_formatter(StrMethodFormatter("{x:,.0f}"))
    total_ax.set_ylabel("Sum of |L_k(A)| over all A")
    total_ax.set_xlabel("Approximation level k")
    total_ax.set_xlim(0, requested_levels)
    total_ax.set_xticks(range(0, requested_levels + 1,
                             max(1, math.ceil(requested_levels / 12))))
    for ax in (start_ax, total_ax):
        ax.grid(axis="y", color="#dce3ec")
    if completed:
        start_ax.annotate(f"{start_sizes[-1]:,}", (completed, start_sizes[-1]),
                          xytext=(-6, 8), textcoords="offset points", ha="right")
        total_ax.annotate(f"{total_sizes[-1]:,}", (completed, total_sizes[-1]),
                          xytext=(-6, 8), textcoords="offset points", ha="right")
    if status != "completed" and exit_record.get("attempted_level", 0) > completed:
        for ax in (start_ax, total_ax):
            ax.axvline(exit_record["attempted_level"], color="#8b95a5", linestyle=":")
    fig.suptitle(f"Roskind language approximation size ({rule_count} productions)")
    completion = f"Completed {completed}/{requested_levels} levels"
    if status != "completed":
        completion += f"; stopped: {status.replace('_', ' ')}"
    start_ax.set_title(f"{scope} · {completion}", fontsize=10, color="#58677d")
    fig.savefig(output, dpi=160)
    plt.close(fig)
    return completed, status


def roskind_approximation_graph(levels, rules, memory_gib, timeout, output):
    if find_spec("matplotlib") is None:
        raise RuntimeError("Matplotlib is unavailable in this Python; run with the project .venv/bin/python")
    if output.suffix.lower() not in (".png", ".svg"):
        raise ValueError("output must end in .png or .svg")
    data = load_grammar(ROSKIND)
    rule_count = len(data["productions"]) if rules is None else rules
    selected = select_roskind_rules(data, rule_count)
    if levels < 1 or memory_gib <= 0 or timeout <= 0:
        raise ValueError("levels, memory-gib, and timeout must be positive")

    output.parent.mkdir(parents=True, exist_ok=True)
    grammar_path = ROSKIND
    if rule_count != len(data["productions"]):
        grammar_path = output.with_suffix(".grammar.json")
        grammar_path.write_text(json.dumps(selected, ensure_ascii=False, indent=2) + "\n",
                                encoding="utf-8")

    with TemporaryDirectory() as temporary:
        log = Path(temporary) / "memory.jsonl"
        command = [
            sys.executable, str(ROOT / "benchmark_roskind.py"),
            "--grammar", str(grammar_path), "--max-levels", str(levels),
            "--memory-gib", str(memory_gib), "--timeout", str(timeout),
            "--output", str(log),
        ]
        completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        if completed.returncode:
            raise RuntimeError(completed.stderr.strip() or "Roskind benchmark failed")
        records = [json.loads(line) for line in log.read_text(encoding="utf-8").splitlines()]
        measurements = output.with_suffix(".jsonl")
        shutil.copyfile(log, measurements)
        completed_levels, status = plot_approximation_size(records, rule_count, levels, output)

    print(f"Roskind: {rule_count} productions; completed {completed_levels}/{levels} levels ({status}).")
    print(f"Graph: {output}")
    print(f"Measurements: {measurements}")
    if grammar_path != ROSKIND:
        print(f"Selected grammar: {grammar_path}")


def main(argv=None):
    parser = argparse.ArgumentParser(description="Plot the sizes of Roskind language approximations.")
    parser.add_argument("--levels", type=int, default=5,
                        help="highest approximation level to attempt (default: 5)")
    parser.add_argument("--rules", type=int,
                        help="number of original Roskind productions to retain (default: all 642)")
    parser.add_argument("--memory-gib", type=float, default=1,
                        help="worker memory limit in GiB (default: 1)")
    parser.add_argument("--timeout", type=float, default=180,
                        help="time limit in seconds (default: 180)")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "benchmark_results" / "roskind_language_size.png",
                        help="graph path (PNG or SVG)")
    args = parser.parse_args(argv)
    roskind_approximation_graph(args.levels, args.rules, args.memory_gib,
                                args.timeout, args.output.expanduser().resolve())


if __name__ == "__main__":
    main()
