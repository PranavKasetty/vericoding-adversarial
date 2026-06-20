"""
Analysis script for the adversarial CEGIS experiment results.
Produces summary statistics, tables, and figures for the writeup.
"""

import csv
import numpy as np
from pathlib import Path
from collections import defaultdict

# ──────────────────────────────────────────────────────────────
# Load data
# ──────────────────────────────────────────────────────────────

RESULTS_DIR = Path(__file__).parent / "experiment_results"

def load_merged_results():
    """Load the baseline merged results (50 tasks, conditions A and B, trial 1)."""
    rows = []
    with open(RESULTS_DIR / "merged_results.csv", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["task_id"]:  # skip empty rows
                rows.append({
                    "task_id": row["task_id"],
                    "condition": row["condition"],
                    "trial": int(row["trial"]),
                    "passed": row["passed"] == "True",
                    "iterations_used": int(row["iterations_used"]),
                    "notes": row.get("notes", ""),
                })
    return rows

def load_opus_oracle_results():
    """Load the Opus oracle experiment results."""
    rows = []
    csv_path = RESULTS_DIR / "run_20260524_230528" / "results.csv"
    with open(csv_path, newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["task_id"]:
                rows.append({
                    "task_id": row["task_id"],
                    "condition": row["condition"],
                    "trial": int(row["trial"]),
                    "passed": row["passed"] == "True",
                    "iterations_used": int(row["iterations_used"]),
                })
    return rows

# ──────────────────────────────────────────────────────────────
# Analysis
# ──────────────────────────────────────────────────────────────

def baseline_summary(data):
    """Compute pass rates and convergence stats for baseline experiment."""
    print("=" * 70)
    print("BASELINE RESULTS (50 tasks, Trial 1)")
    print("=" * 70)

    for cond in ["A", "B"]:
        cond_data = [r for r in data if r["condition"] == cond]
        passed = [r for r in cond_data if r["passed"]]
        total = len(cond_data)
        n_pass = len(passed)
        pct = 100 * n_pass / total

        avg_iters_all = np.mean([r["iterations_used"] for r in passed]) if passed else 0
        # Conditional: tasks needing >1 iteration
        hard_passed = [r for r in passed if r["iterations_used"] > 1]
        avg_iters_hard = np.mean([r["iterations_used"] for r in hard_passed]) if hard_passed else 0

        print(f"\n  Condition {cond} ({'Verifier only' if cond == 'A' else 'Verifier + Oracle'}):")
        print(f"    Pass rate: {n_pass}/{total} ({pct:.1f}%)")
        print(f"    Avg iterations (all passing): {avg_iters_all:.2f}")
        print(f"    Avg iterations (hard tasks, >1 iter): {avg_iters_hard:.2f} ({len(hard_passed)} tasks)")
        print(f"    Pass@1: {sum(1 for r in passed if r['iterations_used'] == 1)}/{total} ({100*sum(1 for r in passed if r['iterations_used'] == 1)/total:.1f}%)")


def pass_at_k_curves(data):
    """Compute pass@k for k=1..5."""
    print("\n" + "=" * 70)
    print("PASS@k CURVES")
    print("=" * 70)
    print(f"\n  {'k':<5}{'Condition A':<20}{'Condition B':<20}{'Difference':<15}")
    print("  " + "-" * 55)

    for cond in ["A", "B"]:
        cond_data = [r for r in data if r["condition"] == cond]
        total = len(cond_data)
        globals()[f"pass_k_{cond}"] = {}

    total_A = len([r for r in data if r["condition"] == "A"])
    total_B = len([r for r in data if r["condition"] == "B"])

    for k in range(1, 6):
        a_pass = sum(1 for r in data if r["condition"] == "A" and r["passed"] and r["iterations_used"] <= k)
        b_pass = sum(1 for r in data if r["condition"] == "B" and r["passed"] and r["iterations_used"] <= k)
        a_pct = 100 * a_pass / total_A
        b_pct = 100 * b_pass / total_B
        diff = b_pct - a_pct
        sign = "+" if diff >= 0 else ""
        print(f"  {k:<5}{a_pass}/{total_A} ({a_pct:5.1f}%)     {b_pass}/{total_B} ({b_pct:5.1f}%)     {sign}{diff:.1f}%")


def paired_iteration_analysis(data):
    """Paired analysis: for tasks both conditions solve, compare iterations."""
    print("\n" + "=" * 70)
    print("PAIRED ITERATION ANALYSIS (tasks solved by BOTH conditions)")
    print("=" * 70)

    # Group by task
    by_task = defaultdict(dict)
    for r in data:
        by_task[r["task_id"]][r["condition"]] = r

    paired_diffs = []  # A_iters - B_iters (positive = B faster)
    details = []

    for task_id in sorted(by_task.keys()):
        if "A" in by_task[task_id] and "B" in by_task[task_id]:
            a = by_task[task_id]["A"]
            b = by_task[task_id]["B"]
            if a["passed"] and b["passed"]:
                diff = a["iterations_used"] - b["iterations_used"]
                paired_diffs.append(diff)
                if diff != 0:
                    details.append((task_id, a["iterations_used"], b["iterations_used"], diff))

    paired_diffs = np.array(paired_diffs)
    n_paired = len(paired_diffs)
    mean_diff = np.mean(paired_diffs)
    median_diff = np.median(paired_diffs)

    print(f"\n  Paired tasks (both pass): {n_paired}")
    print(f"  Mean difference (A-B iters): {mean_diff:.3f} {'(B faster)' if mean_diff > 0 else '(A faster)' if mean_diff < 0 else '(equal)'}")
    print(f"  Median difference: {median_diff:.1f}")
    print(f"  B faster: {sum(1 for d in paired_diffs if d > 0)} tasks")
    print(f"  A faster: {sum(1 for d in paired_diffs if d < 0)} tasks")
    print(f"  Equal: {sum(1 for d in paired_diffs if d == 0)} tasks")

    # Wilcoxon signed-rank test
    nonzero = paired_diffs[paired_diffs != 0]
    if len(nonzero) >= 5:
        from scipy import stats
        stat, p_value = stats.wilcoxon(nonzero)
        print(f"\n  Wilcoxon signed-rank test (on {len(nonzero)} non-zero pairs):")
        print(f"    Test statistic: {stat:.1f}")
        print(f"    p-value: {p_value:.4f}")
        print(f"    Significant at alpha=0.05: {'Yes' if p_value < 0.05 else 'No'}")
    else:
        print(f"\n  Too few non-zero pairs ({len(nonzero)}) for Wilcoxon test")

    if details:
        print(f"\n  Tasks with different iteration counts:")
        print(f"    {'Task':<10}{'A iters':<10}{'B iters':<10}{'Diff (A-B)':<12}{'Winner'}")
        print("    " + "-" * 50)
        for task_id, a_iters, b_iters, diff in sorted(details, key=lambda x: -x[3]):
            winner = "B" if diff > 0 else "A"
            print(f"    {task_id:<10}{a_iters:<10}{b_iters:<10}{diff:<12}{winner}")


def opus_oracle_comparison(baseline_data, opus_data):
    """Compare Sonnet oracle vs Opus oracle on hard tasks."""
    print("\n" + "=" * 70)
    print("OPUS ORACLE EXPERIMENT (17 hard tasks, Condition B only)")
    print("=" * 70)

    # Get baseline B results for the same tasks
    opus_tasks = {r["task_id"] for r in opus_data}
    baseline_b = {r["task_id"]: r for r in baseline_data
                  if r["condition"] == "B" and r["task_id"] in opus_tasks}
    opus_b = {r["task_id"]: r for r in opus_data}

    sonnet_pass = sum(1 for r in baseline_b.values() if r["passed"])
    opus_pass = sum(1 for r in opus_b.values() if r["passed"])
    total = len(opus_tasks)

    print(f"\n  Sonnet oracle B: {sonnet_pass}/{total} ({100*sonnet_pass/total:.1f}%)")
    print(f"  Opus oracle B:   {opus_pass}/{total} ({100*opus_pass/total:.1f}%)")

    # Detailed comparison
    print(f"\n  {'Task':<10}{'Sonnet B':<18}{'Opus B':<18}{'Change'}")
    print("  " + "-" * 60)

    improvements = []
    regressions = []
    new_passes = []

    for task_id in sorted(opus_tasks):
        s = baseline_b.get(task_id)
        o = opus_b.get(task_id)
        if not s or not o:
            continue

        s_str = f"PASS ({s['iterations_used']})" if s["passed"] else f"FAIL ({s['iterations_used']})"
        o_str = f"PASS ({o['iterations_used']})" if o["passed"] else f"FAIL ({o['iterations_used']})"

        if not s["passed"] and o["passed"]:
            change = "*** NEW PASS ***"
            new_passes.append(task_id)
        elif s["passed"] and o["passed"]:
            diff = s["iterations_used"] - o["iterations_used"]
            if diff > 0:
                change = f"-{diff} iters (faster)"
                improvements.append((task_id, diff))
            elif diff < 0:
                change = f"+{-diff} iters (slower)"
                regressions.append((task_id, diff))
            else:
                change = "same"
        elif s["passed"] and not o["passed"]:
            change = "REGRESSION"
            regressions.append((task_id, None))
        else:
            change = "both fail"

        print(f"  {task_id:<10}{s_str:<18}{o_str:<18}{change}")

    print(f"\n  Summary:")
    print(f"    New passes (previously unsolvable): {len(new_passes)} — {new_passes}")
    print(f"    Faster convergence: {len(improvements)} tasks")
    print(f"    Slower/regression: {len(regressions)} tasks (likely non-determinism)")


def failure_mode_analysis(data):
    """Categorize failure modes."""
    print("\n" + "=" * 70)
    print("FAILURE MODE ANALYSIS")
    print("=" * 70)

    by_task = defaultdict(dict)
    for r in data:
        by_task[r["task_id"]][r["condition"]] = r

    both_fail = []
    a_only = []
    b_only = []

    for task_id in sorted(by_task.keys()):
        if "A" in by_task[task_id] and "B" in by_task[task_id]:
            a = by_task[task_id]["A"]
            b = by_task[task_id]["B"]
            if not a["passed"] and not b["passed"]:
                both_fail.append(task_id)
            elif a["passed"] and not b["passed"]:
                a_only.append((task_id, b.get("notes", "")))
            elif not a["passed"] and b["passed"]:
                b_only.append(task_id)

    print(f"\n  Both conditions fail: {len(both_fail)} tasks — {both_fail}")
    print(f"  A passes, B fails: {len(a_only)} tasks")
    for task_id, notes in a_only:
        print(f"    {task_id}: {notes}")
    print(f"  B passes, A fails: {len(b_only)} tasks — {b_only}")


def generate_latex_table(data, opus_data):
    """Generate a LaTeX-ready comparison table."""
    print("\n" + "=" * 70)
    print("LATEX TABLE (for writeup)")
    print("=" * 70)

    by_task = defaultdict(dict)
    for r in data:
        by_task[r["task_id"]][r["condition"]] = r

    # Summary table
    a_data = [r for r in data if r["condition"] == "A"]
    b_data = [r for r in data if r["condition"] == "B"]
    a_pass = sum(1 for r in a_data if r["passed"])
    b_pass = sum(1 for r in b_data if r["passed"])
    total = len(a_data)

    # Pass@1
    a_pass1 = sum(1 for r in a_data if r["passed"] and r["iterations_used"] == 1)
    b_pass1 = sum(1 for r in b_data if r["passed"] and r["iterations_used"] == 1)

    # Avg iters (passing only)
    a_avg = np.mean([r["iterations_used"] for r in a_data if r["passed"]])
    b_avg = np.mean([r["iterations_used"] for r in b_data if r["passed"]])

    print(f"""
\\begin{{table}}[h]
\\centering
\\begin{{tabular}}{{lcc}}
\\toprule
\\textbf{{Metric}} & \\textbf{{Cond. A (Verifier)}} & \\textbf{{Cond. B (Verifier+Oracle)}} \\\\
\\midrule
Pass rate (pass@5) & {a_pass}/{total} ({100*a_pass/total:.1f}\\%) & {b_pass}/{total} ({100*b_pass/total:.1f}\\%) \\\\
Pass@1 & {a_pass1}/{total} ({100*a_pass1/total:.1f}\\%) & {b_pass1}/{total} ({100*b_pass1/total:.1f}\\%) \\\\
Avg iterations (passing) & {a_avg:.2f} & {b_avg:.2f} \\\\
\\bottomrule
\\end{{tabular}}
\\caption{{Baseline results on 50 Dafny APPStest tasks (1 trial). Condition A uses verifier error feedback only; Condition B adds adversarial counterexamples from a Sonnet oracle.}}
\\label{{tab:baseline}}
\\end{{table}}
""")

    # Opus oracle table
    opus_tasks = {r["task_id"] for r in opus_data}
    baseline_b = {r["task_id"]: r for r in data
                  if r["condition"] == "B" and r["task_id"] in opus_tasks}
    opus_b = {r["task_id"]: r for r in opus_data}

    print(f"""
\\begin{{table}}[h]
\\centering
\\begin{{tabular}}{{lccc}}
\\toprule
\\textbf{{Task}} & \\textbf{{Sonnet Oracle}} & \\textbf{{Opus Oracle}} & \\textbf{{Change}} \\\\
\\midrule""")
    for task_id in sorted(opus_tasks):
        s = baseline_b.get(task_id)
        o = opus_b.get(task_id)
        if not s or not o:
            continue
        s_str = f"Pass ({s['iterations_used']})" if s["passed"] else "Fail"
        o_str = f"Pass ({o['iterations_used']})" if o["passed"] else "Fail"
        if not s["passed"] and o["passed"]:
            change = "\\textbf{New pass}"
        elif s["passed"] and o["passed"]:
            diff = s["iterations_used"] - o["iterations_used"]
            if diff > 0:
                change = f"$-{diff}$ iters"
            elif diff < 0:
                change = f"$+{-diff}$ iters"
            else:
                change = "="
        else:
            change = "—"
        print(f"{task_id} & {s_str} & {o_str} & {change} \\\\")
    print(f"""\\bottomrule
\\end{{tabular}}
\\caption{{Opus oracle vs Sonnet oracle on 17 hard tasks (Condition B only). Opus unlocks DA0014 (previously unsolvable) and improves convergence on DA0012, DA0027, DA0034.}}
\\label{{tab:opus}}
\\end{{table}}
""")


# ──────────────────────────────────────────────────────────────
# Main
# ─────────────────────────���────────────────────────────────────

if __name__ == "__main__":
    baseline = load_merged_results()
    opus = load_opus_oracle_results()

    baseline_summary(baseline)
    pass_at_k_curves(baseline)
    paired_iteration_analysis(baseline)
    opus_oracle_comparison(baseline, opus)
    failure_mode_analysis(baseline)
    generate_latex_table(baseline, opus)
