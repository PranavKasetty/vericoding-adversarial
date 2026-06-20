"""Generate figures for the hackathon submission."""

import csv
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict

RESULTS_DIR = Path(__file__).parent / "experiment_results"

def load_merged_results():
    rows = []
    with open(RESULTS_DIR / "merged_results.csv", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["task_id"]:
                rows.append({
                    "task_id": row["task_id"],
                    "condition": row["condition"],
                    "passed": row["passed"] == "True",
                    "iterations_used": int(row["iterations_used"]),
                })
    return rows

def load_opus_oracle_results():
    rows = []
    csv_path = RESULTS_DIR / "run_20260524_230528" / "results.csv"
    with open(csv_path, newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["task_id"]:
                rows.append({
                    "task_id": row["task_id"],
                    "condition": row["condition"],
                    "passed": row["passed"] == "True",
                    "iterations_used": int(row["iterations_used"]),
                })
    return rows

def figure1_pass_at_k(data):
    """Pass@k curves for conditions A and B."""
    fig, ax = plt.subplots(figsize=(7, 4.5))

    total_A = len([r for r in data if r["condition"] == "A"])
    total_B = len([r for r in data if r["condition"] == "B"])

    ks = range(1, 6)
    a_vals = []
    b_vals = []
    for k in ks:
        a_pass = sum(1 for r in data if r["condition"] == "A" and r["passed"] and r["iterations_used"] <= k)
        b_pass = sum(1 for r in data if r["condition"] == "B" and r["passed"] and r["iterations_used"] <= k)
        a_vals.append(100 * a_pass / total_A)
        b_vals.append(100 * b_pass / total_B)

    ax.plot(ks, a_vals, 'o-', color='#2196F3', linewidth=2, markersize=8, label='Condition A (Verifier only)')
    ax.plot(ks, b_vals, 's-', color='#FF5722', linewidth=2, markersize=8, label='Condition B (Verifier + Oracle)')

    # Annotate the pass@2 gap
    ax.annotate('+6%', xy=(2, (a_vals[1] + b_vals[1]) / 2), fontsize=11, fontweight='bold',
                color='#FF5722', ha='left', va='center',
                xytext=(2.3, (a_vals[1] + b_vals[1]) / 2 + 1))

    ax.set_xlabel('Maximum iterations (k)', fontsize=12)
    ax.set_ylabel('Pass@k (%)', fontsize=12)
    ax.set_title('Cumulative Pass Rate by Iteration Budget', fontsize=13)
    ax.set_xticks(range(1, 6))
    ax.set_ylim(40, 95)
    ax.legend(fontsize=10, loc='lower right')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('figure1_pass_at_k.png', dpi=200, bbox_inches='tight')
    plt.savefig('figure1_pass_at_k.pdf', bbox_inches='tight')
    print("Saved figure1_pass_at_k.png and .pdf")
    plt.close()


def figure2_iteration_comparison(data):
    """Bar chart showing iteration counts for tasks where conditions differ."""
    by_task = defaultdict(dict)
    for r in data:
        by_task[r["task_id"]][r["condition"]] = r

    tasks = []
    a_iters = []
    b_iters = []
    for task_id in sorted(by_task.keys()):
        if "A" in by_task[task_id] and "B" in by_task[task_id]:
            a = by_task[task_id]["A"]
            b = by_task[task_id]["B"]
            if a["passed"] and b["passed"] and abs(a["iterations_used"] - b["iterations_used"]) >= 2:
                tasks.append(task_id)
                a_iters.append(a["iterations_used"])
                b_iters.append(b["iterations_used"])

    fig, ax = plt.subplots(figsize=(10, 4))
    x = np.arange(len(tasks))
    width = 0.35

    bars_a = ax.bar(x - width/2, a_iters, width, label='Condition A (Verifier only)', color='#2196F3', alpha=0.85)
    bars_b = ax.bar(x + width/2, b_iters, width, label='Condition B (Verifier + Oracle)', color='#FF5722', alpha=0.85)

    ax.set_xlabel('Task ID', fontsize=11)
    ax.set_ylabel('Iterations to Pass', fontsize=11)
    ax.set_title('Largest Convergence Differences (|diff| >= 2 iterations)', fontsize=12)
    ax.set_xticks(x)
    ax.set_xticklabels(tasks, rotation=45, ha='right', fontsize=9)
    ax.set_ylim(0, 6)
    ax.set_yticks(range(0, 7))
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plt.savefig('figure2_iteration_comparison.png', dpi=200, bbox_inches='tight')
    plt.savefig('figure2_iteration_comparison.pdf', bbox_inches='tight')
    print("Saved figure2_iteration_comparison.png and .pdf")
    plt.close()


def figure3_opus_comparison(baseline, opus):
    """Opus vs Sonnet oracle comparison on hard tasks."""
    opus_tasks_set = {r["task_id"] for r in opus}
    baseline_b = {r["task_id"]: r for r in baseline if r["condition"] == "B" and r["task_id"] in opus_tasks_set}
    opus_b = {r["task_id"]: r for r in opus}

    # Only tasks where at least one oracle solved it
    tasks = []
    sonnet_iters = []
    opus_iters = []
    colors_s = []
    colors_o = []

    for task_id in sorted(opus_tasks_set):
        s = baseline_b.get(task_id)
        o = opus_b.get(task_id)
        if not s or not o:
            continue
        if not s["passed"] and not o["passed"]:
            continue  # skip both-fail

        tasks.append(task_id)
        sonnet_iters.append(s["iterations_used"] if s["passed"] else 5.5)
        opus_iters.append(o["iterations_used"] if o["passed"] else 5.5)
        colors_s.append('#2196F3' if s["passed"] else '#BBDEFB')
        colors_o.append('#FF5722' if o["passed"] else '#FFCCBC')

    fig, ax = plt.subplots(figsize=(9, 4.5))
    x = np.arange(len(tasks))
    width = 0.35

    bars_s = ax.bar(x - width/2, sonnet_iters, width, color=colors_s, edgecolor='black', linewidth=0.5)
    bars_o = ax.bar(x + width/2, opus_iters, width, color=colors_o, edgecolor='black', linewidth=0.5)

    # Legend
    from matplotlib.patches import Patch
    legend_elements = [
        Patch(facecolor='#2196F3', label='Sonnet Oracle (pass)'),
        Patch(facecolor='#BBDEFB', label='Sonnet Oracle (fail)'),
        Patch(facecolor='#FF5722', label='Opus Oracle (pass)'),
        Patch(facecolor='#FFCCBC', label='Opus Oracle (fail)'),
    ]
    ax.legend(handles=legend_elements, fontsize=8, loc='upper right')

    ax.set_xlabel('Task ID', fontsize=11)
    ax.set_ylabel('Iterations Used', fontsize=11)
    ax.set_title('Sonnet Oracle vs Opus Oracle on Hard Tasks (Condition B)', fontsize=12)
    ax.set_xticks(x)
    ax.set_xticklabels(tasks, rotation=45, ha='right', fontsize=9)
    ax.axhline(y=5, color='gray', linestyle='--', alpha=0.5, linewidth=0.8)
    ax.text(len(tasks) - 0.5, 5.1, 'max iters', fontsize=8, color='gray', ha='right')
    ax.set_ylim(0, 6.5)

    # Annotate DA0014
    da14_idx = tasks.index('DA0014') if 'DA0014' in tasks else None
    if da14_idx is not None:
        ax.annotate('New pass!', xy=(da14_idx + width/2, opus_iters[da14_idx]),
                    xytext=(da14_idx + 1.5, opus_iters[da14_idx] - 1.5),
                    arrowprops=dict(arrowstyle='->', color='#FF5722'),
                    fontsize=9, fontweight='bold', color='#FF5722')

    plt.tight_layout()
    plt.savefig('figure3_opus_comparison.png', dpi=200, bbox_inches='tight')
    plt.savefig('figure3_opus_comparison.pdf', bbox_inches='tight')
    print("Saved figure3_opus_comparison.png and .pdf")
    plt.close()


if __name__ == "__main__":
    baseline = load_merged_results()
    opus = load_opus_oracle_results()

    figure1_pass_at_k(baseline)
    figure2_iteration_comparison(baseline)
    figure3_opus_comparison(baseline, opus)
    print("\nAll figures generated.")
