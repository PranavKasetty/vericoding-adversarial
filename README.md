# Adversarial CEGIS for Formally Verified Code Synthesis

This repository contains the experimental framework and results for **"Does Oracle Quality Matter? Adversarial Feedback for Formally Verified Code Synthesis,"** submitted to the Apart Research Secure Program Synthesis hackathon (May 2026).

The work extends the [Vericoding benchmark](https://www.arxiv.org/abs/2509.22908) (Bursuc et al., 2025) by adding an adversarial LLM oracle to the CEGIS repair loop and measuring its effect on pass rates and convergence speed.

## Headline Results

- **Pass@5** (50 Dafny APPStest tasks, 1 trial): Condition A (verifier only) = 43/50 (86%), Condition B (verifier + Sonnet oracle) = 42/50 (84%).
- **Pass@2 advantage for B**: +6% (66% vs 72%).
- **Opus oracle uplift**: a previously unsolvable task (DA0014) passes when the oracle is upgraded from Sonnet to Opus, due to qualitatively different feedback (specific proof-engineering guidance vs symptom descriptions).

Full writeup: [`SUBMISSION_DRAFT.md`](SUBMISSION_DRAFT.md).

## Figures

![Pass@k curves](figure1_pass_at_k.png)

*Figure 1: Cumulative pass rate by iteration budget. Condition B leads Condition A at k=2,3,4.*

![Iteration comparison](figure2_iteration_comparison.png)

*Figure 2: Tasks where the two conditions differ by 2 or more iterations.*

![Opus vs Sonnet oracle](figure3_opus_comparison.png)

*Figure 3: Sonnet oracle vs Opus oracle on 17 hard tasks. DA0014 is newly solved with Opus.*

## Repository Layout

```
run_experiment.py          # CEGIS loop with optional adversarial oracle
analysis.py                # Summary statistics, pass@k, Wilcoxon test
generate_figures.py        # Produces the three figures above
SUBMISSION_DRAFT.md        # Hackathon report
WRITEUP_RESULTS.md         # Earlier results notes
metrics.md                 # Metric definitions
requirements.txt           # Python dependencies
experiment_results/        # Raw run outputs and merged CSV
  merged_results.csv       # Consolidated 50-task baseline
  run_20260524_194452/     # Conditions A and B (Sonnet oracle) baseline
  run_20260524_230528/     # Opus oracle run on 17 hard tasks
  run_20260525_161638/     # DA0008/DA0019 rerun
vericoding/                # Upstream benchmark (submodule)
specs/                     # Dafny/Lean/Verus task specifications
```

## Reproducing the Results

### Setup

```bash
pip install -r requirements.txt
# Ensure Dafny is installed and on PATH
export ANTHROPIC_API_KEY=your_key_here
```

### Baseline experiment (Condition A and B)

```bash
# Condition A: verifier-only feedback
python run_experiment.py --condition A --trials 1

# Condition B: verifier + adversarial Sonnet oracle
python run_experiment.py --condition B --trials 1
```

By default the script runs on the 50-task subset DA0000-DA0049.

### Opus oracle experiment

```bash
python run_experiment.py \
  --tasks DA0003 DA0006 DA0007 DA0009 DA0012 DA0013 DA0014 DA0016 \
          DA0023 DA0024 DA0027 DA0028 DA0034 DA0035 DA0037 DA0038 DA0043 \
  --condition B \
  --oracle-model claude-opus-4-6 \
  --trials 1
```

### Analysis and figures

```bash
python analysis.py            # prints summary tables to stdout
python generate_figures.py    # writes figure1, figure2, figure3 (PNG + PDF)
```

## Experimental Setup

| Component | Value |
|-----------|-------|
| Generator | Claude Sonnet 4.6 (`claude-sonnet-4-6`) |
| Default oracle | Claude Sonnet 4.6 |
| Stronger oracle (DA0014 case study) | Claude Opus 4.6 (`claude-opus-4-6`) |
| Dafny verification timeout | 120 s |
| Max repair iterations | 5 |
| Tasks | 50 Dafny APPStest tasks (DA0000-DA0049) |
| Trials | 1 per task-condition |

## Citation

If you build on this work, please cite the underlying benchmark:

```bibtex
@article{bursuc2025vericoding,
  title={A Benchmark for Vericoding: Formally Verified Program Synthesis},
  author={Bursuc, Sergiu and others},
  journal={arXiv preprint arXiv:2509.22908},
  year={2025}
}
```

## Upstream Benchmark

The `vericoding/` submodule and `specs/` directory come from the original Vericoding benchmark. See [the upstream repository](https://github.com/Beneficial-AI-Foundation/vericoding) for benchmark documentation, the full 12,504 task set across Dafny/Lean/Verus, and the original CEGIS framework.
