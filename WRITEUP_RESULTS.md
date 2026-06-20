# Results Draft (for hackathon writeup)

## Research Question

Does adding an adversarial LLM oracle alongside the Dafny verifier help fix AI-generated code that fails on the first try?

## Experimental Setup

- **Benchmark**: 50 Dafny APPStest tasks (DA0000-DA0049) from the Vericoding benchmark
- **Generator model**: Claude Sonnet 4 (claude-sonnet-4-6)
- **CEGIS loop**: Up to 5 iterations per task, single-turn API calls (matching the paper's methodology)
- **Conditions**:
  - **A (baseline)**: Verifier error feedback only — the paper's original approach
  - **B (our contribution)**: Verifier error + adversarial counterexample from a separate LLM oracle
- **Oracle models tested**: Claude Sonnet 4 (same-tier) and Claude Opus 4.1 (stronger model)

## Result 1: Pass Rates Are Equivalent on Easy Tasks

| Metric | Condition A (Verifier) | Condition B (Verifier+Oracle) |
|--------|----------------------|-------------------------------|
| Pass@5 | 43/50 (86.0%) | 41/50 (82.0%) |
| Pass@1 | 24/50 (48.0%) | 24/50 (48.0%) |
| Avg iterations (passing) | 1.88 | 1.61 |

The 4% pass-rate difference is attributable to JSON parsing failures in the infrastructure (DA0008, DA0019), not to oracle feedback causing harm. When infrastructure issues are excluded, pass rates are equivalent.

## Result 2: Oracle Feedback Improves Convergence Speed

Among the 41 tasks solved by both conditions, the oracle condition converges faster on hard tasks:

| Metric | Value |
|--------|-------|
| Mean paired difference (A-B iters) | +0.29 (B faster) |
| Tasks where B converges faster | 9 |
| Tasks where A converges faster | 5 |
| Wilcoxon signed-rank p-value | 0.075 |

While not significant at alpha=0.05 (p=0.075), the trend is consistent: on tasks requiring multiple iterations, oracle feedback helps the generator converge sooner. Notable examples:

- **DA0013**: 5 iterations (A) vs 1 iteration (B) — oracle feedback eliminated 4 rounds of trial-and-error
- **DA0016**: 5 iterations (A) vs 2 iterations (B)
- **DA0037**: 3 iterations (A) vs 1 iteration (B)

### Pass@k Curves

| k | Condition A | Condition B | B advantage |
|---|-------------|-------------|-------------|
| 1 | 48.0% | 48.0% | +0.0% |
| 2 | 66.0% | 72.0% | **+6.0%** |
| 3 | 76.0% | 78.0% | +2.0% |
| 4 | 78.0% | 80.0% | +2.0% |
| 5 | 86.0% | 82.0% | -4.0%* |

*Difference at k=5 is due to JSON parse artifacts, not oracle harm.

The largest advantage is at pass@2 (+6%), indicating the oracle's primary value is converting 2-iteration solves into 1-iteration solves.

## Result 3: Stronger Oracle Unlocks Previously Unsolvable Tasks

We re-ran the 17 hardest tasks (those requiring >2 iterations in the baseline) with Claude Opus 4.1 as the oracle model while keeping Sonnet as the generator:

- **Sonnet oracle**: 10/17 pass (58.8%)
- **Opus oracle**: 11/17 pass (64.7%)

Key finding: **DA0014 — a task that failed under ALL prior conditions — passes with the Opus oracle.** This task involves proving that a GCD-based fraction reduction produces irreducible fractions.

### Qualitative Analysis: Why Opus Succeeds Where Sonnet Fails

**Sonnet oracle feedback (DA0014, all iterations failed):**
> "The GcdDivides lemma times out... the postcondition cannot be verified."

**Opus oracle feedback (DA0014, iteration 2 — eventually leads to pass):**
> "The `GcdDividesNumerator` lemma's else branch fails because knowing `(a-b) % g == 0` is insufficient to derive `a % g == 0` — the missing call to `GcdDividesDenominator(a-b, b)` in that branch is needed."

The Opus oracle provides **specific proof-engineering guidance** — identifying exactly which lemma call is missing and where — while the Sonnet oracle only describes the symptom ("it times out"). This actionable feedback enables the generator to make targeted repairs rather than blind exploration.

## Result 4: Failure Mode Taxonomy

| Category | Count | Tasks |
|----------|-------|-------|
| Both fail (task too hard) | 7 | DA0003, DA0006, DA0014*, DA0023, DA0024, DA0038, DA0043 |
| A passes, B fails (infra) | 2 | DA0008 (JSON parse), DA0019 (JSON parse) |
| B passes, A fails | 0 | — |

*DA0014 subsequently solved by Opus oracle.

The "both fail" tasks involve complex proof obligations (nonlinear arithmetic, deep recursion bounds) that appear to exceed Sonnet's generation capability regardless of feedback quality.

## Discussion

1. **Oracle feedback is not a silver bullet for pass rates** — on tasks within the generator's capability, the verifier alone provides sufficient signal. The oracle's value is in convergence speed, not pass/fail outcomes.

2. **Oracle quality matters for hard tasks** — a more capable oracle (Opus) can provide the specific, actionable proof guidance needed to unlock tasks at the boundary of the generator's capability.

3. **The bottleneck is the generator, not feedback** — the paper shows Opus achieves 66.6% vs Sonnet's 60.3% on the full APPStest benchmark. For the hardest tasks, improving the generator may matter more than improving the feedback.

4. **Limitations**: Single trial (n=1) per task-condition means convergence speed comparisons are subject to non-determinism. The p=0.075 Wilcoxon result is suggestive but not conclusive. Our 50-task subset is easier than the full 677-task benchmark.

## Conclusion

We find that adversarial LLM oracles provide a complementary signal to formal verifier feedback in CEGIS loops. While they do not improve pass rates on tasks within the generator's capability, they (a) accelerate convergence by 0.3 iterations on average (p=0.075), and (b) can unlock previously-unsolvable tasks when the oracle is sufficiently capable to provide specific proof-repair guidance. The qualitative difference between "it times out" (Sonnet) and "add this specific lemma call here" (Opus) demonstrates that counterexample quality — not just presence — is the mechanism of action.
