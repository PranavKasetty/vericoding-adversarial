# Experiment Metrics

## 1. Pass Rate (Primary)

**Definition:** Fraction of tasks where the model produces a Dafny-verified implementation within `max_iterations`.

**Calculation:**
```
pass_rate(condition) = count(passed == True) / total_tasks
```

**Comparison:** McNemar's test (paired binary outcomes) between conditions A and B.

---

## 2. Convergence Speed (Paired Iteration Difference)

**Definition:** For tasks that BOTH conditions eventually solve, how many fewer iterations does one condition need?

**Calculation:**
```
For each task where passed_A == True AND passed_B == True:
    diff_i = iterations_A_i - iterations_B_i

Report:
- Mean paired difference (positive = B converges faster)
- Median paired difference
- Wilcoxon signed-rank test p-value (non-parametric, handles non-normal distributions)
```

**Why paired:** Raw averages are misleading because task difficulty varies wildly. Pairing controls for task difficulty.

**Interpretation:** If mean diff > 0 and p < 0.05, condition B converges significantly faster.

---

## 3. Pass@k Curves

**Definition:** Fraction of tasks solved within exactly k iterations (cumulative).

**Calculation:**
```
pass_at_k(condition, k) = count(passed == True AND iterations_used <= k) / total_tasks
```

Plot for k = 1, 2, 3, 4, 5 for each condition. Area between curves indicates practical advantage.

---

## 4. Conditional Convergence (Hard-Task Focus)

**Definition:** Average iterations for tasks that needed more than 1 iteration to solve.

**Calculation:**
```
hard_tasks(condition) = {t : passed_t == True AND iterations_t > 1}
conditional_avg(condition) = mean(iterations_t for t in hard_tasks)
```

**Why:** Easy tasks (pass in 1 iter) dominate the average and mask differences on hard tasks where the oracle has the most opportunity to help.

---

## 5. Oracle Uplift (Opus Experiment)

**Definition:** Does a more powerful oracle model (Opus) improve condition B results on hard tasks?

**Tasks:** All tasks where at least one condition required > 2 iterations in the baseline run:
DA0003, DA0006, DA0007, DA0009, DA0012, DA0013, DA0014, DA0016, DA0023, DA0024, DA0027, DA0028, DA0034, DA0035, DA0037, DA0038, DA0043

**Comparison:**
- Sonnet oracle B vs Opus oracle B (same generator model, different oracle)
- Pass rate change on this hard subset
- Iteration count change (paired, Wilcoxon)

---

## 6. Failure Mode Analysis

**Categories:**
- **Both fail:** Task is beyond current model capability regardless of feedback
- **A passes, B fails:** Oracle feedback confused the generator (regression)
- **B passes, A fails:** Oracle feedback resolved a stuck case (uplift)
- **JSON parse failures:** Infrastructure issue, not model capability

---

## Statistical Tests

| Metric | Test | Null Hypothesis |
|--------|------|-----------------|
| Pass rate difference | McNemar's exact test | Same pass/fail distribution |
| Iteration difference | Wilcoxon signed-rank | Median difference = 0 |
| Pass@k dominance | Paired permutation test | Same CDF |

**Significance level:** alpha = 0.05 (two-tailed).

**Multiple comparisons:** With only 2-3 primary comparisons, no correction needed. If adding exploratory sub-analyses, note them as exploratory.

---

## Data Requirements

- **Minimum for powered test:** 50 tasks x 1 trial gives n=50 paired observations. For McNemar's with expected ~4 discordant pairs, power is limited — report effect sizes alongside p-values.
- **Trial replication:** Running >1 trial per task allows within-task variance estimation and more robust paired tests.
