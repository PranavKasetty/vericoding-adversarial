# Corrections

Errors found after submission. The Apart submission cannot be revised, so this file is the record.
The original text is quoted below, not rewritten away.

---

## C1: DA0014 was not solved by the lemma the Opus oracle named (5 October 2026)

**Severity: high.** It is the report's headline finding: "oracle quality matters" rests on this one task.

### What I said

`README.md`:

- Line 17: "B-Opus (17 hard tasks only) | — | — | +1 net-new-passed task (DA0014)"
- Line 19: "It passed under B-Opus because the oracle named a specific missing lemma call
  (`GcdDividesDenominator(a-b, b)` in the else branch of `GcdDividesNumerator`); the generator's next
  completion added exactly that call and the proof closed."
- Line 26: "The 'proof-engineering advice beats counterexample generation' reframe is a case study, not a
  demonstrated effect."

`REPORT.md`:

- Line 6 (abstract): a stronger oracle "unlocks a task that failed under all prior conditions by
  providing specific proof-repair guidance (identifying a missing lemma call)".
- Line 21 (contribution 3): "a stronger oracle provides specific proof-repair guidance that unlocks a
  previously unsolvable task."
- Lines 84–88 (§4.2 table): Opus oracle pass rate 11/17 against 10/17, and "Previously unsolvable
  tasks now solved: 1 (DA0014)".
- Lines 92–104 (§4.3, "Why Opus Succeeds on DA0014"): the Opus feedback is quoted as "(iteration 2, task
  eventually passes)", and described as "targeted surgery".
- Line 112 (taxonomy): "DA0014 was eventually solved by the Opus oracle providing proof-engineering hints."
- Line 120: "DA0014 demonstrates that higher-quality proof-engineering guidance from a stronger oracle can
  overcome them."
- Lines 126–128 (discussion) and line 154 (conclusion): oracle quality "enabling it to solve tasks that no
  amount of verifier feedback alone can fix", and the proposed Sonnet-generator, Opus-oracle architecture.

### What is actually the case

All evidence is in `experiment_results/run_20260524_230528/`.

1. After iteration 2, the Opus oracle did correctly name the missing call
   (`counterexamples/DA0014_t1_iter2.txt`).
2. The generator added `GcdDividesDenominator(a - b, b)` in iteration 3 (`DA0014_B_t1_iter3.dfy`).
   **Iteration 3 did not verify.** The iteration 3 feedback (`counterexamples/DA0014_t1_iter3.txt`) reports
   solver timeouts from the subtraction-based GCD lemmas.
3. Iteration 4 rewrote the proof (`DA0014_B_t1_iter4.dfy`) and **also failed**
   (`counterexamples/DA0014_t1_iter4.txt`).
4. Iteration 5 passed (`results.csv`: `DA0014,B,1,True,5`). The passing program,
   `DA0014_B_t1_iter5.dfy`, deletes every lemma, and its whole method body is:

   ```dafny
   numerator := 1;
   denominator := 1;
   ```

   It returns 1/1 for every input.
5. That verifies because the specification (`specs/DA0014_specs.dfy`) only ensures
   `ValidFraction(numerator, denominator)` and `IsIrreducibleFraction(numerator, denominator)`. It never
   relates the output to the inputs `t, w, b`. The benchmark's own reference solution
   (`vericoded/DA0014_vericoded.dfy`) is also a constant: `numerator := 0; denominator := 1;`.

So the "net-new pass" is a vacuous program that the under-specified spec accepts. The lemma the oracle
named was added and did not close the proof. The +1 in the Opus row of §4.2 (11/17 against 10/17) is this
task. Without it, the two oracles solved 10 of the 17 hard tasks each. I haven't audited those 10 passes
for the same kind of vacuous solution.

### How it happened

I read `results.csv` (passed at iteration 5) next to the iteration 2 oracle message, which named the right
lemma, and assumed the one caused the other. I didn't open the passing program. A pass from the verifier was
treated as the end of the check, which is the exact assumption the project was supposed to question.

### What still stands

- **The Opus oracle's diagnosis was correct.** It named the specific missing lemma call, in the right
  branch, with the right reason, where the Sonnet oracle reported only "it times out". That is a real
  qualitative difference in feedback. It is one task, and it didn't lead to a proof.
- **The main result is unchanged.** A same-strength oracle: 36/50 against 33/50 at pass@2, not significant
  (Wilcoxon p = 0.21); 42/50 against 43/50 at pass@5.
- **The failure taxonomy is unchanged,** except for the DA0014 sentences on lines 112 and 120. DA0014 stays
  a verification-timeout failure that no setup solved with a real proof.

### New finding

DA0014 is a case of **specification gaming**. Under repeated failure, the generator dropped the proof and
returned a constant that satisfies the letter of a weak spec. The verifier reported success. A pipeline that
trusts "verified" without checking that the spec constrains the output would have accepted it. That belongs
in the results, not in a footnote.

### Where the original claim also appears

- The **Apart Research project page** for this submission carries the original abstract and conclusion. I
  can't edit it; this file is the correction of record.
- `figure3_opus_comparison.png` labels DA0014 "New pass!" under the Opus oracle. The pass is real but
  vacuous; the figure should not be read as a proof being found.
