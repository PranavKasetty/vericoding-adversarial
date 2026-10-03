# Future Work

Follow-up experiments motivated by the hackathon submission and reviewer feedback. Rough priority order — items near the top are the ones that most cleanly convert a mechanism claim into an effect-size claim.

## Reviewer asks addressed here

| Ask | Source | Item |
|-----|--------|------|
| Multiple trials per condition | R1, R2 | [1] Multi-seed replication |
| Larger Opus-oracle sample | R1, R2 | [2] Opus oracle at scale |
| Isolate "adversarial counterexample" from "second-model feedback" | R2 | [3] Non-LLM counterexample baseline |
| Extend to Lean | R2 | [4] Lean port |
| Reframe as "proof-debugging assistant" | R1 | [5] Proof-engineering prompt variant |

## [1] Multi-seed replication of the baseline

**Motivation.** Current results are one trial per (task, condition). Wilcoxon p=0.21 on the convergence difference; the DA0008 A→B slowdown (1→4 iterations) is almost certainly sampling variance. Without multiple seeds we cannot separate oracle effect from LLM sampling noise.

**Design.** Same 50 Dafny APPStest tasks (DA0000–DA0049). Conditions A and B. `n = 5` trials per (task, condition), so 500 runs total. Fix `temperature` and seed per-trial to whatever the Anthropic API exposes for reproducibility; if not exposed, treat trials as i.i.d. samples.

**Analysis.** Per-task pass rate over 5 trials, then paired Wilcoxon on mean iterations-to-solve across the 42-ish jointly-solved tasks. Also compute per-task variance so we can identify tasks whose outcome is deterministic vs. genuinely stochastic.

**Cost estimate.** 500 runs × ~5 iterations × ~2 LLM calls per iteration (generator + oracle in B) ≈ 5,000 API calls. At current Sonnet pricing, roughly `$50–100`. Cheap.

**Expected outcome.** Pass@2 advantage for B likely shrinks from +6% to +2–4%. DA0008 slowdown likely disappears. Overall convergence effect probably still not significant at p<0.05.

## [2] Opus oracle at scale

**Motivation.** DA0014 is n=1. The claim that "stronger oracles unlock stuck tasks" needs more than one data point.

**Design.** Take the 100 hardest tasks from the full Dafny APPStest set (677 tasks), defined as: baseline pass rate < 50% with Sonnet generator + verifier-only across 3 seeds. On this subset, run Condition B with Opus oracle, `n = 3` trials, 5-iteration budget.

**Analysis.** Compare against Condition A (same tasks, same seeds) and Condition B with Sonnet oracle. Metrics: net-new-passed count (tasks that pass only with Opus oracle), pass rate at each k, and — importantly — a qualitative categorization of the oracle's feedback style on the newly-passed tasks. Is Opus providing proof-engineering advice, or is it providing something else?

**Cost estimate.** 100 tasks × 3 trials × 3 conditions × 5 iterations × ~2 LLM calls ≈ 9,000 API calls, with Opus in the oracle role for one condition. At current Opus pricing, roughly `$500–1000`.

**Expected outcome.** ~5–10 additional net-new-passed tasks with Opus oracle. Qualitative inspection shows most of them received proof-engineering advice (specific missing lemma/invariant) rather than counterexamples.

## [3] Non-LLM counterexample baseline

**Motivation.** Reviewer 2's cleanest ablation. Currently we can't separate "adversarial-counterexample-shaped feedback specifically helps" from "any second feedback channel helps." A non-LLM counterexample source would isolate the mechanism.

**Options for the non-LLM source:**
- **Dafny SMT model extraction.** Boogie/Z3 can emit a model when a VC is falsified. Parse and format that model as a counterexample string, feed it to the repair prompt.
- **Property-based testing.** Compile the spec's postcondition to a QuickCheck-style checker and search for a counterexample. Feasible only when the postcondition is executable.
- **Symbolic execution.** Run KLEE-style symbolic execution on the extracted method body. Highest engineering cost, probably not worth it.

**Design.** SMT model extraction is the tractable option. Add a Condition C: verifier + SMT-model-derived counterexample string, no LLM oracle. Run on the 50-task baseline set, 5 trials.

**Analysis.** If Condition C shows convergence gains comparable to Condition B with the Sonnet oracle, then the same-tier oracle's benefit is "any counterexample channel." If Condition C doesn't help but Condition B does, the benefit is specifically LLM-generated feedback. If neither shows a robust effect, we downgrade the same-tier oracle claim entirely.

**Cost estimate.** Engineering: 1–2 days to wire up SMT model extraction. API cost: same as [1], ~$50.

**Expected outcome.** Condition C shows a small effect on some tasks (informing the generator about specific input values sometimes helps) but is dominated by Condition B on tasks where the bottleneck is proof engineering. DA0014-class tasks won't be unlocked by Condition C.

## [4] Lean port

**Motivation.** Reviewer 2 asked for it. Vericoding already provides ~4000 Lean tasks (numpy_triple, numpy_simple, verina, fvapps, clever). The proof-engineering-advice mechanism should transfer to Lean better than counterexample generation would — Lean's proof style is more explicit than Dafny's, so proof-repair advice from an oracle has more clearly-defined targets (tactic names, lemma calls) to reference.

**Design.** Start with a 50-task Lean subset. Run Conditions A and B with same-tier oracle. Then Opus oracle on the hard subset. Same protocol as Dafny.

**Prerequisites.** Lean CLI + mathlib setup in the runner. Vericoding already supports Lean, so most of the plumbing is there — likely a config flag flip plus adapting the placeholder-parsing to Lean's tag conventions.

**Cost estimate.** Engineering: 2–3 days to adapt the runner and validate the pipeline on 5 tasks before scaling. API: ~$100 for the baseline sweep + ~$300 for the Opus subset.

**Expected outcome.** Larger oracle-quality effect in Lean than Dafny. Prediction: the DA0014-analog rate is higher in Lean because tactic-mode proofs have more places for a strong oracle to be specifically useful.

## [5] Proof-engineering prompt variant

**Motivation.** The strongest reframe from Reviewer 1 is that the useful oracle is a proof-debugging assistant. The current oracle prompt asks for a counterexample. What if we ask directly for the missing proof step?

**Design.** Two oracle prompts, A/B'd on the same 50-task baseline set:
- **Prompt V1 (current):** "Produce a concrete counterexample: input values that violate the postcondition, and a one-line explanation of which clause fails."
- **Prompt V2 (proof-repair):** "Identify the specific proof obligation Dafny cannot discharge. Name the missing lemma call, loop invariant, or assertion that would allow the proof to go through, and briefly explain why it's needed."

Run each with Sonnet oracle (same-tier) and Opus oracle. `n = 3` trials.

**Analysis.** Direct comparison of pass rates and convergence. My prediction is that V2 with Sonnet approaches V1 with Opus — i.e., the "oracle quality" effect is partly a "prompted-to-give-the-right-kind-of-advice" effect, and prompting recovers some of the gap. If V2-Sonnet ≈ V1-Opus, the cost story gets much better. If not, oracle capability really is the bottleneck.

**Cost estimate.** ~$100 for the Sonnet variants, ~$300 for the Opus variants.

**Expected outcome.** V2 outperforms V1 at each oracle tier. V2-Sonnet closes maybe half the gap to V1-Opus. Neither closes the gap fully — some Opus advantage is capability, not prompting.

## Nice-to-haves, lower priority

- **Cheat detection audit.** Only 2 `assume`/`{:axiom}` cheats caught in 50 tasks. Worth checking whether the detector is complete — Dafny has other soundness bypasses (`{:verify false}`, `decreases *`, unrestricted trigger annotations) that a determined generator could exploit.
- **Verification budget sweep.** 4/7 irreducible failures were timeouts. Try 300s and 600s budgets on the hard subset to see how many fall over into the "solvable but slow" category. This informs whether "throw more compute at the SMT solver" is a viable alternative to oracle improvements.
- **Failure-mode-conditional oracle routing.** Once we have a good failure taxonomy, condition the oracle prompt on the detected failure mode: "this is a nonlinear arithmetic failure, focus on lemma preconditions" vs. "this is a quantifier trigger failure, focus on trigger annotations." Speculative but cheap.
- **Verus port.** Vericoding's Verus benchmarks (verified-cogen etc.) sit at higher baseline pass rates, so oracle effects may be smaller but the ownership/lifetime axis is a different proof-engineering domain worth exploring.

## Rough sequencing

If I had to pick a next sprint, I'd do [1] and [5] together (both are ~$150 total and directly address the reviewer critiques), then [3] as the cleanest mechanism ablation. [2] and [4] are the bigger commitments and are worth doing only if the mechanism claim survives [1], [3], and [5].
