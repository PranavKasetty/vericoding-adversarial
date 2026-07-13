# Notes on Adding an LLM Oracle to a Dafny Repair Loop

**One-line summary.** I added a second LLM as an "adversarial counterexample" oracle to a CEGIS-style repair loop for Dafny code generation. The aggregate result on 50 tasks is underpowered and I can't distinguish it from noise. The interesting observation is qualitative: on one task that had failed under every prior configuration, upgrading the oracle from Sonnet to Opus produced a completion that named a specific missing lemma call, and the task then passed. I think the useful reframe is that the second oracle is doing proof-debugging, not counterexample generation — but that's a single case study, and the rest of this post is about how much weight it deserves.

**Epistemic status.** One trial per (task, condition). 50 Dafny tasks total; 17 in the Opus-oracle subset; n=1 for the case study I lead with. The aggregate CEGIS-with-oracle-vs-verifier-only comparison is a Wilcoxon signed-rank p=0.21 — I can't distinguish it from sampling noise, and treat it that way throughout. Predictions in this post come with probability estimates because they should be checkable.

**Code, data, and full traces.** [github.com/PranavKasetty/vericoding-adversarial](https://github.com/PranavKasetty/vericoding-adversarial). Every LLM completion, verifier output, and oracle counterexample from every run is committed; nothing about the case study below relies on data I haven't posted.

---

## Setup, compactly

The [Vericoding benchmark](https://arxiv.org/abs/2509.22908) (Bursuc et al., 2025) hands you a Dafny (or Lean, or Verus) spec with holes tagged `<vc-code>` and `<vc-helpers>`. An LLM fills the holes; Dafny verifies. If verification fails, standard practice is a CEGIS loop: feed the error back into the LLM, ask it to repair, repeat up to some iteration budget. Vericoding's paper uses 5; I use 5.

I test two conditions:

- **Condition A (baseline).** Repair prompt = spec + broken code + verifier error string. Nothing else.
- **Condition B ("adversarial oracle").** Before each repair, a second LLM is prompted with the same materials and asked to produce a concrete counterexample: specific input values that violate the postcondition, plus a one-line explanation of which clause fails. That counterexample is appended to the repair prompt.

Generator is Claude Sonnet 4.6 throughout. Tasks are Dafny APPStest DA0000–DA0049 from Vericoding. Verification timeout is 120s. One trial per (task, condition). The oracle is initially Sonnet (same tier as generator); a follow-up run uses Opus on the 17 tasks that took more than 2 iterations in Condition A.

## The observation: what happened on DA0014

DA0014 asks the model to write a Dafny method that, given a fraction `(a, b)`, returns the reduced form `(a/g, b/g)` where `g = gcd(a, b)`, and proves the postcondition `IsIrreducibleFraction(a', b')`. Almost all of the difficulty is in the ghost lemmas: proving that dividing both parts by their GCD yields a coprime pair. The code itself is small.

DA0014 failed under all of the following: Condition A (verifier-only), Condition B with Sonnet oracle across all 5 iterations, and a Condition B rerun with a different seed. In every case, the generator got stuck on the `GcdDividesNumerator` lemma — specifically the branch where the induction hypothesis has to be transported across a subtraction step.

When I re-ran DA0014 in Condition B with the oracle upgraded to Opus, the second-iteration oracle message was:

> *"The `GcdDividesNumerator` lemma's else branch fails because knowing `(a-b) % g == 0` is insufficient to derive `a % g == 0`. The missing call to `GcdDividesDenominator(a-b, b)` in that branch is needed."*

The generator's next completion added exactly that lemma call — `GcdDividesDenominator(a-b, b)` — in that branch. The proof went through on iteration 3.

For contrast, here is what the Sonnet oracle produced on the same task across iterations 2–4 (all three completions read similarly; this one is representative and I've committed the others):

> *"The `GcdDivides` lemma times out. The postcondition `IsIrreducibleFraction` cannot be verified."*

The Sonnet oracle described what was failing. The Opus oracle described what to fix.

**What I actually observed vs what I'm inferring.** What I observed: on this task, Opus's completion contained a specific proof-repair instruction; the generator's next code contained that instruction; the proof closed. What I'm inferring: the instruction caused the proof to close, rather than the generator finding the fix independently on iteration 3 for unrelated reasons. That inference is defensible for DA0014 specifically — the call the generator added was novel to iteration 3, appeared exactly where the oracle said to put it, and the generator had failed to produce that call across many prior attempts under all other conditions — but it is still an inference from one task. The full iteration-by-iteration trace is in `experiment_results/run_20260524_230528/DA0014_B_t1_iter*.dfy`; skepticism is welcome.

## The aggregate result, and why it doesn't do much work

![Cumulative pass rate by iteration budget](figure1_pass_at_k.png)

| k | Condition A | Condition B | Δ    |
|---|-------------|-------------|------|
| 1 | 48%         | 48%         | 0    |
| 2 | 66%         | 72%         | +6   |
| 3 | 76%         | 78%         | +2   |
| 4 | 78%         | 82%         | +4   |
| 5 | 86%         | 84%         | −2   |

Reading these numbers charitably: adding a same-tier oracle bumps pass@2 by 6 points, holds a +4 edge through k=4, and lands within one task of the baseline at k=5.

Reading them un-charitably, which is the correct reading: with 50 tasks and one trial per condition, a 9-vs-6 split among 42 jointly-solved tasks on iteration count gives Wilcoxon signed-rank p = 0.21, and the pass@k differences are within what single-seed noise can produce. **I can't distinguish this from "the oracle does nothing on average."** The pass@2 line reads well as a headline but it's not doing evidential work.

The task-level swings illustrate why. DA0013 drops 5→1 iterations under B; DA0037 drops 3→1; DA0016 drops 5→2. Those look like signal. But DA0008 goes 1→4 under B — with only one trial, I have no principled way to say the DA0013 speedup is real signal while the DA0008 slowdown is sampling variance. They're the same evidential status. The right conclusion from the aggregate is: the point estimate is directionally positive, the confidence interval covers zero, and any per-task story is speculative until I re-run with multiple seeds.

![Iteration comparison for tasks where A and B differ by ≥2](figure2_iteration_comparison.png)

## The Opus subset, with the same skepticism

I re-ran the 17 tasks that took more than 2 iterations under Condition A, this time with Opus as the oracle (generator remains Sonnet). Result: 11/17 pass with Opus oracle vs 10/17 with Sonnet oracle. The +1 is DA0014.

![Sonnet-oracle vs Opus-oracle on 17 hard tasks](figure3_opus_comparison.png)

A +1 delta on 17 tasks is not statistical evidence of an oracle-quality effect. What it is is: one net-new-passed task where I can look at the transcript and identify a specific mechanism (proof-repair advice) that the weaker configuration didn't produce. That's a case study, not a trend.

I'm labeling this correctly because I want the reader to take DA0014 as the piece of evidence it actually is: a compelling qualitative datapoint that suggests a specific mechanism worth testing, not a demonstrated general result.

## The reframing (what an Apart reviewer pointed out)

I originally framed this as "adversarial counterexamples improve CEGIS," borrowing the vocabulary from CEGIS-for-program-synthesis. An Apart Research reviewer wrote back:

> *"In some cases the oracle seems less like a counterexample generator and more like a proof-debugging assistant. That may actually be the better framing: the most useful oracle is not necessarily one that finds bad inputs, but one that gives targeted proof repair advice."*

I think this is right, and it changes what I think I was measuring. Dafny doesn't have a "which input breaks my code" bottleneck in the CEGIS sense — its SMT solver already reasons over the full input space. When Dafny fails, it fails because a specific verification condition can't be discharged. What the generator is stuck on is not "which input to worry about" but "which lemma to call so the solver can close this VC." A made-up input value from a same-tier LLM doesn't help with that. A stronger LLM naming the missing lemma call apparently does, at least on DA0014.

So the mechanism claim I would defend, weakly, on the current evidence:

**When a formal verifier's error is cryptic, a sufficiently strong second LLM can provide proof-engineering advice — the name of a missing lemma, invariant, or assertion — specific enough to steer the next repair attempt. This is different from counterexample generation and is what actually seems to help.**

The word "sufficiently strong" is doing real work in that claim. The Sonnet-Sonnet configuration gave, at best, a noise-level bump; the Opus-oracle configuration gave a case-study-level qualitative shift. Whether that shift generalizes is the thing to test next.

## Failure modes on tasks nothing solves

Seven tasks failed under both conditions. Rough taxonomy — noting up front that these categories overlap (DA0003, DA0024, and DA0038 each fit two), so the counts sum above 7:

- **Solver timeout (4):** DA0003, DA0014, DA0023, DA0038. The SMT solver runs past 120s on the main method or a helper lemma. DA0014 was the one Opus unlocked, which suggests timeout failures are not necessarily irreducible — sometimes the solver would close the goal quickly if it had the right hint.
- **Nonlinear arithmetic (2):** DA0003, DA0024. GCD, mod, exponentiation. The LLM generates lemmas with malformed preconditions (e.g., `GcdSymmetric(b, a%b)` when `a%b` may be 0, violating `requires b > 0`) and cannot debug the proof structure across iterations.
- **Quantifier reasoning (1):** DA0006. Nested existentials over 6-digit permutations. Dafny warns "could not find trigger for this quantifier"; loop invariants come out untriggerable.
- **Spec complexity (2):** DA0038, DA0043. Multiple interacting concepts (step-constrained string traversal; floor-division monotonicity across signs). Helper lemmas time out individually, so the main proof can't assemble.
- **Repair oscillation (1):** DA0024 iteration 5 emitted invalid Dafny syntax (`ensures gcd_positive(a, b); a % gcd(a, b) == 0`, a semicolon inside `ensures`). The model was cycling between proof strategies and eventually broke syntax.

Nonlinear arithmetic and quantifier reasoning look like they need specialized lemma libraries and explicit trigger annotations that current LLMs don't reliably produce. Timeouts are the interesting category — DA0014 shows they can be broken with the right hint, when the hint is proof-engineering advice rather than a symptom description.

## Predictions, with numbers

I want these to be checkable when I run the follow-up experiments in `FUTURE_WORK.md`. Probabilities are calibrated to "I'd bet at these odds," not to false precision:

1. **P(a non-LLM counterexample generator — SMT model extraction, or property-based testing over the postcondition — does not close the Sonnet-oracle-vs-Opus-oracle gap on DA0014-class tasks) ≈ 75%.** Rationale: the bottleneck seems to be proof advice, not counterexamples. If I'm wrong, the mechanism story reduces to "any second feedback channel helps."

2. **P(multi-seed replication, 5 trials per task-condition, preserves the sign of the pass@2 advantage for Condition B) ≈ 60%.** **P(the effect size at least halves) ≈ 55%.** DA0008-type single-seed swings should smooth out. The +6% headline is likely partly noise.

3. **P(DA0014 replicates as a net-new-passed task under Opus-oracle across 5 fresh seeds) ≈ 65%.** The specific proof-advice pattern I observed is unlikely to be a total fluke — it engaged with the correct lemma by name — but oracle output at temperature > 0 is stochastic and I've only seen one success.

4. **P(a Sonnet oracle explicitly prompted with "identify the missing lemma call, invariant, or assertion" — rather than "produce a counterexample" — solves DA0014 in at least 1 of 5 trials) ≈ 50%.** If this comes in high, the story is more about prompting than model capability, and the practical architecture below gets much cheaper.

5. **P(scaling to the full 677-task Dafny APPStest set widens the Opus-oracle net-new-passed count to ≥5 tasks, relative to Sonnet oracle, on the same subset of hard tasks) ≈ 55%.** Hard-tasks-only, because on easy tasks there's nothing for a stronger oracle to unlock.

Numbers 1 and 4 are the load-bearing ones for the "proof-debugging vs counterexample" reframe. If number 1 is wrong or number 4 is very high, the reframe survives in weaker form or in modified form; I'd update accordingly.

## Practical architecture and rough cost

The setup this suggests, if the case study generalizes:

- Cheap model as the generator, always.
- Strong model as an oracle, invoked *only when the generator's repair fails*, and *only for the failing task*.
- Prompt the oracle for proof-engineering advice, not counterexamples.

Rough per-task cost at current Anthropic API pricing, for the observed distribution of iteration counts:

- Sonnet-generator, verifier-only: ~$0.02–0.05 per task on the 50-task set (median 1 iteration, tail out to 5).
- Sonnet-generator + Opus-oracle-on-failure: ~$0.05–0.15 per task, most of the cost being Opus calls on the tail.
- Sonnet-generator + Opus-oracle-always: ~$0.20+ per task, driven by Opus calls on easy tasks that don't need them.
- Opus-generator throughout: substantially more than Opus-oracle-on-failure, since Opus generation on easy tasks is the dominant cost.

The relevant comparison is Opus-oracle-on-failure against Opus-generator-throughout. If the case study generalizes even weakly, gated Opus-oracle looks like a Pareto improvement: comparable quality on hard tasks at a fraction of the cost. That's the number I'd want to see checked against a real run.

## Limitations and what would change my mind

- **The p=0.21 aggregate is not evidence for the same-tier oracle mechanism.** It's compatible with zero effect. If I ran a 5-trial replication and the pass@2 advantage vanished, I'd downgrade the aggregate story to "same-tier oracle appears not to help on average, though the case-study mechanism for stronger oracles may still hold."
- **DA0014 is n=1 across models.** If the Opus-oracle replication (prediction 3) fails to unlock DA0014 on ≥1 of 5 fresh seeds, I'd downgrade the case study substantially and rewrite the reframe as tentative rather than defended.
- **I didn't run a non-LLM counterexample baseline.** If prediction 1 comes in wrong — an SMT-model-extraction counterexample source matches the Opus-oracle result on hard tasks — the reframe collapses: what's helping is having *any* structured additional feedback, not proof-engineering advice specifically.
- **My 50-task subset is easier than the full benchmark.** 86% baseline vs 60–67% on the full Dafny APPStest set. Effects on genuinely hard tasks are unmeasured.
- **Prompt-vs-capability confound is unresolved.** Prediction 4 exists because I don't currently know whether Opus's advantage is model capability or the fact that Opus interpreted my counterexample prompt loosely and gave proof advice anyway. This is the cheapest experiment on the list.

## What's next

The follow-up plan is in [FUTURE_WORK.md](FUTURE_WORK.md). Rough priority order matches the predictions above: multi-seed replication first (cheap, addresses prediction 2), then the prompt-vs-capability A/B (also cheap, addresses prediction 4), then the non-LLM counterexample baseline (addresses prediction 1 and reviewer 2's cleanest ablation), then Lean and larger Opus samples.

If any of the predictions comes in differently, I'll update this post with a note at the top pointing at the newer results.

## The takeaway I'd defend

Not: "adversarial oracles improve CEGIS by X%." I don't have the sample size to support that.

Yes: **the "counterexample generator" mental model for a second oracle in a formal-verification repair loop is probably the wrong mental model. On the one task where my strong-oracle configuration unlocked something no other configuration could, the mechanism wasn't a counterexample — it was proof-engineering advice at the level of "call this lemma in that branch." If that pattern replicates, it changes what oracle you want and what you ask it: strongest reasoner you can afford, prompted for missing-proof-step diagnosis rather than input generation.** The rest of this post is my current best estimate of how likely that reframe is to survive scrutiny, which is somewhere between "worth taking seriously" and "settled."

## Acknowledgments

The anonymous Apart Research reviewers directly shaped this post — one of them wrote the reframe I use in Section 4 more clearly than I had. The Vericoding benchmark team built the CEGIS infrastructure and prompt templates I extended.

## References

- Bursuc, S., et al. (2025). "A Benchmark for Vericoding: Formally Verified Program Synthesis." [arXiv:2509.22908](https://arxiv.org/abs/2509.22908).
- Regehr, J. "Use of Formal Methods for LLM-Generated Code." Blog post, [blog.regehr.org/archives/2874](https://blog.regehr.org/archives/2874).
- Solar-Lezama, A., et al. (2006). "Combinatorial Sketching for Finite Programs." ASPLOS.
- Sun, C., et al. (2024). "Clover: Closed-Loop Verifiable Code Generation." arXiv:2310.17807.
- Ren, S., et al. (2024). "Laurel: Generating Dafny Assertions Using Large Language Models." arXiv:2405.16792.
