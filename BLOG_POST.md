# The Most Useful "Adversarial" Oracle Is a Proof-Debugging Assistant

**TL;DR.** I built a CEGIS loop around Dafny that repairs LLM-generated verified code, and added a second LLM as an "adversarial oracle" that produces counterexamples alongside the verifier's error. On 50 tasks from the Vericoding benchmark, adding a same-tier oracle (Sonnet-generator, Sonnet-oracle) gave a small, non-significant convergence bump (+6% at pass@2, +4% at pass@4). The interesting result is qualitative: when I upgraded the oracle to Opus on the hard tasks, one task that had failed under every prior configuration passed. The reason wasn't that Opus found a better counterexample — it was that Opus named the specific missing lemma call. The "adversarial counterexample" framing was wrong; what actually helps is *proof-engineering advice*.

**Epistemic status.** One trial per (task, condition). n=50 tasks, n=17 for the Opus subset, n=1 for the headline case study. Take this as a mechanism claim, not an effect-size claim.

**Code and data.** [github.com/PranavKasetty/vericoding-adversarial](https://github.com/PranavKasetty/vericoding-adversarial). All raw outputs and counterexamples are in the repo.

---

## What I was actually testing

The setup extends the [Vericoding benchmark](https://arxiv.org/abs/2509.22908) (Bursuc et al., 2025). Vericoding gives you a Dafny (or Lean, or Verus) spec with holes tagged `<vc-code>` and `<vc-helpers>`, and an LLM has to fill the holes such that Dafny verifies the file. When verification fails, the standard fix is a CEGIS loop: feed the error back into the LLM, ask it to try again, iterate up to some budget (5, in the paper and here).

The pitch I wanted to test came from [John Regehr's "zero degrees of freedom" post](https://blog.regehr.org/archives/2874) and the classic CEGIS papers: multiple oracles are better than one. Specifically — the Dafny verifier is a *soundness* oracle. It tells you "postcondition X fails at line Y" but not *why*, and not with concrete values. What if we added an LLM as a semantic oracle that generates concrete counterexamples in natural language?

Concretely, the setup is:

- **Condition A (baseline):** verifier-only feedback. `repair_prompt = spec + broken_code + verifier_error`.
- **Condition B (adversarial oracle):** verifier + LLM oracle. Before each repair, a *second* LLM (initially Sonnet, same tier as the generator) is prompted with the spec, the broken code, and the verifier error, and asked to produce a concrete counterexample — specific input values that violate the postcondition, plus a one-line explanation of which clause fails. That counterexample is appended to the repair prompt.

Generator is Claude Sonnet 4.6. Tasks are the first 50 Dafny APPStest problems (DA0000–DA0049). Verification timeout is 120s per file. Max repair iterations is 5. One trial per (task, condition).

## The headline numbers

![Figure 1: Cumulative pass rate by iteration budget](figure1_pass_at_k.png)

| k | Condition A | Condition B | Δ    |
|---|-------------|-------------|------|
| 1 | 48%         | 48%         | 0    |
| 2 | 66%         | 72%         | +6   |
| 3 | 76%         | 78%         | +2   |
| 4 | 78%         | 82%         | +4   |
| 5 | 86%         | 84%         | −2   |

Pass rates converge to statistical equivalence at k=5 (86% vs 84%; the 2-point gap at k=5 is one JSON parsing failure on DA0019, not oracle-induced regression). But B leads at k=2,3,4. Among the 42 tasks both conditions solve, B is faster on 9 tasks and A is faster on 6. Mean paired difference: 0.21 iterations in B's favor. Wilcoxon signed-rank p = 0.21.

That p-value is important. **The convergence advantage is not statistically significant at this sample size**, and I want to lead with that rather than bury it. What the numbers do tell you is that adding a same-tier oracle didn't hurt overall, and there's a directional trend toward faster convergence when both conditions solve.

The largest speedups are on the tasks Condition A struggled with: DA0013 drops 5→1 iterations, DA0016 drops 5→2, DA0037 drops 3→1. The largest slowdown is DA0008 (1→4), which I think is sampling noise rather than the oracle steering the model wrong — a 1-iteration solve in A means Sonnet nailed it on the first try; the oracle rerun happened to hit a rougher initial sample.

![Figure 2: Iteration comparison for tasks where A and B differ by ≥2](figure2_iteration_comparison.png)

## The actually interesting result

After the baseline run, I looked at the 17 tasks that took more than 2 iterations in Condition A and re-ran them with the oracle upgraded to Opus (generator stays Sonnet). This isolates *oracle quality* from *generator quality*.

![Figure 3: Sonnet-oracle vs Opus-oracle on 17 hard tasks](figure3_opus_comparison.png)

11/17 with Opus vs 10/17 with Sonnet oracle, and — the thing that made me actually excited — **DA0014 passed**. DA0014 had failed under Condition A, under Condition B with Sonnet, and across multiple reruns. The task is to prove that GCD-based fraction reduction produces an irreducible fraction: a proof-heavy Dafny problem where the code is almost incidental and the ghost lemmas do the work.

The Sonnet oracle's feedback on iterations 2–4 (task fails):

> *"The `GcdDivides` lemma times out. The postcondition `IsIrreducibleFraction` cannot be verified."*

The Opus oracle's feedback on iteration 2 (task eventually passes):

> *"The `GcdDividesNumerator` lemma's else branch fails because knowing `(a-b) % g == 0` is insufficient to derive `a % g == 0`. The missing call to `GcdDividesDenominator(a-b, b)` in that branch is needed."*

Notice what's different. The Sonnet oracle described a *symptom* — a timeout, a failing postcondition. The Opus oracle named the *proof step*: which lemma to call, in which branch, and why the branch fails without it. That's not a counterexample. That is proof-engineering advice.

## What the reviewers pointed out that I want to sit with

I submitted an earlier version of this to the Apart Research secure program synthesis hackathon. One reviewer wrote:

> *"The 'adversarial counterexample' framing is not always fully matched to formal verification repair. In some cases the oracle seems less like a counterexample generator and more like a proof-debugging assistant. That may actually be the better framing: the most useful oracle is not necessarily one that finds bad inputs, but one that gives targeted proof repair advice."*

I think this is right, and I want to be direct about it. My original framing was "adversarial counterexamples improve CEGIS," which imported vocabulary from CEGIS-for-synthesis (where counterexamples are the mechanism) into a setting where the actual bottleneck is different.

Dafny doesn't need better counterexamples in the CEGIS-for-program-synthesis sense. Dafny's SMT solver already reasons over the full input space. If a proof goes through, it goes through for all inputs; if it fails, the failure isn't usually "here's a bad input" — it's "I can't discharge this VC." What the LLM generator is stuck on is not "which input breaks my code" but "which lemma do I need to call so the solver can close this VC." A same-tier LLM generating a made-up input value doesn't help with that. A stronger LLM naming the missing lemma call does.

So the mechanism I'm actually measuring — and the one worth building on — is:

**When verifier errors are cryptic, a sufficiently strong second LLM can act as a proof-debugging assistant. The benefit is not counterexample generation. The benefit is proof-engineering advice specific enough to steer the next repair attempt.**

## Where the same-tier result fits

If the mechanism is proof-engineering advice, why does the same-tier Sonnet-Sonnet configuration show any convergence benefit at all?

My best guess: the Sonnet oracle sometimes provides advice that's *narrower* than what the generator was going to try next, even if it's less precise than Opus's advice. Even a mediocre pointer ("the postcondition about the third case is what's failing, not the first two") narrows search. That's why the effect shows up at pass@2 — you're saving one round of exploration. But same-tier advice is not qualitatively different from what the generator could produce for itself, so it doesn't unlock genuinely stuck tasks. Opus does, because Opus's advice is qualitatively different.

That's a testable prediction, not a settled claim.

## What resists everything

I looked at the 7 tasks that failed under both conditions. Rough taxonomy:

- **Verification timeouts (4 tasks):** DA0003, DA0014, DA0023, DA0038. The solver runs past 120s on the main method or on a helper lemma. DA0014 was solvable with the Opus oracle — timeouts are not necessarily irreducible; sometimes they're a signal that a specific missing hint would let the solver close the goal.
- **Nonlinear arithmetic (2 tasks):** DA0003, DA0024. GCD, mod, exponentiation. The LLM generates lemmas whose preconditions don't hold at their call site (`GcdSymmetric(b, a%b)` when `a%b` might be 0, violating `requires b > 0`) and can't debug the proof structure across iterations.
- **Quantifier reasoning (1 task):** DA0006. Nested existentials over 6-digit permutations. Dafny warns "could not find trigger for this quantifier"; the LLM generates loop invariants with untriggerable quantifiers.
- **Spec complexity (2 tasks):** DA0038, DA0043. Multiple interacting concepts (step-constrained string traversal; floor-division monotonicity across signs). Helper lemmas time out individually, so the main proof can't assemble.
- **Repair oscillation (1 task):** DA0024 iteration 5, the LLM emitted invalid Dafny syntax (`ensures gcd_positive(a, b); a % gcd(a, b) == 0` — a semicolon inside `ensures`). The model was cycling between proof strategies without converging and eventually broke syntax.

Nonlinear arithmetic and quantifier reasoning look like they need specialized lemma libraries or trigger annotations that current LLMs don't reliably generate. Timeouts are the interesting category — DA0014 shows they can be broken with the right hint.

## Predictions I'd bet on

Concrete predictions, at the risk of being wrong:

1. **A non-LLM counterexample generator (e.g., Dafny's `/proverOpt:MODEL_COMPRESS`, or exposing the SMT model directly) will not close the Sonnet-vs-Opus gap on DA0014-style tasks.** Because the bottleneck isn't the counterexample. It's the proof advice.

2. **Multi-trial replication (say 5 trials per task-condition) will preserve the sign of the pass@2 advantage for Condition B, but the effect size will be noisier than the raw +6% suggests.** DA0008's 1→4 slowdown is almost certainly sampling variance; averaging across trials should smooth that out and probably reduce the observed gap somewhat.

3. **Scaling to the full 677-task Dafny APPStest set will amplify the Opus-oracle effect.** The 50-task subset I used runs at 86% baseline; the full set runs at ~60–67%. More hard tasks = more opportunities for the oracle to unlock something.

4. **A prompt that explicitly asks the oracle "which lemma call is missing?" or "which VC is not being discharged, and why?" will outperform the current counterexample-shaped prompt on hard tasks, even holding the oracle model fixed.** The Opus advantage on DA0014 came from Opus *choosing* to give proof-engineering advice despite my prompt asking for a counterexample. A prompt that asks for it directly should get more of it.

## What would change my mind

- If a non-LLM counterexample source (SMT model, symbolic execution, property-based tester) closes the pass@2 gap or unlocks DA0014, I'd conclude the mechanism is "any additional feedback channel," not "proof-engineering advice specifically."
- If multi-seed replication shows the pass@2 advantage collapse to ≤1% and the DA0014 result doesn't replicate on a rerun of the Opus-oracle configuration, I'd downgrade the story to "modest same-tier benefit, no oracle-quality effect."
- If a Sonnet oracle prompted with an explicit "name the missing lemma call" instruction matches Opus on DA0014, the story is about prompting, not about model capability.

I think 1 and 2 are the most important to run. Both are on the list.

## Why this might be interesting for secure program synthesis

The practical architecture this suggests is:

- Use a cheaper model as the generator, most of the time.
- Route to a stronger model as a proof-debugging oracle *only when repair fails*, and *only for the failing task*.
- Prompt the oracle for proof-engineering advice, not counterexamples.

That's cheaper than "just use Opus for everything," and it's a natural fit for the CEGIS iteration structure — you already know when a repair failed, so the routing decision is free.

The safety-relevant angle: fewer wasted iterations means fewer opportunities for the generator to fall back to `assume` or `{:axiom}` cheats. I caught 2 such cheat attempts across the 50-task run. Faster convergence probably reduces this failure mode, though I didn't design an experiment to test it directly.

## Limitations, straight

- **One trial per (task, condition).** The p=0.21 on the Wilcoxon is honest. Treat everything above as a mechanism claim, not an effect-size claim.
- **DA0014 is n=1.** It's the single most compelling data point in this writeup and I want to note explicitly that a single unlocked task is not a general result.
- **50 tasks is a small slice** of the 677-task Dafny APPStest set, and my subset runs at 86% baseline versus the paper's 60–67% on the full set. My subset is easier. Effects on hard tasks are likely larger than what I measured.
- **I didn't compare against a non-LLM counterexample baseline.** So I can't distinguish "second-model feedback in general helps" from "adversarial-counterexample-shaped feedback specifically helps." A reviewer flagged this and it's a real gap.

## What's next

I have a follow-up plan doc ([FUTURE_WORK.md](FUTURE_WORK.md)) covering (in rough order): multi-seed replication for stats, extending to Lean, non-LLM counterexample baseline, and testing the "ask for proof-engineering advice" prompt variant. If any of that lands differently than I predict above, I'll post an update.

The main thing I want to leave you with: if you're designing a CEGIS-style repair loop around a formal verifier, the mental model of "second oracle = counterexample generator" is probably the wrong one. The mental model that matches what actually helps is "second oracle = proof-debugging colleague." You want the oracle to look at the verifier error and tell you *what proof step to add*, not *what input to worry about*. That reframes both the prompt design and the model-selection question — you want the strongest reasoner you can afford for the oracle role, and you want to ask it the right question.

## Acknowledgments

Thanks to the anonymous Apart Research reviewers, whose feedback (particularly on the "counterexample vs proof-debugging" framing) directly shaped this writeup. Thanks also to the Vericoding benchmark team for the infrastructure — the CEGIS loop and prompt templates I used are theirs.

## References

- Bursuc, S., et al. (2025). "A Benchmark for Vericoding: Formally Verified Program Synthesis." [arXiv:2509.22908](https://arxiv.org/abs/2509.22908).
- Regehr, J. (2026). "Zero-Degree-of-Freedom LLM Coding using Executable Oracles." Blog post.
- Solar-Lezama, A., et al. (2006). "Combinatorial Sketching for Finite Programs." ASPLOS.
- Sun, C., et al. (2024). "Clover: Closed-Loop Verifiable Code Generation." arXiv:2310.17807.
- Ren, S., et al. (2024). "Laurel: Generating Dafny Assertions Using Large Language Models." arXiv:2405.16792.
