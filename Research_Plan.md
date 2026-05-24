Research question: Does adding an adversarial LLM oracle alongside the Dafny verifier help fix AI-generated code that fails on the first try?

## Context from the vericoding paper (ArXiv 2509.22908)

The paper already uses a verifier-feedback CEGIS loop (up to 5 iterations, multi-turn
conversation with error messages passed back). Claude Sonnet 4 achieves 64.6% on Dafny
with this approach; model union reaches 82.2%. Our single-shot baseline of 44% is expected
— it matches their "iteration 1" performance level.

Key paper features we must match:
- Multi-turn conversation (not single-turn repair prompts)
- ValidateBlocks: catch assume/sorry/spec-trivializing cheats before verification
- JSON array format for placeholder replacement (vc-helpers + vc-code)

What the paper does NOT do (our novel contribution):
- Adversarial LLM oracle generating concrete counterexamples
- Taxonomy of irreducible failure modes

## Revised experimental plan

### Step 1: Single-shot baseline (DONE)
- 50 Dafny specs, Claude Sonnet 4.6, single-shot generation
- Result: 22/50 passed (44%)
- 28 failures, of which 18 have .dfy files, 10 had API errors

### Step 1b: Classify failures (NEW — do before spending more API credits)
Read the 18 .dfy error outputs and classify each as:
- STRUCTURAL: spec references undefined identifiers, no vc-helpers placeholder (unfixable)
- PROOF_GAP: valid Dafny syntax but assertion/postcondition fails (fixable by CEGIS)
- TIMEOUT: verification doesn't terminate within limit
- API_ERROR: transient connection/parse failures (re-run)

Only PROOF_GAP and TIMEOUT tasks are valid subjects for the A vs B comparison.
STRUCTURAL tasks go straight to the taxonomy.

### Step 2: Fix the CEGIS script methodology
Current issues:
1. Single-turn repair (should be multi-turn conversation with history)
2. No cheat validation (model tries to mutate specs, use assume, etc.)
3. No early-exit for structurally impossible tasks
4. Must revert the always-add-helpers change (breaks passing tasks)

### Step 3: Run CEGIS on PROOF_GAP tasks only
- Condition A: multi-turn verifier-error feedback (replicates the paper's approach)
- Condition B: multi-turn verifier-error + adversarial counterexample
- 5 iterations max per condition
- 3 trials per task per condition (address non-determinism)
- Store counterexamples for all B iterations

### Step 4: Compare
- Pass rate within k iterations (A vs B)
- Mean iterations to convergence (A vs B)
- Tasks fixed by B but not A (the headline number)
- Bootstrap confidence intervals over the 3 trials

### Step 5: Taxonomy of irreducible failures
Categories observed so far:
- Spec references undefined helpers (no injection point)
- LLM mutates spec to cheat (observed in DA0015)
- Non-terminating verification (timeout oscillation)
- Oscillating repair (model alternates between two failure modes)
- Model correctly diagnoses constraint but can't work around it

### Step 6: Write up
4-8 page paper. Framing: Regehr's zero-degree-of-freedom thesis applied to vericoding.
The taxonomy is the primary contribution; the A vs B comparison is secondary evidence.
