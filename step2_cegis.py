"""
Step 2: CEGIS repair loop — Conditions A and B.

For each failing spec from step1_results/single_shot_results.csv:
  Condition A: [broken code + verifier error] → Claude → verify → repeat ≤ MAX_ITER
  Condition B: [broken code + verifier error + adversarial counterexample] → Claude → verify → repeat ≤ MAX_ITER

Output: step2_results/cegis_results.csv
  task_id, condition, iteration, passed, error, dfy_path

BEFORE RUNNING:
  Set ANTHROPIC_API_KEY in your environment.
"""

import json
import subprocess
import csv
import os
import re
import sys
import time
from pathlib import Path

import anthropic

# ──────────────────────────────────────────────────────────────
REPO_PATH    = os.environ.get("REPO_PATH", str(Path(__file__).parent))
MODEL        = "claude-sonnet-4-6"
MAX_ITER     = 5
DAFNY_TIMEOUT = 60          # seconds — longer than step1 to give repairs a fair shot
STEP1_CSV    = os.path.join(REPO_PATH, "step1_results", "single_shot_results.csv")
JSONL_PATH   = os.path.join(REPO_PATH, "jsonl", "dafny_tasks.jsonl")
OUTPUT_DIR   = os.path.join(REPO_PATH, "step2_results")
# ──────────────────────────────────────────────────────────────

_client = anthropic.Anthropic()

# ── shared system prompt (identical to step1, cached) ─────────
_SYSTEM_PROMPT = """\
CRITICAL: Respond with ONLY a JSON array. No explanations, reasoning, or markdown. \
Start with [ and end with ].

The task is to generate implementations for '<vc-code>' and '<vc-helpers>' sections \
in a Dafny file.

SECTION-SPECIFIC RULES:
**For '<vc-helpers>' sections:**
- Provide COMPLETE helper function/lemma definitions ONLY
- Each helper should be a standalone function/predicate/lemma with a proper signature
- Example: 'function min(a: int, b: int): int { if a < b then a else b }'
- Example: 'predicate IsValid(x: int) { x >= 0 }'
- Example: 'lemma HelperLemma(x: int) ensures x + 0 == x {}'
- DO NOT include method body code, variable assignments, or code fragments
- DO NOT include opening/closing braces unless they are part of the function body

**For '<vc-code>' sections:**
- Provide method body implementation code ONLY
- Always include opening/closing braces: '{\\n\\n}'
- Example: '{\\n  result := min(a, b) + 1;\\n}'
- Include variable declarations, assignments, loop invariants, and control flow

CRITICAL RULES:
- NEVER use verification bypasses: '{:axiom}', 'assume' statements, or shortcuts
- Implement actual proofs and logic — do NOT bypass verification
- Use valid Dafny syntax for all implementations
- Satisfy all 'requires' and 'ensures' clauses from the specification
- Do not add trivial or unnecessary annotations
- Return ONLY a valid JSON array — no explanations, reasoning, or markdown
- Your response must start with [ and end with ]
- Each JSON string must be properly escaped

CRITICAL: Your entire response must be ONLY the JSON array. Any text before or after \
will cause a parsing failure.
CRITICAL: Do NOT use 'assume {:axiom}', 'assume', or any verification bypasses."""

# ── utility: balanced JSON-array extractor ─────────────────────
def _extract_json_array(text: str, start: int) -> str | None:
    if start >= len(text) or text[start] != "[":
        return None
    depth = 0
    in_string = False
    escape = False
    for i in range(start, len(text)):
        c = text[i]
        if escape:
            escape = False
            continue
        if c == "\\" and in_string:
            escape = True
            continue
        if c == '"':
            in_string = not in_string
            continue
        if in_string:
            continue
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0:
                return text[start : i + 1]
    return None


def _parse_implementations(text: str, expected_count: int) -> list[str]:
    original = text
    text = text.strip()

    if text.startswith("```"):
        inner = re.search(r"```(?:json)?\n?(.*?)```", text, re.DOTALL)
        if inner:
            text = inner.group(1).strip()

    if text.startswith("["):
        try:
            data = json.loads(text)
            if isinstance(data, list) and len(data) == expected_count:
                return [str(item) for item in data]
        except json.JSONDecodeError:
            pass

    for m in re.finditer(r'\[\s*"', text):
        candidate = _extract_json_array(text, m.start())
        if candidate is None:
            continue
        try:
            data = json.loads(candidate)
            if isinstance(data, list) and len(data) == expected_count:
                return [str(item) for item in data]
        except json.JSONDecodeError:
            continue

    raise ValueError(
        f"Could not find a valid JSON array with {expected_count} element(s).\n"
        f"Raw response (first 600 chars):\n{original[:600]}"
    )


# ── task helpers ───────────────────────────────────────────────
def build_placeholder_file(task: dict) -> tuple[str, int, str]:
    preamble  = task.get("vc-preamble",  task.get("preamble",  ""))
    helpers   = task.get("vc-helpers",   task.get("helpers",   ""))
    spec      = task.get("vc-spec",      task.get("spec",      ""))
    postamble = task.get("vc-postamble", task.get("postamble", ""))
    task_id   = task.get("id", task.get("task_id", task.get("name", "unknown")))

    parts: list[str] = []
    placeholder_count = 0

    if preamble:
        parts.append(preamble)
    # Always include a helpers placeholder — even when vc-helpers is empty,
    # the model needs an injection point for helper functions the spec may reference.
    parts.append("<vc-helpers>")
    placeholder_count += 1
    if spec:
        parts.append(spec)
    parts.append("<vc-code>")
    placeholder_count += 1
    if postamble:
        parts.append(postamble)

    return "\n".join(parts), placeholder_count, task_id


def reconstruct_file(file_with_placeholders: str, implementations: list[str]) -> str:
    result = file_with_placeholders
    impl_iter = iter(implementations)
    for tag in ("<vc-helpers>", "<vc-code>"):
        if tag in result:
            result = result.replace(tag, next(impl_iter), 1)
    return result


# ── Claude calls ───────────────────────────────────────────────
def call_claude_generate(file_with_placeholders: str, placeholder_count: int) -> list[str]:
    """Fresh generation (same as step1)."""
    user_msg = (
        f"TURN 1 of 1: Generate implementations for the {placeholder_count} "
        f"placeholder section(s) in the Dafny file below.\n\n"
        f"INPUT: Dafny file with {placeholder_count} placeholder(s).\n\n"
        f"OUTPUT: Return a JSON array with EXACTLY {placeholder_count} element(s), "
        f"one per placeholder in top-to-bottom order.\n\n"
        f"DAFNY FILE WITH PLACEHOLDER SECTIONS:\n{file_with_placeholders}"
    )
    response = _client.messages.create(
        model=MODEL,
        max_tokens=4096,
        system=[{"type": "text", "text": _SYSTEM_PROMPT,
                 "cache_control": {"type": "ephemeral"}}],
        messages=[{"role": "user", "content": user_msg}],
    )
    text_block = next(
        (b for b in response.content if getattr(b, "type", None) == "text"), None
    )
    if text_block is None:
        raise ValueError("No text block in generate response")
    return _parse_implementations(text_block.text, placeholder_count)


def call_claude_repair_a(
    file_with_placeholders: str,
    placeholder_count: int,
    broken_dfy: str,
    verifier_error: str,
    iteration: int,
) -> list[str]:
    """Condition A repair: verifier error only."""
    user_msg = (
        f"REPAIR ITERATION {iteration}: The previous Dafny implementation failed verification.\n\n"
        f"VERIFIER ERROR:\n{verifier_error}\n\n"
        f"CURRENT (BROKEN) IMPLEMENTATION:\n{broken_dfy}\n\n"
        f"ORIGINAL FILE WITH PLACEHOLDERS (for reference):\n{file_with_placeholders}\n\n"
        f"Fix the implementation. Identify the root cause of the verifier error and correct it.\n"
        f"Return a JSON array with EXACTLY {placeholder_count} element(s), "
        f"one per placeholder in top-to-bottom order."
    )
    response = _client.messages.create(
        model=MODEL,
        max_tokens=4096,
        system=[{"type": "text", "text": _SYSTEM_PROMPT,
                 "cache_control": {"type": "ephemeral"}}],
        messages=[{"role": "user", "content": user_msg}],
    )
    text_block = next(
        (b for b in response.content if getattr(b, "type", None) == "text"), None
    )
    if text_block is None:
        raise ValueError("No text block in repair-A response")
    return _parse_implementations(text_block.text, placeholder_count)


def call_oracle(spec: str, broken_dfy: str) -> str:
    """Adversarial oracle: find a counterexample to the broken implementation."""
    oracle_system = (
        "You are a formal verification adversary. Given a Dafny specification and a broken "
        "implementation, find a CONCRETE input that satisfies the preconditions but violates "
        "the postconditions.\n"
        "Be concise: describe only the counterexample input values and which postcondition "
        "they violate. Do not include code."
    )
    user_msg = (
        f"SPECIFICATION:\n{spec}\n\n"
        f"BROKEN IMPLEMENTATION:\n{broken_dfy}\n\n"
        f"Find a concrete counterexample. Describe the input values (e.g. x=5, arr=[1,2,3]) "
        f"and which postcondition is violated."
    )
    response = _client.messages.create(
        model=MODEL,
        max_tokens=512,
        system=oracle_system,
        messages=[{"role": "user", "content": user_msg}],
    )
    text_block = next(
        (b for b in response.content if getattr(b, "type", None) == "text"), None
    )
    return text_block.text.strip() if text_block else "(oracle returned no text)"


def call_claude_repair_b(
    file_with_placeholders: str,
    placeholder_count: int,
    broken_dfy: str,
    verifier_error: str,
    counterexample: str,
    iteration: int,
) -> list[str]:
    """Condition B repair: verifier error + adversarial counterexample."""
    user_msg = (
        f"REPAIR ITERATION {iteration}: The previous Dafny implementation failed verification.\n\n"
        f"VERIFIER ERROR:\n{verifier_error}\n\n"
        f"ADVERSARIAL COUNTEREXAMPLE (concrete input that breaks the spec):\n{counterexample}\n\n"
        f"CURRENT (BROKEN) IMPLEMENTATION:\n{broken_dfy}\n\n"
        f"ORIGINAL FILE WITH PLACEHOLDERS (for reference):\n{file_with_placeholders}\n\n"
        f"Fix the implementation. The counterexample reveals a specific failure mode — "
        f"make sure your fix handles it.\n"
        f"Return a JSON array with EXACTLY {placeholder_count} element(s), "
        f"one per placeholder in top-to-bottom order."
    )
    response = _client.messages.create(
        model=MODEL,
        max_tokens=4096,
        system=[{"type": "text", "text": _SYSTEM_PROMPT,
                 "cache_control": {"type": "ephemeral"}}],
        messages=[{"role": "user", "content": user_msg}],
    )
    text_block = next(
        (b for b in response.content if getattr(b, "type", None) == "text"), None
    )
    if text_block is None:
        raise ValueError("No text block in repair-B response")
    return _parse_implementations(text_block.text, placeholder_count)


# ── Dafny ──────────────────────────────────────────────────────
def verify_dafny(dfy_path: str, timeout: int = DAFNY_TIMEOUT) -> tuple[bool, str]:
    try:
        result = subprocess.run(
            ["dafny", "verify", dfy_path],
            capture_output=True, text=True, timeout=timeout,
        )
        return result.returncode == 0, (result.stdout + "\n" + result.stderr).strip()
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except FileNotFoundError:
        print("ERROR: 'dafny' not found on PATH.")
        sys.exit(1)


# ── data loading ───────────────────────────────────────────────
def load_failing_tasks_from_csv() -> list[dict]:
    rows = []
    with open(STEP1_CSV, encoding="utf-8") as f:
        for row in csv.DictReader(f):
            if row["passed"].lower() == "false":
                rows.append(row)
    return rows


def load_all_tasks_from_jsonl() -> dict[str, dict]:
    tasks = {}
    with open(JSONL_PATH, encoding="utf-8") as f:
        for line in f:
            t = json.loads(line)
            tasks[t["id"]] = t
    return tasks


# ── repair loop ────────────────────────────────────────────────
def run_one_condition(
    condition: str,          # "A" or "B"
    task: dict,
    initial_dfy: str,        # content of the current broken .dfy
    initial_error: str,
    out_dir: str,
    task_id: str,
) -> list[dict]:
    """
    Run up to MAX_ITER repair iterations for one condition.
    Returns a list of result dicts (one per iteration attempted).
    """
    file_with_placeholders, placeholder_count, _ = build_placeholder_file(task)
    spec = task.get("vc-spec", task.get("spec", ""))

    results = []
    current_dfy = initial_dfy
    current_error = initial_error

    for i in range(1, MAX_ITER + 1):
        print(f"    [{condition}] iter {i}/{MAX_ITER} ...", end=" ", flush=True)
        ce = ""
        try:
            if condition == "A":
                impls = call_claude_repair_a(
                    file_with_placeholders, placeholder_count,
                    current_dfy, current_error, i,
                )
            else:
                ce = call_oracle(spec, current_dfy)
                print(f"(oracle ok)", end=" ", flush=True)
                # Save counterexample to its own file for later analysis
                ce_path = os.path.join(out_dir, f"{task_id}_condB_iter{i}.ce.txt")
                with open(ce_path, "w", encoding="utf-8") as f:
                    f.write(ce)
                impls = call_claude_repair_b(
                    file_with_placeholders, placeholder_count,
                    current_dfy, current_error, ce, i,
                )
        except Exception as e:
            print(f"API error: {e}")
            results.append({
                "task_id": task_id, "condition": condition, "iteration": i,
                "passed": False, "error": f"API_ERROR: {e}", "dfy_path": "",
                "counterexample": ce,
            })
            time.sleep(1)
            continue

        new_dfy = reconstruct_file(file_with_placeholders, impls)
        dfy_path = os.path.join(out_dir, f"{task_id}_cond{condition}_iter{i}.dfy")
        with open(dfy_path, "w", encoding="utf-8") as f:
            f.write(new_dfy)

        passed, output = verify_dafny(dfy_path)
        if passed:
            print("PASSED")
        else:
            err_summary = output[:120].replace("\n", " | ")
            print(f"failed: {err_summary}")

        results.append({
            "task_id": task_id, "condition": condition, "iteration": i,
            "passed": passed, "error": "" if passed else output, "dfy_path": dfy_path,
            "counterexample": ce,
        })

        if passed:
            break

        # Early exit: same error signature twice in a row → stuck, won't improve
        if len(results) >= 2:
            prev_err = results[-2]["error"]
            # Compare first 200 chars (enough to catch identical error types)
            if output[:200] == prev_err[:200] and not passed:
                print(f"    [{condition}] stuck (same error twice) — stopping early")
                break

        current_dfy = new_dfy
        current_error = output
        time.sleep(0.4)

    return results


# ── main ───────────────────────────────────────────────────────
def main():
    os.makedirs(OUTPUT_DIR, exist_ok=True)

    failing_rows = load_failing_tasks_from_csv()
    all_tasks = load_all_tasks_from_jsonl()

    # Only work on tasks with an existing .dfy file (skip pure API errors)
    workable = [r for r in failing_rows if r.get("dfy_path")]
    api_errors = [r for r in failing_rows if not r.get("dfy_path")]

    print(f"Failing tasks: {len(failing_rows)} total")
    print(f"  With .dfy file (workable): {len(workable)}")
    print(f"  API errors (no .dfy, skipping): {len(api_errors)}")
    if api_errors:
        print(f"  Skipped: {[r['task_id'] for r in api_errors]}")
    print()

    csv_path = os.path.join(OUTPUT_DIR, "cegis_results.csv")
    FIELDS = ["task_id", "condition", "iteration", "passed", "error", "dfy_path", "counterexample"]

    all_results: list[dict] = []

    def save():
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=FIELDS, extrasaction="ignore")
            w.writeheader()
            w.writerows(all_results)

    try:
        for idx, row in enumerate(workable):
            task_id = row["task_id"]
            task = all_tasks.get(task_id)
            if task is None:
                print(f"[{idx+1}/{len(workable)}] {task_id}: not found in JSONL, skipping")
                continue

            dfy_path = row["dfy_path"]
            if not os.path.exists(dfy_path):
                print(f"[{idx+1}/{len(workable)}] {task_id}: .dfy file missing, skipping")
                continue

            with open(dfy_path, encoding="utf-8") as f:
                initial_dfy = f.read()
            initial_error = row["error"]

            print(f"[{idx+1}/{len(workable)}] {task_id}")

            for condition in ("A", "B"):
                res = run_one_condition(
                    condition, task, initial_dfy, initial_error,
                    OUTPUT_DIR, task_id,
                )
                all_results.extend(res)
                converged = any(r["passed"] for r in res)
                iters_needed = next((r["iteration"] for r in res if r["passed"]), None)
                status = f"converged at iter {iters_needed}" if converged else f"failed all {MAX_ITER} iters"
                print(f"    [{condition}] {status}")

            save()
            print()

    except KeyboardInterrupt:
        print(f"\nInterrupted. Saving {len(all_results)} results...")

    save()

    # Summary
    print("=" * 60)
    print(f"CEGIS RESULTS")
    print("=" * 60)
    for cond in ("A", "B"):
        cond_rows = [r for r in all_results if r["condition"] == cond]
        tasks_done = {r["task_id"] for r in cond_rows}
        tasks_fixed = {r["task_id"] for r in cond_rows if r["passed"]}
        print(f"Condition {cond}: {len(tasks_fixed)}/{len(tasks_done)} tasks fixed")

    b_only = {r["task_id"] for r in all_results if r["condition"] == "B" and r["passed"]} - \
             {r["task_id"] for r in all_results if r["condition"] == "A" and r["passed"]}
    print(f"Fixed by B but not A: {sorted(b_only)}")
    print(f"\nDetailed results: {csv_path}")


if __name__ == "__main__":
    main()
