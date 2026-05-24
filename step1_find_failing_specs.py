"""
Step 1: Single-shot vericoding to identify Dafny specs that fail.

This script:
1. Discovers the JSONL structure in your vericoding-benchmark clone
2. Extracts spec-only prompts (without solution code)
3. Sends each to Claude Sonnet 4.6 for code generation
4. Assembles the result into a .dfy file and runs `dafny verify`
5. Saves results to a CSV for use in Steps 2-5

BEFORE RUNNING:
- Set your API key:  export ANTHROPIC_API_KEY="sk-ant-..."
- Set REPO_PATH below to your local clone of vericoding-benchmark
- Install: pip install anthropic
"""

import json
import subprocess
import csv
import os
import sys
import time
from pathlib import Path

# ──────────────────────────────────────────────────────────────
# CONFIGURE THESE
# ──────────────────────────────────────────────────────────────
REPO_PATH = os.environ.get("REPO_PATH", str(Path(__file__).parent))
MODEL = "claude-sonnet-4-6"
MAX_SPECS = 50  # How many specs to test (start small, increase later)
DAFNY_TIMEOUT = 30  # seconds per verification
OUTPUT_DIR = "step1_results"
# ──────────────────────────────────────────────────────────────


def discover_repo(repo_path: str):
    """Print repo structure so you can verify paths."""
    print("=== Repo structure ===")
    for item in sorted(Path(repo_path).rglob("*")):
        depth = len(item.relative_to(repo_path).parts)
        if depth <= 2 and (item.is_dir() or item.suffix in [".jsonl", ".csv"]):
            prefix = "  " * depth
            print(f"{prefix}{item.name}{'/' if item.is_dir() else ''}")
    print()


def discover_jsonl_fields(jsonl_path: str):
    """Print the fields from the first JSONL entry so you know what to use."""
    with open(jsonl_path) as f:
        first_line = f.readline()
        entry = json.loads(first_line)
        print(f"=== JSONL fields in {Path(jsonl_path).name} ===")
        for key, val in entry.items():
            preview = str(val)[:120].replace("\n", "\\n")
            print(f"  {key}: {preview}...")
        print()
        return entry


def find_dafny_jsonl(repo_path: str) -> str:
    """Find the Dafny tasks JSONL file."""
    candidates = list(Path(repo_path).rglob("*dafny*task*.jsonl"))
    if not candidates:
        # Broader search
        candidates = list(Path(repo_path).rglob("*.jsonl"))
        candidates = [c for c in candidates if "dafny" in str(c).lower()]
    if not candidates:
        candidates = list(Path(repo_path).rglob("*.jsonl"))

    if not candidates:
        print("ERROR: No JSONL files found. Check REPO_PATH.")
        sys.exit(1)

    print(f"Found JSONL files: {[str(c) for c in candidates]}")
    # Prefer 'tasks' over 'issues'
    for c in candidates:
        if "task" in c.name.lower() and "dafny" in str(c).lower():
            return str(c)
    return str(candidates[0])


def load_tasks(jsonl_path: str, max_n: int) -> list:
    """Load tasks from JSONL. Adapt field names based on discover_jsonl_fields output."""
    tasks = []
    with open(jsonl_path) as f:
        for line in f:
            entry = json.loads(line)
            tasks.append(entry)
            if len(tasks) >= max_n:
                break
    return tasks


import re
import anthropic
_client = anthropic.Anthropic()

# Static system prompt — identical across all calls so it will be cached.
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


def build_placeholder_file(task: dict) -> tuple[str, int, str]:
    """
    Build the Dafny file with <vc-code>/<vc-helpers> placeholder tags.

    Returns (file_with_placeholders, placeholder_count, task_id).
    placeholder_count is the number of tags inserted, which the LLM must match
    with exactly that many elements in its JSON array response.
    """
    preamble  = task.get("vc-preamble", task.get("preamble", ""))
    spec      = task.get("vc-spec",     task.get("spec", ""))
    postamble = task.get("vc-postamble", task.get("postamble", ""))
    task_id   = task.get("id", task.get("task_id", task.get("name", "unknown")))

    parts: list[str] = []
    placeholder_count = 0

    if preamble:
        parts.append(preamble)

    # Always include a helpers placeholder so the model has an injection point
    # for any helper functions the spec references (even when vc-helpers is empty).
    parts.append("<vc-helpers>")
    placeholder_count += 1

    if spec:
        parts.append(spec)

    # vc-code is always a placeholder (the stub is `{ assume {:axiom} false; }`)
    parts.append("<vc-code>")
    placeholder_count += 1

    if postamble:
        parts.append(postamble)

    return "\n".join(parts), placeholder_count, task_id


def reconstruct_file(file_with_placeholders: str, implementations: list[str]) -> str:
    """Splice LLM implementations back into the placeholder file, in order."""
    result = file_with_placeholders
    impl_iter = iter(implementations)
    for tag in ("<vc-helpers>", "<vc-code>"):
        if tag in result:
            result = result.replace(tag, next(impl_iter), 1)
    return result


def _extract_json_array(text: str, start: int) -> str | None:
    """Return the balanced [...] substring starting at text[start], or None."""
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
    """Extract and validate the JSON array from the model's response."""
    original = text
    text = text.strip()

    # Strip markdown code fence if the model added one despite instructions
    if text.startswith("```"):
        inner = re.search(r"```(?:json)?\n?(.*?)```", text, re.DOTALL)
        if inner:
            text = inner.group(1).strip()

    # Fast path: text is already a bare JSON array
    if text.startswith("["):
        try:
            data = json.loads(text)
            if isinstance(data, list) and len(data) == expected_count:
                return [str(item) for item in data]
        except json.JSONDecodeError:
            pass

    # Fallback: scan for a JSON *array of strings* — pattern `[` then optional
    # whitespace then `"`.  This skips prose matches like `[1, x]` or `[-1]`.
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


def call_claude(file_with_placeholders: str, placeholder_count: int) -> list[str]:
    """
    Send the placeholder file to Claude using the paper's prompt format.
    Returns a list of implementation strings (one per placeholder, in order).
    """
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

    usage = response.usage
    if getattr(usage, "cache_read_input_tokens", 0):
        print(f"    [cache hit: {usage.cache_read_input_tokens} tokens read]")

    text_block = next(
        (block for block in response.content if getattr(block, "type", None) == "text"),
        None,
    )
    if text_block is None:
        raise ValueError(f"No text block in response; blocks: {[b.type for b in response.content]}")
    return _parse_implementations(text_block.text, placeholder_count)


def verify_dafny(dfy_path: str, timeout: int = 30) -> tuple[bool, str]:
    """Run dafny verify and return (success, error_output)."""
    try:
        result = subprocess.run(
            ["dafny", "verify", dfy_path],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        success = result.returncode == 0
        output = result.stdout + "\n" + result.stderr
        return success, output.strip()
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except FileNotFoundError:
        print("ERROR: 'dafny' not found. Is it installed and on PATH?")
        sys.exit(1)


def main():
    os.makedirs(OUTPUT_DIR, exist_ok=True)

    # Step 0: Discover repo structure
    print(f"Looking at repo: {REPO_PATH}\n")
    if not Path(REPO_PATH).exists():
        print(f"ERROR: REPO_PATH '{REPO_PATH}' doesn't exist.")
        print("Set it: export REPO_PATH=/path/to/vericoding-benchmark")
        sys.exit(1)

    discover_repo(REPO_PATH)

    # Step 1: Find and inspect JSONL
    jsonl_path = find_dafny_jsonl(REPO_PATH)
    print(f"Using JSONL: {jsonl_path}\n")
    discover_jsonl_fields(jsonl_path)

    # Ask user to confirm before spending API credits
    print(f"Will test {MAX_SPECS} specs using {MODEL}")
    input("Press Enter to continue (or Ctrl+C to abort and adjust field names)...\n")

    # Step 2: Load tasks
    tasks = load_tasks(jsonl_path, MAX_SPECS)
    print(f"Loaded {len(tasks)} tasks\n")

    # Step 3: Run single-shot vericoding
    results = []
    pass_count = 0
    fail_count = 0
    csv_path = os.path.join(OUTPUT_DIR, "single_shot_results.csv")
    RESULT_FIELDS = ["task_id", "passed", "error", "dfy_path", "spec_prompt_len", "generated_len"]

    def save_results():
        if not results:
            print("  (no results to save)")
            return
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=RESULT_FIELDS, extrasaction="ignore")
            writer.writeheader()
            writer.writerows(results)
        total = pass_count + fail_count
        pct = f"{100*pass_count/total:.0f}%" if total else "n/a"
        print(f"\n{'='*50}")
        print(f"RESULTS: {pass_count}/{total} passed ({pct})")
        print(f"         {fail_count}/{total} failed — these are your Step 2 inputs")
        print(f"\nResults saved to: {csv_path}")
        print(f"Failed specs saved to: {OUTPUT_DIR}/*.error.txt")
        print("Next: use the failing task IDs for the CEGIS experiment (Steps 2-3)")

    try:
        for i, task in enumerate(tasks):
            file_with_placeholders, placeholder_count, task_id = build_placeholder_file(task)

            print(f"[{i+1}/{len(tasks)}] Task: {task_id}")

            # Call Claude
            try:
                implementations = call_claude(file_with_placeholders, placeholder_count)
            except Exception as e:
                print(f"  API error: {e}")
                results.append({
                    "task_id": task_id,
                    "passed": False,
                    "error": f"API_ERROR: {e}",
                    "dfy_path": "",
                    "spec_prompt_len": len(file_with_placeholders),
                    "generated_len": 0,
                })
                fail_count += 1
                continue

            # Splice implementations back into the file
            generated = reconstruct_file(file_with_placeholders, implementations)

            # Save generated code
            dfy_path = os.path.join(OUTPUT_DIR, f"{task_id}.dfy")
            with open(dfy_path, "w", encoding="utf-8") as f:
                f.write(generated)

            # Verify
            passed, output = verify_dafny(dfy_path, DAFNY_TIMEOUT)

            if passed:
                print("  ✓ PASSED")
                pass_count += 1
            else:
                error_summary = output[:200].replace("\n", " | ")
                print(f"  ✗ FAILED: {error_summary}")
                fail_count += 1

            results.append({
                "task_id": task_id,
                "passed": passed,
                "error": "" if passed else output,
                "dfy_path": dfy_path,
                "spec_prompt_len": len(file_with_placeholders),
                "generated_len": len(generated),
            })

            # Save error output for failed specs (needed for CEGIS in Step 2)
            if not passed:
                err_path = os.path.join(OUTPUT_DIR, f"{task_id}.error.txt")
                with open(err_path, "w", encoding="utf-8") as f:
                    f.write(output)

            # Brief pause to stay under rate limits
            time.sleep(0.5)

    except KeyboardInterrupt:
        print(f"\n\nInterrupted after {len(results)} tasks. Saving partial results...")

    # Step 4: Save results (runs on normal completion AND after interrupt)
    save_results()


if __name__ == "__main__":
    main()
