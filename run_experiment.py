"""
Vericoding CEGIS experiment — matches the paper's methodology exactly.

Reads spec files directly from specs/ (as the paper does), uses the paper's
prompts and JSON replacement logic, and adds our adversarial oracle condition.

Conditions:
  A: verifier-error feedback only (replicates the paper)
  B: verifier-error + adversarial counterexample (our contribution)

Usage:
  python run_experiment.py                    # run all 50 tasks, both conditions
  python run_experiment.py --tasks DA0001 DA0004  # specific tasks
  python run_experiment.py --condition A      # only condition A
  python run_experiment.py --trials 2         # 2 independent trials
"""

import json
import re
import subprocess
import csv
import os
import sys
import time
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional
import argparse

import anthropic
import yaml

# ──────────────────────────────────────────────────────────────
# Configuration
# ──────────────────────────────────────────────────────────────
SPECS_DIR = Path(__file__).parent / "specs"
PROMPTS_FILE = Path(__file__).parent / "vericoding" / "src" / "dafny" / "prompts.yaml"
MODEL = "claude-sonnet-4-6"
ORACLE_MODEL = "claude-sonnet-4-6"
MAX_ITERATIONS = 5
DAFNY_TIMEOUT = 120
OUTPUT_DIR = Path(__file__).parent / "experiment_results"
API_DELAY = 1.0

# ──────────────────────────────────────────────────────────────
# Load prompts from the paper's prompts.yaml
# ──────────────────────────────────────────────────────────────

def load_prompts() -> dict[str, str]:
    if PROMPTS_FILE.exists():
        with PROMPTS_FILE.open() as f:
            return yaml.safe_load(f)
    # Fallback: look in local directory
    local = Path(__file__).parent / "prompts.yaml"
    if local.exists():
        with local.open() as f:
            return yaml.safe_load(f)
    print(f"ERROR: prompts.yaml not found at {PROMPTS_FILE} or {local}")
    sys.exit(1)


# ──────────────────────────────────────────────────────────────
# Core logic — matches file_processor.py from the paper
# ──────────────────────────────────────────────────────────────

def count_placeholders(code: str) -> int:
    """Count <vc-code> + <vc-helpers> tags in the file (paper's method)."""
    return code.count("<vc-code>") + code.count("<vc-helpers>")


def _extract_json_array(text: str, start: int) -> Optional[str]:
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


def _parse_json_array(text: str, expected_count: int) -> tuple[Optional[list[str]], str]:
    """
    Extract and validate a JSON array from the model's response.
    Uses balanced-bracket scanning to handle reasoning before/after JSON.

    Returns (replacements_list, error_message). One will be None.
    """
    text = text.strip()

    # Strip markdown code fence if present
    fence_match = re.search(r"```(?:json)?\s*(.*?)```", text, re.DOTALL | re.IGNORECASE)
    if fence_match:
        text = fence_match.group(1).strip()

    # Fast path: text is already a bare JSON array
    if text.startswith("["):
        try:
            data = json.loads(text)
            if isinstance(data, list) and len(data) == expected_count:
                return [str(item) for item in data], ""
        except json.JSONDecodeError:
            pass

    # Scan for a JSON array of strings: pattern `[` then whitespace then `"`
    for m in re.finditer(r'\[\s*"', text):
        candidate = _extract_json_array(text, m.start())
        if candidate is None:
            continue
        try:
            data = json.loads(candidate)
            if isinstance(data, list) and len(data) == expected_count:
                return [str(item) for item in data], ""
        except json.JSONDecodeError:
            continue

    # Last resort: try any `[...]` substring
    for m in re.finditer(r'\[', text):
        candidate = _extract_json_array(text, m.start())
        if candidate is None:
            continue
        try:
            data = json.loads(candidate)
            if isinstance(data, list) and len(data) == expected_count:
                return [str(item) for item in data], ""
        except json.JSONDecodeError:
            continue

    return None, f"JSON parsing failed: No valid JSON array with {expected_count} elements found"


def apply_json_replacements(original_code: str, llm_response: str) -> tuple[str, Optional[str]]:
    """
    Apply JSON array replacements to the original code.
    Matches the paper's code_fixer.py logic for Dafny.

    Returns (modified_code, error_message_or_None).
    """
    # Find all vc-code and vc-helpers sections to know expected count
    lines = original_code.split("\n")
    vc_sections = []
    for i, line in enumerate(lines):
        if "<vc-code>" in line:
            for j in range(i + 1, len(lines)):
                if "</vc-code>" in lines[j]:
                    vc_sections.append((i, j, "vc-code"))
                    break
        elif "<vc-helpers>" in line:
            for j in range(i + 1, len(lines)):
                if "</vc-helpers>" in lines[j]:
                    vc_sections.append((i, j, "vc-helpers"))
                    break

    vc_sections.sort(key=lambda x: x[0])
    expected_count = len(vc_sections)

    # Parse JSON array from response using robust scanner
    replacements, error = _parse_json_array(llm_response, expected_count)
    if replacements is None:
        return original_code, error

    if not isinstance(replacements, list):
        return original_code, "JSON parsing failed: Expected JSON array"

    # Apply replacements in reverse order to preserve line indices
    for section_idx in range(len(vc_sections) - 1, -1, -1):
        replacement = replacements[section_idx]
        if not isinstance(replacement, str):
            return original_code, f"Replacement {section_idx} must be a string"

        start_line, end_line, _ = vc_sections[section_idx]
        replacement_lines = replacement.split("\n")
        lines[start_line + 1 : end_line] = replacement_lines

    return "\n".join(lines), None


# ──────────────────────────────────────────────────────────────
# Cheat detection (from the paper's cheat_checker.py)
# ──────────────────────────────────────────────────────────────

DAFNY_CHEAT_PATTERNS = [
    (r"\{:axiom\}", "uses '{:axiom}' to bypass verification"),
    (r"\bassume\b", "uses 'assume' to bypass verification"),
]


def check_for_cheats(code: str) -> list[tuple[str, str]]:
    """Check for verification bypasses in editable sections only."""
    editable_sections = []
    for section_name in ("vc-code", "vc-helpers"):
        pattern = rf"<{section_name}>(.*?)</{section_name}>"
        for m in re.finditer(pattern, code, re.DOTALL):
            editable_sections.append((m.start(), m.end()))

    detected = []
    for pattern, description in DAFNY_CHEAT_PATTERNS:
        for m in re.finditer(pattern, code):
            if any(start <= m.start() < end for start, end in editable_sections):
                detected.append((pattern, description))
                break
    return detected


# ──────────────────────────────────────────────────────────────
# LLM calls
# ──────────────────────────────────────────────────────────────

_client = anthropic.Anthropic()


def call_llm(prompt: str) -> str:
    """Single-turn LLM call (matches the paper — no conversation history)."""
    time.sleep(API_DELAY)
    response = _client.messages.create(
        model=MODEL,
        max_tokens=16384,
        messages=[{"role": "user", "content": prompt}],
    )
    text_block = next(
        (b for b in response.content if getattr(b, "type", None) == "text"), None
    )
    if text_block is None:
        raise ValueError("No text block in LLM response")
    return text_block.text


def call_adversarial_oracle(original_code: str, current_code: str, error_details: str) -> str:
    """
    Condition B: Generate an adversarial counterexample that exposes
    why the current implementation fails.
    """
    prompt = f"""You are an adversarial testing oracle for Dafny programs. Your job is to
generate a CONCRETE counterexample that demonstrates why the implementation below
fails to satisfy its specification.

SPECIFICATION (original file with requirements):
{original_code}

CURRENT BROKEN IMPLEMENTATION:
{current_code}

VERIFICATION ERROR FROM DAFNY:
{error_details}

Generate a CONCRETE counterexample: specific input values that would violate the
postconditions or trigger the verification error. Format your response as:

COUNTEREXAMPLE:
- Input: [specific values for method parameters]
- Expected output: [what the spec requires]
- Actual behavior: [what the broken implementation would produce]
- Why it fails: [1-2 sentence explanation linking to the spec clause that's violated]

Be specific and concrete — use actual numbers/values, not abstract descriptions.
"""
    time.sleep(API_DELAY)
    response = _client.messages.create(
        model=ORACLE_MODEL,
        max_tokens=2048,
        messages=[{"role": "user", "content": prompt}],
    )
    text_block = next(
        (b for b in response.content if getattr(b, "type", None) == "text"), None
    )
    if text_block is None:
        return "Could not generate counterexample."
    return text_block.text


# ──────────────────────────────────────────────────────────────
# Verification
# ──────────────────────────────────────────────────────────────

def verify_dafny(dfy_path: str) -> tuple[bool, str]:
    """Run dafny verify. Returns (success, error_or_output)."""
    try:
        result = subprocess.run(
            ["dafny", "verify", "--allow-warnings", dfy_path],
            capture_output=True,
            text=True,
            timeout=DAFNY_TIMEOUT,
        )
        output = (result.stdout + "\n" + result.stderr).strip()
        return result.returncode == 0, output
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except FileNotFoundError:
        print("ERROR: 'dafny' not found on PATH.")
        sys.exit(1)


# ──────────────────────────────────────────────────────────────
# Main experiment loop
# ──────────────────────────────────────────────────────────────

@dataclass
class IterationResult:
    iteration: int
    passed: bool
    error: str
    had_cheats: bool = False
    counterexample: str = ""


@dataclass
class TaskResult:
    task_id: str
    condition: str
    trial: int
    passed: bool
    iterations_used: int
    iteration_results: list[IterationResult] = field(default_factory=list)


def run_task(
    task_id: str,
    condition: str,
    trial: int,
    prompts: dict[str, str],
    run_dir: Path,
) -> TaskResult:
    """
    Run one task under one condition for one trial.
    Matches the paper's file_processor.py logic.
    """
    spec_file = SPECS_DIR / f"{task_id}_specs.dfy"
    if not spec_file.exists():
        print(f"    SKIP: {spec_file} not found")
        return TaskResult(task_id, condition, trial, False, 0)

    original_code = spec_file.read_text(encoding="utf-8")
    placeholder_count = count_placeholders(original_code)

    # Step 1: Initial generation (same for A and B)
    generate_prompt = prompts["generate_code"].format(
        code=original_code,
        placeholder_count=placeholder_count,
        max_iterations=MAX_ITERATIONS,
    )
    try:
        gen_response = call_llm(generate_prompt)
    except Exception as e:
        print(f"    LLM error on generation: {e}")
        return TaskResult(task_id, condition, trial, False, 0)

    current_code, json_error = apply_json_replacements(original_code, gen_response)
    if json_error:
        # Retry once (paper does this)
        try:
            gen_response = call_llm(generate_prompt)
            current_code, json_error = apply_json_replacements(original_code, gen_response)
        except Exception:
            pass
        if json_error:
            print(f"    JSON parse failed: {json_error[:80]}")
            return TaskResult(task_id, condition, trial, False, 0)

    # Iterative verification loop
    iteration_results = []
    for iteration in range(1, MAX_ITERATIONS + 1):
        # Write current code to file
        iter_file = run_dir / f"{task_id}_{condition}_t{trial}_iter{iteration}.dfy"
        iter_file.write_text(current_code, encoding="utf-8")

        # Check for cheats
        cheats = check_for_cheats(current_code)
        if cheats:
            cheat_desc = "; ".join(d for _, d in cheats)
            error_details = f"CHEATS DETECTED: {cheat_desc}"
            passed = False
        else:
            # Verify
            passed, error_details = verify_dafny(str(iter_file))

        iter_result = IterationResult(
            iteration=iteration,
            passed=passed,
            error="" if passed else error_details,
            had_cheats=bool(cheats),
        )

        if passed:
            print(f"    iter {iteration}: PASSED")
            iteration_results.append(iter_result)
            return TaskResult(task_id, condition, trial, True, iteration, iteration_results)

        # Not last iteration — attempt fix
        if iteration < MAX_ITERATIONS:
            # Condition B: get adversarial counterexample
            counterexample_text = ""
            if condition == "B":
                try:
                    counterexample_text = call_adversarial_oracle(
                        original_code, current_code, error_details
                    )
                    iter_result.counterexample = counterexample_text
                except Exception as e:
                    counterexample_text = f"(oracle failed: {e})"

            iteration_results.append(iter_result)

            # Build fix prompt — uses the paper's exact format
            fix_error_details = error_details
            if condition == "B" and counterexample_text:
                fix_error_details = (
                    f"{error_details}\n\n"
                    f"ADVERSARIAL COUNTEREXAMPLE (concrete input showing why this fails):\n"
                    f"{counterexample_text}"
                )

            fix_prompt = prompts["fix_verification"].format(
                code=current_code,
                original_code=original_code,
                errorDetails=fix_error_details,
                iteration=iteration + 1,
                placeholder_count=placeholder_count,
                max_iterations=MAX_ITERATIONS,
            )

            try:
                fix_response = call_llm(fix_prompt)
            except Exception as e:
                print(f"    iter {iteration}: LLM error on fix: {e}")
                break

            # Apply fix to ORIGINAL code (paper's approach — not to current broken code)
            fixed_code, fix_error = apply_json_replacements(original_code, fix_response)
            if fix_error:
                print(f"    iter {iteration}: fix JSON failed: {fix_error[:60]}")
                continue  # Skip to next iteration (paper does this)

            current_code = fixed_code
            print(f"    iter {iteration}: FAILED, fixing... ({error_details[:60]})")
        else:
            iteration_results.append(iter_result)
            print(f"    iter {iteration}: FAILED (final)")

    return TaskResult(task_id, condition, trial, False, MAX_ITERATIONS, iteration_results)


def main():
    global MAX_ITERATIONS, DAFNY_TIMEOUT, MODEL, ORACLE_MODEL

    parser = argparse.ArgumentParser(description="Vericoding CEGIS experiment")
    parser.add_argument("--tasks", nargs="*", help="Specific task IDs (default: all DA0000-DA0049)")
    parser.add_argument("--condition", choices=["A", "B", "both"], default="both")
    parser.add_argument("--trials", type=int, default=1, help="Number of independent trials")
    parser.add_argument("--max-iter", type=int, default=5)
    parser.add_argument("--model", default=MODEL)
    parser.add_argument("--oracle-model", default=None, help="Model for adversarial oracle (default: same as --model)")
    parser.add_argument("--timeout", type=int, default=DAFNY_TIMEOUT)
    args = parser.parse_args()

    MAX_ITERATIONS = args.max_iter
    DAFNY_TIMEOUT = args.timeout
    MODEL = args.model
    ORACLE_MODEL = args.oracle_model if args.oracle_model else MODEL

    # Determine tasks
    if args.tasks:
        task_ids = args.tasks
    else:
        # Default: DA0000-DA0049 (the paper's evaluation set)
        task_ids = sorted(
            f.stem.replace("_specs", "")
            for f in SPECS_DIR.glob("DA00[0-4][0-9]_specs.dfy")
        )

    conditions = ["A", "B"] if args.condition == "both" else [args.condition]

    print(f"=== Vericoding CEGIS Experiment ===")
    print(f"Tasks: {len(task_ids)}")
    print(f"Conditions: {conditions}")
    print(f"Trials: {args.trials}")
    print(f"Max iterations: {MAX_ITERATIONS}")
    print(f"Model: {MODEL}")
    if ORACLE_MODEL != MODEL:
        print(f"Oracle model: {ORACLE_MODEL}")
    print(f"Dafny timeout: {DAFNY_TIMEOUT}s")
    print()

    # Load prompts
    prompts = load_prompts()
    print(f"Loaded prompts: {list(prompts.keys())}")

    # Create output directory
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    run_dir = OUTPUT_DIR / f"run_{time.strftime('%Y%m%d_%H%M%S')}"
    run_dir.mkdir(parents=True, exist_ok=True)

    # Results tracking
    all_results: list[TaskResult] = []
    csv_path = run_dir / "results.csv"

    print(f"Output: {run_dir}")
    print()

    try:
        for task_id in task_ids:
            for condition in conditions:
                for trial in range(1, args.trials + 1):
                    label = f"{task_id} cond={condition} trial={trial}"
                    print(f"[{label}]")

                    result = run_task(task_id, condition, trial, prompts, run_dir)
                    all_results.append(result)

                    status = "PASS" if result.passed else "FAIL"
                    print(f"  -> {status} (iters={result.iterations_used})")
                    print()

    except KeyboardInterrupt:
        print("\nInterrupted. Saving partial results...")
    except anthropic.APIError as e:
        print(f"\nAPI error: {e}. Saving partial results...")

    # Save results CSV
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["task_id", "condition", "trial", "passed", "iterations_used"])
        for r in all_results:
            writer.writerow([r.task_id, r.condition, r.trial, r.passed, r.iterations_used])

    # Save counterexamples
    counterexamples_dir = run_dir / "counterexamples"
    counterexamples_dir.mkdir(exist_ok=True)
    for r in all_results:
        if r.condition == "B":
            for ir in r.iteration_results:
                if ir.counterexample:
                    ce_file = counterexamples_dir / f"{r.task_id}_t{r.trial}_iter{ir.iteration}.txt"
                    ce_file.write_text(ir.counterexample, encoding="utf-8")

    # Print summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)

    for condition in conditions:
        cond_results = [r for r in all_results if r.condition == condition]
        passed = sum(1 for r in cond_results if r.passed)
        total = len(cond_results)
        pct = f"{100 * passed / total:.1f}%" if total else "n/a"
        print(f"  Condition {condition}: {passed}/{total} ({pct})")

        if total > 0:
            avg_iters = sum(r.iterations_used for r in cond_results if r.passed) / max(passed, 1)
            print(f"    Avg iterations to pass: {avg_iters:.1f}")

    # Tasks fixed by B but not A
    if "A" in conditions and "B" in conditions:
        a_passed = {r.task_id for r in all_results if r.condition == "A" and r.passed}
        b_passed = {r.task_id for r in all_results if r.condition == "B" and r.passed}
        b_only = b_passed - a_passed
        a_only = a_passed - b_passed
        if b_only:
            print(f"\n  Fixed by B but NOT A: {sorted(b_only)}")
        if a_only:
            print(f"  Fixed by A but NOT B: {sorted(a_only)}")

    print(f"\nResults saved to: {csv_path}")
    print(f"Counterexamples saved to: {counterexamples_dir}")


if __name__ == "__main__":
    main()
