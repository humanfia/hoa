#!/usr/bin/env python3
"""Validate preservation of the public IMO 2026 Lean problem skeletons."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


THEOREMS = {
    "imo2026_q1": [
        "statement_a_termination",
        "statement_a_unique_large",
        "statement_b_invariance",
        "terminal_value_eq_Mval",
        "Mval_gt_one",
    ],
    "imo2026_q2": ["main_theorem"],
    "imo2026_q3": [
        "pieceLengths_sum",
        "pieceLengths_length",
        "L_mem_Icc",
        "V_eq",
        "lower_bound",
        "upper_bound",
    ],
    "imo2026_q4": ["main_theorem"],
    "imo2026_q5": ["main_theorem"],
    "imo2026_q6": ["main_theorem"],
}

FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|native_decide)\b")


def theorem_header(source: str, name: str) -> str:
    start = re.search(rf"(?m)^theorem\s+{re.escape(name)}\b", source)
    if start is None:
        raise ValueError(f"missing theorem {name}")
    proof = source.find(":= by", start.start())
    if proof < 0:
        raise ValueError(f"theorem {name} has no ':= by' proof boundary")
    return source[start.start() : proof + len(":= by")]


def preceding_docstring(source: str, theorem_start: int) -> str | None:
    prefix = source[:theorem_start]
    end = prefix.rfind("-/")
    if end < 0 or prefix[end + 2 :].strip():
        return None
    start = prefix.rfind("/--", 0, end)
    if start < 0:
        return None
    return prefix[start : end + 2]


def validate(problem: str, original: Path, candidate: Path) -> list[str]:
    errors: list[str] = []
    original_text = original.read_text(encoding="utf-8")
    candidate_text = candidate.read_text(encoding="utf-8")

    if FORBIDDEN.search(candidate_text):
        errors.append("candidate contains a forbidden proof marker")

    names = THEOREMS[problem]
    first = re.search(rf"(?m)^theorem\s+{re.escape(names[0])}\b", original_text)
    if first is None:
        return [f"original is missing expected theorem {names[0]}"]
    protected_prefix = original_text[: first.start()]
    if not candidate_text.startswith(protected_prefix):
        errors.append("definitions/imports before the first theorem changed")

    last_position = -1
    for name in names:
        try:
            header = theorem_header(original_text, name)
        except ValueError as exc:
            errors.append(str(exc))
            continue
        position = candidate_text.find(header)
        if position < 0:
            errors.append(f"exact theorem header changed or disappeared: {name}")
            continue
        if position <= last_position:
            errors.append(f"theorem order changed at {name}")
        last_position = position

        original_start = original_text.find(header)
        docstring = preceding_docstring(original_text, original_start)
        if docstring is not None and docstring not in candidate_text:
            errors.append(f"docstring changed or disappeared: {name}")

    if problem in {"imo2026_q3", "imo2026_q4"}:
        expected_end = "end LiuBangXiangYu" if problem == "imo2026_q3" else "end TriangleGame"
        if not candidate_text.rstrip().endswith(expected_end):
            errors.append(f"namespace terminator changed: {expected_end}")

    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--problem", choices=sorted(THEOREMS), required=True)
    parser.add_argument("--original", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    args = parser.parse_args()

    try:
        errors = validate(args.problem, args.original, args.candidate)
    except (OSError, UnicodeError) as exc:
        print(f"input error: {exc}", file=sys.stderr)
        return 2
    if errors:
        for error in errors:
            print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print(f"PASS: preserved {len(THEOREMS[args.problem])} theorem signature(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
