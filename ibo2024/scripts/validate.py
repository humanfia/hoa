#!/usr/bin/env python3
"""Validate coverage, structure, and official-key agreement."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
KEY = ROOT / "official-answers.tsv"

expected = {}
for raw in KEY.read_text(encoding="utf-8").splitlines():
    if not raw or raw.startswith("#"):
        continue
    part, task, pattern = raw.split("\t")
    expected[(part, int(task))] = pattern

errors = []
seen = set()
for part in ("A", "B"):
    directory = ROOT / "solutions" / f"part-{part.lower()}"
    actual_files = sorted(directory.glob("q*.md"))
    wanted_names = {f"q{i:02}.md" for i in range(1, 51)}
    actual_names = {p.name for p in actual_files}
    for missing in sorted(wanted_names - actual_names):
        errors.append(f"missing: solutions/part-{part.lower()}/{missing}")
    for extra in sorted(actual_names - wanted_names):
        errors.append(f"unexpected: solutions/part-{part.lower()}/{extra}")

    for task in range(1, 51):
        path = directory / f"q{task:02}.md"
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        seen.add((part, task))
        if not re.search(rf"^# Part {part} .+ Task {task}\s*$", text, re.M):
            errors.append(f"{path.relative_to(ROOT)}: missing/correct title")
        answer_line = next(
            (line for line in text.splitlines() if "Official answer:" in line),
            "",
        )
        values = re.findall(r"\b(True|False)\b", answer_line, re.I)
        if len(values) != 4:
            errors.append(
                f"{path.relative_to(ROOT)}: official answer line has {len(values)} truth values"
            )
        else:
            pattern = "".join("T" if v.lower() == "true" else "F" for v in values)
            if pattern != expected[(part, task)]:
                errors.append(
                    f"{path.relative_to(ROOT)}: declared {pattern}, official {expected[(part, task)]}"
                )
        for label in "ABCD":
            if not re.search(rf"(?m)^\*\*{label}(?:[. —:-]|\*\*)", text):
                errors.append(f"{path.relative_to(ROOT)}: missing separate reasoning for {label}")
        if re.search(r"https?://", text):
            errors.append(f"{path.relative_to(ROOT)}: contains external URL")

if len(expected) != 100:
    errors.append(f"official key has {len(expected)} entries instead of 100")

if errors:
    print("VALIDATION FAILED")
    for error in errors:
        print(f"- {error}")
    sys.exit(1)

print("VALIDATION PASSED: 100 task files, structures, and official answer patterns agree.")
