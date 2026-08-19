#!/usr/bin/env python3
"""Validate exact task coverage, identity, ownership, and official answers."""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import sys


EXPECTED_COORDS = {(part, task) for part in ("A", "B") for task in range(1, 51)}


def relative(path: Path, root: Path) -> str:
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path)


def read_three_column_tsv(
    path: Path,
    root: Path,
    label: str,
    value_validator,
    errors: list[str],
) -> dict[tuple[str, int], str]:
    rows: dict[tuple[str, int], str] = {}
    if not path.is_file():
        errors.append(f"missing: {relative(path, root)}")
        return rows

    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw or raw.startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 3:
            errors.append(f"{label}: malformed row {line_number}")
            continue
        part, task_text, value = fields
        if part not in {"A", "B"} or not task_text.isdigit():
            errors.append(f"{label}: malformed coordinate on row {line_number}")
            continue
        coordinate = (part, int(task_text))
        if coordinate in rows:
            errors.append(f"{label}: duplicate coordinate {part}{task_text}")
            continue
        if not value_validator(value):
            errors.append(f"{label}: invalid value on row {line_number}")
            continue
        rows[coordinate] = value

    actual = set(rows)
    if actual != EXPECTED_COORDS:
        missing = ", ".join(f"{part}{task}" for part, task in sorted(EXPECTED_COORDS - actual))
        extra = ", ".join(f"{part}{task}" for part, task in sorted(actual - EXPECTED_COORDS))
        details = []
        if missing:
            details.append(f"missing {missing}")
        if extra:
            details.append(f"extra {extra}")
        errors.append(f"{label}: coordinates differ ({'; '.join(details)})")
    return rows


def normalize_topic(line: str) -> str:
    topic = re.sub(r"^#{2,6}\s+", "", line.strip())
    topic = topic.replace("*", "").replace("`", "")
    return re.sub(r"\s+", " ", topic).strip()


def extract_topic(text: str) -> str:
    for line in text.splitlines()[1:]:
        if line.strip():
            return normalize_topic(line)
    return ""


def validate_workers(root: Path, errors: list[str]) -> None:
    path = root / "WORKERS.md"
    if not path.is_file():
        errors.append("missing: WORKERS.md")
        return

    row_pattern = re.compile(
        r"^\| ([AB]) \| ([0-9]+) \| `([^`]+)` \| ([^|]+?) \| `([^`]+)` \|$"
    )
    rows: list[tuple[tuple[str, int], str, str, str]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        match = row_pattern.match(raw)
        if not match:
            continue
        part, task_text, worker, status, output = match.groups()
        rows.append(((part, int(task_text)), worker, status.strip(), output))

    coordinates = [row[0] for row in rows]
    workers = [row[1] for row in rows]
    outputs = [row[3] for row in rows]
    if len(rows) != 100:
        errors.append(f"worker ledger: found {len(rows)} task rows instead of 100")
    if set(coordinates) != EXPECTED_COORDS or len(coordinates) != len(set(coordinates)):
        errors.append("worker ledger: task coordinates are not exactly A1-A50 and B1-B50 once")
    if len(workers) != len(set(workers)):
        duplicates = sorted(worker for worker, count in Counter(workers).items() if count > 1)
        errors.append(f"worker ledger: worker aliases not unique: {', '.join(duplicates)}")
    if len(outputs) != len(set(outputs)):
        duplicates = sorted(output for output, count in Counter(outputs).items() if count > 1)
        errors.append(f"worker ledger: output paths not unique: {', '.join(duplicates)}")

    for (part, task), _worker, status, output in rows:
        canonical = f"solutions/part-{part.lower()}/q{task:02}.md"
        if status != "completed":
            errors.append(f"worker ledger: {part}{task} status is {status!r}, not 'completed'")
        if output != canonical:
            errors.append(f"worker ledger: {part}{task} output is {output!r}, expected {canonical!r}")


def validate_solutions(
    root: Path,
    official: dict[tuple[str, int], str],
    topics: dict[tuple[str, int], str],
    errors: list[str],
) -> None:
    for part in ("A", "B"):
        directory = root / "solutions" / f"part-{part.lower()}"
        wanted_names = {f"q{task:02}.md" for task in range(1, 51)}
        actual_names = {path.name for path in directory.glob("q*.md")} if directory.is_dir() else set()
        for missing in sorted(wanted_names - actual_names):
            errors.append(f"missing: solutions/part-{part.lower()}/{missing}")
        for extra in sorted(actual_names - wanted_names):
            errors.append(f"unexpected: solutions/part-{part.lower()}/{extra}")

        for task in range(1, 51):
            coordinate = (part, task)
            path = directory / f"q{task:02}.md"
            if not path.is_file():
                continue
            text = path.read_text(encoding="utf-8")
            lines = text.splitlines()
            canonical_heading = f"# Part {part} — Task {task}"
            if not lines or lines[0] != canonical_heading:
                errors.append(f"{relative(path, root)}: first heading is not {canonical_heading!r}")

            topic = extract_topic(text)
            expected_topic = topics.get(coordinate)
            if expected_topic is not None and topic != expected_topic:
                errors.append(
                    f"{relative(path, root)}: topic {topic!r} does not match task map {expected_topic!r}"
                )

            answer_lines = [line for line in lines if "Official answer:" in line]
            if len(answer_lines) != 1:
                errors.append(
                    f"{relative(path, root)}: expected one official answer line, found {len(answer_lines)}"
                )
            else:
                values = re.findall(r"\b(True|False)\b", answer_lines[0], re.IGNORECASE)
                if len(values) != 4:
                    errors.append(
                        f"{relative(path, root)}: official answer line has {len(values)} truth values"
                    )
                else:
                    pattern = "".join("T" if value.lower() == "true" else "F" for value in values)
                    expected_pattern = official.get(coordinate)
                    if expected_pattern is not None and pattern != expected_pattern:
                        errors.append(
                            f"{relative(path, root)}: declared {pattern}, official {expected_pattern}"
                        )

            for label in "ABCD":
                if not re.search(rf"(?m)^\*\*{label}(?:[. —:-]|\*\*)", text):
                    errors.append(f"{relative(path, root)}: missing separate reasoning for {label}")
            if re.search(r"https?://", text):
                errors.append(f"{relative(path, root)}: contains external URL")


def validate(root: Path) -> list[str]:
    errors: list[str] = []
    official = read_three_column_tsv(
        root / "official-answers.tsv",
        root,
        "official key",
        lambda value: re.fullmatch(r"[TF]{4}", value) is not None,
        errors,
    )
    topics = read_three_column_tsv(
        root / "task-map.tsv",
        root,
        "task map",
        lambda value: bool(value.strip()) and value == value.strip(),
        errors,
    )
    validate_workers(root, errors)
    validate_solutions(root, official, topics, errors)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="repository or isolated fixture root",
    )
    args = parser.parse_args()
    errors = validate(args.root.resolve())
    if errors:
        print("VALIDATION FAILED")
        for error in errors:
            print(f"- {error}")
        return 1
    print("VALIDATION PASSED: 100 unique task identities, workers, outputs, and official patterns agree.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
