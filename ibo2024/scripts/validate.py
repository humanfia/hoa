#!/usr/bin/env python3
"""Validate the complete offline IBO 2024 theory solution collection."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import os
from pathlib import Path
import re
import stat
import subprocess
import sys

from build import check_outputs, load_solutions, render_outputs, truth_words


EXPECTED_COORDS = [(part, task) for part in ("A", "B") for task in range(1, 51)]
EXPECTED_SET = set(EXPECTED_COORDS)
ANSWER_BLOCK = re.compile(r"(?m)^\s*Task\s+#(\d+)\.?\s*$")
SOURCE_VERDICT = re.compile(
    r"(?m)^\s*(?:(?:[A-D][.)]?)|[.•])?\s*(TRUE|FALSE)\b"
)
REASONING_VERDICT = re.compile(
    r"(?mi)^\*\*([ABCD])(?:\s*[.:\-—])?\s*(True|False)\b"
)


def rel(path: Path, root: Path) -> str:
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path)


def markdown_links(text: str) -> list[tuple[str, str]]:
    """Return inline Markdown links, excluding images and code regions."""
    text = re.sub(r"<!--.*?-->", "", text, flags=re.DOTALL)
    visible_lines: list[str] = []
    fence_character: str | None = None
    fence_length = 0
    for line in text.splitlines():
        stripped = line.lstrip()
        indent = len(line) - len(stripped)
        fence = re.match(r"(`{3,}|~{3,})", stripped) if indent <= 3 else None
        if fence_character is not None:
            closing = re.fullmatch(
                rf"{re.escape(fence_character)}{{{fence_length},}}[ \t]*",
                stripped,
            )
            if closing:
                fence_character = None
                fence_length = 0
            continue
        if fence:
            marker = fence.group(1)
            fence_character = marker[0]
            fence_length = len(marker)
            continue
        if line.startswith(("    ", "\t")):
            continue
        visible_lines.append(line)

    visible_text = "\n".join(visible_lines)
    visible_text = re.sub(r"(`+).*?\1", "", visible_text, flags=re.DOTALL)
    return re.findall(r"(?<!!)\[([^]\n]+)\]\(([^)\n]+)\)", visible_text)


def markdown_section_lines(text: str, heading: str) -> list[str] | None:
    """Return the nonblank lines in one unique level-two Markdown section."""
    lines = text.splitlines()
    if lines.count(heading) != 1:
        return None
    start = lines.index(heading) + 1
    end = next(
        (index for index in range(start, len(lines)) if lines[index].startswith("## ")),
        len(lines),
    )
    return [line for line in lines[start:end] if line.strip()]


def read_tsv(
    path: Path,
    root: Path,
    label: str,
    value_validator,
    errors: list[str],
) -> dict[tuple[str, int], str]:
    rows: dict[tuple[str, int], str] = {}
    if not path.is_file():
        errors.append(f"missing: {rel(path, root)}")
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
    if actual != EXPECTED_SET:
        missing = ", ".join(f"{part}{task}" for part, task in sorted(EXPECTED_SET - actual))
        extra = ", ".join(f"{part}{task}" for part, task in sorted(actual - EXPECTED_SET))
        details = [value for value in (f"missing {missing}" if missing else "", f"extra {extra}" if extra else "") if value]
        errors.append(f"{label}: coordinates differ ({'; '.join(details)})")
    return rows


def extract_embedded_answers(
    source_dir: Path, errors: list[str]
) -> dict[tuple[str, int], str]:
    embedded: dict[tuple[str, int], str] = {}
    for part in ("A", "B"):
        pdf = source_dir / f"IBO2024 Theory {part}.pdf"
        extract = source_dir / f"part-{part.lower()}.txt"
        if not pdf.is_file():
            errors.append(f"missing local official source: {pdf}")
            continue
        try:
            result = subprocess.run(
                ["pdftotext", "-layout", str(pdf), "-"],
                check=False,
                capture_output=True,
            )
        except OSError as error:
            errors.append(f"could not run pdftotext: {error}")
            continue
        if result.returncode != 0:
            errors.append(f"pdftotext failed for official Part {part} PDF")
            continue
        pdf_bytes = result.stdout
        if not extract.is_file():
            errors.append(f"missing local official extract: {extract}")
        elif extract.read_bytes() != pdf_bytes:
            errors.append(f"official Part {part} text extract differs from pdftotext -layout output")
        text = pdf_bytes.decode("utf-8")
        markers = list(ANSWER_BLOCK.finditer(text))
        coordinates = [int(marker.group(1)) for marker in markers]
        if coordinates != list(range(1, 51)):
            errors.append(f"official Part {part} embedded answer tasks are not exactly 1-50 in order")
            continue
        for index, marker in enumerate(markers):
            end = markers[index + 1].start() if index + 1 < len(markers) else len(text)
            verdicts = SOURCE_VERDICT.findall(text[marker.end() : end])[:4]
            if len(verdicts) != 4:
                errors.append(f"official Part {part} Task {marker.group(1)} has {len(verdicts)} parsed verdicts")
                continue
            embedded[(part, int(marker.group(1)))] = "".join(
                "T" if verdict == "TRUE" else "F" for verdict in verdicts
            )
    if set(embedded) != EXPECTED_SET:
        errors.append(f"embedded official answers: parsed {len(embedded)} of 100 coordinates")
    return embedded


def validate_official_key(
    official: dict[tuple[str, int], str],
    embedded: dict[tuple[str, int], str],
    errors: list[str],
) -> None:
    for coordinate in EXPECTED_COORDS:
        if coordinate in official and coordinate in embedded and official[coordinate] != embedded[coordinate]:
            part, task = coordinate
            errors.append(
                f"official key {part}{task} differs from embedded PDF: "
                f"{official[coordinate]} != {embedded[coordinate]}"
            )


def canonical_paths() -> list[str]:
    return [f"solutions/part-{part.lower()}/q{task:02}.md" for part, task in EXPECTED_COORDS]


def validate_manifest(root: Path, errors: list[str]) -> None:
    path = root / "reviewed-solutions.sha256"
    if not path.is_file():
        errors.append("missing: reviewed-solutions.sha256")
        return
    parsed: list[tuple[str, str]] = []
    row_pattern = re.compile(r"^([0-9a-f]{64})  (solutions/part-[ab]/q[0-9]{2}\.md)$")
    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        match = row_pattern.fullmatch(raw)
        if not match:
            errors.append(f"reviewed manifest: malformed row {line_number}")
            continue
        parsed.append((match.group(2), match.group(1)))
    paths = [row[0] for row in parsed]
    expected = canonical_paths()
    if paths != expected:
        errors.append("reviewed manifest: paths are not exactly the 100 canonical solutions in order")
    if len(paths) != len(set(paths)):
        errors.append("reviewed manifest: duplicate paths")
    for relative_path, expected_hash in parsed:
        solution = root / relative_path
        if not solution.is_file():
            continue
        actual_hash = hashlib.sha256(solution.read_bytes()).hexdigest()
        if actual_hash != expected_hash:
            errors.append(f"reviewed manifest: hash mismatch for {relative_path}")


def validate_workers(root: Path, errors: list[str]) -> None:
    path = root / "WORKERS.md"
    if not path.is_file():
        errors.append("missing: WORKERS.md")
        return
    lines = path.read_text(encoding="utf-8").splitlines()
    table_header = "| Part | Task | Worker | Status | Output |"
    table_separator = "|---|---:|---|---|---|"
    canonical_prefix = [
        "# Worker Ledger",
        "",
        "Each row is a distinct one-problem assignment. Workers must remain offline and use the embedded official answer in the corresponding local PDF.",
        "",
        table_header,
        table_separator,
    ]
    if (
        lines[: len(canonical_prefix)] != canonical_prefix
        or len(lines) != len(canonical_prefix) + 100
        or lines.count(table_header) != 1
        or lines.count(table_separator) != 1
    ):
        errors.append(
            "worker ledger: document is not exactly canonical preamble and 100-row table"
        )
    try:
        header = lines.index(table_header)
    except ValueError:
        errors.append("worker ledger: missing canonical table header")
        return
    if header + 1 >= len(lines) or lines[header + 1] != table_separator:
        errors.append("worker ledger: missing canonical table separator")
        return
    row_pattern = re.compile(
        r"^\| ([AB]) \| ([0-9]+) \| `([^`]+)` \| ([^|]+?) \| `([^`]+)` \|$"
    )
    rows: list[tuple[tuple[str, int], str, str, str]] = []
    for line_number, raw in enumerate(lines[header + 2 :], header + 3):
        if not raw.strip():
            continue
        match = row_pattern.fullmatch(raw)
        if not match:
            errors.append(f"worker ledger: malformed data row {line_number}")
            continue
        part, task_text, worker, status, output = match.groups()
        rows.append(((part, int(task_text)), worker, status.strip(), output))
    coordinates = [row[0] for row in rows]
    workers = [row[1] for row in rows]
    outputs = [row[3] for row in rows]
    if coordinates != EXPECTED_COORDS:
        errors.append("worker ledger: rows are not exactly A1-A50 then B1-B50")
    if len(coordinates) != len(set(coordinates)):
        errors.append("worker ledger: task coordinates not unique")
    if len(workers) != len(set(workers)):
        duplicates = sorted(value for value, count in Counter(workers).items() if count > 1)
        errors.append(f"worker ledger: worker aliases not unique: {', '.join(duplicates)}")
    if len(outputs) != len(set(outputs)):
        duplicates = sorted(value for value, count in Counter(outputs).items() if count > 1)
        errors.append(f"worker ledger: output paths not unique: {', '.join(duplicates)}")
    for (part, task), _worker, status, output in rows:
        canonical = f"solutions/part-{part.lower()}/q{task:02}.md"
        if (part, task) not in EXPECTED_SET:
            errors.append(f"worker ledger: out-of-domain coordinate {part}{task}")
        if status != "completed":
            errors.append(f"worker ledger: {part}{task} status is not completed")
        if output != canonical:
            errors.append(f"worker ledger: {part}{task} output is not canonical")


def normalize_topic(line: str) -> str:
    topic = re.sub(r"^#{2,6}\s+", "", line.strip()).replace("*", "").replace("`", "")
    return re.sub(r"\s+", " ", topic).strip()


def answer_pattern(answer_line: str) -> str | None:
    values = re.findall(r"\b(True|False)\b", answer_line, re.IGNORECASE)
    if len(values) != 4:
        return None
    return "".join("T" if value.lower() == "true" else "F" for value in values)


def validate_solutions(
    root: Path,
    official: dict[tuple[str, int], str],
    topics: dict[tuple[str, int], str],
    errors: list[str],
) -> None:
    solutions_root = root / "solutions"
    if solutions_root.is_symlink():
        errors.append("solution root must be a real directory, not a symlink")
        return
    if not solutions_root.is_dir():
        errors.append("missing: solutions")
        return

    expected_paths = set(canonical_paths())
    inventory_entries: list[Path] = []
    for directory, subdirectories, filenames in os.walk(solutions_root, followlinks=False):
        current = Path(directory)
        inventory_entries.extend(
            current / name
            for name in subdirectories
            if (current / name).is_symlink()
        )
        inventory_entries.extend(current / name for name in filenames)
    actual_paths = {
        rel(path, root)
        for path in inventory_entries
    }
    for missing in sorted(expected_paths - actual_paths):
        errors.append(f"missing: {missing}")
    for unexpected in sorted(actual_paths - expected_paths):
        errors.append(f"unexpected solution Markdown file: {unexpected}")
    for solution_path in inventory_entries:
        if solution_path.is_symlink():
            errors.append(f"solution path is a symlink: {rel(solution_path, root)}")
    for expected in sorted(expected_paths & actual_paths):
        if not stat.S_ISREG((root / expected).lstat().st_mode):
            errors.append(f"solution path is not a regular file: {expected}")

    bodies: dict[str, str] = {}
    for part in ("A", "B"):
        directory = root / "solutions" / f"part-{part.lower()}"
        for task in range(1, 51):
            coordinate = (part, task)
            path = directory / f"q{task:02}.md"
            if not path.is_file():
                continue
            relative_path = rel(path, root)
            text = path.read_text(encoding="utf-8")
            lines = text.splitlines()
            heading = f"# Part {part} — Task {task}"
            if not lines or lines[0] != heading:
                errors.append(f"{relative_path}: first heading is not canonical")
            topic_line = next((line for line in lines[1:] if line.strip()), "")
            topic = normalize_topic(topic_line)
            if coordinate in topics and topic != topics[coordinate]:
                errors.append(f"{relative_path}: topic does not match task map")
            answer_lines = [line for line in lines if "Official answer:" in line]
            declared = None
            if len(answer_lines) != 1:
                errors.append(f"{relative_path}: expected exactly one official answer line")
            else:
                declared = answer_pattern(answer_lines[0])
                if declared is None:
                    errors.append(f"{relative_path}: official answer line does not contain four verdicts")
                elif coordinate in official and declared != official[coordinate]:
                    errors.append(f"{relative_path}: declared {declared}, official {official[coordinate]}")
            verdicts = REASONING_VERDICT.findall(text)
            labels = [label.upper() for label, _value in verdicts]
            reasoning_pattern = "".join(
                "T" if value.lower() == "true" else "F" for _label, value in verdicts
            )
            if labels != list("ABCD"):
                errors.append(f"{relative_path}: reasoning labels are not exactly A-D once in order")
            elif declared is not None and reasoning_pattern != declared:
                errors.append(
                    f"{relative_path}: reasoning verdicts {reasoning_pattern} do not match official line {declared}"
                )
            if text.count("## Reasoning") != 1:
                errors.append(f"{relative_path}: expected exactly one reasoning heading")
            else:
                body = re.sub(r"\s+", " ", text.split("## Reasoning", 1)[1]).strip()
                if body in bodies:
                    errors.append(f"duplicate normalized reasoning body: {bodies[body]} and {relative_path}")
                else:
                    bodies[body] = relative_path
            if re.search(r"https?://", text):
                errors.append(f"{relative_path}: contains external URL")


def validate_answers(root: Path, official: dict[tuple[str, int], str], errors: list[str]) -> None:
    path = root / "answers.md"
    if not path.is_file():
        errors.append("missing: answers.md")
        return
    row_pattern = re.compile(
        r"^\| ([AB])([0-9]+) \| (True|False) \| (True|False) \| "
        r"(True|False) \| (True|False) \| \[Solution\]\(([^)]+)\) \| "
        r"\[Part ([AB]) §([0-9]+)\]\(([^#)]+)#([^)]+)\) \|$"
    )
    rows = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        match = row_pattern.fullmatch(raw)
        if match:
            rows.append(match.groups())
    coords = [(row[0], int(row[1])) for row in rows]
    if coords != EXPECTED_COORDS:
        errors.append("answers.md: rows are not exactly A1-A50 then B1-B50")
    for row in rows:
        part, task_text, a, b, c, d, individual, linked_part, linked_task, volume, anchor = row
        task = int(task_text)
        coordinate = (part, task)
        values = [a, b, c, d]
        if coordinate in official and values != truth_words(official[coordinate]):
            errors.append(f"answers.md: {part}{task} values disagree with official key")
        expected_individual = f"solutions/part-{part.lower()}/q{task:02}.md"
        expected_volume = f"theory-{part.lower()}-solutions.md"
        expected_anchor = f"part-{part.lower()}-task-{task}"
        if individual != expected_individual:
            errors.append(f"answers.md: {part}{task} individual link is not canonical")
        if (linked_part, int(linked_task), volume, anchor) != (part, task, expected_volume, expected_anchor):
            errors.append(f"answers.md: {part}{task} consolidated link is not canonical")


def validate_consolidated(root: Path, part: str, errors: list[str]) -> None:
    name = f"theory-{part.lower()}-solutions.md"
    path = root / name
    if not path.is_file():
        errors.append(f"missing: {name}")
        return
    text = path.read_text(encoding="utf-8")
    try:
        solutions = [solution for solution in load_solutions(root) if solution.part == part]
    except (OSError, KeyError, ValueError):
        return
    anchors = re.findall(rf'<a id="part-{part.lower()}-task-([0-9]+)"></a>', text)
    if anchors != [str(task) for task in range(1, 51)]:
        errors.append(f"{name}: anchors are not exactly 1-50 once in order")
    toc = re.findall(rf"^([0-9]+)\. \[Task [0-9]+ — .*\]\(#part-{part.lower()}-task-([0-9]+)\)$", text, re.M)
    if toc != [(str(task), str(task)) for task in range(1, 51)]:
        errors.append(f"{name}: contents links are not exactly 1-50 once in order")
    sections = list(re.finditer(r"(?m)^## Task ([0-9]+) — (.+)$", text))
    if [int(section.group(1)) for section in sections] != list(range(1, 51)):
        errors.append(f"{name}: task sections are not exactly 1-50 once in order")
        return
    for index, section in enumerate(sections):
        solution = solutions[index]
        end = sections[index + 1].start() if index + 1 < len(sections) else len(text)
        section_text = text[section.start() : end]
        if section.group(2) != solution.topic:
            errors.append(f"{name}: Task {solution.task} topic disagrees with task map")
        if solution.answer_line not in section_text:
            errors.append(f"{name}: Task {solution.task} official answer is missing or changed")
        if solution.reasoning not in section_text:
            errors.append(f"{name}: Task {solution.task} reasoning is incomplete or changed")


def validate_readme(root: Path, errors: list[str]) -> None:
    path = root / "README.md"
    if not path.is_file():
        errors.append("missing: README.md")
        return
    text = path.read_text(encoding="utf-8")
    if "<!--" in text or "-->" in text:
        errors.append("README.md: HTML comments are not allowed")
    if re.search(r"(?m)^[ \t]{0,3}</?[A-Za-z][A-Za-z0-9-]*(?:[ \t][^>]*)?>", text):
        errors.append("README.md: raw HTML blocks are not allowed")

    collection_items = [
        "- [Official answer summary](answers.md)",
        "- [Theory Part A consolidated solutions](theory-a-solutions.md)",
        "- [Theory Part B consolidated solutions](theory-b-solutions.md)",
        "- [Part A individual solutions](solutions/part-a/)",
        "- [Part B individual solutions](solutions/part-b/)",
        "- [One-worker assignment ledger](WORKERS.md)",
    ]
    if markdown_section_lines(text, "## Read the collection") != collection_items:
        errors.append("README.md: Read the collection navigation list is not canonical")

    structure_items = [
        "- `solutions/part-a/` and `solutions/part-b/`: the 100 independently authored source solutions.",
        "- `official-answers.tsv`: official A-D patterns derived from the embedded answer sections.",
        "- `task-map.tsv`: canonical source-grounded topic identity for every coordinate.",
        "- `reviewed-solutions.sha256`: integrity manifest for the source-reviewed solution corpus.",
        "- `answers.md`: generated 100-row answer and navigation index.",
        "- `theory-a-solutions.md` and `theory-b-solutions.md`: generated ordered volumes.",
        "- [scripts/build.py](scripts/build.py): deterministic collection builder and freshness check.",
        "- [scripts/validate.py](scripts/validate.py): end-to-end offline source, ownership, content, document, and navigation validator.",
        "- [scripts/test_validate.py](scripts/test_validate.py): isolated negative fixtures for the validation contract.",
    ]
    if markdown_section_lines(text, "## Repository structure") != structure_items:
        errors.append("README.md: Repository structure list is not canonical")

    requirements = {
        "IBO source attribution": "International Biology Olympiad",
        "license": "CC BY-NC-SA 4.0",
        "attribution obligation": "attribution",
        "noncommercial obligation": "noncommercial",
        "share-alike obligation": "share-alike",
        "offline methodology": "offline",
        "one-worker ownership": "Exactly one distinct",
        "Theory A source filename": "source/IBO2024 Theory A.pdf",
        "Theory B source filename": "source/IBO2024 Theory B.pdf",
        "discrepancy policy": "discrepancy note",
        "manifest review rule": "Do not update a hash merely to make validation pass",
        "build command": "python scripts/build.py",
        "build check command": "python scripts/build.py --check",
        "validation command": "python scripts/validate.py",
        "negative-test command": "python scripts/test_validate.py",
    }
    for label, phrase in requirements.items():
        if phrase not in text:
            errors.append(f"README.md: missing required {label}")
    required_links = (
        ("Official answer summary", "answers.md"),
        ("Theory Part A consolidated solutions", "theory-a-solutions.md"),
        ("Theory Part B consolidated solutions", "theory-b-solutions.md"),
        ("Part A individual solutions", "solutions/part-a/"),
        ("Part B individual solutions", "solutions/part-b/"),
        ("One-worker assignment ledger", "WORKERS.md"),
        ("scripts/build.py", "scripts/build.py"),
        ("scripts/validate.py", "scripts/validate.py"),
        ("scripts/test_validate.py", "scripts/test_validate.py"),
    )
    parsed_links = markdown_links(text)
    readme_lines = text.splitlines()
    for label, target in required_links:
        targets = [link_target for link_label, link_target in parsed_links if link_label == label]
        canonical_line = f"- [{label}]({target})"
        canonical_lines = sum(
            line == canonical_line or line.startswith(canonical_line + ":")
            for line in readme_lines
        )
        if targets != [target] or canonical_lines != 1:
            errors.append(
                f"README.md: canonical link for {label!r} must occur exactly once"
            )


def validate_links(root: Path, errors: list[str]) -> None:
    for name in ("README.md", "answers.md", "theory-a-solutions.md", "theory-b-solutions.md"):
        path = root / name
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        local_anchors = set(re.findall(r'<a id="([^"]+)"></a>', text))
        for _label, target in markdown_links(text):
            if target.startswith(("http://", "https://")):
                continue
            if target.startswith("#"):
                if target[1:] not in local_anchors:
                    errors.append(f"{name}: broken internal link {target}")
                continue
            file_text, separator, anchor = target.partition("#")
            destination = root / file_text
            if not destination.exists():
                errors.append(f"{name}: broken file link {file_text}")
            elif separator and destination.is_file():
                destination_text = destination.read_text(encoding="utf-8")
                if f'<a id="{anchor}"></a>' not in destination_text:
                    errors.append(f"{name}: broken anchor link {target}")


def validate_generated(root: Path, errors: list[str]) -> None:
    try:
        outputs = render_outputs(root)
    except (OSError, KeyError, ValueError) as error:
        errors.append(f"could not render generated documents: {error}")
        return
    errors.extend(check_outputs(root, outputs))


def validate(root: Path, source_dir: Path) -> list[str]:
    errors: list[str] = []
    official = read_tsv(
        root / "official-answers.tsv",
        root,
        "official key",
        lambda value: re.fullmatch(r"[TF]{4}", value) is not None,
        errors,
    )
    topics = read_tsv(
        root / "task-map.tsv",
        root,
        "task map",
        lambda value: bool(value.strip()) and value == value.strip(),
        errors,
    )
    embedded = extract_embedded_answers(source_dir, errors)
    validate_official_key(official, embedded, errors)
    validate_manifest(root, errors)
    validate_workers(root, errors)
    validate_solutions(root, official, topics, errors)
    validate_answers(root, official, errors)
    validate_consolidated(root, "A", errors)
    validate_consolidated(root, "B", errors)
    validate_readme(root, errors)
    validate_links(root, errors)
    validate_generated(root, errors)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--source-dir", type=Path, help="directory containing the two local official PDFs")
    args = parser.parse_args()
    root = args.root.resolve()
    source_dir = args.source_dir.resolve() if args.source_dir else root / "source"
    errors = validate(root, source_dir)
    if errors:
        print("VALIDATION FAILED")
        for error in errors:
            print(f"- {error}")
        return 1
    print(
        "VALIDATION PASSED: 100 source-reviewed tasks agree with the embedded PDF key, "
        "ownership ledger, answer index, consolidated volumes, and provenance contract."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
