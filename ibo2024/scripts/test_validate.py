#!/usr/bin/env python3
"""Exercise the complete validator contract with isolated defective fixtures."""

from __future__ import annotations

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SOURCE_DIR = ROOT / "source"
TOP_FILES = (
    "official-answers.tsv",
    "task-map.tsv",
    "reviewed-solutions.sha256",
    "WORKERS.md",
    "README.md",
    "answers.md",
    "theory-a-solutions.md",
    "theory-b-solutions.md",
)


def make_fixture(destination: Path) -> None:
    for filename in TOP_FILES:
        shutil.copy2(ROOT / filename, destination / filename)
    shutil.copytree(ROOT / "solutions", destination / "solutions")
    shutil.copytree(
        ROOT / "scripts",
        destination / "scripts",
        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"),
    )


def run_validator(root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(root / "scripts" / "validate.py"),
            "--root",
            str(root),
            "--source-dir",
            str(SOURCE_DIR),
        ],
        check=False,
        capture_output=True,
        text=True,
    )


def replace_once(path: Path, old: str, new: str) -> None:
    text = path.read_text(encoding="utf-8")
    if old not in text:
        raise AssertionError(f"fixture setup could not find {old!r} in {path}")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


def duplicate_worker(root: Path) -> None:
    replace_once(root / "WORKERS.md", "`ibo_a02`", "`ibo_a01`")


def duplicate_output(root: Path) -> None:
    replace_once(root / "WORKERS.md", "`solutions/part-a/q02.md`", "`solutions/part-a/q01.md`")


def transplant_b19_reasoning_behind_b4_metadata(root: Path) -> None:
    q04 = root / "solutions" / "part-b" / "q04.md"
    q19 = root / "solutions" / "part-b" / "q19.md"
    prefix = q04.read_text(encoding="utf-8").split("## Reasoning", 1)[0]
    reasoning = q19.read_text(encoding="utf-8").split("## Reasoning", 1)[1]
    q04.write_text(prefix + "## Reasoning" + reasoning, encoding="utf-8")


def duplicate_task_map_coordinate(root: Path) -> None:
    path = root / "task-map.tsv"
    text = path.read_text(encoding="utf-8")
    first_row = next(line for line in text.splitlines() if line.startswith("A\t1\t"))
    path.write_text(text + first_row + "\n", encoding="utf-8")


def omit_task_map_coordinate(root: Path) -> None:
    path = root / "task-map.tsv"
    lines = path.read_text(encoding="utf-8").splitlines()
    path.write_text("\n".join(line for line in lines if not line.startswith("A\t1\t")) + "\n", encoding="utf-8")


def drift_key_and_answer_from_pdf(root: Path) -> None:
    replace_once(root / "official-answers.tsv", "B\t4\tTFFF", "B\t4\tFFFF")
    replace_once(root / "solutions" / "part-b" / "q04.md", "A — True;", "A — False;")


def contradict_reasoning_verdict(root: Path) -> None:
    replace_once(root / "solutions" / "part-b" / "q04.md", "**A — True.**", "**A — False.**")


def add_malformed_worker_row(root: Path) -> None:
    path = root / "WORKERS.md"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "| C | 1 | `outside_domain` | completed | `solutions/part-c/q01.md` |\n",
        encoding="utf-8",
    )


def add_no_leading_pipe_worker_row(root: Path) -> None:
    path = root / "WORKERS.md"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "A | 1 | `second_a1_owner` | completed | `solutions/part-a/q01.md` |\n",
        encoding="utf-8",
    )


def add_leading_whitespace_worker_row(root: Path) -> None:
    path = root / "WORKERS.md"
    path.write_text(
        path.read_text(encoding="utf-8")
        + " | A | 1 | `second_a1_owner` | completed | `solutions/part-a/q01.md` |\n",
        encoding="utf-8",
    )


def add_unexpected_solution_file(root: Path) -> None:
    shutil.copy2(
        root / "solutions" / "part-b" / "q19.md",
        root / "solutions" / "part-b" / "copy.md",
    )


def add_nested_solution_copy(root: Path) -> None:
    destination = root / "solutions" / "part-a" / "archive" / "q01.md"
    destination.parent.mkdir()
    shutil.copy2(root / "solutions" / "part-a" / "q01.md", destination)


def add_case_variant_solution_copy(root: Path) -> None:
    destination = root / "solutions" / "part-a" / "archive" / "q01.MD"
    destination.parent.mkdir()
    shutil.copy2(root / "solutions" / "part-a" / "q01.md", destination)


def stale_answer_summary(root: Path) -> None:
    path = root / "answers.md"
    path.write_text(path.read_text(encoding="utf-8") + "\nStale manual edit.\n", encoding="utf-8")


def wrong_answer_summary_pattern(root: Path) -> None:
    replace_once(
        root / "answers.md",
        "| A1 | False | False | True | True |",
        "| A1 | True | False | True | True |",
    )


def remove_consolidated_task(root: Path) -> None:
    path = root / "theory-a-solutions.md"
    text = path.read_text(encoding="utf-8")
    start = text.index('<a id="part-a-task-25"></a>')
    end = text.index('<a id="part-a-task-26"></a>')
    path.write_text(text[:start] + text[end:], encoding="utf-8")


def reorder_consolidated_tasks(root: Path) -> None:
    path = root / "theory-a-solutions.md"
    text = path.read_text(encoding="utf-8")
    start_24 = text.index('<a id="part-a-task-24"></a>')
    start_25 = text.index('<a id="part-a-task-25"></a>')
    start_26 = text.index('<a id="part-a-task-26"></a>')
    block_24 = text[start_24:start_25]
    block_25 = text[start_25:start_26]
    path.write_text(text[:start_24] + block_25 + block_24 + text[start_26:], encoding="utf-8")


def duplicate_consolidated_anchor(root: Path) -> None:
    replace_once(
        root / "theory-a-solutions.md",
        '<a id="part-a-task-26"></a>',
        '<a id="part-a-task-25"></a>',
    )


def break_answer_link(root: Path) -> None:
    replace_once(
        root / "answers.md",
        "theory-a-solutions.md#part-a-task-1",
        "theory-a-solutions.md#part-a-task-999",
    )


def remove_readme_attribution(root: Path) -> None:
    path = root / "README.md"
    path.write_text(
        path.read_text(encoding="utf-8").replace("International Biology Olympiad", "the competition", 2),
        encoding="utf-8",
    )


def remove_readme_license(root: Path) -> None:
    path = root / "README.md"
    path.write_text(path.read_text(encoding="utf-8").replace("CC BY-NC-SA 4.0", "the project license"), encoding="utf-8")


def redirect_readme_summary(root: Path) -> None:
    replace_once(
        root / "README.md",
        "[Official answer summary](answers.md)",
        "[Official answer summary](theory-a-solutions.md)",
    )


def duplicate_readme_summary_label(root: Path) -> None:
    path = root / "README.md"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "\n[Official answer summary](theory-a-solutions.md)\n",
        encoding="utf-8",
    )


def replace_readme_summary_with_image(root: Path) -> None:
    replace_once(
        root / "README.md",
        "[Official answer summary](answers.md)",
        "![Official answer summary](answers.md)",
    )


def replace_readme_summary_with_code(root: Path) -> None:
    replace_once(
        root / "README.md",
        "[Official answer summary](answers.md)",
        "`[Official answer summary](answers.md)`",
    )


CASES = (
    ("duplicate worker", duplicate_worker, "worker aliases not unique"),
    ("duplicate output", duplicate_output, "output paths not unique"),
    ("hidden B19 reasoning behind B4 metadata", transplant_b19_reasoning_behind_b4_metadata, "reviewed manifest: hash mismatch"),
    ("duplicate task-map coordinate", duplicate_task_map_coordinate, "duplicate coordinate A1"),
    ("missing task-map coordinate", omit_task_map_coordinate, "task map: coordinates differ"),
    ("coordinated key drift from PDF", drift_key_and_answer_from_pdf, "official key B4 differs from embedded PDF"),
    ("contradictory reasoning verdict", contradict_reasoning_verdict, "reasoning verdicts FFFF do not match official line TFFF"),
    ("malformed extra worker row", add_malformed_worker_row, "worker ledger: malformed data row"),
    ("no-leading-pipe worker row", add_no_leading_pipe_worker_row, "worker ledger: malformed data row"),
    ("leading-whitespace worker row", add_leading_whitespace_worker_row, "worker ledger: malformed data row"),
    ("unexpected solution Markdown", add_unexpected_solution_file, "unexpected solution Markdown file"),
    (
        "nested duplicate solution Markdown",
        add_nested_solution_copy,
        "unexpected solution Markdown file: solutions/part-a/archive/q01.md",
    ),
    (
        "case-variant duplicate solution Markdown",
        add_case_variant_solution_copy,
        "unexpected solution Markdown file: solutions/part-a/archive/q01.MD",
    ),
    ("stale answer summary", stale_answer_summary, "stale generated file: answers.md"),
    ("wrong answer-summary pattern", wrong_answer_summary_pattern, "answers.md: A1 values disagree with official key"),
    ("missing consolidated task", remove_consolidated_task, "anchors are not exactly 1-50 once in order"),
    ("reordered consolidated tasks", reorder_consolidated_tasks, "anchors are not exactly 1-50 once in order"),
    ("duplicate consolidated anchor", duplicate_consolidated_anchor, "anchors are not exactly 1-50 once in order"),
    ("broken answer link", break_answer_link, "answers.md: A1 consolidated link is not canonical"),
    ("missing README attribution", remove_readme_attribution, "README.md: missing required IBO source attribution"),
    ("missing README license", remove_readme_license, "README.md: missing required license"),
    (
        "wrong existing README target",
        redirect_readme_summary,
        "README.md: canonical link for 'Official answer summary' must occur exactly once",
    ),
    (
        "additive duplicate README label",
        duplicate_readme_summary_label,
        "README.md: canonical link for 'Official answer summary' must occur exactly once",
    ),
    (
        "README image is not navigation",
        replace_readme_summary_with_image,
        "README.md: canonical link for 'Official answer summary' must occur exactly once",
    ),
    (
        "README code span is not navigation",
        replace_readme_summary_with_code,
        "README.md: canonical link for 'Official answer summary' must occur exactly once",
    ),
)


def main() -> int:
    baseline = run_validator(ROOT)
    if baseline.returncode != 0:
        print("BASELINE VALIDATION FAILED")
        print(baseline.stdout, end="")
        print(baseline.stderr, end="", file=sys.stderr)
        return 1
    with tempfile.TemporaryDirectory(prefix="ibo-validator-pristine-") as temporary:
        pristine_fixture = Path(temporary)
        make_fixture(pristine_fixture)
        pristine = run_validator(pristine_fixture)
        if pristine.returncode != 0:
            print("PRISTINE FIXTURE VALIDATION FAILED")
            print(pristine.stdout, end="")
            print(pristine.stderr, end="", file=sys.stderr)
            return 1
    failures: list[str] = []
    for name, mutate, expected_message in CASES:
        with tempfile.TemporaryDirectory(prefix="ibo-validator-") as temporary:
            fixture = Path(temporary)
            make_fixture(fixture)
            mutate(fixture)
            result = run_validator(fixture)
            output = result.stdout + result.stderr
            if result.returncode == 0:
                failures.append(f"{name}: validator unexpectedly passed")
            elif expected_message not in output:
                failures.append(f"{name}: missing expected diagnostic {expected_message!r}\n{output}")
            else:
                print(f"EXPECTED FAILURE PASS: {name}")
    if failures:
        print("NEGATIVE VALIDATION TESTS FAILED")
        for failure in failures:
            print(f"- {failure}")
        return 1
    print(f"NEGATIVE VALIDATION TESTS PASSED: {len(CASES)} fixtures rejected.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
