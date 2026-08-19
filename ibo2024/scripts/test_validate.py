#!/usr/bin/env python3
"""Exercise validator failure paths with isolated repository fixtures."""

from __future__ import annotations

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
VALIDATOR = ROOT / "scripts" / "validate.py"


def make_fixture(destination: Path) -> None:
    for filename in ("official-answers.tsv", "task-map.tsv", "WORKERS.md"):
        shutil.copy2(ROOT / filename, destination / filename)
    shutil.copytree(ROOT / "solutions", destination / "solutions")


def run_validator(root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(VALIDATOR), "--root", str(root)],
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
    replace_once(
        root / "WORKERS.md",
        "`solutions/part-a/q02.md`",
        "`solutions/part-a/q01.md`",
    )


def substitute_b19_for_b4(root: Path) -> None:
    q04 = root / "solutions" / "part-b" / "q04.md"
    q19 = root / "solutions" / "part-b" / "q19.md"
    replacement = q19.read_text(encoding="utf-8").replace(
        "# Part B — Task 19", "# Part B — Task 4", 1
    )
    answer_line = next(
        line for line in q04.read_text(encoding="utf-8").splitlines() if "Official answer:" in line
    )
    replacement_lines = replacement.splitlines()
    replacement_lines = [
        answer_line if "Official answer:" in line else line for line in replacement_lines
    ]
    q04.write_text("\n".join(replacement_lines) + "\n", encoding="utf-8")


def duplicate_task_map_coordinate(root: Path) -> None:
    path = root / "task-map.tsv"
    text = path.read_text(encoding="utf-8")
    first_row = next(line for line in text.splitlines() if line.startswith("A\t1\t"))
    path.write_text(text + first_row + "\n", encoding="utf-8")


def omit_task_map_coordinate(root: Path) -> None:
    path = root / "task-map.tsv"
    lines = path.read_text(encoding="utf-8").splitlines()
    path.write_text(
        "\n".join(line for line in lines if not line.startswith("A\t1\t")) + "\n",
        encoding="utf-8",
    )


CASES = (
    ("duplicate worker", duplicate_worker, "worker aliases not unique"),
    ("duplicate output", duplicate_output, "output paths not unique"),
    ("B19 substituted for B4", substitute_b19_for_b4, "does not match task map"),
    ("duplicate task-map coordinate", duplicate_task_map_coordinate, "duplicate coordinate A1"),
    ("missing task-map coordinate", omit_task_map_coordinate, "task map: coordinates differ"),
)


def main() -> int:
    baseline = run_validator(ROOT)
    if baseline.returncode != 0:
        print("BASELINE VALIDATION FAILED")
        print(baseline.stdout, end="")
        print(baseline.stderr, end="", file=sys.stderr)
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
                failures.append(
                    f"{name}: failed without expected message {expected_message!r}\n{output}"
                )
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
