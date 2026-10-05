#!/usr/bin/env python3
"""Build the answer index and consolidated IBO 2024 theory solutions."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
OUTPUT_NAMES = ("answers.md", "theory-a-solutions.md", "theory-b-solutions.md")
ATTRIBUTION = (
    "Source: the International Biology Olympiad (IBO) official English 2024 "
    "Theoretical Exam, Parts A and B, including the embedded official solutions."
)
LICENSE = (
    "The source material and this derived solution collection are shared under "
    "CC BY-NC-SA 4.0: attribution is required, use is noncommercial, and adaptations "
    "must be shared under the same license."
)


@dataclass(frozen=True)
class Solution:
    part: str
    task: int
    topic: str
    pattern: str
    answer_line: str
    reasoning: str
    relative_path: str

    @property
    def coordinate(self) -> str:
        return f"{self.part}{self.task}"

    @property
    def anchor(self) -> str:
        return f"part-{self.part.lower()}-task-{self.task}"

    @property
    def consolidated_name(self) -> str:
        return f"theory-{self.part.lower()}-solutions.md"


def read_three_column_tsv(path: Path) -> dict[tuple[str, int], str]:
    rows: dict[tuple[str, int], str] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        if not raw or raw.startswith("#"):
            continue
        part, task_text, value = raw.split("\t")
        coordinate = (part, int(task_text))
        if coordinate in rows:
            raise ValueError(f"duplicate coordinate in {path.name}: {part}{task_text}")
        rows[coordinate] = value
    return rows


def normalize_topic(line: str) -> str:
    topic = re.sub(r"^#{2,6}\s+", "", line.strip())
    topic = topic.replace("*", "").replace("`", "")
    return re.sub(r"\s+", " ", topic).strip()


def load_solutions(root: Path) -> list[Solution]:
    topics = read_three_column_tsv(root / "task-map.tsv")
    patterns = read_three_column_tsv(root / "official-answers.tsv")
    solutions: list[Solution] = []
    for part in ("A", "B"):
        for task in range(1, 51):
            coordinate = (part, task)
            relative_path = f"solutions/part-{part.lower()}/q{task:02}.md"
            text = (root / relative_path).read_text(encoding="utf-8")
            lines = text.splitlines()
            topic_line = next(line for line in lines[1:] if line.strip())
            topic = normalize_topic(topic_line)
            if topic != topics[coordinate]:
                raise ValueError(f"{relative_path}: topic does not match task-map.tsv")
            answer_lines = [line for line in lines if "Official answer:" in line]
            if len(answer_lines) != 1:
                raise ValueError(f"{relative_path}: expected exactly one official answer line")
            marker = "## Reasoning"
            if text.count(marker) != 1:
                raise ValueError(f"{relative_path}: expected exactly one reasoning heading")
            reasoning = text.split(marker, 1)[1].strip()
            solutions.append(
                Solution(
                    part=part,
                    task=task,
                    topic=topic,
                    pattern=patterns[coordinate],
                    answer_line=answer_lines[0],
                    reasoning=reasoning,
                    relative_path=relative_path,
                )
            )
    return solutions


def truth_words(pattern: str) -> list[str]:
    return ["True" if value == "T" else "False" for value in pattern]


def render_answers(solutions: list[Solution]) -> str:
    lines = [
        "# IBO 2024 Theory A/B — Official Answer Summary",
        "",
        ATTRIBUTION,
        "",
        LICENSE,
        "",
        "The rows are ordered A1–A50, then B1–B50. Each answer is linked to its "
        "individual worked solution and its section in the consolidated volume.",
        "",
        "| Task | A | B | C | D | Individual solution | Consolidated solution |",
        "|---|---|---|---|---|---|---|",
    ]
    for solution in solutions:
        a, b, c, d = truth_words(solution.pattern)
        lines.append(
            f"| {solution.coordinate} | {a} | {b} | {c} | {d} | "
            f"[Solution]({solution.relative_path}) | "
            f"[Part {solution.part} §{solution.task}]"
            f"({solution.consolidated_name}#{solution.anchor}) |"
        )
    return "\n".join(lines) + "\n"


def render_consolidated(part: str, solutions: list[Solution]) -> str:
    selected = [solution for solution in solutions if solution.part == part]
    lines = [
        f"# IBO 2024 Theory Part {part} — Worked Solutions",
        "",
        ATTRIBUTION,
        "",
        LICENSE,
        "",
        "These are natural-language worked solutions. The official T/F verdict is "
        "retained even where a solution includes a clearly labeled source discrepancy note.",
        "",
        "## Contents",
        "",
    ]
    for solution in selected:
        lines.append(
            f"{solution.task}. [Task {solution.task} — {solution.topic}](#{solution.anchor})"
        )
    for solution in selected:
        lines.extend(
            [
                "",
                f'<a id="{solution.anchor}"></a>',
                f"## Task {solution.task} — {solution.topic}",
                "",
                solution.answer_line,
                "",
                "### Reasoning",
                "",
                solution.reasoning,
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def render_outputs(root: Path) -> dict[str, str]:
    solutions = load_solutions(root)
    return {
        "answers.md": render_answers(solutions),
        "theory-a-solutions.md": render_consolidated("A", solutions),
        "theory-b-solutions.md": render_consolidated("B", solutions),
    }


def check_outputs(root: Path, outputs: dict[str, str]) -> list[str]:
    errors: list[str] = []
    for name in OUTPUT_NAMES:
        path = root / name
        if not path.is_file():
            errors.append(f"missing generated file: {name}")
        elif path.read_text(encoding="utf-8") != outputs[name]:
            errors.append(f"stale generated file: {name}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="check without writing")
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        outputs = render_outputs(root)
    except (OSError, KeyError, ValueError) as error:
        print(f"BUILD FAILED: {error}", file=sys.stderr)
        return 1

    if args.check:
        errors = check_outputs(root, outputs)
        if errors:
            for error in errors:
                print(f"BUILD CHECK FAILED: {error}")
            return 1
        print("BUILD CHECK PASSED: all three generated documents are current.")
        return 0

    for name, content in outputs.items():
        (root / name).write_text(content, encoding="utf-8")
        print(f"WROTE {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
