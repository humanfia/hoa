#!/usr/bin/env python3
"""Check that relative links in tracked Markdown files point at tracked paths.

Only the path part of each link is checked; anchors and external URLs are
ignored. Links inside fenced code blocks and inline code spans are skipped.
Exits 1 and lists every broken link if any are found.
"""

import re
import subprocess
import sys
from pathlib import Path, PurePosixPath
from urllib.parse import unquote

# Vendored third-party snapshots whose documentation describes their own
# upstream layout, not this repository.
EXCLUDED_PREFIXES = (
    "putnambench/humanize/",
    "imo2026/tools/lean4export/",
)

# Archived model outputs, kept byte-for-byte under their run checksums. Their
# links refer to the solver's workspace at the time of the run.
EXCLUDED_PATTERNS = (
    re.compile(r"^icho2026/[^/]+/jobs/[^/]+/campaign/workspace/"),
    re.compile(r"^icho2026/kimi-k3-nl-36-formalization/kimi-original-answers/"),
    re.compile(r"^icho2026/[^/]+/solutions/"),
)

INLINE_LINK = re.compile(r"!?\[(?:[^\[\]]|\[[^\]]*\])*\]\(\s*<?([^)\s>]+)>?(?:\s+\"[^\"]*\")?\s*\)")
REFERENCE_DEF = re.compile(r"^\s{0,3}\[[^\]]+\]:\s*<?(\S+?)>?(?:\s+.*)?$", re.M)
FENCE = re.compile(r"^\s{0,3}(```|~~~)")
CODE_SPAN = re.compile(r"`+[^`]*`+")
SCHEME = re.compile(r"^[a-zA-Z][a-zA-Z0-9+.-]*:")


def tracked_files(root: Path) -> list[str]:
    output = subprocess.run(
        ["git", "ls-files", "-z"], cwd=root, check=True, capture_output=True
    ).stdout
    return [name for name in output.decode("utf-8").split("\0") if name]


def strip_code(text: str) -> str:
    lines = []
    in_fence = False
    for line in text.splitlines():
        if FENCE.match(line):
            in_fence = not in_fence
            lines.append("")
            continue
        lines.append("" if in_fence else CODE_SPAN.sub("", line))
    return "\n".join(lines)


def main() -> int:
    root = Path(
        subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
    )
    files = tracked_files(root)
    paths = set(files)
    directories = {str(parent) for name in files for parent in PurePosixPath(name).parents}

    broken = []
    for name in files:
        if not name.lower().endswith(".md") or name.startswith(EXCLUDED_PREFIXES):
            continue
        if any(pattern.match(name) for pattern in EXCLUDED_PATTERNS):
            continue
        text = strip_code((root / name).read_text(encoding="utf-8", errors="replace"))
        targets = INLINE_LINK.findall(text) + REFERENCE_DEF.findall(text)
        for target in targets:
            if target.startswith(("#", "//")) or SCHEME.match(target):
                continue
            path_part = unquote(target.split("#", 1)[0].split("?", 1)[0])
            if not path_part:
                continue
            if path_part.startswith("/"):
                resolved = PurePosixPath(path_part.lstrip("/"))
            else:
                resolved = PurePosixPath(name).parent / path_part
            parts = []
            escaped = False
            for part in resolved.parts:
                if part == "..":
                    if not parts:
                        escaped = True
                        break
                    parts.pop()
                elif part != ".":
                    parts.append(part)
            normalized = "/".join(parts) or "."
            if escaped or (normalized not in paths and normalized not in directories):
                broken.append(f"{name}: {target}")

    for entry in broken:
        print(f"broken relative link: {entry}")
    if broken:
        print(f"{len(broken)} broken relative link(s)", file=sys.stderr)
        return 1
    print("All relative Markdown links resolve to tracked paths.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
