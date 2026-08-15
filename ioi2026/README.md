# IOI 2026 clean reproduction bundle

This directory contains both a clean snapshot of the six IOI 2026 results and
the machinery needed to recreate the six concurrent Humanize solving runs from
the bundled official problem material.

## Contents

- `submissions/`: one submission-ready C++ source file per task.
- `problems/day1/`: the three official Day 1 statements, contestant
  attachments, graders, headers, and public examples.
- `problems/day2/`: the three official English statement PDFs. The pinned
  official archive snapshot did not yet contain Day 2 contestant attachments.
- `interfaces/classroom.h`: a statement-derived compilation shim for the
  Classroom API; it is not an official attachment.
- `orchestration/`: six immutable task plans plus launch, monitor, resume, and
  collection scripts for independent Humanize RLCR workers.
- `MANIFEST.sha256`: checksums for every bundled file except the manifest.
- `verify.sh`: verifies the checksums, builds all six sources, and runs every
  released Day 1 public example.

The official Day 1 attachment stubs are retained unchanged because they are
part of the problem packages. No official/editorial solutions, alternative
solutions, hidden tests, Humanize runtime state, model transcripts, build
products, or nested Git repositories are included.

## Reproduce the six Humanize runs

The worker repositories are seeded with the problems and plans only; the
files under `submissions/` are not copied into them. On Linux, the default
filesystem boundary prevents workers from reading those reference results or
any sibling repository.

```sh
# No-write prerequisite check
./orchestration/launch-six.sh --dry-run

# Explicitly launch six detached gpt-5.6-sol:max Humanize workers
./orchestration/launch-six.sh --start

# Follow their RLCR rounds
./orchestration/monitor.sh
```

See `orchestration/README.md` for waiting, resuming, collecting results, model
overrides, isolation behavior, prerequisites, and output layout. Six max-effort
runs can consume substantial time and model quota, so the launcher never starts
them without the explicit `--start` flag.

## Reproduce the public result

Requirements: Bash, Python 3, `sha256sum`, and a C++20-capable `g++` (or set
`CXX` to a compatible compiler).

```sh
./verify.sh
```

The script builds in a disposable directory outside this tree. It checks exact
outputs for all Monuments and Tiling public examples, validates Ball Machine's
public topology and resource accounting, and strictly compiles the three Day 2
artifacts. A successful run ends with `PASS: IOI 2026 clean bundle verified`.

This reproduces the checks possible from the released public material. It
cannot reproduce an official hidden-test score because hidden grading data is
not present.

## Submission files

| Day | Task | Source |
|---|---|---|
| 1 | Ball Machine | `submissions/ballmachine.cpp` |
| 1 | Monuments | `submissions/monuments.cpp` |
| 1 | Tiling Game | `submissions/tiling.cpp` |
| 2 | Classroom Game | `submissions/classroom.cpp` |
| 2 | Magic City | `submissions/magiccity.cpp` |
| 2 | Partition | `submissions/partition.cpp` |

Each file implements its task's contestant API and must be submitted or linked
separately with that task's grader and header.

## Provenance

The six sources were copied byte-for-byte from this repository's root sources
at commit
`b1c4c8bd775cadab3c00de11e49ff79f7c98a0a9`. Their hashes also match the
finalized Humanize worker artifacts, including the separately reviewed
Partition artifact.

Day 1 problem material was copied unchanged from the official IOI 2026 release.
Day 2 problem material was copied unchanged from a snapshot that pins the
official IOI task archive at commit
`3140cde0e3bf1e9bfc5508387455ae8bc6d0f9f2` and records the statement hashes.
