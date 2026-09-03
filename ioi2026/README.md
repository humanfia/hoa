# Humanfia at IOI 2026

> **Note:** [Humanize](https://github.com/humanfia/humanize2) is part of the RSI effort and is led by [NVIDIA Research](https://www.nvidia.com/en-us/research/).

**Result: 100% passed — all 6/6 IOI 2026 solutions received full scores on
Codeforces.** Humanfia produced a submission-ready C++ solution for every task
from both contest days. This repository releases the accepted solutions, the
official problem material that can be redistributed, and the Humanize plans
and orchestration used to recreate the six independent solving runs.

## Results

| Day | Task | Result | Submission |
|---|---|---:|---|
| 1 | Ball Machine | 100% passed | [`ballmachine.cpp`](submissions/ballmachine.cpp) |
| 1 | Monuments | 100% passed | [`monuments.cpp`](submissions/monuments.cpp) |
| 1 | Tiling Game | 100% passed | [`tiling.cpp`](submissions/tiling.cpp) |
| 2 | Classroom Game | 100% passed | [`classroom.cpp`](submissions/classroom.cpp) |
| 2 | Magic City | 100% passed | [`magiccity.cpp`](submissions/magiccity.cpp) |
| 2 | Partition | 100% passed | [`partition.cpp`](submissions/partition.cpp) |
|  | **Total** | **6/6 (100%)** |  |

The solutions cover the full stated constraints. In particular, Ball Machine
meets its full-score resource bounds, Classroom Game uses at most two integers
per paper, Magic City stays within its construction bounds, and Partition
supports the complete stated range. See [`solutions/README.md`](solutions/README.md)
for the precise per-task guarantees.

The 100% result comes from the Codeforces submissions. The public bundle can
also compile every solution and replay every released Day 1 example locally;
the Codeforces hidden judge remains an external verification step.

## Open model × open harness

[Humanize](https://github.com/humanfia/humanize2) supports
[Kimi-K3](https://github.com/MoonshotAI/Kimi-K3), pairing an open model with an
open harness. The task plans and problem-only worker seeds in this repository
are model-independent, so they can be reused for a Kimi-K3 run through
Humanize's Kimi backend.

The checked-in IOI submissions and the
[token-cost report](ioi2026-token-costs.md) come from the archived
`gpt-5.6-sol:max` runs. This repository does not label them as Kimi-generated;
the Kimi support is the reproducible backend path for new experiments.

## Reproduce the public result

Requirements: Bash, Python 3, `sha256sum`, and a C++20-capable `g++` (or set
`CXX` to a compatible compiler).

```sh
git clone https://github.com/humanfia/ioi2026.git
cd ioi2026
./verify.sh
```

The verifier checks the bundle manifest, validates every orchestration script,
builds all six sources in a disposable directory, runs every released Day 1
example, validates Ball Machine's public topology and resource accounting, and
strictly compiles the three Day 2 artifacts. A successful run ends with:

```text
PASS: IOI 2026 clean bundle verified
```

## Reproduce the six Humanize runs

The worker repositories are seeded only with the corresponding official
problem and immutable plan; the final files under `submissions/` are never
copied into them. On Linux, the default filesystem boundary also prevents a
worker from reading the reference results or sibling repositories.

```sh
# Check prerequisites without writing or launching workers.
./orchestration/launch-six.sh --dry-run

# Launch six detached Humanize RLCR workers.
./orchestration/launch-six.sh --start

# Follow their review rounds and final status.
./orchestration/monitor.sh
```

The checked-in launcher reproduces the archived Codex-backed configuration.
For a Kimi-K3 experiment, configure the Kimi backend in Humanize and reuse the
six problem seeds and matching plans under `orchestration/plans/`. See
[`orchestration/README.md`](orchestration/README.md) for prerequisites,
isolation behavior, model configuration, waiting, resuming, result collection,
and output layout. Six max-effort runs can consume substantial time and model
quota, so the launcher requires the explicit `--start` flag.

## What is included

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
- `verify.sh`: the one-command public reproduction gate.

The official Day 1 attachment stubs are retained unchanged because they are
part of the problem packages. No official or editorial solutions, hidden
tests, Humanize runtime state, model transcripts, build products, or nested Git
repositories are included.

## Provenance

The six sources were copied byte-for-byte from this repository's root sources
at commit `b1c4c8bd775cadab3c00de11e49ff79f7c98a0a9`. Their hashes also match the
finalized Humanize worker artifacts, including the separately reviewed
Partition artifact.

Day 1 problem material was copied unchanged from the official IOI 2026 release.
Day 2 problem material was copied unchanged from a snapshot that pins the
official IOI task archive at commit
`3140cde0e3bf1e9bfc5508387455ae8bc6d0f9f2` and records the statement hashes.
