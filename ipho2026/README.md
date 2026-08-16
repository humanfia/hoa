# IPhO 2026 Lean Solutions

This repository contains the completed Lean 4 formalizations for all 41
subparts of the 56th International Physics Olympiad, together with the shared
physics libraries needed to compile them.

The work was produced under an answer-blind workflow. Official solutions were
consulted only after proof completion, for the separate evaluation recorded in
[GRADING_REPORT.md](GRADING_REPORT.md).

## Contents

- `Ipho2026Gpt56solBlind/Solutions/` — 41 completed subpart formalizations.
- `Ipho2026Gpt56solBlind/Shared/` — shared typed physics and mathematics APIs.
- `Ipho2026Gpt56solBlind/Solutions.lean` — aggregate import of all solutions.
- `GRADING_REPORT.md` — post-completion comparison with the official results.

The submission intentionally excludes blank originals, answer/reference
archives, source PDFs, blind assets, agent state, contracts, and workflow
metadata.

## Build

The project uses Lean `v4.32.0`, Mathlib, and PhysLean.

```bash
lake exe cache get
lake build
```

Every submitted proof elaborates without `sorry`, `admit`, custom axioms, or
unsafe proof escapes. Its transitive axiom closure uses only Lean/Mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
