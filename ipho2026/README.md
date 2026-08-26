# IPhO 2026 answer-blind solutions

This repository contains completed GPT-5.6 Sol Lean 4 formalizations for all
41 subparts of the 56th International Physics Olympiad, GPT-5.6 Sol
natural-language solutions for the three theory problems, and a separate Kimi
answer set.

The work was produced under answer-blind workflows. Official solutions and
marking schemes were unavailable to the answer-generating workers and were
used only for separate grading audits.

## Contents

- `Ipho2026Gpt56solBlind/Solutions/` — 41 completed subpart formalizations.
- `Ipho2026Gpt56solBlind/Shared/` — shared typed physics and mathematics APIs.
- `Ipho2026Gpt56solBlind/Solutions.lean` — aggregate import of all solutions.
- `GRADING_REPORT.md` — post-completion comparison with the official results.
- `NaturalLanguage/` — GPT-5.6 Sol natural-language theory solutions and
  official-scheme grading audit.
- `Kimi/` — a separate Kimi K3 Max answer set and its official-answer grading
  report.

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
