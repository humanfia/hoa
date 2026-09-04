# Humanfia at IPhO 2026

> [!NOTE]
> This is part of RSI Effort at NVIDIA Research. [Humanize](https://github.com/humanfia/humanize2) is an open agent loop/flow framework that led by [NVIDIA Research](https://www.nvidia.com/en-us/research), [UCLA PolyArch](https://polyarch.cs.ucla.edu), and [MIT HAN Lab](https://hanlab.mit.edu). We are skying the limit with the power of agents with community members.

The **Humanfia team completed all 41 subparts of the 56th International
Physics Olympiad** using a *fully agentic, answer-blind approach*. The release
includes GPT-5.6 Sol Lean 4 formalizations for all 41 subparts, GPT-5.6 Sol
natural-language solutions for the three theory problems, and a separate Kimi
K3 Max Lean answer set.

The answer-generating workers could not access official solutions or marking
schemes. Those materials were introduced only after completion, in separate
grading audits. Every submitted Lean proof elaborates without `sorry`,
`admit`, custom axioms, or unsafe proof escapes.

We build with open source, and build for open source. We release:

- the [GPT-5.6 Sol formal Lean 4 solutions](Ipho2026Gpt56solBlind/Solutions/)
  and their [shared typed physics and mathematics APIs](Ipho2026Gpt56solBlind/Shared/);
- the [GPT-5.6 Sol natural-language theory solutions](NaturalLanguage/);
- the separate [Kimi K3 Max Lean answer set](Kimi/);
- the complete post-completion grading evidence for the
  [GPT-5.6 Sol formalizations](GRADING_REPORT.md),
  [natural-language solutions](NaturalLanguage/GRADING_REPORT.md), and
  [Kimi answer set](Kimi/GRADING_REPORT.md).

## Results

| Submission | Coverage | Grading-audit result |
| --- | ---: | ---: |
| Humanfia (GPT-5.6 Sol), natural-language theory | 23/23 theory subparts | **30.00/30.00 (100%)** |
| Humanfia (GPT-5.6 Sol), Lean 4 | 41/41 subparts | **47.45/50.00 (94.9%)** |
| Humanfia (Kimi K3 Max), Lean 4 | 41/41 subparts | **29.90/50.00 (59.8%)** |

The GPT-5.6 Sol formal submission earned full audit credit on 32 of 41
subparts, including a perfect 10/10 on Theory Problem 2. Its deductions came
from a lost signed orientation, one unconstrained physical constant, and
missing uncertainty propagation in seven experimental results. The separate
natural-language submission received full credit on all three theory
problems. All 41 Kimi answer files compile; its lower audit score reflects
under-specified physical targets rather than Lean compilation failures.

These scores are source-level estimates against the official solutions and
marking schemes, not official jury adjudications. See the linked grading
reports for the itemized evidence and methodology.

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
