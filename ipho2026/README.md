# Humanfia at IPhO 2026

> [!NOTE]
> This is part of RSI Effort at NVIDIA Research. [Humanize](https://github.com/humanfia/humanize2) is an open agent loop/flow framework that led by [NVIDIA Research](https://www.nvidia.com/en-us/research), [UCLA PolyArch](https://polyarch.cs.ucla.edu), and [MIT HAN Lab](https://hanlab.mit.edu). We are skying the limit with the power of agents with community members.

The **Humanfia team aced all three theory problems of the 56th International
Physics Olympiad**, earning **30.00/30.00 (100%)** with GPT-5.6 Sol
natural-language solutions produced through a *fully agentic, answer-blind
approach*. The release also includes Lean 4 formalizations for all 41 subparts
and a separate Kimi K3 Max Lean answer set.

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

The Humanfia (GPT-5.6 Sol) natural-language submission answered all 23 theory
subparts and received full credit on every problem in the grading audit.

| Problem | Humanfia (GPT-5.6 Sol) | Accuracy |
| --- | ---: | ---: |
| Theory 1 | ✅ 10.00/10.00 | 100% |
| Theory 2 | ✅ 10.00/10.00 | 100% |
| Theory 3 | ✅ 10.00/10.00 | 100% |
| **Theory total** | **✅ 30.00/30.00** | **100%** |

This is a source-level estimate against the official solutions and itemized
marking schemes, not an official jury adjudication. See the
[natural-language grading report](NaturalLanguage/GRADING_REPORT.md) for the
complete evidence and methodology.

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
