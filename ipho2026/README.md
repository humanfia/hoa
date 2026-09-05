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

- the [GPT-5.6 Sol natural-language theory solutions](NaturalLanguage/);
- the separate [Kimi K3 Max natural-language theory solutions](Kimi/NaturalLanguage/);
- optional [GPT-5.6 Sol formal Lean 4 solutions](Ipho2026Gpt56solBlind/Solutions/)
  and the [Kimi K3 Max Lean answer set](Kimi/);
- independent post-completion grading for the
  [GPT-5.6 Sol natural-language solutions](NaturalLanguage/GRADING_REPORT.md),
  [Kimi natural-language solutions](Kimi/NaturalLanguage/GRADING_REPORT.md), and
  optional [formalizations](GRADING_REPORT.md).

## Start the natural-language experiment

The primary experiment is the answer-blind natural-language run: one isolated
Humanize worker solves one theory problem and writes a complete `solution.md`.
Install [Humanize](https://github.com/humanfia/humanize2), create a clean
workspace containing only the problem statement and its figures, and launch a
worker from that workspace:

```bash
python3 -m pip install 'git+https://github.com/humanfia/humanize2.git'

mkdir -p ipho2026-nl-runs/T1
cp /path/to/T1-problem-and-figures.pdf ipho2026-nl-runs/T1/problem.pdf
cd ipho2026-nl-runs/T1

hmz exec -f ralph_loop \
  -a codex/gpt-5.6-sol:max \
  "Solve every part of the supplied IPhO theory problem. Write a rigorous, self-contained solution to solution.md, including derivations, units, numerical work, requested figures, and consistency checks. Do not use official solutions or marking schemes."
```

Replace the input path and workspace name for T2 and T3, keeping the three
workers isolated. To preserve the answer-blind setup, do not place official
solutions, marking schemes, this repository's grading reports, or previous
answers in a worker workspace. Run the workers with outbound web access blocked
by your sandbox; the command above starts the Humanize loop but does not define
the host's network policy.

The published outputs are
[`NaturalLanguage/T1_solution.md`](NaturalLanguage/T1_solution.md),
[`T2_solution.md`](NaturalLanguage/T2_solution.md), and
[`T3_solution.md`](NaturalLanguage/T3_solution.md). Their independent
post-completion evaluation is in the
[natural-language grading report](NaturalLanguage/GRADING_REPORT.md).

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

- `NaturalLanguage/` — GPT-5.6 Sol natural-language theory solutions and
  official-scheme grading audit.
- `Kimi/NaturalLanguage/` — Kimi K3 Max natural-language theory solutions and
  their grading audit.
- `Ipho2026Gpt56solBlind/` — optional GPT-5.6 Sol formalizations.
- `Kimi/Ipho2026KimiK3Blind32/` — optional Kimi K3 Max formalizations.
- `GRADING_REPORT.md` — post-completion comparison of the formalizations with
  the official results.

The submission intentionally excludes blank originals, answer/reference
archives, source PDFs, blind assets, agent state, contracts, and workflow
metadata.

## Optional: verify the Lean formalizations

The natural-language experiment does not require Lean. As an additional check,
install [Git](https://git-scm.com/) and
[Elan](https://lean-lang.org/install/), then build the two optional formal
projects:

```bash
git clone git@github.com:humanfia/ipho2026-no-leakage.git
cd ipho2026-no-leakage

# GPT-5.6 Sol: Lean 4.32.0, Mathlib, and PhysLean.
lake exe cache get
lake build

# Kimi K3 Max: Lean and Mathlib 4.31.0.
(
  cd Kimi
  lake update
  lake exe cache get
  lake build
)
```

Elan reads each project's `lean-toolchain` file and selects the pinned version
automatically. A successful pair of `lake build` commands verifies all released
Lean files.

Every submitted proof elaborates without `sorry`, `admit`, custom axioms, or
unsafe proof escapes. Its transitive axiom closure uses only Lean/Mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
