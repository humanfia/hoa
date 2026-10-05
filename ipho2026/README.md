# Humanfia at IPhO 2026

> [!NOTE]
> This is part of RSI Effort at NVIDIA Research. [Humanize](https://github.com/humanfia/humanize2) is an open agent loop/flow framework that led by [NVIDIA Research](https://www.nvidia.com/en-us/research), [UCLA PolyArch](https://polyarch.cs.ucla.edu), and [MIT HAN Lab](https://hanlab.mit.edu). We are skying the limit with the power of agents with community members.

The **Humanfia team aced all three theory problems of the 56th International
Physics Olympiad**. Both the GPT-5.6 Sol and Kimi K3 Max natural-language
solution sets earned **30.00/30.00 (100%)—full marks** in source-level grading
audits after being produced through a *fully agentic, answer-blind approach*.
The release also includes Lean 4 formalizations for all 41 subparts and a
separate Kimi K3 Max Lean answer set.

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

## Results

The Humanfia GPT-5.6 Sol and Kimi K3 Max natural-language submissions each
answered all 23 theory subparts and received full credit on every problem in
their grading audits.

| Problem | Humanfia (GPT-5.6 Sol) | Humanfia (Kimi K3 Max) |
| --- | ---: | ---: |
| Theory 1 | ✅ 10.00/10.00 | ✅ 10.00/10.00 |
| Theory 2 | ✅ 10.00/10.00 | ✅ 10.00/10.00 |
| Theory 3 | ✅ 10.00/10.00 | ✅ 10.00/10.00 |
| **Theory total** | **✅ 30.00/30.00 (100%)** | **✅ 30.00/30.00 (100%) — Full marks** |

These are source-level estimates against the official solutions and itemized
marking schemes, not official jury adjudications. See the grading reports for
the [GPT-5.6 Sol](NaturalLanguage/GRADING_REPORT.md) and
[Kimi K3 Max](Kimi/NaturalLanguage/GRADING_REPORT.md) natural-language
solutions for the complete evidence and methodology.

## Natural-language experiment

The primary experiment is the answer-blind natural-language run: one isolated
Humanize builder/reviewer loop solves one theory problem and writes a complete
solution.
The repository now includes
[`scripts/run-natural-language-experiment.sh`](scripts/run-natural-language-experiment.sh),
which prepares a clean problem-only Git workspace and starts the Humanize RLCR
builder/reviewer loop.

Install [Humanize](https://github.com/humanfia/humanize2), place one problem
statement and its figures in an input directory, and run:

```bash
scripts/run-natural-language-experiment.sh \
  T1 /path/to/T1-input ../ipho2026-runs/T1
```

Repeat with `T2` and `T3` in separate input and run directories. The run
directory must be new or empty and outside this checkout; the launcher refuses
obvious solution, answer, grading, marking-scheme, and rubric files. Humanize
uses `codex/gpt-5.6-sol:max` for both builder and reviewer by default. Pass a
fourth and fifth argument to select different Humanize agents. Run `--help` for
the full command syntax.

The launcher creates `solution.md` in the run directory. To reproduce the
answer-blind conditions, execute it in a host or container whose network policy
blocks outbound web access; the script prepares an isolated workspace and tells
the agents not to use the network, but it cannot change the host network policy.

The published outputs are
[`NaturalLanguage/T1_solution.md`](NaturalLanguage/T1_solution.md),
[`T2_solution.md`](NaturalLanguage/T2_solution.md), and
[`T3_solution.md`](NaturalLanguage/T3_solution.md). Their independent
post-completion evaluation is in the
[natural-language grading report](NaturalLanguage/GRADING_REPORT.md).

## Contents

- `NaturalLanguage/` — GPT-5.6 Sol natural-language theory solutions and
  official-scheme grading audit.
- `Kimi/NaturalLanguage/` — Kimi K3 Max natural-language theory solutions and
  their grading audit.
- `Ipho2026Gpt56solBlind/` — optional GPT-5.6 Sol formalizations.
- `Kimi/Ipho2026KimiK3Blind32/` — optional Kimi K3 Max formalizations.
- `scripts/run-natural-language-experiment.sh` — answer-blind Humanize launcher.
- `GRADING_REPORT.md` — post-completion comparison of the formalizations with
  the official results.

The submission intentionally excludes blank originals, answer/reference
archives, source PDFs, blind assets, agent state, contracts, and workflow
metadata.

## Optional: verify the Lean formalizations

The natural-language experiment does not require Lean. As an additional check,
the GPT-5.6 Sol formalizations can be built with Lean `v4.32.0`, Mathlib, and
PhysLean. After cloning this repository, open a shell in the repository root and
run the existing commands below:

```bash
lake exe cache get
lake build
```

`lake exe cache get` downloads the precompiled dependencies for the pinned
toolchain. `lake build` then checks every GPT-5.6 Sol formalization. The check is
complete when `lake build` exits successfully without an error.

The separate Kimi formalizations have their own optional build instructions in
[`Kimi/README.md`](Kimi/README.md).

Every submitted proof elaborates without `sorry`, `admit`, custom axioms, or
unsafe proof escapes. Its transitive axiom closure uses only Lean/Mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
