# Humanfia at IChO 2026

> [!NOTE]
> This is part of RSI Effort at NVIDIA Research. [Humanize](https://github.com/humanfia/humanize2) is an open agent loop/flow framework that led by [NVIDIA Research](https://www.nvidia.com/en-us/research), [UCLA PolyArch](https://polyarch.cs.ucla.edu), and [MIT HAN Lab](https://hanlab.mit.edu). We are skying the limit with the power of agents with community members.

**Full verified result: both GPT-5.6 Sol and Kimi-K3 solved all 32/32 selected
answer-blind Lean formalization targets, produced 47/47 requested outputs, and
passed every proof review and the pinned Lean build with zero placeholders.**

This repository also preserves Humanize runs over all nine theoretical
problems of the 58th International Chemistry Olympiad (IChO 2026), together
with worked solutions, grading reports, provenance, and independently
buildable Lean projects.

## Results

### Answer-blind Lean: full score

The models received the official problem statements and images, but not the
official solutions. Official-answer comparison happened only after generation
and review had finished.

| Run | Formalization review | Proof review | Lean build | Placeholders | Official-answer comparison |
|---|---:|---:|---:|---:|---:|
| [GPT-5.6 Sol](gpt-5.6-sol-answer-blind/) | **32/32** | **32/32** | passed | 0 | **47/47 outputs** |
| [Kimi-K3](kimi-k3-answer-blind/) | **32/32** | **32/32** | passed | 0 | **47/47 outputs** |

The normalized records are published in the
[`humanfia-lab/icho-2026`](https://huggingface.co/datasets/humanfia-lab/icho-2026)
dataset. Those records include official solution and rubric text as post-run
evaluation metadata; those fields were never model inputs.

### Full theoretical-paper runs

| Run | Raw rubric score | Raw accuracy | Weighted theory score | Weighted accuracy |
|---|---:|---:|---:|---:|
| GPT-5.6 Sol max | 418.5/437 | 95.77% | 58.341/60 | 97.24% |
| Kimi-K3 max | 417.5/437 | 95.54% | 58.209/60 | 97.02% |

These are strict rubric-based reconstructions against the official English
IChO 2026 solutions, not scores issued by the IChO jury. Both runs received
full credit on Q1, Q2, Q4, Q5, and Q7; GPT also received full credit on Q9.

Kimi-K3's one-point shortfall on Q9 was caused only by decimal rounding, not
by the solution method. It rounded the molar mass of water to `18.02` before
the final calculation and obtained `1134.98 g mol⁻¹`; retaining the booklet's
atomic-mass precision gives the official `1135.01 g mol⁻¹`. The remaining
deductions in the natural-language runs are documented under Q3, Q6, and Q8.
See each run's `GRADING.md` for every subproblem-level deduction and the full
grading convention.

## Open model x open harness: Kimi-K3

Humanize gives an open-model path the same auditable loop used for the
frontier-model run. Kimi-K3 reached the full **32/32** answer-blind Lean result
and **47/47** requested outputs, while the repository releases its final Lean
project, checksums, grading, experiment record, and worked solutions.

The historical Kimi campaign used `anthropic-kimi-k3` through Claude Code as
the model client, with Humanize providing the agent loop and review workflow.
Its four grounding-log completeness warnings are disclosed in the run README;
they do not change the compile or proof-review results.

## Reproduce the verified result

Clone the repository and verify the released files:

```bash
git clone https://github.com/humanfia/icho2026.git
cd icho2026

for run in gpt-5.6-sol-answer-blind kimi-k3-answer-blind; do
  (cd "$run" && sha256sum -c CHECKSUMS.sha256)
done
```

Build both pinned Lean projects:

```bash
for run in gpt-5.6-sol-answer-blind kimi-k3-answer-blind; do
  (
    cd "$run"
    lake exe cache get
    lake build
  )
done
```

A successful `lake build` type-checks the released formalizations and proofs
under the toolchain pinned inside each project.

## Released artifacts

- [`gpt-5.6-sol-max`](gpt-5.6-sol-max/solutions/) and
  [`kimi-k3-max`](kimi-k3-max/solutions/) contain `Q1.md` through `Q9.md`.
- Each full-paper run includes `GRADING.md` and `EXPERIMENT.md`.
- [`gpt-5.6-sol-answer-blind`](gpt-5.6-sol-answer-blind/) and
  [`kimi-k3-answer-blind`](kimi-k3-answer-blind/) are standalone Lean 4
  projects with pinned dependencies and checksums.
- [`FIRST_TURN_ABLATION.md`](kimi-k3-max/FIRST_TURN_ABLATION.md) compares the
  nine unreviewed Kimi round-0 outputs with the final Humanize result under the
  same grading convention.

## Scope

The preserved runs cover the nine **theoretical** problems. The separate
practical laboratory examination is not part of these model runs or scores.
