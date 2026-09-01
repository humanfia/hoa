# IChO 2026 Humanize results

This repository preserves two Humanize runs for all nine theoretical problems
of the 58th International Chemistry Olympiad (IChO 2026):

- [`gpt-5.6-sol-max`](gpt-5.6-sol-max/solutions/) — GPT-5.6 Sol at maximum
  reasoning for implementation and review.
- [`kimi-k3-max`](kimi-k3-max/solutions/) — Kimi K3 at maximum reasoning for
  implementation and review, followed by a focused image-aware audit.

## Results

| Run | Raw rubric score | Raw accuracy | Weighted theory score | Weighted accuracy |
|---|---:|---:|---:|---:|
| GPT-5.6 Sol max | 418.5/437 | 95.77% | 58.341/60 | 97.24% |
| Kimi K3 max | 417.5/437 | 95.54% | 58.209/60 | 97.02% |

Both final result sets received full credit on Q1, Q2, Q4, Q5, and Q7. GPT
also received full credit on Q9; Kimi received 52/53 because its final molar
mass in Q9.1 differs from the official value after premature rounding. The
other deductions were in Q3, Q6, and Q8. See each run's grading report for
the subproblem-level breakdown and grading conventions.

The scores are strict rubric-based reconstructions against the official
English IChO 2026 solutions. They are not scores issued by the IChO jury.
Textual descriptions of chemical drawings were accepted only when they
unambiguously specified the required structure and stereochemistry.

## Contents

Each run contains:

- `solutions/Q1.md` through `solutions/Q9.md` — final worked solutions;
- `GRADING.md` — official-key grading and detailed deductions; and
- `EXPERIMENT.md` — Humanize configuration, review process, and provenance.

The Kimi directory also contains [`FIRST_TURN_ABLATION.md`](kimi-k3-max/FIRST_TURN_ABLATION.md),
which grades the nine unreviewed round-0 outputs and compares them with the
final Humanize result under the same grading convention.

## Answer-blind Lean formalizations

The repository additionally publishes two fresh answer-blind Lean 4 runs over
the same 32 selected theory subquestions (47 requested outputs, 168 rubric
points). These runs were generated without access to the official solutions;
the official-key comparison was performed only after generation and review.

| Run | Formalization review | Proof review | Lake build | Placeholders | Official-answer comparison |
|---|---:|---:|---:|---:|---:|
| [GPT-5.6 Sol answer-blind](gpt-5.6-sol-answer-blind/) | 32/32 | 32/32 | passed | 0 | 47/47 outputs |
| [Kimi-K3 answer-blind](kimi-k3-answer-blind/) | 32/32 | 32/32 | passed | 0 | 47/47 outputs |

The corresponding normalized records are published in the
[`humanfia-lab/icho-2026`](https://huggingface.co/datasets/humanfia-lab/icho-2026)
dataset. Kimi has four non-proof grounding-log completeness warnings, disclosed
in its run README; they do not change its compile or review results.

Those normalized records include official solution and rubric text as post-run
evaluation metadata. For both answer-blind runs, those fields were never model
inputs.

## Scope

The preserved runs cover the nine **theoretical** problems. The separate
practical laboratory examination is not part of these model runs or scores.
