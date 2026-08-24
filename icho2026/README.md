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
| Kimi K3 max | 418.5/437 | 95.77% | 58.341/60 | 97.24% |

Both final result sets received full credit on Q1, Q2, Q4, Q5, Q7, and Q9.
The remaining deductions were in Q3, Q6, and Q8. See each run's grading
report for the subproblem-level breakdown and grading conventions.

The scores are strict rubric-based reconstructions against the official
English IChO 2026 solutions. They are not scores issued by the IChO jury.
Textual descriptions of chemical drawings were accepted only when they
unambiguously specified the required structure and stereochemistry.

## Contents

Each run contains:

- `solutions/Q1.md` through `solutions/Q9.md` — final worked solutions;
- `GRADING.md` — official-key grading and detailed deductions; and
- `EXPERIMENT.md` — Humanize configuration, review process, and provenance.

For the Kimi run, `HUMANIZE_IMPACT.md` additionally compares the first worker
round with the final audited result. Its weighted score rose from 37.667/60
(62.78%) to 58.341/60 (97.24%).

## Scope

The preserved runs cover the nine **theoretical** problems. The separate
practical laboratory examination is not part of these model runs or scores.
