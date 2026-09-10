# Validation results

## Scope

This release covers 32 selected theory-ready subquestions from IChO 2026
papers T1--T9, containing 47 requested outputs and 168 raw rubric points.
Practical papers P1--P3 and the remaining theory subquestions are excluded.
Accordingly, “32/32” and “168/168” below refer only to this selected target
set, not to the complete competition exam.

The fresh campaign was launched from commit `10b04c62` in answer-blind mode.
All published source reports record `official_answer_seen: false`. The official
solutions were used only after the campaign terminated, for the independent
score comparison reported below.

## Checks

| Check | Result |
| --- | --- |
| Selected targets | 32/32 |
| Requested outputs | 47/47 equivalent to the official rubric answers |
| Expected raw score in selected set | 168/168 |
| Formalization review | 32/32 passed |
| Proof review | 32/32 solved |
| Active `sorry` or `admit` placeholders | None |
| Final axiom sweep | 32/32 passed; 0 `sorryAx` laundering findings |
| Default `lake build` | Passed |

## Numerical presentation notes

Four accepted outputs are mathematically equivalent to the official rubric but
are not identical display strings:

- T4-A8 reports `7.03e12 J day^-1` from the unrounded calculation; the rubric
  prints `7.04e12 J day^-1` after earlier intermediate rounding.
- T8-A6 reports `1.93%`; the rubric prints `1.94%`. The formalization uses exact
  SI constants and defers rounding to the final result.
- T8-A9 reports `43.9%` for S1 quenching; the rubric prints `44%`.
- T9-A1 reports `1.14e3 g mol^-1` to the campaign's three-significant-figure
  policy; its unrounded value is `1135.015 g mol^-1`, versus `1135.01` in the
  rubric.

These differences preserve the official methods and are within ordinary
competition-answer precision.

## Known T7-A3 auxiliary-carrier limitation

The requested T7-A3 outputs, `5.6662 mol` and `189 cycles`, exactly match the
official rubric and earn the expected 15/15 points. However, an auxiliary
previous-part carrier in the final Lean file describes mixture M1 as containing
`N2`, `CO2`, and `H2`; the source figure shows `N2`, `CO`, and `H2` at that
stage. The erroneous auxiliary species label is not used to derive either
T7-A3 requested output, but it means the published development should not be
described as free of every non-output semantic defect.

## Release links

- [Source code](https://github.com/humanfia/science-mango/tree/chemistry-blind-solver-gpt/icho_2026_run)
- [Dataset](https://huggingface.co/datasets/humanfia-lab/icho-2026)

## Report provenance

The scope, checks, and limitations above are reproduced from
[`science-mango/icho_2026_run/RESULTS.md` at commit `515f485c`](https://github.com/humanfia/science-mango/blob/515f485c841b55a349a755aa3afa4659a8c6cd4d/icho_2026_run/RESULTS.md).
They describe the historical campaign validation; publishing this report does
not constitute a new Lean build or a new grading run. The expected score is an
independent rubric-based reconstruction, not a score issued by the IChO jury.
