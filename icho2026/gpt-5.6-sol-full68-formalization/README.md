# GPT-5.6 Sol: complete theoretical-paper formalization

**All 68 numbered subquestions across the 9 theory problems have completed the
formalization experiment and passed its formalization/proof acceptance gates.**
The scope is **66 original-problem-input results plus 2 conditional results**,
not 68 unconditional chemistry theorems or an official-answer full score.

| Theory problem | Numbered subquestions | Formalization passed | Proof solved |
|---|---:|---:|---:|
| Q1 | 6 | 6 | 6 |
| Q2 | 7 | 7 | 7 |
| Q3 | 7 | 7 | 7 |
| Q4 | 9 | 9 | 9 |
| Q5 | 6 | 6 | 6 |
| Q6 | 7 | 7 | 7 |
| Q7 | 7 | 7 | 7 |
| Q8 | 10 | 10 | 10 |
| Q9 | 9 | 9 | 9 |
| **Total** | **68** | **68** | **68** |

Counts are by unique subquestion ID. The umbrella module `All.lean`, supporting
libraries, and the 12 T8 auxiliary lemmas are **not additional subquestions**.
The historical 32-target experiment remains in its original directory/table.

## Answer scoring — generous, non-official

| Raw points | Raw accuracy | Weighted theory score | Weighted accuracy |
|---:|---:|---:|---:|
| **424.5/437** | **97.14%** | **58.736/60** | **97.89%** |

This is the user-requested generous assessment, not an official IChO jury
score. The only non-full-credit subquestions are **T3-A3: 15/23** and
**T8-A4: 24.5/29**. The latter receives justified feature-level structure
credit, while wrong redox assignments still lose points. Details and the
grading method are in [the item-level report](grading/GRADING.md).

The scoring workflow reused frozen initial grades and existing completed
reviews, independently rechecked the substantive deductions, and completed Q6
by the coordinating assistant's direct official-page comparison. It was not a
full-paper independent human marking or a second solving run. The strict
baseline remains in the audit data, not in this README's score table.

The full68 campaign used GPT-5.6-sol, initially at concurrency 32, with official
problem statements/images and no official solutions as solver inputs. Selective
recovery and review followed. The latest isolated T8 repair reused verified
proofs; it was not a fresh answer-blind rerun. This release is distinct from
both the historical 32-target experiment and the nine natural-language essays.

## Contents

- `IChO2026Problems/`: all 68 submitted problem formalizations and their umbrella.
- `IChO2026Chem/`, `IChO2026Run/`: the supporting Lean modules.
- `answers/`: all 68 frozen structured answer submissions.
- `verification/targets.json`: per-target gate results and artifact hashes.
- `verification/release-build.json`: fresh publication-copy Lean checks.
- `assumptions/T4-A8.json`: the explicit flow-unit supplement.
- `t8-contest-model/`: the latest accepted T8-A8 main theorem, all 12 local
  lemmas, model-axiom ledger, independent approval and kernel receipts.

The main project's T8-A8 file preserves the original campaign artifact. The
separate `t8-contest-model/Main.lean` is the newer, provenance-corrected proof;
it is not silently substituted for the historical campaign file.

## Conditional results and limits

| Target | Additional input | Claim scope |
|---|---|---|
| T4-A8 | Interpret the printed `2.2 × 10⁵ m³` flow datum as `m³/day`. | User-authorized unit supplement, not an official erratum. |
| T8-A8 M001 | A category assigned to the dark condition has no drawn H₂/CO stack. | Does not assert that absolutely no dark reaction occurs. |
| T8-A8 M002 | Among the three illuminated conditions, increasing photon energy strictly increases the H₂ mole fraction. | Local qualitative contest model, not a universal law or a relation proved from the image. |

Under M001/M002 and the reviewed source inputs, T8 proves
**a=N, b=B, c=G, d=R**. Two diagnostic lemmas separately expose why the original
source observations alone do not identify all these relations. The unused
duplicate `src_L005_A01` was removed from the corrected source and axiom ledger;
the actual proof dependencies were unchanged. Both local model axioms remain
explicit and are used by the main theorem.

“68/68” counts accepted formalization targets. Lean validates the submitted
mathematical deductions, not the empirical truth or official-answer fidelity
of every model/encoding. The separate post-run grading can therefore deduct
chemistry-answer points even from compiled, gate-accepted targets. Post-run
comparison has identified discrepancies in the T3-A3 topology table and the
T8-A4 intermediate redox assignments; these frozen answers are preserved here,
not silently repaired. Full68 rubric scoring is reported separately; no
official-answer full-score claim is made in this release.
The historical selected-set and natural-language scores must not be attributed
to this expanded experiment.

## Reproduce

With the pinned Lean toolchain available:

```bash
cd gpt-5.6-sol-full68-formalization
sha256sum -c CHECKSUMS.sha256
lake exe cache get
lake build

cd t8-contest-model
lake exe cache get
lake build
```

The main project imports all 68 problem files. The separate audit project has
13 default library targets: `Main` and `L001`–`L012`. Each audit module is
self-contained; do not combine them by importing all of them into one Lean
module, because they deliberately preserve the original repeated declarations.

The publication copy was checked separately from the live solver workspace.
No authentication files, model home directories, API credentials, session logs
or dependency caches are included. The original campaign files were not changed.
