# Kimi-K3 — native Codex `/goal` baseline

Separate fresh answer-blind experiment over **9 theory problems / 68 numbered
subquestions**, using native persisted Codex goals, Kimi-K3
(`nvidia/moonshotai/kimi-k3`) and an observed peak of **32 concurrent solver
jobs**. This is not the Humanize review/redraft solver loop and is not the
earlier 32+36 Humanize coverage.

| Measure | Result |
|---|---:|
| Native goals completed | 67/68 (T1-A6 blocked) |
| Independently checked Lean compilation | 66/68 canonical; T3-A6 and T4-A6 have alternate-path receipts only |
| Semantic review passed | 46/68 |
| Proof review passed | 44/68 |
| Combined independent acceptance | **31/68 (45.59%)** |
| Official-answer rubric score | **340.2/437 (77.85%); 47.674/60 (79.46%)** |

Semantic outcomes: 46 passed, 13 conditional, 7 failed, 2 pending (T5-A3 and
T8-A5 are review-format errors, not scientific fail verdicts). Proof outcomes:
44 passed, 15 conditional, 7 failed, 2 pending. Canonical compilation is
necessary but does not establish that a theorem faithfully proves the chemistry
question. Independent reviews are model assessments, not infallible judgments.

See [all 68 results and reviewer explanations](controller/RESULTS.md),
[machine-readable outcomes](controller/results-summary.json),
[final experiment audit](controller/FINAL-AUDIT.md), and the
[official-answer grade](grading/GRADING.md).

## Protocol and scope

- Solvers received question-only material, original question images/PDF and blank
  student answer sheets. No previous GPT/Kimi answers, grading records, or
  supplementary user model assumptions were provided.
- All solver outputs were frozen before independent semantic/proof evaluation.
  Reviews did not feed back into solver goals; failed outputs were not repaired.
  T1-A6 is a final blocked native goal by user instruction.
- Ordinary scientific web references were allowed; official competition answers
  were forbidden during solving. This run recorded zero native web-search events.
  That is not a network-isolation guarantee.
- PyMuPDF was installed before launch so the already supplied PDF could be read.
- Reported native-goal usage: 21,134,287 tokens. This is not a billing estimate.
- This is not a matched-budget causal comparison against the historical
  Humanize experiments, which used different workflows and input scopes.

## Official-answer scoring status

Post-run official-rubric comparison of the frozen answers is now complete:
**340.2/437 raw (77.85%)**, **47.674/60 weighted
(79.46%)**. Remaining deductions include T1-A6 (1/4),
T2-A4 (0/2), T3-A3 (12/23), T3-A6 (0/12), T4-A3 (1.2/3), T4-A8 (1/2),
T4-A9 (2/4), T5-A5 (0/2), T6-A1 (5/10), T6-A2 (5/11), T6-A6 (9/20),
T7-A3 (2/15), T7-A5 (3/6), T8-A5 (3/5), T8-A6 (6/10), T8-A8 (0/4),
T9-A2 (2/6), T9-A6 (0/4) and T9-A7 (0/6). The 45.59% figure
above is formalization acceptance, not this chemistry score. No grading result
was sent back to the frozen solvers. See [GRADING.md](grading/GRADING.md).

## Released files and local verification

Each `jobs/<target>/campaign/workspace/` contains the frozen natural-language
answer, result metadata, verification notes, Lean sources and pinned Lake files.
`reviews/<target>/` contains the independent review and candidate-hash receipt;
T5-A3 and T8-A5 also keep their format-recovery records. `controller/validation/<target>/`
contains the independent Lean receipt and log, or the alternate-path receipt for
T3-A6 and T4-A6. `inputs/` contains the shared question-only source material.

```bash
sha256sum -c CHECKSUMS.sha256
cd jobs/icho_2026_t1_a1/campaign/workspace
lake exe cache get
lake env lean IChO2026Problems/problem_icho_2026_t1_a1.lean
```

Repeat the target-specific command for other jobs. The release contains separate
projects, not a merged `lake build` project. Any optional source-image lookup from
a job workspace can use the shared `../../../../inputs/` directory. Historical
verification commands and controller receipts retain their original absolute
paths as provenance; those host paths are not prerequisites for local compilation.

`harness-snapshot/` preserves the main launcher/evaluator scripts for inspection.
They retain original host paths and depend on infrastructure outside this release;
they are **not a turnkey portable launcher**. Authentication homes, API credentials,
raw model conversations, runtime binaries and dependency caches are excluded.
