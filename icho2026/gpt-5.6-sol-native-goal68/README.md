# GPT-5.6 Sol — native Codex `/goal` baseline

Separate fresh answer-blind experiment over **9 theory problems / 68 numbered
subquestions**, using native persisted Codex goals, GPT-5.6 Sol with `xhigh`
reasoning, and an observed peak of **32 concurrent solver jobs**. This is not
the Humanize review/redraft solver loop and is not the earlier selected 32-task run.

| Measure | Result |
|---|---:|
| Native goals completed | 68/68 |
| Independently checked Lean compilation | 68/68 |
| Semantic review passed | 45/68 |
| Proof review passed | 32/68 |
| Combined independent acceptance | **32/68 (47.06%)** |
| Official-answer rubric score | **415/437 (94.97%); 57.875/60 (96.46%)** |

Semantic outcomes: 45 passed, 15 conditional, 8 failed. Proof outcomes:
32 passed, 13 conditional, 23 failed. Compilation is necessary but does not
establish that a theorem faithfully proves the chemistry question.
Independent reviews are model assessments, not infallible judgments.

See [all 68 results and reviewer explanations](controller/RESULTS.md),
[machine-readable outcomes](controller/results-summary.json),
[completion audit](controller/COMPLETION.md), and the
[official-answer grade](grading/GRADING.md).

## Protocol and scope

- Solvers received question-only material, original question images/PDF and blank
  student answer sheets. No previous GPT/Kimi answers, grading records, or
  supplementary user model assumptions were provided.
- All solver outputs were frozen before independent semantic/proof evaluation.
  Reviews did not feed back into solver goals; failed outputs were not repaired.
- Ordinary scientific web references were allowed; official competition answers
  were forbidden during solving. Screening of 107 native web-search records
  found no flagged answer-source terms. This is not a network-isolation guarantee.
- PyMuPDF was added during execution to read the already supplied PDF. See the
  [environment amendment](controller/pdf-dependency-amendment.json).
- Reported native-goal usage: 8,502,158 tokens. This is not a billing estimate.
- This is not a matched-budget causal comparison against the historical
  Humanize experiments, which used different workflows and input scopes.

## Official-answer scoring status

Post-run official-rubric comparison of the frozen answers is now complete:
**415/437 raw (94.97%)**, **57.875/60 weighted (96.46%)**. Q1 and Q3–Q9 were
graded by isolated GPT-5.6 Sol sessions with a second audit. Q2 timed out in
that pipeline and was finished by direct official-page comparison; it scores
35/35. Remaining deductions include T3-A1 (0/2), T3-A2 (0/3), T3-A3 (21/23),
T8-A4 (20/29), T8-A6 (6/10) and T9-A8 (16/18). The 47.06% figure above is
formalization acceptance, not this chemistry score. No grading result was sent
back to the frozen solvers. See [GRADING.md](grading/GRADING.md).

## Released files and local verification

Each `jobs/<target>/campaign/workspace/` contains the frozen natural-language
answer, result metadata, verification notes, Lean sources and pinned Lake files.
`reviews/<target>/` contains the independent review and candidate-hash receipt;
`controller/validation/<target>/` contains the independent Lean log and receipt.
`inputs/` contains the shared question-only source material.

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
