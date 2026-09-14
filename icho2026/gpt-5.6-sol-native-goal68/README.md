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
| Official-answer rubric score | **Incomplete; no aggregate score claimed** |

Semantic outcomes: 45 passed, 15 conditional, 8 failed. Proof outcomes:
32 passed, 13 conditional, 23 failed. Compilation is necessary but does not
establish that a theorem faithfully proves the chemistry question.
Independent reviews are model assessments, not infallible judgments.

See [all 68 results and reviewer explanations](controller/RESULTS.md),
[machine-readable outcomes](controller/results-summary.json), and
[completion audit](controller/COMPLETION.md).

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

A separate post-run official-rubric scoring attempt was made. Q3, Q5, Q7 and Q8
finished initial grading and an independent audit. Q1/Q6 initial grading and
Q4/Q9 audits exceeded their 30-minute stage limits. Q2 was rejected by the
tool-free-session validator after a disabled-tool error/tool event.
Consequently **no raw /437 or weighted /60 total is published**. The 47.06%
above is formalization acceptance, not chemistry answer accuracy. No partial
grading result was sent back to the frozen solvers.

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
