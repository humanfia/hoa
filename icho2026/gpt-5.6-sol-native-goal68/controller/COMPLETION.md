# Baseline execution and independent validation completed

The requested separate fresh answer-blind native-goal baseline has finished.
Completion means all 68 trials and their independent evaluations finished, not
that all submitted formalizations were accepted.

- Scope: 68 distinct question IDs and 68 distinct native persisted goal threads.
- Model: GPT-5.6 Sol, xhigh; observed peak solver concurrency 32.
- Native API preflight: passed before solver launch (`preflight.json`).
- Inputs: question-only seed, original question PDF and blank answer sheets;
  source hashes remain unchanged (`native-record-audit.json`, `../manifest.json`).
- Isolation: separate job workspaces/private homes and rootless restricted mounts;
  no historical answer inputs or supplementary user model assumptions supplied.
  Ordinary scientific web access was allowed. Keyword screening of 107 native
  web-search records found no flagged answer-source terms; this is not a proof
  of complete network isolation.
- Method: native goal lifecycle, no Humanize review/redraft solver loop;
  independent post-run reviews did not feed back into the solvers.
- Artifacts: all 68 retain answer.md, result.json, verification.md, Lean source,
  native events/status/usage, kernel receipts and structured independent reviews.
- Verification: all 68 kernel checks passed; all 68 reviews cover the exact
  requested output IDs. Original and frozen-review candidate hashes were checked,
  and all acceptance decisions were independently recomputed from their receipts.
- Native goals complete: 68/68. Lean compilation passed: 68/68.
- Semantic review: 45 passed, 15 conditional, 8 failed.
- Proof review: 32 passed, 13 conditional, 23 failed.
- Combined independent acceptance: 32/68 (47.06%). Official-answer comparison
  of the frozen outputs is **415/437 (94.97%) raw**, **57.875/60 (96.46%)
  weighted**. Reviews are model assessments, not infallible judgments.
- Reported native-goal tokens: 8,502,158; this is not a monetary cost estimate.
- Environment amendment: PyMuPDF was added during the run to read the already
  provided original PDF; see `pdf-dependency-amendment.json`.
- All independent review controllers exited. Existing older experiments were
  preserved and are not stopped by completion of this baseline.

See `RESULTS.md` for every target and links to its immutable input receipt,
candidate outputs, Lean verification and substantive reviewer explanation.
