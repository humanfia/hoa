# Kimi-K3 — native Codex `/goal` baseline

Fresh answer-blind experiment over **9 theory problems / 68 numbered subquestions**,
using NVIDIA `nvidia/moonshotai/kimi-k3` and native persisted Codex goals.
Maximum solver concurrency: **32**. This is separate from the historical
Kimi 32+36 formalizations and does not use the Humanize review/redraft loop.

| Measure | Result |
|---|---:|
| Native goals completed | 67/68; T1-A6 blocked and finally marked failed |
| Canonical-path Lean compilation | 66/68 |
| Alternate-path Lean compilation | 2/2 (T3-A6, T4-A6; filename exceptions) |
| Semantic review passed | 46/68 |
| Proof review passed | 44/68 |
| Combined independent acceptance | **31/68 (45.59%)** |
| Structured reviews obtained | 66/68; 2 review-format errors |
| Official-answer score | Not performed for this release |

Semantic outcomes: 46 passed, 13 conditional, 7 failed, 2 unavailable.
Proof outcomes: 44 passed, 15 conditional, 7 failed, 2 unavailable.
T5-A3 and T8-A5 produced prose-only reviews without valid structured verdicts;
they are not accepted and are not silently counted as scientific failures.
The aggregate gate also checks output coverage, unsupported-assumption fields,
artifact conformance and fresh hashes. Reviewer field inconsistencies are preserved.
Review verdicts are model assessments, not infallible judgments.

See [per-target results](controller/RESULTS.md),
[machine-readable summary](controller/results-summary.json), and
[final audit](controller/FINAL-AUDIT.md).
Compilation and native goal completion do not establish chemistry correctness.
**45.59% is formalization acceptance, not official-answer accuracy.**

## Protocol

Solvers received original questions, diagrams and blank answer sheets, but no
historical generated answers, standard answers, grading records or supplementary
user model assumptions. Each job had an isolated workspace. Other question
statements were permitted; other generated answers and reviews were not inputs.
Independent Kimi reviews used fresh contexts, without feedback to solvers.
No rejected or conditional candidate was repaired during this evaluation.

Ordinary scientific HTTP was permitted; this was not a network air gap.
The [transport record](controller/TRANSPORT.md) documents compatibility handling
and two rate-limit recoveries preserving the original threads. Solver concurrency
is not simultaneous upstream request concurrency. Reported native-goal usage:
21,134,287 tokens, excluding review/preflight work; not a provider billing total.

## Files and verification

Each `jobs/<target>/campaign/workspace/` contains the frozen answer, metadata,
verification notes, Lean sources and pinned Lake files. `reviews/` contains
original review outputs and input hashes; `controller/validation/` contains
independent compilation receipts. Shared problem material is in `inputs/`.

```bash
sha256sum -c CHECKSUMS.sha256
cd jobs/icho_2026_t1_a1/campaign/workspace
lake exe cache get
lake env lean IChO2026Problems/problem_icho_2026_t1_a1.lean
```

These are 68 separate projects, not one merged build. T3-A6 and T4-A6 use the
alternate filenames in their validation receipts. Historical absolute paths
are retained as provenance; optional source lookup can use `../../../../inputs/`.
The harness snapshot is for inspection, not a portable turnkey launcher.
Credentials, authentication homes, raw model conversations, binaries and
dependency caches are excluded. Prior experiments are unchanged by this release.
