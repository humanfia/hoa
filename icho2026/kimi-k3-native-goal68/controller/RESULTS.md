# Kimi-K3 + native /goal — fresh answer-blind IChO 68

Execution status: `finished_with_review_errors`; this is not an official-answer score.

Model: `nvidia/moonshotai/kimi-k3`. Maximum 32 solver jobs. Independent reviews use fresh Kimi contexts, without feedback to solvers.

Native goal outcomes: `{'goal_complete': 67, 'goal_blocked': 1}`.
Fresh canonical-path Lean passes: 66/68.
Review states: `{'reviewed': 66, 'review_error': 2}`. Accepted with fresh evidence: 31/68.

Goal completion and Lean compilation alone do not establish chemistry correctness. Pending reviews are not failures. Conditional findings will remain conditional. Official-answer comparison of the frozen answers is now complete: **340.2/437 (77.85%)**, **47.674/60 (79.46%)**. See [GRADING.md](../grading/GRADING.md).

Review errors mean no valid structured verdict was obtained, not a scientific failure or acceptance. A semantic/proof passed pair can still fail the aggregate gate (for example, a nonempty unsupported-assumptions field). Original reviewer fields are preserved, including inconsistencies.

Original problem PDF and blank student answer sheets were supplied before launch. PyMuPDF was installed before this Kimi run. Historical answers and supplementary user model assumptions were not supplied.

Transport-only recoveries preserve existing threads and candidates: see [transport audit](TRANSPORT.md). Reviewer interface preflight and host JSON validation are recorded in [interface amendment](../reviews/interface-amendment.json). These amendments do not change scientific inputs or acceptance criteria.

An alternate-path receipt is a filename exception, not a canonical artifact pass. Reported goal tokens are not a provider billing total and exclude separate reviewer/preflight usage.

## Final dispositions

- icho_2026_t1_a6: **failed**; rerun: False. Terminal goal_blocked; independent semantic and proof reviews both failed. Not awaiting further solver work.

Original native statuses and reviewer verdicts are preserved; these terminal failures are not pending solver work.

| Target | Goal | Canonical Lean | Fresh hashes | Semantic | Proof | Accepted |
|---|---|---|---|---|---|---|
| [icho_2026_t1_a1](../jobs/icho_2026_t1_a1/campaign/workspace/) | goal_complete | passed | True | passed | conditional | False |
| [icho_2026_t1_a2](../jobs/icho_2026_t1_a2/campaign/workspace/) | goal_complete | passed | True | passed | conditional | False |
| [icho_2026_t1_a3](../jobs/icho_2026_t1_a3/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t1_a4](../jobs/icho_2026_t1_a4/campaign/workspace/) | goal_complete | passed | True | conditional | conditional | False |
| [icho_2026_t1_a5](../jobs/icho_2026_t1_a5/campaign/workspace/) | goal_complete | passed | True | conditional | conditional | False |
| [icho_2026_t1_a6](../jobs/icho_2026_t1_a6/campaign/workspace/) | goal_blocked | passed | True | failed | failed | False |
| [icho_2026_t2_a1](../jobs/icho_2026_t2_a1/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t2_a2](../jobs/icho_2026_t2_a2/campaign/workspace/) | goal_complete | passed | True | passed | passed | False |
| [icho_2026_t2_a3](../jobs/icho_2026_t2_a3/campaign/workspace/) | goal_complete | passed | True | passed | passed | False |
| [icho_2026_t2_a4](../jobs/icho_2026_t2_a4/campaign/workspace/) | goal_complete | passed | True | passed | passed | False |
| [icho_2026_t2_a5](../jobs/icho_2026_t2_a5/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t2_a6](../jobs/icho_2026_t2_a6/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t2_a7](../jobs/icho_2026_t2_a7/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t3_a1](../jobs/icho_2026_t3_a1/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t3_a2](../jobs/icho_2026_t3_a2/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t3_a3](../jobs/icho_2026_t3_a3/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t3_a4](../jobs/icho_2026_t3_a4/campaign/workspace/) | goal_complete | passed | True | passed | passed | False |
| [icho_2026_t3_a5](../jobs/icho_2026_t3_a5/campaign/workspace/) | goal_complete | passed | True | passed | conditional | False |
| [icho_2026_t3_a6](../jobs/icho_2026_t3_a6/campaign/workspace/) | goal_complete | not_run (alternate-path receipt) | True | conditional | conditional | False |
| [icho_2026_t3_a7](../jobs/icho_2026_t3_a7/campaign/workspace/) | goal_complete | passed | True | passed | passed | False |
| [icho_2026_t4_a1](../jobs/icho_2026_t4_a1/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t4_a2](../jobs/icho_2026_t4_a2/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t4_a3](../jobs/icho_2026_t4_a3/campaign/workspace/) | goal_complete | passed | True | failed | failed | False |
| [icho_2026_t4_a4](../jobs/icho_2026_t4_a4/campaign/workspace/) | goal_complete | passed | True | passed | passed | False |
| [icho_2026_t4_a5](../jobs/icho_2026_t4_a5/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t4_a6](../jobs/icho_2026_t4_a6/campaign/workspace/) | goal_complete | not_run (alternate-path receipt) | True | passed | passed | False |
| [icho_2026_t4_a7](../jobs/icho_2026_t4_a7/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t4_a8](../jobs/icho_2026_t4_a8/campaign/workspace/) | goal_complete | passed | True | conditional | conditional | False |
| [icho_2026_t4_a9](../jobs/icho_2026_t4_a9/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t5_a1](../jobs/icho_2026_t5_a1/campaign/workspace/) | goal_complete | passed | True | conditional | passed | False |
| [icho_2026_t5_a2](../jobs/icho_2026_t5_a2/campaign/workspace/) | goal_complete | passed | True | passed | passed | False |
| [icho_2026_t5_a3](../jobs/icho_2026_t5_a3/campaign/workspace/) | goal_complete | passed | True | pending | pending | False |
| [icho_2026_t5_a4](../jobs/icho_2026_t5_a4/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t5_a5](../jobs/icho_2026_t5_a5/campaign/workspace/) | goal_complete | passed | True | conditional | conditional | False |
| [icho_2026_t5_a6](../jobs/icho_2026_t5_a6/campaign/workspace/) | goal_complete | passed | True | conditional | failed | False |
| [icho_2026_t6_a1](../jobs/icho_2026_t6_a1/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t6_a2](../jobs/icho_2026_t6_a2/campaign/workspace/) | goal_complete | passed | True | failed | conditional | False |
| [icho_2026_t6_a3](../jobs/icho_2026_t6_a3/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t6_a4](../jobs/icho_2026_t6_a4/campaign/workspace/) | goal_complete | passed | True | conditional | conditional | False |
| [icho_2026_t6_a5](../jobs/icho_2026_t6_a5/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t6_a6](../jobs/icho_2026_t6_a6/campaign/workspace/) | goal_complete | passed | True | failed | failed | False |
| [icho_2026_t6_a7](../jobs/icho_2026_t6_a7/campaign/workspace/) | goal_complete | passed | True | conditional | conditional | False |
| [icho_2026_t7_a1](../jobs/icho_2026_t7_a1/campaign/workspace/) | goal_complete | passed | True | conditional | conditional | False |
| [icho_2026_t7_a2](../jobs/icho_2026_t7_a2/campaign/workspace/) | goal_complete | passed | True | conditional | passed | False |
| [icho_2026_t7_a3](../jobs/icho_2026_t7_a3/campaign/workspace/) | goal_complete | passed | True | failed | failed | False |
| [icho_2026_t7_a4](../jobs/icho_2026_t7_a4/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t7_a5](../jobs/icho_2026_t7_a5/campaign/workspace/) | goal_complete | passed | True | failed | failed | False |
| [icho_2026_t7_a6](../jobs/icho_2026_t7_a6/campaign/workspace/) | goal_complete | passed | True | conditional | passed | False |
| [icho_2026_t7_a7](../jobs/icho_2026_t7_a7/campaign/workspace/) | goal_complete | passed | True | passed | passed | False |
| [icho_2026_t8_a1](../jobs/icho_2026_t8_a1/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t8_a2](../jobs/icho_2026_t8_a2/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t8_a3](../jobs/icho_2026_t8_a3/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t8_a4](../jobs/icho_2026_t8_a4/campaign/workspace/) | goal_complete | passed | True | passed | conditional | False |
| [icho_2026_t8_a5](../jobs/icho_2026_t8_a5/campaign/workspace/) | goal_complete | passed | True | pending | pending | False |
| [icho_2026_t8_a6](../jobs/icho_2026_t8_a6/campaign/workspace/) | goal_complete | passed | True | passed | passed | False |
| [icho_2026_t8_a7](../jobs/icho_2026_t8_a7/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t8_a8](../jobs/icho_2026_t8_a8/campaign/workspace/) | goal_complete | passed | True | conditional | conditional | False |
| [icho_2026_t8_a9](../jobs/icho_2026_t8_a9/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t8_a10](../jobs/icho_2026_t8_a10/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t9_a1](../jobs/icho_2026_t9_a1/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t9_a2](../jobs/icho_2026_t9_a2/campaign/workspace/) | goal_complete | passed | True | failed | failed | False |
| [icho_2026_t9_a3](../jobs/icho_2026_t9_a3/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t9_a4](../jobs/icho_2026_t9_a4/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t9_a5](../jobs/icho_2026_t9_a5/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t9_a6](../jobs/icho_2026_t9_a6/campaign/workspace/) | goal_complete | passed | True | passed | conditional | False |
| [icho_2026_t9_a7](../jobs/icho_2026_t9_a7/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t9_a8](../jobs/icho_2026_t9_a8/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
| [icho_2026_t9_a9](../jobs/icho_2026_t9_a9/campaign/workspace/) | goal_complete | passed | True | passed | passed | True |
