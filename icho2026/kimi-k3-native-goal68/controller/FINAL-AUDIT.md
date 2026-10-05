# Final experiment audit

The fresh Kimi-K3 native-goal 68-target run and its independent validation/review attempts have ended. This is an experiment completion record, not a claim that every answer or proof passed.

- Endpoint and multimodal/tool/native-goal compatibility: `preflight.json` and `TRANSPORT.md`. Early failures remain in `provider-compatibility.json`; the later successful preflight preceded solver launch.
- Scope/model: `../manifest.json`, 68 targets, `nvidia/moonshotai/kimi-k3`, NVIDIA endpoint, no Humanize loop. No historical generated answers or supplementary user model assumptions were supplied.
- Native persisted goals: `native-record-audit.json`, freshly replayed after all jobs ended: 68 distinct threads, 67 complete and 1 blocked; objectives, task IDs, and reported token usage agree. Recorded solver interval peak is 32, with no skipped intervals. This is not a process-level concurrency trace.
- Isolation/input evidence: `input-snapshot-audit.json`, manifest seed hashes (rechecked in native audit), and problem-only seed isolation manifest. Original questions and blank answer sheets are authorized. Other generated candidates and reviews are not solver inputs. Ordinary scientific HTTP was permitted; zero native web-search events is not proof of full network isolation.
- Artifact integrity: `final-artifact-audit.json` checks all 68 original and reviewer-copy candidate hash sets. All are fresh. All 66 structured verdicts reproduce under the existing strict aggregate gate.
- Lean: 66 canonical-path passes. T3-A6 and T4-A6 have independently compiled alternate-path receipts, with current source hashes verified; they are not relabeled canonical passes. Compilation does not establish chemistry correctness or compliance with the proof policy.
- Review: 66 structured results, 31 aggregate acceptances. T5-A3 and T8-A5 ended with prose-only outputs, not valid structured verdicts; their original outputs and failed format-recovery records are preserved. They are neither accepted nor silently assigned scientific failure verdicts. No reviewer feedback was supplied to solvers.
- Semantic verdicts: 46 passed, 13 conditional, 7 failed, 2 unavailable. Proof verdicts: 44 passed, 15 conditional, 7 failed, 2 unavailable. Aggregate acceptance additionally requires complete output coverage, no listed unsupported assumptions, artifact conformance, and fresh evidence. Reviewer field inconsistencies were not silently corrected.
- T1-A6 is final failed/no rerun by user instruction; original native blocked and failed review records remain unchanged.
- Review limitation: T6-A6's reviewer noted an apparent mismatch between the requested P output and the printed scheme. The original task and verdict are preserved, not retroactively repaired.
- Usage: 21,134,287 reported native goal tokens, excluding separate review/preflight work; not a provider billing total.
- Relevant regression tests: 35 passed. No solver restart, extra scientific assumptions, commit, or push was performed during final audit. Prior experiments remain separate.
- All known solver, validation, and review controller handles were confirmed absent after terminal results. No jobs remain queued.
- `../reviews/status.json` is the controller's original exit snapshot (65 reviewed, 3 errors, 30 accepted), before host-only T9-A9 format recovery. The current per-target records and `results-summary.json` supersede those counts (66 reviewed, 2 errors, 31 accepted); the exit snapshot is preserved for provenance.

Official-answer comparison of the frozen answers is recorded in [GRADING.md](../grading/GRADING.md): 340.2/437 raw, 47.674/60 weighted. The 31/68 aggregate acceptance fraction is **not** an official-answer accuracy score.

See [per-target results](RESULTS.md) and [machine-readable summary](results-summary.json).
