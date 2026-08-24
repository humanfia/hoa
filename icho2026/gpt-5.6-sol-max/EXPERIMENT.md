# IChO 2026 Humanize experiment: GPT-5.6 max

## Outcome

Nine isolated Humanize RLCR workers solved Q1 through Q9 in parallel. Every
worker exited successfully, every final Humanize state is complete, every
final alignment review ends in `COMPLETE`, and all nine structural validators
pass on the consolidated result branch.

The run started at 2026-08-10 06:27 UTC and the final worker completed at
2026-08-10 08:14 UTC.

## Configuration

- Worker model: `gpt-5.6-sol`
- Reasoning effort: `max`
- Humanize alignment reviewer: `gpt-5.6-sol` at `max`
- Humanize review model: `gpt-5.6-sol` at `max`
- Parallelism: nine isolated Git worktrees and branches
- Maximum Humanize iterations per problem: 8
- Worker network setting: disabled
- Response format: natural-language Markdown with calculations and textual
  chemical structures
- Formal prover: none; Lean was not used
- Sources: only the local official problem PDF text/page images and local
  general booklet; Wikipedia, wiki sources, web search, external answer keys,
  prior solutions, and cross-worker communication were prohibited

Each worker had a separate `CODEX_HOME`, its own Humanize loop state, and
access only to the files for its assigned problem plus the general booklet.

## Results

| Problem | Preserved source branch | Final source head | Final review round | Bytes | Result |
|---|---|---:|---:|---:|---|
| Q1 | `humanize-gpt56max-q01` | `26a40f5` | 0 | 8168 | COMPLETE |
| Q2 | `humanize-gpt56max-q02` | `295cb5c` | 0 | 8827 | COMPLETE |
| Q3 | `humanize-gpt56max-q03` | `3cdb991` | 0 | 13954 | COMPLETE |
| Q4 | `humanize-gpt56max-q04` | `1f97e01` | 0 | 8074 | COMPLETE |
| Q5 | `humanize-gpt56max-q05` | `6d14b81` | 0 | 8595 | COMPLETE |
| Q6 | `humanize-gpt56max-q06` | `10efb99` | 1 | 11256 | Corrected significant figures; COMPLETE |
| Q7 | `humanize-gpt56max-q07` | `dcfe5f7` | 0 | 10309 | COMPLETE |
| Q8 | `humanize-gpt56max-q08` | `0a73325` | 0 | 10803 | COMPLETE |
| Q9 | `humanize-gpt56max-q09` | `d777b5f` | 0 | 11476 | COMPLETE |

Q6 was the only worker requiring another implementation round. Its reviewer
found that the energy derived from 2.5 V had been displayed with three
significant figures. Round 1 changed the reported result to
`2.4 x 10^2 kJ mol^-1`, retained the unrounded value for the bond-energy
threshold comparison, and passed a second independent alignment review.

## Verification

The final audit required, for every problem:

- runner state `complete`, exit code 0, and `humanize_complete=true`;
- a nonempty Humanize `complete-state.md` and `finalize-summary.md`;
- exact `codex_model: gpt-5.6-sol` and `codex_effort: max` metadata;
- a final alignment-review result ending in `COMPLETE`;
- a clean isolated Git worktree whose only tracked delta from the experiment
  scaffold is its assigned `solutions/QN.md`;
- a successful `scripts/validate_solution.py N` run; and
- a clean `git diff --check` result.

The generic `codex review` subprocess could not run repository shell commands
because this host disallows the nested Bubblewrap namespace it requested. The
Humanize alignment reviewers were unaffected and performed the substantive
source, chemistry, completeness, and acceptance-criteria audits. The final
post-run validation and Git-diff audit were also run independently across all
nine branch heads.

## Preservation

- Consolidated branch: `gpt56-sol-max-results`
- Consolidated worktree: `/root/zhengyang-workspace/icho-2026-humanize-gpt56-sol-max-results`
- Original GPT-5.5 result branch: `main` in the source repository
- Original GPT-5.5 Humanize/runtime archive:
  `/root/zhengyang-workspace/icho-2026-humanize-gpt55-xhigh-archive-20260809`

The consolidated branch starts from the experiment scaffold and contains the
nine reviewed GPT-5.6 solution files plus this report. It does not overwrite
the earlier GPT-5.5 solutions.
