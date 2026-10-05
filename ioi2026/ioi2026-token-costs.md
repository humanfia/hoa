# IOI 2026 six-problem token-cost report

Generated: 2026-08-14 UTC

## Pricing basis

This is an **API-equivalent text-token estimate**, not an assertion about the
actual ChatGPT Business invoice. The experiments used `gpt-5.6-sol:max`.
Published GPT-5.6 Sol rates are:

- uncached input: **$5.00 per 1M tokens**;
- cached input: **$0.50 per 1M tokens**;
- output: **$30.00 per 1M tokens**.

Source: [OpenAI GPT-5.6 Sol model documentation](https://developers.openai.com/api/docs/models/gpt-5.6-sol).

The documentation applies 2x input and 1.5x output pricing to an individual
request with more than 272K input tokens. The cost calculation reconstructed
individual requests from cumulative rollout-ledger deltas; none crossed that
threshold. The ledgers recorded zero cache-write tokens. Reasoning tokens are
already included in output tokens and are not charged a second time.

## Cost by problem

| Day | Problem | Worker cost | Reviewer-side cost | Total cost |
|---|---|---:|---:|---:|
| 1 | Ball Machine | $78.97 | $64.47 | **$143.44** |
| 1 | Monuments | $10.52 | $15.68 | **$26.20** |
| 1 | Tiling Game | $16.12 | $22.81 | **$38.92** |
| 2 | Classroom Game | $19.05 | $29.43 | **$48.48** |
| 2 | Magic City | $12.02 | $8.26 | **$20.28** |
| 2 | Partition | $33.51 | $19.55 | **$53.06** |
|  | **All six** | **$170.19** | **$160.19** | **$330.37** |

Unrounded totals used in the calculation:

| Problem | Worker cost | Reviewer-side cost | Total cost |
|---|---:|---:|---:|
| Ball Machine | $78.966311 | $64.472921 | $143.439232 |
| Monuments | $10.520218 | $15.675078 | $26.195296 |
| Tiling Game | $16.119013 | $22.805159 | $38.924172 |
| Classroom Game | $19.052569 | $29.427998 | $48.480567 |
| Magic City | $12.020366 | $8.258379 | $20.278745 |
| Partition | $33.506646 | $19.549986 | $53.056632 |
| **All six** | **$170.185123** | **$160.189521** | **$330.374644** |

## Cost by contest day

| Day | Total cost |
|---|---:|
| Day 1 | $208.558700 |
| Day 2 | $121.815944 |
| **Both days** | **$330.374644** |

## Aggregate token and price components

| Component | Tokens | Rate per 1M | Cost |
|---|---:|---:|---:|
| Uncached input | 15,367,120 | $5.00 | $76.835600 |
| Cached input | 304,415,488 | $0.50 | $152.207744 |
| Output, including reasoning | 3,377,710 | $30.00 | $101.331300 |
| **Total** | **323,160,318** |  | **$330.374644** |

## Scope

`Worker` includes implementation, recovery, and outer finalization sessions.
`Reviewer-side` includes Humanize round reviewers, full-alignment and guardian
checks, mandatory final code review, and final simplifier reviews. Failed,
interrupted, recovery, and successful sessions are included because all of
them consumed tokens. Top-level orchestration-agent tokens, local shell work,
and tool execution are excluded.
