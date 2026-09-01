# Kimi-K3 answer-blind Lean formalizations

This directory publishes the standalone Lean 4 project produced by the fresh4
Kimi-K3 answer-blind run over the same 32 selected IChO 2026 theory
subquestions. The model received the official problem statements and images,
but not the official solutions. Official-answer comparison occurred only after
the campaign had terminated.

For evaluation convenience, the linked normalized JSONL includes official
solution and rubric text as post-run metadata. Those fields were never model
inputs.

## Result

- Formalization review: 32/32 passed.
- Proof review: 32/32 solved.
- Default `lake build`: passed.
- Active `sorry`/`admit` placeholders: 0.
- Requested outputs: 47/47 equivalent to the official rubric answers under
  equivalent chemical notation and ordinary numerical precision.
- Grounding logs: 28 complete; four documentation warnings remain for T5-A4,
  T6-A3, T6-A4, and T6-A7. All four still compiled and passed both reviews.

Generation used `anthropic-kimi-k3` through Claude Code at source commit
`49360f26a1196d108ec98f66a341b5d04f3c6d2c` in
`humanfia/science-mango`. The run used four-way target concurrency, completed
in about 14 hours 13 minutes of wall time, and reported a cost of $309.3249.

Four stale comments describing an earlier proof-construction stage were
updated and one trailing blank line was normalized for publication; no Lean
declaration or proof term was changed.

## Build

```bash
lake exe cache get
lake build
```

The normalized dataset records are available as
[`icho_2026_kimi_k3_answer_blind.jsonl`](https://huggingface.co/datasets/humanfia-lab/icho-2026/blob/main/data/icho_2026_kimi_k3_answer_blind.jsonl).

Runtime logs, prompts, model sessions, credentials, caches, official PDFs, and
source images are intentionally excluded.
