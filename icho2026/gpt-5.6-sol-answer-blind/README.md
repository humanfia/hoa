# GPT-5.6 Sol answer-blind Lean formalizations

> [!NOTE]
> [Humanize](https://humanfia.ai) is part of the RSI effort and is led by [NVIDIA Research](https://research.nvidia.com/).

This directory publishes the standalone Lean 4 project produced by the fresh
GPT-5.6 Sol answer-blind run over 32 selected IChO 2026 theory subquestions.
The model received the official problem statements and images, but not the
official solutions. Official-answer comparison occurred only after generation
and review had finished.

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

Generation used OpenAI `gpt-5.6-sol` through Codex. The release project comes
from source commit `c9fcdb4c7abcb33f242edc401bef9131f2417c53` in
`humanfia/science-mango`.

## Build

```bash
lake exe cache get
lake build
```

The normalized dataset records are available as
[`icho_2026_gpt_answer_blind.jsonl`](https://huggingface.co/datasets/humanfia-lab/icho-2026/blob/main/data/icho_2026_gpt_answer_blind.jsonl).

Runtime logs, prompts, model sessions, credentials, caches, official PDFs, and
source images are intentionally excluded.
