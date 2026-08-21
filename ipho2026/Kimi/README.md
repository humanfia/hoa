# IPhO 2026 Kimi K3 Max submission

This directory contains two Kimi answer-blind submissions for IPhO 2026 and
their separate post-completion grading audits: the original Lean answer set
and a later natural-language, theory-only Humanize RLCR experiment.

## Contents

- `Ipho2026KimiK3Blind32/Solutions/` — the 41 Lean answer files.
- `Ipho2026KimiK3Blind32.lean` — an aggregate import for the full answer set.
- `GRADING_REPORT.md` — comparison of the Lean submission with the official
  answers and marking schemes.
- `NaturalLanguage/` — three Markdown theory solutions and their independent
  official-scheme grading report.

The worker configuration used Kimi K3 with maximum reasoning effort through
MagikCloud (`https://api.magikcloud.cn`). The run used independent target
workers in an answer-blind workspace; official answers were consulted only
after the answer set was complete.

## Build

The nested project is pinned to Lean and Mathlib `v4.31.0`.

```bash
cd Kimi
lake update
lake exe cache get
lake build
```

All 41 submitted modules elaborate. The answer sources contain no active
`sorry`, `admit`, custom axiom declaration, or unsafe declaration.
