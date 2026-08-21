# IPhO 2026 Kimi K3 Max submission

This directory contains the Kimi answer-blind submission for all 41 subparts
of IPhO 2026 and its separate post-completion grading audit.

## Contents

- `Ipho2026KimiK3Blind32/Solutions/` — the 41 Lean answer files.
- `Ipho2026KimiK3Blind32.lean` — an aggregate import for the full answer set.
- `GRADING_REPORT.md` — comparison with the official answers and marking
  schemes.

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
