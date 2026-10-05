# Blind Humanize IMO 2026 Proof: {{PROBLEM}}

## Goal

Solve every theorem hole in the exact IMO 2026 statement snapshot in
`MathFlowBench/{{MODULE}}.lean` without consulting prior solutions.

## Acceptance Criteria

- AC-1: Original declarations, theorem signatures, and docstrings are preserved.
- AC-2: The candidate contains no `sorry`, `admit`, `axiom`, or `native_decide`.
- AC-3: `lake env lean MathFlowBench/{{MODULE}}.lean` succeeds.
- AC-4: `bash tools/check-with-comparator.sh` ends with `Your solution is okay!`.
- AC-5: The isolated AXLE reviewer returns Boolean `okay: true` against the
  exact upstream problem statement using the Lean 4.31.0 AXLE environment.

## Constraints

- The worker may read only this sanitized workspace and the mounted Mathlib tree.
- The worker must not use the Internet, prior attempts, session archives, or existing solutions.
- The reviewer must not edit the candidate. Its only permitted external network call is AXLE verification.
- The worker uses Kimi Code with model `{{KIMI_MODEL}}` and thinking enabled.
- The independent reviewer uses Codex model `{{CODEX_MODEL}}` with
  `{{CODEX_REASONING_EFFORT}}` reasoning effort.
- Stop after at most {{MAX_TURNS}} worker/reviewer turns.
