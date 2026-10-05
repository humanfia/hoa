# Verification record — icho_2026_t2_a4 (IChO 2026, T2, part 2.4)

## Environment

- Project: `icho_2026_run`, Lean toolchain `leanprover/lean4:v4.31.0`,
  Mathlib `v4.31.0` (prebuilt in `.lake/packages`).
- Command lines were run from the workspace root
  `/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t2_a4/campaign/workspace`.

## 1. Direct elaboration of the target file

Command:

    lake env lean IChO2026Problems/problem_icho_2026_t2_a4.lean

Exit status: `0`. Output:

    'IChO2026T2A4.icho_2026_t2_a4_answer' does not depend on any axioms
    'IChO2026T2A4.icho_2026_t2_a4_phase_direction_checks' does not depend on any axioms
    'IChO2026T2A4.icho_2026_t2_a4_unique_direction' does not depend on any axioms
    'IChO2026T2A4.icho_2026_t2_a4_supports_choice' does not depend on any axioms
    'IChO2026T2A4.counterclockwise_traversal' depends on axioms: [propext, Classical.choice, Quot.sound]

The four final classification theorems depend on **no axioms at all**. The
auxiliary geometric lemma `counterclockwise_traversal` mentions the three
standard Lean logical axioms (`propext`, `Classical.choice`, `Quot.sound`),
which are permitted; no custom or unchecked axioms are introduced anywhere.

## 2. Full project build

Command:

    lake build

Result: `Build completed successfully (8581 jobs).` The only diagnostics are
the repository-wide style-linter warnings (file-header length, a long line in
the pre-existing umbrella `IChO2026Problems.lean`); there are no errors.

## 3. No-proof-shortcut check

Command:

    grep -nE 'sorry|admit|axiom |native_decide' IChO2026Problems/problem_icho_2026_t2_a4.lean

Result: no matches — the file contains no `sorry`, `admit`, `axiom`, or
`native_decide`. All proofs are by definitional unfolding (`rfl`), case
analysis, and explicit term construction.

## 4. Semantic faithfulness check (answer_blind protocol)

The requested output is a classification: the direction of motion in the
`[HBrO₂]` vs `[Br⁻]` phase portrait.

- The problem statement's own text between items 2.4 and 2.5 (printed page
  Q2-3 / `T2_page-3.png`) says "[Br⁻] slowly **decreases** from [Br⁻]max to
  [Br⁻]critical, and then almost immediately reaches [Br⁻]max again". This
  fixes the bottom edge as **right → left** and the fast legs (the vertical
  switch edges) as the immediate jumps. The formalization encodes this as
  `bottomBr = .dec` inside `CompatibleWithProblem`.
- Bromide is consumed by Process B steps (4) and (5) and *produced* by the
  continuous Process C step (7), so during Process A (top edge) [Br⁻]
  increases: `topBr = .inr`. At the B→A switch [HBrO₂] jumps up to its
  autocatalytic Process-A level (`leftHbro2 = .inr`); at the A→B switch
  (rate(4) > rate(1), as the problem states) [HBrO₂] is quenched
  (`rightHbro2 = .dec`).
- `icho_2026_t2_a4_answer` proves that the counterclockwise direction is
  the *unique* direction meeting these four problem-stated constraints and
  that the reversed (clockwise) option is excluded;
  `icho_2026_t2_a4_supports_choice` identifies the correct tick box as
  exactly the counterclockwise diagram (bottom-left on answer sheet A2-3).

Answer recorded in `answer.md`: **counterclockwise** traversal — bottom edge
leftward ([Br⁻]: max → critical), left edge upward ([HBrO₂]: B → A), top edge
rightward ([Br⁻]: critical → max), right edge downward ([HBrO₂]: A → B).

## 5. Source inputs used

- `TASK.json` (target contract, requested output `phase_direction`).
- `T2_page-3.png`, `T2_page-2.png` (question text, portrait, mechanism).
- `theory_problem.pdf`: printed pages Q2-1…Q2-4 (PDF pp. 15–18) and blank
  student answer sheets A2-1…A2-5 (PDF pp. 19–23), in particular the four
  tick-box options for 2.4 on A2-3 (PDF p. 21).

No official solutions, marking schemes, or external answer repositories were
consulted (`official_answer_seen = false`).
