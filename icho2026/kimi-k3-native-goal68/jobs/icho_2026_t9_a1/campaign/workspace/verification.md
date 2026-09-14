# Verification record — icho_2026_t9_a1

## Deliverables

- `answer.md` — natural-language answer and source-grounding explanation.
- `IChO2026Problems/problem_icho_2026_t9_a1.lean` — Lean 4 formalization.
- `IChO2026Problems/All.lean` — umbrella (imports only this target, as allowed by the fixed controller).

## Sources used

- Q9-1 problem statement: `icho_2026_source/image/T9_page-1.png` and `icho_2026_source/raw/theory_problem.pdf` page 84.
- Blank student answer sheet: `theory_problem.pdf` page 89 (A9-1), showing `M𝑤 : β-CD = ____`.
- Atomic masses: IChO 2026 data sheet printed on the inside front cover of `theory_problem.pdf` (A_r(H)=1.008, A_r(O)=16.00).

No official solutions, marking schemes, grading reports, historical answers, or answer repositories were used.

## Verification commands and results

1. Initial build of the shared scaffold:
   ```
   lake build
   ```
   Result: completed successfully (8581 jobs).

2. Direct check of the final target file (deterministic, no cache dependency):
   ```
   lake env lean IChO2026Problems/problem_icho_2026_t9_a1.lean
   ```
   Exit code: `0`. Output:
   ```
   'IChO2026Problems.T9A1.waterMass_value' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026Problems.T9A1.betaCDMolarMass_value' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026Problems.T9A1.betaCDMolarMass_reports_1135' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026Problems.T9A1.betaCDSubmission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

## Axiom audit

All final theorems depend only on the standard Lean logical axioms `propext`, `Classical.choice`, and `Quot.sound`. There are no custom or unchecked axioms, no `sorry`/`admit`, and no `unsafe` code.

## Semantic faithfulness check

- The theorem `betaCDMolarMassRaw` is defined as `7 * glucoseMass − 7 * waterMass`, i.e. 7 glucose units minus 7 waters, which matches the chemically correct formula `C₄₂H₇₀O₃₅` for β-CD.
- `waterMass_value` proves `2×1.008 + 16.00 = 18.016` exactly.
- `betaCDMolarMass_value` proves the raw value is exactly `1135008/1000 = 1135.008 g mol⁻¹`.
- `betaCDMolarMass_reports_1135` proves via the fixed `ReportsAtQuantum` relation that, at quantum `1 g mol⁻¹` with ties half-away-from-zero, the raw value rounds to `1135 g mol⁻¹`, matching the TASK.json three-significant-figure requirement.
- `betaCDSubmission_valid` ties the exact raw expression to the printed answer, separating raw value from displayed value as required by the answer-blind protocol.

The formalization therefore proves the requested chemistry from the stated problem inputs and the data sheet, with no weakening of the statement.
