# Verification — IChO 2026 T2-A2

## Commands executed

1. Build shared infrastructure (provides `IChO2026Chem.Reporting` olean):

   ```
   lake build IChO2026Chem
   ```
   Result: `Build completed successfully (8561 jobs).`

2. Compile and check the target formalization (exact command):

   ```
   lake env lean IChO2026Problems/problem_icho_2026_t2_a2.lean
   ```
   Result: exit code 0, no errors, no warnings (a previous `hX` unused-variable
   warning was fixed by renaming to `_hX`), no `sorry`.

3. `#print axioms` output (embedded at the end of the target file, reproduced
   verbatim from the run in step 2):

   ```
   'IChO2026.T2.A2.hbro2_process_A' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T2.A2.hbro2_process_B' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T2.A2.hbro2A_value' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T2.A2.hbro2B_value' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T2.A2.valid_submission_A' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T2.A2.valid_submission_B' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.T2.A2.icho_2026_t2_a2_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Only the standard Lean logical axioms appear; no custom axioms, no
   `sorryAx`.

## Semantic faithfulness audit (independent of build success)

- The target question (statement Q2-2, box 2.2, and blank answer sheets
  A2-1/A2-2) requests two numbers: stationary `[HBrO₂]A` and `[HBrO₂]B`
  in mol dm⁻³ under the steady-state approximation.
- `hbro2_process_A` formalizes the exact SSA balance derived from
  Process A stoichiometry: radical SSA (r₂ = 2 r₁, recorded as hypotheses
  `hYssa`/`hrad` with Ce species `u+ v`) plus HBrO₂ SSA (−r₁ + r₂ − 2 r₃ = 0)
  collapse to `k₁ X B H = 2 k₃ X²` (`h1`); the theorem proves the unique
  positive root equals the closed form `k₁·B·H/(2 k₃)`. `hbro2A_value`
  evaluates it with the printed constants (1.0e4, 0.06, 0.8, 4.0e7) to
  exactly `6.0e-6`.
- `hbro2_process_B` formalizes the Process B SSA: only steps 4/5 involve
  HBrO₂ (step 6 does not), giving `k₅ B Br H² = k₄ X Br H` (`h2`); after
  cancelling the common nonzero factor `Br·H` (Br⁻ held constant), the
  unique positive root is `k₅·B·H/k₄ = 5.04e-11`.
- `valid_submission_A/B` prove the reported values 6.00e-6 / 5.04e-11 are
  the nearest multiples of the 3-significant-figure quanta (1.0e-8 / 1.0e-13)
  with no tie, satisfying the project-wide `ValidNumericSubmission` contract
  (raw value kept exact; no intermediate rounding).
- Consistency cross-check with the problem's own printed fallback values
  (1 × 10⁻⁵ M and 1 × 10⁻¹⁰ M, supplied only for later parts): orders of
  magnitude match (6.00 × 10⁻⁶ vs 10⁻⁵; 5.04 × 10⁻¹¹ vs 10⁻¹⁰), confirming
  no factor-of-100 slip in the derivation.

## Files

- `answer.md` — natural-language solution and source grounding.
- `IChO2026Problems/problem_icho_2026_t2_a2.lean` — formalization.
- `result.json` — run record.

## Note

Lean is compiled with toolchain `leanprover/lean4:v4.31.0`, lake dependency
graph pinned by `lakefile.toml`/`lake-manifest.json`; no source inputs or
generic infrastructure were modified.
