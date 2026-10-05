# Verification record — icho_2026_t4_a8

## Build environment

* Workspace: `jobs/icho_2026_t4_a8/campaign/workspace`
* Lean toolchain: `leanprover/lean4:v4.31.0` (`lake --version` →
  `Lake version 5.0.0-src+68218e8 (Lean version 4.31.0)`)
* Dependencies pinned through the shared prebuilt package store: Mathlib
  v4.31.0, Physlib `1706ae68…`, crnt-lean `99137993…`.

## Exact commands run and their results

1. `lake build IChO2026Chem`
   → `Build completed successfully (8561 jobs).`
   (only pre-existing style-linter warnings about header copyright in the
   fixed infrastructure files `IChO2026Chem/Core.lean`,
   `IChO2026Chem/Reporting.lean`; generic infrastructure was not modified).

2. `lake env lean IChO2026Problems/problem_icho_2026_t4_a8.lean`
   → exit code 0, **no output** (no errors, no warnings, no `sorry`).
   Elapsed ≈ 1 min (12.2 s user, 65.6 s wall on the shared store).

3. `lake build IChO2026Problems.problem_icho_2026_t4_a8`
   → `✔ Built IChO2026Problems.problem_icho_2026_t4_a8 (34s).`
   `Build completed successfully (8559 jobs).`

4. Axiom inspection. A temporary script (since deleted) containing
   `import IChO2026Problems.problem_icho_2026_t4_a8` plus `#print axioms`
   for each final theorem was run with `lake env lean`. Output:

   ```
   'IChO2026T4A8.h_dH298'                    → [propext, Classical.choice, Quot.sound]
   'IChO2026T4A8.h_deltaCp'                  → [propext, Classical.choice, Quot.sound]
   'IChO2026T4A8.h_dH2000'                   → [propext, Classical.choice, Quot.sound]
   'IChO2026T4A8.molarFlowPerDay_eq'         → [propext, Classical.choice, Quot.sound]
   'IChO2026T4A8.rawDailyEnergy_eq'          → [propext, Classical.choice, Quot.sound]
   'IChO2026T4A8.dailyEnergy_rounds_three_sig' → [propext, Classical.choice, Quot.sound]
   'IChO2026T4A8.validSubmission'            → [propext, Classical.choice, Quot.sound]
   'IChO2026T4A8.dailyEnergy_gt'             → [propext, Classical.choice, Quot.sound]
   'IChO2026T4A8.dailyEnergy_lt'             → [propext, Classical.choice, Quot.sound]
   'IChO2026T4A8.energy_per_hour_gt_tnt'     → [propext, Classical.choice, Quot.sound]
   ```

   Only the three standard Lean logical axioms appear; no custom or
   unchecked axioms are introduced anywhere in the file.

5. `#check` spot inspection of the final statements
   (`lake env lean` on a scratch script):

   ```
   IChO2026T4A8.rawDailyEnergy_eq :
     rawDailyEnergy = 25098031949760000000000 / 41273
   IChO2026T4A8.validSubmission :
     IChO2026Chem.Reporting.ValidNumericSubmission rawDailyEnergy submission
   ```

## Independence checks of the semantics

* The raw rational `25098031949760000000000 / 41273` was reproduced with an
  independent exact-rational computation (Python `fractions`) from the
  printed inputs:
  `781876 × 101325 × (2.2×10⁵) × 86400 / (8.31 × 298)`; equality holds, and
  the decimal is `6.080980774297967…×10¹⁷ J day⁻¹`.
* The rounding certificate was verified independently:
  `E / 10¹⁵ = 608.09807742…`, fractional part `0.09807… < 1/2`, so the
  3-significant-figure display is `6.08×10¹⁷ J day⁻¹` under the
  half-away-from-zero tie rule of `IChO2026Chem.Reporting`.
* Sensitivity: replacing `R = 8.31` by `R = 8.314` gives `6.079×10¹⁷`
  (unchanged at 3 s.f.); using the printed 4.7 fallback `−700 kJ mol⁻¹`
  instead of the derived `−781.876 kJ mol⁻¹` would give `5.45×10¹⁷ J day⁻¹`
  (fallback not needed, as required, since 4.7 was derived inline).

## No-shortcut audit

`grep -n "sorry\|admit\|axiom \|native_decide\|unsafe" IChO2026Problems/problem_icho_2026_t4_a8.lean`
→ no matches. Source inputs (`icho_2026_source/…`, `TASK.json`,
infrastructure libraries) were not modified.
