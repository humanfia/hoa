# Verification record — icho_2026_t4_a7

## Commands and results

1. `lake build IChO2026Chem`
   - Result: `Build completed successfully (8561 jobs).` — builds the shared
     chemistry/reporting infrastructure (`IChO2026Chem.Core`,
     `IChO2026Chem.Reporting`) that the problem file imports.

2. `lake env lean IChO2026Problems/problem_icho_2026_t4_a7.lean`
   - Result (stdout, exit code 0, no errors/warnings, no `sorry`):

     ```
     'IChO2026Problems.Icho2026T4A7.reaction_enthalpy_2000_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
     'IChO2026Problems.Icho2026T4A7.final_submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
     ```

   - Both final theorems depend only on the standard Lean logical axioms
     (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`, no custom
     unchecked axioms. The `#print axioms` diagnostics are embedded at the end
     of the problem file itself, so every re-check re-verifies them.

## Theorem inventory

- `IChO2026Problems.Icho2026T4A7.CombustionStoichiometry.unique` — atom
  balances + one-mole-of-methane normalization force ν = (−1, −2, +1, +2).
- `IChO2026Problems.Icho2026T4A7.reaction_enthalpy_298` — ΔrH°₂₉₈ = −802.3
  kJ mol⁻¹ (Part 4.6 prerequisite derived from the problem data via Hess's
  law).
- `IChO2026Problems.Icho2026T4A7.reaction_heat_capacity` — ΔCₚ = 12
  J mol⁻¹ K⁻¹ from the problem's constant Cₚ table.
- `IChO2026Problems.Icho2026T4A7.reaction_enthalpy_2000_exact` — final: with
  Kirchhoff's law at constant Cₚ, ΔrH₂₀₀₀ = −781.876 kJ mol⁻¹ exactly.
- `IChO2026Problems.Icho2026T4A7.rawAnswer2000_eq` — the solver-owned raw
  expression equals the same exact value.
- `IChO2026Problems.Icho2026T4A7.reported_at_2000` — reporting certificate:
  −782 is the nearest 1 kJ mol⁻¹ quantum (3 s.f.) to the raw value, ties-away
  convention.
- `IChO2026Problems.Icho2026T4A7.final_submission_valid` — full
  answer-blind submission validity.

## Semantic faithfulness check (independent of build success)

- The reaction formalized is exactly the one the problem statement names:
  methane combustion, all species gaseous (CH₄(g) + 2 O₂(g) → CO₂(g) +
  2 H₂O(g)); stoichiometry is proved from atom balances rather than asserted.
- Every numerical constant in the Lean file appears verbatim in the Part 4.6
  data table / Part 4.7 question (−74.8, −241.8, −393.5, 35, 34, 29, 37,
  T = 2000 K, reference 298 K); the only additional input is ΔfH°₂₉₈(O₂) = 0
  (element in standard state — trusted general law).
- The formula is Kirchhoff's law with constant Cₚ, which is the intended
  route: the problem gives single Cₚ values and no temperature dependence.
- Arithmetic cross-check by hand: −393.5 + 2(−241.8) + 74.8 = −802.3;
  37 + 68 − 35 − 58 = 12; 12/1000 × 1702 = 20.424;
  −802.3 + 20.424 = −781.876 → −782 (3 s.f.).

## Assumptions / gaps

- Heat capacities treated as temperature independent over 298–2000 K. The
  problem supplies exactly one Cₚ value per species and no functional
  dependence; this is the only reading the problem grounds. No gap: the
  underdetermination policy is satisfied because the problem itself fixes the
  model.
- ΔfH°₂₉₈(O₂(g)) = 0: trusted general law (standard-state convention).
- The conditional fallback values (−750 for 4.6, −700 for 4.7) are not used;
  they apply only when the corresponding part was not answered.
- `IChO2026Problems/All.lean` is reserved for the trusted controller
  (per the fixed umbrella note in `IChO2026Problems.lean`), so verification is
  performed with `lake env lean` on the target file directly; no source inputs
  or generic infrastructure were modified.
