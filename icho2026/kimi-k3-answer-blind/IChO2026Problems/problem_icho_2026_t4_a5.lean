import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T4 (Q4-2, part 4.5) — Neutron moderation: average number of collisions

**Source contract** (problem_text, Q4-2 box 4.5 on `T4_page-2.png`, together
with the shared context printed above it):

* "Fission neutrons are produced with an average energy of 2 MeV and slow down
  through many scatterings with nuclei." (shared context, problem_text,
  `T4_page-2.png`; the value 2 MeV is a stipulated constant, exact as printed).
* The **logarithmic energy decrement** is defined on the problem sheet by
  `ξ = ln (E_initial / E_final)`, where `E_initial` and `E_final` are the
  initial and final neutron energies *per collision*, and the sheet stipulates
  that "**ξ is a constant for each type of material and does not depend on the
  initial neutron energy**" (problem_text, `T4_page-2.png`).
* Box 4.5: "**Determine** the average number of collisions required, `n_c`, to
  slow a neutron from 2 MeV to 0.012 eV, using water as the moderator.
  ξ(water) = 0.948."  All three numerical inputs are stipulated constants,
  exact as printed; no measurement uncertainty is declared for them
  (source `measurement_policy`).
* Requested output: the average number of collisions `n_c` (unit: collisions).

**Unit bookkeeping** (trusted_general_law, SI prefix): `1 MeV = 10^6 eV`, so
`E₀ = 2 MeV = 2·10^6 eV` and `E_f = 0.012 eV` are expressed in the same unit
before the logarithm is taken; the ratio `E₀/E_f = (5·10^8)/3` is
dimensionless, as the printed definition `ξ = ln(E_initial/E_final)` requires.

**Governing relation** (problem_text stipulation + trusted_general_law of
averages of a per-collision constant): since ξ is the *average* decrease of
`ln E` per collision and is constant for water, after `n` collisions the
average total decrease of the logarithm of the neutron energy is `n·ξ`.
Slowing from `E₀` to `E_f` therefore requires

```
n_c · ξ = ln E₀ − ln E_f = ln (E₀/E_f),
```

which fixes `n_c` uniquely because `ξ = 0.948 ≠ 0`:

```
n_c = ln (E₀/E_f) / ξ = ln ((2·10^6) / 0.012) / 0.948
    = ln (500000000/3) / 0.948
    = 18.9315063… / 0.948 = 19.9699434… collisions.
```

No intermediate rounding is applied; the Lean carrier below is the exact
unrounded expression over the stipulated constants, not a precomputed decimal.

**Previous-part dependency.** None: `previous_parts` is empty for T4-A5.  The
2 MeV initial energy is stipulated both in the shared context and in box 4.5
itself, so no earlier answer or fallback value is consumed.

**Reporting** (uniform blind evaluation default; the problem requests no
explicit precision): three significant figures, ties half away from zero.  For
a value of magnitude `2·10^1` the quantum is `0.1`, the committed reporting
cell of the computed raw value `19.9699434…` is `[19.95, 20.05)`, and the
reported value is `20.0` collisions.

The two result contracts at the end are the answer-blind certificates: the raw
contract carries the derivation spec together with the certified
non-degenerate interval `399/20 ≤ raw ≤ 401/20` (the closed reporting cell,
fixed by the reporting policy *after* the raw value was computed from the
stipulated constants, not from any target decimal), and the reported contract
carries the `ReportsAtQuantum` certificate for `20.0` at quantum `0.1`.
-/

namespace IChO2026.T4.A5

/-- Problem-stipulated initial neutron energy, expressed in eV: the sheet
stipulates an average fission-neutron energy of 2 MeV (problem_text, shared
context and box 4.5 on `T4_page-2.png`), and `1 MeV = 10^6 eV`
(trusted_general_law, SI prefix), so `E₀ = 2·10^6 eV`.  Exact as printed. -/
def initialEnergy_eV : ℝ := 2 * 10 ^ 6

/-- Problem-stipulated final (thermalised) neutron energy `E_f = 0.012 eV`
(problem_text, box 4.5 on `T4_page-2.png`), exact as printed. -/
def finalEnergy_eV : ℝ := 0.012

/-- Problem-stipulated logarithmic energy decrement of the moderator water,
`ξ(water) = 0.948` (problem_text, box 4.5 on `T4_page-2.png`), exact as
printed. -/
def logEnergyDecrementWater : ℝ := 0.948

/-- The printed per-collision definition of the logarithmic energy decrement
(problem_text, shared context on `T4_page-2.png`): for one collision with
initial energy `Einit` and final energy `Efinal`, the average decrease of the
logarithm of the neutron energy is `ξ = ln (Einit / Efinal)`. -/
def PerCollisionDecrement (ξ Einit Efinal : ℝ) : Prop :=
  ξ = Real.log (Einit / Efinal)

/-- **Neutron slowing-down model** (problem_text stipulation that ξ is a
material constant independent of the neutron energy): after `n` collisions the
average total decrease of `ln E` is `n · ξ`, so the average number of
collisions needed to slow a neutron from `initialEnergy_eV` to
`finalEnergy_eV` in water is the (necessarily unique) real number `n` with
`n · ξ(water) = ln (E₀ / E_f)`. -/
def CollisionCountModel (n : ℝ) : Prop :=
  n * logEnergyDecrementWater = Real.log (initialEnergy_eV / finalEnergy_eV)

/-- **Raw (unrounded) average collision count**: the exact source-derived
expression `ln (E₀/E_f) / ξ = ln ((2·10^6)/0.012) / 0.948` over the stipulated
constants, in collisions.  No intermediate rounding is applied. -/
noncomputable def averageCollisionsRaw : ℝ :=
  Real.log (initialEnergy_eV / finalEnergy_eV) / logEnergyDecrementWater

/-- The stipulated initial energy is positive. -/
theorem initialEnergy_eV_pos : (0 : ℝ) < initialEnergy_eV := by
  norm_num [initialEnergy_eV]

/-- The stipulated final energy is positive. -/
theorem finalEnergy_eV_pos : (0 : ℝ) < finalEnergy_eV := by
  norm_num [finalEnergy_eV]

/-- The stipulated decrement of water is positive. -/
theorem logEnergyDecrementWater_pos : (0 : ℝ) < logEnergyDecrementWater := by
  norm_num [logEnergyDecrementWater]

/-- The stipulated decrement of water is nonzero (the model equation is
solvable). -/
theorem logEnergyDecrementWater_ne_zero : logEnergyDecrementWater ≠ 0 :=
  ne_of_gt logEnergyDecrementWater_pos

/-- The dimensionless energy ratio in the same unit (eV):
`(2·10^6) / 0.012 = 500000000/3`. -/
theorem energyRatio : initialEnergy_eV / finalEnergy_eV = 500000000 / 3 := by
  norm_num [initialEnergy_eV, finalEnergy_eV]

/-- The neutron loses energy: `E₀/E_f > 1`. -/
theorem energyRatio_gt_one : (1 : ℝ) < initialEnergy_eV / finalEnergy_eV := by
  rw [energyRatio]; norm_num

/-- The total required decrease of `ln E` is strictly positive. -/
theorem log_energyRatio_pos :
    (0 : ℝ) < Real.log (initialEnergy_eV / finalEnergy_eV) :=
  Real.log_pos energyRatio_gt_one

/-- The raw average collision count is strictly positive. -/
theorem averageCollisionsRaw_pos : (0 : ℝ) < averageCollisionsRaw :=
  div_pos log_energyRatio_pos logEnergyDecrementWater_pos

/-- Faithfulness bridge: the integrated model `n · ξ = ln(E₀/E_f)` is exactly
the statement that the average total decrease of the logarithm of the neutron
energy over `n` collisions, `n·ξ`, equals `ln E₀ − ln E_f` (the printed
per-collision definition summed over `n` collisions under the stipulated
constancy of ξ). -/
theorem collisionCountModel_iff_log_sub_log (n : ℝ) :
    CollisionCountModel n ↔
      n * logEnergyDecrementWater =
        Real.log initialEnergy_eV - Real.log finalEnergy_eV := by
  unfold CollisionCountModel
  rw [Real.log_div (ne_of_gt initialEnergy_eV_pos) (ne_of_gt finalEnergy_eV_pos)]

/-- The derived raw candidate satisfies the slowing-down model. -/
theorem collisionCountModel_candidate : CollisionCountModel averageCollisionsRaw := by
  unfold CollisionCountModel averageCollisionsRaw
  exact div_mul_cancel₀ _ logEnergyDecrementWater_ne_zero

/-- The model fixes `n_c` uniquely, because `ξ ≠ 0`. -/
theorem collisionCountModel_unique {n : ℝ} (h : CollisionCountModel n) :
    n = averageCollisionsRaw :=
  (eq_div_iff logEnergyDecrementWater_ne_zero).mpr h

/-- **Raw derivation specification** for the average collision count: the raw
candidate satisfies — and is uniquely fixed by — the stipulated slowing-down
model `n_c · ξ = ln(E₀/E_f)`; the count is positive; and the three stipulated
constants are exactly the printed values `ξ(water) = 0.948`, `E₀ = 2·10^6 eV`
(`= 2 MeV`), `E_f = 0.012 eV`. -/
def RawCollisionCountSpec : Prop :=
  CollisionCountModel averageCollisionsRaw ∧
    (∀ n : ℝ, CollisionCountModel n → n = averageCollisionsRaw) ∧
    (0 : ℝ) < averageCollisionsRaw ∧
    logEnergyDecrementWater = 0.948 ∧
    initialEnergy_eV = 2 * 10 ^ 6 ∧
    finalEnergy_eV = 0.012

/-- The derivation specification holds for the derived candidate. -/
theorem rawCollisionCountSpec_holds : RawCollisionCountSpec :=
  ⟨collisionCountModel_candidate, fun _ h => collisionCountModel_unique h,
    averageCollisionsRaw_pos, rfl, rfl, rfl⟩

/-- Certified non-degenerate interval for the raw collision count, fixed
before reporting: `399/20 = 19.95 ≤ n_c < 20.05 = 401/20` (the closed
reporting cell of the computed raw value at the 3-significant-figure quantum
`0.1`).  Proved from the stipulated constants via `exp(1)` to nine digits
(Mathlib `Real.exp_one_gt_d9` / `Real.exp_one_lt_d9`) and
`x + 1 ≤ exp x`, with no intermediate rounding. -/
theorem averageCollisionsRaw_bounds :
    ((399 : ℝ) / 20) ≤ averageCollisionsRaw ∧
      averageCollisionsRaw < ((401 : ℝ) / 20) := by
  have hRpos : (0 : ℝ) < initialEnergy_eV / finalEnergy_eV :=
    div_pos initialEnergy_eV_pos finalEnergy_eV_pos
  have hxi : (0 : ℝ) < logEnergyDecrementWater := logEnergyDecrementWater_pos
  -- `exp 19 = (exp 1) ^ 19`.
  have e19 : Real.exp (19 : ℝ) = Real.exp 1 ^ 19 := by
    rw [show (19 : ℝ) = (19 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
  -- Nine-digit bounds on `exp 19` from Mathlib's bounds on `exp 1`.
  have h19lo : (2.7182818283 : ℝ) ^ 19 < Real.exp 19 := by
    rw [e19]
    exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h19up : Real.exp 19 < (2.7182818286 : ℝ) ^ 19 := by
    rw [e19]
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos 1)) (by norm_num)
  -- Lower bound: `18.9126 = 94563/5000 ≤ ln (E₀/E_f)`, i.e.
  -- `exp 19 / exp (437/5000) ≤ E₀/E_f`; use `exp(0.0874) ≥ 1.0874` and
  -- `exp 19 ≤ 2.7182818286^19 ≤ (5·10^8/3)·1.0874`.
  have hlb : (94563 : ℝ) / 5000 ≤ Real.log (initialEnergy_eV / finalEnergy_eV) := by
    rw [Real.le_log_iff_exp_le hRpos]
    have hsplit : Real.exp ((94563 : ℝ) / 5000) =
        Real.exp 19 / Real.exp ((437 : ℝ) / 5000) := by
      have h : (94563 : ℝ) / 5000 = 19 - 437 / 5000 := by norm_num
      rw [h, Real.exp_sub]
    rw [hsplit, div_le_iff₀ (Real.exp_pos _)]
    have hge : (437 : ℝ) / 5000 + 1 ≤ Real.exp ((437 : ℝ) / 5000) :=
      Real.add_one_le_exp _
    calc Real.exp 19 ≤ (2.7182818286 : ℝ) ^ 19 := le_of_lt h19up
      _ ≤ (initialEnergy_eV / finalEnergy_eV) * (437 / 5000 + 1) := by
          rw [energyRatio]; norm_num
      _ ≤ (initialEnergy_eV / finalEnergy_eV) * Real.exp ((437 : ℝ) / 5000) :=
          mul_le_mul_of_nonneg_left hge (le_of_lt hRpos)
  -- Upper bound: `ln (E₀/E_f) < 95037/5000 = 19.0074`, i.e.
  -- `E₀/E_f < exp 19 · exp (37/5000)`; use `exp(0.0074) ≥ 1` and
  -- `5·10^8/3 < 2.7182818283^19 < exp 19`.
  have hub : Real.log (initialEnergy_eV / finalEnergy_eV) < (95037 : ℝ) / 5000 := by
    rw [Real.log_lt_iff_lt_exp hRpos]
    have hsplit : Real.exp ((95037 : ℝ) / 5000) =
        Real.exp 19 * Real.exp ((37 : ℝ) / 5000) := by
      have h : (95037 : ℝ) / 5000 = 19 + 37 / 5000 := by norm_num
      rw [h, Real.exp_add]
    rw [hsplit]
    have hge1 : (1 : ℝ) ≤ Real.exp ((37 : ℝ) / 5000) := by
      have h := Real.add_one_le_exp ((37 : ℝ) / 5000)
      have hnn : (0 : ℝ) ≤ (37 : ℝ) / 5000 := by norm_num
      linarith
    calc initialEnergy_eV / finalEnergy_eV = 500000000 / 3 := energyRatio
      _ < (2.7182818283 : ℝ) ^ 19 := by norm_num
      _ < Real.exp 19 := h19lo
      _ = Real.exp 19 * 1 := (mul_one _).symm
      _ ≤ Real.exp 19 * Real.exp ((37 : ℝ) / 5000) :=
          mul_le_mul_of_nonneg_left hge1 (le_of_lt (Real.exp_pos 19))
  -- Divide through by `ξ = 0.948 > 0`: `0.948·(399/20) = 94563/5000` and
  -- `0.948·(401/20) = 95037/5000`.
  constructor
  · rw [averageCollisionsRaw, le_div_iff₀ hxi]
    have hmul : (399 : ℝ) / 20 * logEnergyDecrementWater = 94563 / 5000 := by
      norm_num [logEnergyDecrementWater]
    rw [hmul]; exact hlb
  · rw [averageCollisionsRaw, div_lt_iff₀ hxi]
    have hmul : (401 : ℝ) / 20 * logEnergyDecrementWater = 95037 / 5000 := by
      norm_num [logEnergyDecrementWater]
    rw [hmul]; exact hub

/-- **Raw result contract** (answer-blind): the derivation specification
`RawCollisionCountSpec` holds for the source-derived raw expression
`averageCollisionsRaw = ln(E₀/E_f)/ξ`, together with the certified
non-degenerate interval `399/20 = 19.95 ≤ raw ≤ 20.05 = 401/20`. -/
theorem raw_result_contract :
    (IChO2026.T4.A5.RawCollisionCountSpec) ∧
      (((399 : ℝ) / 20) ≤ (IChO2026.T4.A5.averageCollisionsRaw) ∧
        (IChO2026.T4.A5.averageCollisionsRaw) ≤ ((401 : ℝ) / 20)) :=
  ⟨rawCollisionCountSpec_holds, averageCollisionsRaw_bounds.1,
    le_of_lt averageCollisionsRaw_bounds.2⟩

/-- **Reported result contract** (answer-blind): at the
three-significant-figure quantum `0.1` collisions (ties half away from zero),
the raw value `ln(500000000/3)/0.948 = 19.9699434…` is reported as
`20.0 = 200/10` collisions, since `19.95 = 20.0 − 0.05 ≤ raw < 20.0 + 0.05 =
20.05` by the certified bounds. -/
theorem reported_result_contract :
    IChO2026Chem.Reporting.ReportsAtQuantum (IChO2026.T4.A5.averageCollisionsRaw)
      ((200 : ℝ) / 10) ((1 : ℝ) / 10) := by
  have hb := averageCollisionsRaw_bounds
  have hpos : (0 : ℝ) ≤ averageCollisionsRaw := le_of_lt averageCollisionsRaw_pos
  refine ⟨by norm_num, ⟨200, by norm_num⟩, ?_⟩
  rw [if_pos hpos]
  constructor
  · have h1 : (200 : ℝ) / 10 - (1 : ℝ) / 10 / 2 = 399 / 20 := by norm_num
    linarith [hb.1]
  · have h2 : (200 : ℝ) / 10 + (1 : ℝ) / 10 / 2 = 401 / 20 := by norm_num
    linarith [hb.2]

end IChO2026.T4.A5
