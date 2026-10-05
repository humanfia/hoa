import IChO2026Chem

/-!
# IChO 2026, Theory Problem T4, part 4.8 (target `icho_2026_t4_a8`)

## Current subquestion

Calculate the total energy released per day, `E`, (in J day⁻¹) by complete
isothermic combustion of methane at `T = 2000 K`.

## Problem-side evidence (answer-blind inventory)

From the bound problem images and the controller-curated erratum
`t4-a8-flow-time-basis-v1`:

* `T4_page-2.png` (Q4-2, item 4.6): thermodynamic table for the complete
  combustion `CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)` with all species gaseous:
  `ΔfH°₂₉₈(CH₄) = -74.8 kJ mol⁻¹`, `ΔfH°₂₉₈(H₂O, gas) = -241.8 kJ mol⁻¹`,
  `ΔfH°₂₉₈(CO₂) = -393.5 kJ mol⁻¹`, `C_P(CH₄) = 35 J mol⁻¹ K⁻¹`,
  `C_P(H₂O, gas) = 34 J mol⁻¹ K⁻¹`, `C_P(O₂) = 29 J mol⁻¹ K⁻¹`,
  `C_P(CO₂) = 37 J mol⁻¹ K⁻¹`.
* `T4_page-3.png` (Q4-3, items 4.7-4.8): methane flows out of the well at
  `101.325 kPa` and `298 K`; the combustion is complete and isothermic at
  `T = 2000 K`.
* Erratum `t4-a8-flow-time-basis-v1` (part of the problem evidence for this
  run): the volumetric flow is `Q = 2.2 × 10⁵ m³ day⁻¹`.
* Student-visible constants pages (`theory_problem.pdf`, PDF pages 3-4, as
  quoted by the bound addendum): `R = 8.314 J K⁻¹ mol⁻¹` and `PV = nRT`.

## Previous-part handling

T4-A7 (`ΔrH₂₀₀₀` per mole of methane combustion at 2000 K) has dependency
policy `derive_in_answer_blind_run_or_use_problem_stated_fallback`.  It is
derived inline below from the problem-stated table via Hess's law at 298 K
and Kirchhoff's law to 2000 K; the printed fallback `ΔH₂₀₀₀ = -700 kJ mol⁻¹`
is therefore not used.

## Derivation encoded below

1. Hess's law at the 298 K reference:
   `ΔrH₂₉₈ = (ΔfH(CO₂) + 2·ΔfH(H₂O,g)) - (ΔfH(CH₄) + 2·ΔfH(O₂))`
   `= -802300 J mol⁻¹`.
2. Reaction heat-capacity difference:
   `ΔC_P = (C_P(CO₂) + 2·C_P(H₂O,g)) - (C_P(CH₄) + 2·C_P(O₂))`
   `= 12 J mol⁻¹ K⁻¹`.
3. Kirchhoff's law (constant `C_P`, as the problem supplies one value per
   species): `ΔrH₂₀₀₀ = ΔrH₂₉₈ + ΔC_P·(2000 - 298) = -781876 J mol⁻¹`.
4. Ideal-gas molar flow at the well: `ṅ = P·Q/(R·T)`.
5. Daily released energy (magnitude of the exothermic enthalpy):
   `E = ṅ·(-ΔrH₂₀₀₀) ≈ 7.0347860 × 10¹² J day⁻¹`, which rounds to
   `7.03 × 10¹² J day⁻¹` at the project default of 3 significant figures
   (tie rule half-away-from-zero).
-/

namespace IChO2026Problems.problem_icho_2026_t4_a8

/-- Standard enthalpy of formation of gaseous methane at 298 K, in J mol⁻¹.
Problem table value `-74.8 kJ mol⁻¹` (T4 page 2, item 4.6), unit-converted. -/
def formationEnthalpyCH4_298 : ℝ := -74800

/-- Standard enthalpy of formation of gaseous water at 298 K, in J mol⁻¹.
Problem table value `-241.8 kJ mol⁻¹` (T4 page 2, item 4.6), unit-converted. -/
def formationEnthalpyH2Ogas_298 : ℝ := -241800

/-- Standard enthalpy of formation of carbon dioxide at 298 K, in J mol⁻¹.
Problem table value `-393.5 kJ mol⁻¹` (T4 page 2, item 4.6), unit-converted. -/
def formationEnthalpyCO2_298 : ℝ := -393500

/-- Standard enthalpy of formation of gaseous oxygen at 298 K, in J mol⁻¹.
An element in its standard reference state has zero formation enthalpy
(trusted general law; the problem table omits it for exactly this reason). -/
def formationEnthalpyO2_298 : ℝ := 0

/-- Molar heat capacity of gaseous methane, `35 J mol⁻¹ K⁻¹`
(T4 page 2, item 4.6). -/
def heatCapacityCH4 : ℝ := 35

/-- Molar heat capacity of gaseous water, `34 J mol⁻¹ K⁻¹`
(T4 page 2, item 4.6). -/
def heatCapacityH2Ogas : ℝ := 34

/-- Molar heat capacity of gaseous oxygen, `29 J mol⁻¹ K⁻¹`
(T4 page 2, item 4.6). -/
def heatCapacityO2 : ℝ := 29

/-- Molar heat capacity of carbon dioxide, `37 J mol⁻¹ K⁻¹`
(T4 page 2, item 4.6). -/
def heatCapacityCO2 : ℝ := 37

/-- Gas constant `R = 8.314 J K⁻¹ mol⁻¹` from the student-visible Physical
Constants and Equations pages, as recorded by the bound addendum. -/
def gasConstantR : ℝ := 8.314

/-- Well-head pressure `P = 101.325 kPa = 101325 Pa` (T4 page 3, flow
sentence above item 4.8), unit-converted. -/
def wellPressure : ℝ := 101325

/-- Temperature of the methane flowing out of the well, `298 K`
(T4 page 3, flow sentence above item 4.8). -/
def wellTemperature : ℝ := 298

/-- Volumetric flow of methane `Q = 2.2 × 10⁵ m³ day⁻¹`: the printed value
`2.2 × 10⁵` (T4 page 3) with the day⁻¹ time basis fixed by the
controller-curated erratum `t4-a8-flow-time-basis-v1`. -/
def volumetricFlowRate : ℝ := 220000

/-- Isothermic combustion temperature `T = 2000 K` (item 4.8). -/
def combustionTemperature : ℝ := 2000

/-- Reference temperature of the thermodynamic table, `298 K` (item 4.6).
Kept distinct from `wellTemperature`: the two roles coincide numerically in
this problem but enter different physical relations. -/
def referenceTemperature : ℝ := 298

/-- Reaction enthalpy of `CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)` at 298 K by
Hess's law from the problem table, in J mol⁻¹. -/
def reactionEnthalpy298 : ℝ :=
  (formationEnthalpyCO2_298 + 2 * formationEnthalpyH2Ogas_298) -
    (formationEnthalpyCH4_298 + 2 * formationEnthalpyO2_298)

/-- Reaction heat-capacity difference `ΔC_P` for the same stoichiometry,
in J mol⁻¹ K⁻¹. -/
def reactionHeatCapacity : ℝ :=
  (heatCapacityCO2 + 2 * heatCapacityH2Ogas) - (heatCapacityCH4 + 2 * heatCapacityO2)

/-- Reaction enthalpy at 2000 K by Kirchhoff's law with the constant
problem-supplied heat capacities, in J mol⁻¹.  This is the inline
answer-blind derivation of the T4-A7 prerequisite. -/
def reactionEnthalpy2000 : ℝ :=
  reactionEnthalpy298 + reactionHeatCapacity * (combustionTemperature - referenceTemperature)

/-- Molar flow of methane out of the well, in mol day⁻¹, from the ideal-gas
law `PV = nRT` applied to the volumetric flow: `ṅ = P·Q/(R·T)`. -/
noncomputable def molarFlowRate : ℝ :=
  wellPressure * volumetricFlowRate / (gasConstantR * wellTemperature)

/-- Raw daily energy released by complete isothermic combustion of the
methane stream at 2000 K, in J day⁻¹: the molar flow times the magnitude of
the (negative, exothermic) molar reaction enthalpy. -/
noncomputable def dailyEnergyRaw : ℝ := molarFlowRate * -reactionEnthalpy2000

/-- Governing-relation specification for the raw daily energy.  The
conjunction binds, for the complete combustion
`CH₄(g) + 2 O₂(g) → CO₂(g) + 2 H₂O(g)`:

1. Hess's law at the 298 K reference;
2. the reaction heat-capacity difference for the same stoichiometry;
3. Kirchhoff's law from 298 K to the 2000 K combustion temperature;
4. the ideal-gas law `ṅ·R·T = P·Q` at the well conditions; and
5. the daily released energy `E = ṅ·(-ΔrH₂₀₀₀)` with its sign and positivity
   side conditions (exothermic reaction, positive molar flow). -/
def DailyEnergyRawSpec : Prop :=
  (reactionEnthalpy298 =
      (formationEnthalpyCO2_298 + 2 * formationEnthalpyH2Ogas_298) -
        (formationEnthalpyCH4_298 + 2 * formationEnthalpyO2_298)) ∧
    (reactionHeatCapacity =
      (heatCapacityCO2 + 2 * heatCapacityH2Ogas) - (heatCapacityCH4 + 2 * heatCapacityO2)) ∧
    (reactionEnthalpy2000 =
      reactionEnthalpy298 +
        reactionHeatCapacity * (combustionTemperature - referenceTemperature)) ∧
    (molarFlowRate * (gasConstantR * wellTemperature) = wellPressure * volumetricFlowRate) ∧
    (dailyEnergyRaw = molarFlowRate * -reactionEnthalpy2000) ∧
    (0 < molarFlowRate) ∧
    (reactionEnthalpy2000 < 0)

/-- Raw-result certificate: the governing-relation specification holds and
the raw daily energy lies inside the non-degenerate certified enclosure
`[7025000000000, 7035000000000]` J day⁻¹ (the half-quantum cell of the
3-significant-figure reporting grid around the reported value). -/
theorem dailyEnergyRaw_certified :
    (IChO2026Problems.problem_icho_2026_t4_a8.DailyEnergyRawSpec) ∧
      ((7025000000000 : ℝ) ≤ (IChO2026Problems.problem_icho_2026_t4_a8.dailyEnergyRaw) ∧
        (IChO2026Problems.problem_icho_2026_t4_a8.dailyEnergyRaw) ≤
          (7035000000000 : ℝ)) := by
  -- Kirchhoff value `ΔrH₂₀₀₀ = -802300 + 12·1702 = -781876 J mol⁻¹ < 0`.
  have hRTH2000_neg : reactionEnthalpy2000 < 0 := by
    norm_num [reactionEnthalpy2000, reactionEnthalpy298, reactionHeatCapacity,
      formationEnthalpyCH4_298, formationEnthalpyH2Ogas_298, formationEnthalpyCO2_298,
      formationEnthalpyO2_298, heatCapacityCH4, heatCapacityH2Ogas, heatCapacityO2,
      heatCapacityCO2, combustionTemperature, referenceTemperature]
  -- `R·T = 8.314·298 = 2477.572 ≠ 0` at the well conditions.
  have hRT_ne : gasConstantR * wellTemperature ≠ 0 := by
    norm_num [gasConstantR, wellTemperature]
  -- Ideal-gas governing relation `ṅ·R·T = P·Q` from `ṅ = P·Q/(R·T)`.
  have hflow : molarFlowRate * (gasConstantR * wellTemperature) =
      wellPressure * volumetricFlowRate := by
    unfold molarFlowRate
    exact div_mul_cancel₀ _ hRT_ne
  -- The molar flow `101325·220000/2477.572` is positive.
  have hflow_pos : 0 < molarFlowRate := by
    norm_num [molarFlowRate, wellPressure, volumetricFlowRate, gasConstantR, wellTemperature]
  -- Exact rational evaluation `E = 4357297213500000000/619393 ≈ 7.034786014·10¹²`
  -- lies in the certified half-quantum cell `[7.025·10¹², 7.035·10¹²)`.
  have hbounds : (7025000000000 : ℝ) ≤ dailyEnergyRaw ∧
      dailyEnergyRaw < (7035000000000 : ℝ) := by
    refine ⟨?_, ?_⟩ <;>
      norm_num [dailyEnergyRaw, molarFlowRate, reactionEnthalpy2000, reactionEnthalpy298,
        reactionHeatCapacity, formationEnthalpyCH4_298, formationEnthalpyH2Ogas_298,
        formationEnthalpyCO2_298, formationEnthalpyO2_298, heatCapacityCH4,
        heatCapacityH2Ogas, heatCapacityO2, heatCapacityCO2, gasConstantR, wellPressure,
        wellTemperature, volumetricFlowRate, combustionTemperature, referenceTemperature]
  exact ⟨⟨rfl, rfl, rfl, hflow, rfl, hflow_pos, hRTH2000_neg⟩, hbounds.1, le_of_lt hbounds.2⟩

/-- Reported-value certificate: the raw daily energy is reported as
`7.03 × 10¹² J day⁻¹` on the 3-significant-figure grid (quantum `10¹⁰`,
ties away from zero) fixed by the project reporting policy. -/
theorem dailyEnergyRaw_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (IChO2026Problems.problem_icho_2026_t4_a8.dailyEnergyRaw) (7030000000000 : ℝ)
      (10000000000 : ℝ) := by
  -- Same exact rational evaluation as in `dailyEnergyRaw_certified`.
  have hbounds : (7025000000000 : ℝ) ≤ dailyEnergyRaw ∧
      dailyEnergyRaw < (7035000000000 : ℝ) := by
    refine ⟨?_, ?_⟩ <;>
      norm_num [dailyEnergyRaw, molarFlowRate, reactionEnthalpy2000, reactionEnthalpy298,
        reactionHeatCapacity, formationEnthalpyCH4_298, formationEnthalpyH2Ogas_298,
        formationEnthalpyCO2_298, formationEnthalpyO2_298, heatCapacityCH4,
        heatCapacityH2Ogas, heatCapacityO2, heatCapacityCO2, gasConstantR, wellPressure,
        wellTemperature, volumetricFlowRate, combustionTemperature, referenceTemperature]
  -- The raw value is positive, so the reporting cell is `[r − q/2, r + q/2)`.
  have hpos : (0 : ℝ) ≤ dailyEnergyRaw := le_trans (by norm_num) hbounds.1
  refine ⟨by norm_num, ⟨703, by norm_num⟩, ?_⟩
  rw [if_pos hpos]
  constructor
  · -- `7030000000000 − 10000000000/2 = 7025000000000 ≤ E`.
    have h1 : (7030000000000 : ℝ) - 10000000000 / 2 = 7025000000000 := by norm_num
    linarith [hbounds.1]
  · -- `E < 7035000000000 = 7030000000000 + 10000000000/2`.
    have h2 : (7030000000000 : ℝ) + 10000000000 / 2 = 7035000000000 := by norm_num
    linarith [hbounds.2]

end IChO2026Problems.problem_icho_2026_t4_a8
