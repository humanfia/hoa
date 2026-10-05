import IChO2026Chem.Reporting

/-!
# IChO 2026 Theory T4, Part 4.8 (T4-A8): Daily combustion energy of the
Urtabulak methane blowout

## Problem (58th IChO 2026, theory paper T4, page Q4-3)

"Calculate the total energy released per day, `E`, (in J day⁻¹) by complete
isothermic combustion of methane at `T = 2000 K`", using:

* the flow statement printed directly above 4.8: *"Assume that methane is
  flowing out the well at 101.325 kPa and 298 K with volumetric flow
  `Q = 2.2 × 10⁵ m³` before it catches fire."* — the well feeds a
  continuous flame, so `Q` is a volumetric **flow rate** and the volume of
  gas escaping per day is `Q × 86400 s` (the source's unit glyph is printed
  as "m³" with its time basis clipped at the line break; every definition
  below keeps the flow parameter symbolic, so the derivation itself does not
  depend on any unit restoration);
* the combustion-enthalpy chain of 4.6–4.7, re-derived here under the same
  all-gaseous convention used throughout part 4:
  `ΔᵣH°₂₉₈ = −802.3 kJ mol⁻¹` (Hess's law on the printed formation
  enthalpies) and `ΔᵣH₂₀₀₀ = ΔᵣH₂₉₈ + ΔC_P·(2000 − 298 K) = −781.876 kJ mol⁻¹`
  (Kirchhoff's law with the printed constant heat capacities,
  `ΔC_P = 2·34 + 37 − 35 − 2·29 = 12 J mol⁻¹ K⁻¹`).

No value of the gas constant is printed anywhere in the paper; we use the
ordinary scientific reference value `R = 8.31 J mol⁻¹ K⁻¹`
(`trusted_general_law`, a permitted source class for this target).

## Numerical chain (raw, no intermediate rounding)

```
n(CH4)/day = p·Q·86400 / (R·298)
           = 101325 × 2.2×10⁵ × 86400 / (8.31 × 298)  mol day⁻¹
           = 7.77742349720156…×10¹⁴ mol day⁻¹
E          = |ΔrH2000| × n = 781876 J mol⁻¹ × n
           = 6.08098077…×10¹⁷ J day⁻¹
```

Reported to three significant figures (uniform default reporting rule):
**`E = 6.08 × 10¹⁷ J day⁻¹`**, i.e. visible digits `608` at the final display
quantum `10¹⁵ J day⁻¹`.

## Content of this file

* exact real-valued definitions of every printed input and of the derived
  quantities (Hess value `deltaH298`, Kirchhoff correction `deltaCp`,
  enthalpy at 2000 K, molar daily throughput, daily energy);
* `h_dH298`, `h_deltaCp`, `h_dH2000`: the derivation of the reaction
  enthalpies exactly as performed in 4.6–4.7;
* `rawDailyEnergy_eq`: the raw answer evaluated to the exact rational
  `E = 25098031949760000000000 / 41273` J day⁻¹;
* `dailyEnergy_rounds_three_sig`: the three-significant-figure rounding
  certificate `|raw / 10¹⁵ − 608| < 1/2`;
* `validSubmission`: the project reporting contract
  `ValidNumericSubmission rawDailyEnergy submission`;
* `dailyEnergy_gt`, `dailyEnergy_lt`: interval bounds on the raw answer that
  do not assume the final rounded decimal;
* `energy_per_hour_gt_tnt`: an independent physical sanity check — the
  well's combustion releases, every hour, more than 200 times the printed
  30-kiloton TNT reference energy `30 × 10³ × 4.184×10⁹ J`.
-/

namespace IChO2026T4A8

open IChO2026Chem.Reporting

/-! ## Problem inputs (exactly as printed in theory_problem.pdf, pages Q4-2/Q4-3) -/

/-- Well outlet pressure, 101.325 kPa, in Pa. -/
def wellPressurePa : ℝ := 101325

/-- Printed volumetric flow setting, `Q = 2.2 × 10⁵`. -/
def wellFlowQ : ℝ := 2.2e5

/-- Well outlet (measurement) temperature, 298 K. -/
def wellTempK : ℝ := 298

/-- Flame temperature for the isothermic combustion, 2000 K. -/
def flameTempK : ℝ := 2000

/-- Reference temperature of the printed formation enthalpies, 298 K. -/
def refTempK : ℝ := 298

/-- Gas constant, `R = 8.31 J mol⁻¹ K⁻¹` (ordinary scientific reference value;
no value of `R` is printed in this paper). -/
def gasConstant : ℝ := 8.31

/-- Seconds per day. -/
def secondsPerDay : ℝ := 86400

/-- Printed standard molar formation enthalpy of CH₄ at 298 K, J mol⁻¹. -/
def dHfCH4 : ℝ := -74.8 * 1000

/-- Printed standard molar formation enthalpy of H₂O (gas) at 298 K, J mol⁻¹. -/
def dHfH2O : ℝ := -241.8 * 1000

/-- Printed standard molar formation enthalpy of CO₂ at 298 K, J mol⁻¹. -/
def dHfCO2 : ℝ := -393.5 * 1000

/-- Printed molar heat capacity of CH₄, J mol⁻¹ K⁻¹. -/
def cpCH4 : ℝ := 35

/-- Printed molar heat capacity of O₂, J mol⁻¹ K⁻¹. -/
def cpO2 : ℝ := 29

/-- Printed molar heat capacity of CO₂, J mol⁻¹ K⁻¹. -/
def cpCO2 : ℝ := 37

/-- Printed molar heat capacity of H₂O (gas), J mol⁻¹ K⁻¹. -/
def cpH2O : ℝ := 34

/-- Printed TNT equivalence, 4.184 GJ per ton, in J. -/
def tntPerTonJ : ℝ := 4.184e9

/-- Printed explosive yield of the leak-sealing shot, 30 kilotons TNT. -/
def explosionKilotons : ℝ := 30

/-! ## Derived quantities (Hess + Kirchhoff, exactly as in 4.6–4.7) -/

/-- Hess's-law reaction enthalpy at 298 K for
CH₄ + 2 O₂ → CO₂ + 2 H₂O (all gaseous), in J per mole of CH₄:
`2 ΔfH(H₂O) + ΔfH(CO₂) − ΔfH(CH₄) − 2 ΔfH(O₂)`, with `ΔfH(O₂) = 0`. -/
def deltaH298 : ℝ := 2 * dHfH2O + dHfCO2 - dHfCH4

/-- Reaction heat-capacity difference
`ΔC_P = C_P(CO₂) + 2 C_P(H₂O) − C_P(CH₄) − 2 C_P(O₂)`,
in J mol⁻¹ K⁻¹ (the printed values are temperature-independent). -/
def deltaCp : ℝ := cpCO2 + 2 * cpH2O - cpCH4 - 2 * cpO2

/-- Kirchhoff's law: molar combustion enthalpy at the flame temperature
2000 K, in J per mole of CH₄ (gaseous convention of part 4). -/
def deltaH2000 : ℝ := deltaH298 + deltaCp * (flameTempK - refTempK)

/-- Moles of methane flowing out per day, from the ideal-gas law applied to
the well conditions: `n = p·Q·86400 / (R·298)`. -/
noncomputable def molarFlowPerDay : ℝ :=
  wellPressurePa * wellFlowQ * secondsPerDay / (gasConstant * wellTempK)

/-- Raw daily energy released by the isothermic combustion at 2000 K, J day⁻¹. -/
noncomputable def rawDailyEnergy : ℝ := |deltaH2000| * molarFlowPerDay

/-! ## Verified evaluations of the derived enthalpies -/

/-- The 4.6 value: `ΔᵣH°₂₉₈ = −802300 J mol⁻¹ = −802.3 kJ mol⁻¹`
(contrast with the printed fallback −750 kJ mol⁻¹). -/
theorem h_dH298 : deltaH298 = -802300 := by
  unfold deltaH298 dHfCH4 dHfH2O dHfCO2; norm_num

theorem h_deltaCp : deltaCp = 12 := by
  unfold deltaCp cpCH4 cpO2 cpCO2 cpH2O; norm_num

/-- The 4.7 value: `ΔᵣH₂₀₀₀ = −781876 J mol⁻¹ = −781.876 kJ mol⁻¹`
(contrast with the printed fallback −700 kJ mol⁻¹). -/
theorem h_dH2000 : deltaH2000 = -781876 := by
  unfold deltaH2000 flameTempK refTempK
  rw [h_dH298, h_deltaCp]; norm_num

/-- The daily molar throughput evaluates to the exact rational
`32099760000000000 / 41273 = 7.7774234972…×10¹⁴` mol day⁻¹. -/
theorem molarFlowPerDay_eq :
    molarFlowPerDay = 32099760000000000 / 41273 := by
  unfold molarFlowPerDay wellPressurePa wellFlowQ secondsPerDay gasConstant wellTempK
  norm_num

/-- The raw daily energy, evaluated exactly:
`E = 25098031949760000000000 / 41273 ≈ 6.0809808×10¹⁷` J day⁻¹. -/
theorem rawDailyEnergy_eq :
    rawDailyEnergy = 25098031949760000000000 / 41273 := by
  unfold rawDailyEnergy
  rw [h_dH2000, molarFlowPerDay_eq]
  norm_num

/-! ## Three-significant-figure rounding certificate

`E = 6.0809808…×10¹⁷`, so `E/10¹⁵ = 608.09808…` and the distance to the
rounded value `608` is `0.09808… < 1/2`. Both bounds are certified by direct
rational inequalities below. -/

theorem dailyEnergy_rounds_lower :
    608 - 1 / 2 < rawDailyEnergy / (10 : ℝ) ^ 15 := by
  rw [rawDailyEnergy_eq]
  norm_num

theorem dailyEnergy_rounds_upper :
    rawDailyEnergy / (10 : ℝ) ^ 15 < 608 + 1 / 2 := by
  rw [rawDailyEnergy_eq]
  norm_num

/-- The raw answer rounds to `608 × 10¹⁵ = 6.08 × 10¹⁷ J day⁻¹` at the
three-significant-figure display quantum `10¹⁵ J day⁻¹`. -/
theorem dailyEnergy_rounds_three_sig :
    |rawDailyEnergy / (10 : ℝ) ^ 15 - 608| < 1 / 2 := by
  rw [abs_lt]
  constructor
  · linarith [dailyEnergy_rounds_lower]
  · linarith [dailyEnergy_rounds_upper]

/-! ## Reporting -/

/-- Final displayed value, `6.08 × 10¹⁷ J day⁻¹`, at the 3-s.f. quantum
`10¹⁵ J day⁻¹`. -/
noncomputable def submission : NumericSubmission where
  rawValue := rawDailyEnergy
  reportedValue := 608 * (10 : ℝ) ^ 15
  reportingQuantum := (10 : ℝ) ^ 15

/-- The submission satisfies the answer-blind reporting contract:
exact raw value, reported value a multiple of the quantum, and the raw value
inside the correct half-quantum rounding window. -/
theorem validSubmission :
    ValidNumericSubmission rawDailyEnergy submission := by
  refine ⟨rfl, ?_, ⟨608, ?_⟩, ?_⟩
  · norm_num [submission]
  · norm_num [submission]
  · have hpos : (0 : ℝ) ≤ rawDailyEnergy := by
      rw [rawDailyEnergy_eq]; positivity
    simp only [submission, if_pos hpos]
    constructor
    · calc 608 * (10 : ℝ) ^ 15 - (10 : ℝ) ^ 15 / 2
          = (608 - 1 / 2) * (10 : ℝ) ^ 15 := by ring
        _ ≤ rawDailyEnergy / (10 : ℝ) ^ 15 * (10 : ℝ) ^ 15 := by
            apply mul_le_mul_of_nonneg_right
            · exact le_of_lt dailyEnergy_rounds_lower
            · positivity
        _ = rawDailyEnergy := by
            field_simp
    · calc rawDailyEnergy
          = rawDailyEnergy / (10 : ℝ) ^ 15 * (10 : ℝ) ^ 15 := by field_simp
        _ < (608 + 1 / 2) * (10 : ℝ) ^ 15 := by
            apply mul_lt_mul_of_pos_right dailyEnergy_rounds_upper
            positivity
        _ = 608 * (10 : ℝ) ^ 15 + (10 : ℝ) ^ 15 / 2 := by ring

/-! ## Interval bounds on the raw answer (no assumption of the final decimal) -/

theorem dailyEnergy_gt : 6.08 * (10 : ℝ) ^ 17 < rawDailyEnergy := by
  rw [rawDailyEnergy_eq]
  norm_num

theorem dailyEnergy_lt : rawDailyEnergy < 6.09 * (10 : ℝ) ^ 17 := by
  rw [rawDailyEnergy_eq]
  norm_num

/-! ## Physical sanity check against the printed 30-kiloton TNT reference -/

/-- The well's hourly combustion energy `E / 24 h` exceeds 200 times the
printed reference explosion energy (30 kilotons TNT
= `30 × 10³ × 4.184×10⁹ J ≈ 1.25552×10¹⁴ J`): the burning well out-releases,
every hour, two hundred of the bombs that eventually sealed it. -/
theorem energy_per_hour_gt_tnt :
    rawDailyEnergy / 24 >
      200 * (explosionKilotons * 1000 * tntPerTonJ) := by
  unfold explosionKilotons tntPerTonJ
  rw [rawDailyEnergy_eq]
  norm_num

end IChO2026T4A8
