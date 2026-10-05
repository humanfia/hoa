import Mathlib
import IChO2026Chem
import IChO2026Chem.Reporting

/-!
# IChO 2026, Theory Problem T8 (Recycling of Carbon Dioxide), Part 8.6

**Question.** Calculate the quantum yield, φ (%), for CO formation.

## Grounding in the official problem page (Q8-2, `T8_page-2.png`, printed page 2)

The problem page states, immediately before 8.6:

* "The Turnover Frequency of a catalyst (TOF) is the number of product molecules
  formed per active catalyst molecule per hour."
* "Under LED illumination (λ = 390 nm) with power of 50 mW, there was a TOF of
  8 h⁻¹ for 10 mg of C₃N₄, loaded with 1 with ω_cat = 3.8 %"
* From 8.5 (top of same page, restated above): M_cat = 557.21 g mol⁻¹,
  ω_cat = 3.8 %.
* φ = (number of reacted electrons / number of incident photons) · 100 %.

The 2-electron stoichiometry per CO comes from 8.1 on the same problem:
the reduction half-equation in acidic medium is CO₂ + 2H⁺ + 2e⁻ → CO + H₂O
(carbon goes from oxidation state +4 in CO₂ to +2 in CO, a 2-electron reduction;
balance of atoms and charge fixes the proton/electron count uniquely).

The photon-counting uses the Planck relation E = h c / λ and photon rate
= optical power / photon energy — standard general physics
("trusted_general_law" per the allowed-sources policy), with the SI-exact
constants h, c, N_A used as exact stipulated values.

No official solution, marking scheme, grading report, or answer repository was
consulted.
-/

namespace IChO2026.T8.A6

open IChO2026Chem.Reporting

/-- The reduction of CO₂ to CO (part 8.1, acidic medium) transfers this many
reacted electrons per CO molecule formed: CO₂ + 2H⁺ + 2e⁻ → CO + H₂O,
carbon +4 → +2. -/
noncomputable def electronsPerCO : ℝ := 2

/-- Wavelength of the LED illumination, in metres (problem page Q8-2: 390 nm). -/
noncomputable def lambdaPhot : ℝ := 390 / 10 ^ 9
/-- LED optical power, in watts (problem page Q8-2: 50 mW). -/
noncomputable def powerLED : ℝ := 50 / 1000
/-- Observation time used for the photon/electron count, in seconds (one hour,
matching the per-hour basis of the stated TOF; the choice of period cancels). -/
noncomputable def obsTime : ℝ := 3600
/-- Turnover frequency for CO formation, per hour (problem page Q8-2: 8 h⁻¹). -/
noncomputable def tofCO : ℝ := 8
/-- Mass of the C₃N₄ sample, in grams (problem page Q8-2: 10 mg). -/
noncomputable def massSample : ℝ := 10 / 1000
/-- Mass fraction of catalyst 1 in the loaded sample (8.5, Q8-2: 3.8 %). -/
noncomputable def omegaCat : ℝ := (3.8 : ℝ) / 100
/-- Molar mass of catalyst 1 (8.5, Q8-2: M_cat = 557.21 g mol⁻¹). -/
noncomputable def molarMassCat : ℝ := 557.21
/-- Avogadro constant, exact since the 2019 SI redefinition (mol⁻¹). -/
noncomputable def avogadroConst : ℝ := 6.02214076 * 10 ^ 23
/-- Planck constant, exact since the 2019 SI redefinition (J·s). -/
noncomputable def planckConst : ℝ := 6.62607015 * 10 ^ (-34 : ℤ)
/-- Speed of light in vacuum, exact since 1983 (m s⁻¹). -/
noncomputable def speedOfLight : ℝ := 2.99792458 * 10 ^ 8

/-- Energy of one photon of wavelength λ: E = h c / λ (Planck relation). -/
noncomputable def photonEnergy : ℝ := planckConst * speedOfLight / lambdaPhot

/-- Moles of active catalyst 1 in the sample: n_cat = m·ω_cat / M_cat. -/
noncomputable def molesCatalyst : ℝ := massSample * omegaCat / molarMassCat

/-- CO molecules formed during the observation time: TOF (h⁻¹) times the
observation time in hours times the number of catalyst molecules. -/
noncomputable def coMolecules : ℝ :=
  tofCO * (obsTime / 3600) * molesCatalyst * avogadroConst

/-- Reacted electrons during the observation time: 2 electrons per CO (8.1). -/
noncomputable def reactedElectrons : ℝ := electronsPerCO * coMolecules

/-- Photons incident during the observation time from a source of power P:
total optical energy P·t divided by the photon energy h c / λ. -/
noncomputable def incidentPhotons : ℝ := powerLED * obsTime / photonEnergy

/-- Quantum yield for CO formation, in percent, exactly as defined on the
problem page: φ = (reacted electrons / incident photons) · 100 %. -/
noncomputable def quantumYieldPercent : ℝ := reactedElectrons / incidentPhotons * 100

/-- The exact closed form obtained by algebraic simplification of
`quantumYieldPercent`. Substituting the definitions, dividing out the common
powers of ten, and cancelling the observation time gives the reduced fraction

  φ = 18940872892793693114789369 / 10186495312500000000000000 ≈ 1.859410161 %.

Every factor in the original expression is exactly the printed problem data
(390 nm, 50 mW, 8 h⁻¹, 10 mg, 3.8 %, 557.21 g mol⁻¹) or an exact SI constant. -/
theorem quantumYieldPercent_eq :
    quantumYieldPercent = 18940872892793693114789369 / 10186495312500000000000000 := by
  unfold quantumYieldPercent reactedElectrons coMolecules molesCatalyst
    incidentPhotons photonEnergy electronsPerCO tofCO obsTime massSample
    omegaCat molarMassCat avogadroConst planckConst speedOfLight lambdaPhot
    powerLED
  norm_num

/-- The raw quantum yield lies strictly between 1.8594 % and 1.8595 %. -/
theorem quantumYieldPercent_bounds :
    18594 / 10000 < quantumYieldPercent ∧ quantumYieldPercent < 18595 / 10000 := by
  rw [quantumYieldPercent_eq]
  norm_num

/-- The quantum yield is positive (all problem inputs are positive). -/
theorem quantumYieldPercent_pos : 0 < quantumYieldPercent :=
  lt_trans (by norm_num) quantumYieldPercent_bounds.1

/-- **Main result (raw value).** The quantum yield for CO formation computed from
the printed problem data is exactly
18940872892793693114789369 / 10186495312500000000000000 ≈ 1.8594101613683622… %,
in particular it lies in (1.8594 %, 1.8595 %). -/
theorem co_quantum_yield_raw :
    quantumYieldPercent = 18940872892793693114789369 / 10186495312500000000000000 ∧
    18594 / 10000 < quantumYieldPercent ∧ quantumYieldPercent < 18595 / 10000 :=
  ⟨quantumYieldPercent_eq, quantumYieldPercent_bounds⟩

/-- **Main result (reported value).** Reported at three significant figures
(reporting quantum 0.01 %, half-away-from-zero per the project reporting
contract), the quantum yield is 1.86 %: the raw value 1.85941016… % lies in the
rounding cell [1.855, 1.865). -/
theorem co_quantum_yield_reported :
    ReportsAtQuantum quantumYieldPercent 1.86 (1 / 100) := by
  have hpos : 0 ≤ quantumYieldPercent := le_of_lt quantumYieldPercent_pos
  rw [quantumYieldPercent_eq] at hpos ⊢
  refine ⟨by norm_num, ⟨186, by norm_num⟩, ?_⟩
  rw [if_pos hpos]
  norm_num

#print axioms co_quantum_yield_raw
#print axioms co_quantum_yield_reported

end IChO2026.T8.A6
