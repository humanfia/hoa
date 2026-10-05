import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T8 (Recycling of Carbon Dioxide), part 8.6 — `icho_2026_t8_a6`

**Question (verbatim, problem text).** Calculate the quantum yield, 𝜑(%), for CO
formation.

## Source contract (answer-blind; problem-only inputs)

* Source images: `icho_2026_source/image/T8_page-2.png` (the 8.6 question box,
  the TOF/LED/quantum-yield paragraph, and the catalytic-cycle scheme) and
  `icho_2026_source/image/T8_page-1.png` (shared context: photocatalytic CO₂→CO
  reduction by molecular catalyst **1**, and item 8.1 asking for the acidic
  half-equation of the CO₂→CO reduction).
* Problem-stipulated data (T8_page-2.png, exact as printed):
  * LED illumination at λ = 390 nm with power P = 50 mW;
  * TOF = 8 h⁻¹ for 10 mg of C₃N₄ loaded with **1** at ω_cat = 3.8 %;
  * TOF is the number of product molecules formed per active catalyst molecule
    per hour;
  * the quantum-yield formula
    φ = (number of reacted electrons)/(number of incident photons) · 100 %.
* Carried over from the shared context / previous part (same printed pages):
  * ω_cat = 3.8 %, specific surface area S = 17.8 m² g⁻¹ of C₃N₄, and
    M_cat = 557.21 g mol⁻¹ (all printed in part 8.5);
  * part 8.1: the reduction of CO₂ to CO in acidic medium is the two-electron
    half-reaction CO₂ + 2H⁺ + 2e⁻ → CO + H₂O (carbon oxidation state +IV →
    +II), so every CO molecule formed corresponds to exactly 2 reacted
    electrons.
* Exact SI defining constants (provenance `trusted_general_law`, 2019 SI):
  N_A = 6.02214076 × 10²³ mol⁻¹, h = 6.62607015 × 10⁻³⁴ J s,
  c = 299 792 458 m s⁻¹; exact unit relations 1 m² = 10¹⁸ nm² and 1 h = 3600 s.

## Assumption / target split

Assumptions (all problem-side): the mass-fraction law
ω_cat = m_cat/(m_cat + m_support) on the total-mixture basis (no other basis is
stated); the 10 mg is the mass of the C₃N₄ **support**, as printed ("a TOF of
8 h⁻¹ for 10 mg of C₃N₄, loaded with 1 with ω_cat = 3.8 %" — C₃N₄ is the named
support of part 8.5, and this reading is exactly what makes the 8.5 surface
density multiply against S·m_support); the TOF counts CO molecules per loaded
catalyst molecule per hour; the incident-photon rate is the LED power divided
by the single-photon energy E = hc/λ; and the problem's own φ formula.
Target: φ for CO formation, raw and unrounded, and reported at three
significant figures (project default; ties half away from zero).

## Derivation encoded below

For the stipulated run (m_support = 0.010 g of C₃N₄):
* inline T8-8.5 prerequisite (policy
  `derive_in_answer_blind_run_or_use_problem_stated_fallback`): the catalyst
  surface density N_cat = (ω_cat/(1−ω_cat))·N_A/(M_cat·S·10¹⁸) molecules nm⁻²
  is sample-size independent, proved for every admissible loaded sample;
* total catalyst molecules on the 10 mg support:
  N = N_cat·S·m_support·10¹⁸ = (ω_cat/(1−ω_cat))·N_A·m_support/M_cat;
* CO production rate: TOF·N molecules per hour; reacted-electron rate:
  2·TOF·N per hour;
* incident-photon rate: P·3600/(h·c/λ) photons per hour;
* φ = 100·(2·TOF·N)/(P·3600·λ/(h·c)).

The raw value is the exact rational
18940872892793693114789369/9799408490625000000000000 ≈ 1.9328588 (%); the
certified enclosure is (77/40, 387/200) = (1.925, 1.935); the reported value at
quantum 0.01 is 1.93 %.
-/

namespace IChO2026T8A6

open IChO2026Chem.Reporting

/-- Mass fraction of catalyst **1** in the loaded C₃N₄ material,
ω_cat = 3.8 % = 0.038 (catalyst mass over total mixture mass).
Problem-stipulated, exact as printed (T8, parts 8.5–8.6). -/
noncomputable def omegaCat : ℝ := 0.038

/-- Specific surface area of the crystalline C₃N₄ support, S = 17.8 m² g⁻¹.
Problem-stipulated, exact as printed (T8, part 8.5). -/
noncomputable def specificSurfaceArea : ℝ := 17.8

/-- Molar mass of catalyst **1**, M_cat = 557.21 g mol⁻¹.
Problem-stipulated, exact as printed (T8, part 8.5). -/
noncomputable def molarMassCat : ℝ := 557.21

/-- Mass of C₃N₄ support in the stipulated photocatalytic run,
10 mg = 0.010 g ("a TOF of 8 h⁻¹ for 10 mg of C₃N₄, loaded with **1** with
ω_cat = 3.8 %", T8, part 8.6).  Problem-stipulated, exact as printed. -/
noncomputable def sampleSupportMass : ℝ := 0.010

/-- Turnover frequency of the loaded catalyst, TOF = 8 h⁻¹ (product molecules
per active catalyst molecule per hour).  Problem-stipulated, exact as printed
(T8, part 8.6). -/
noncomputable def turnoverFrequency : ℝ := 8

/-- LED illumination wavelength, λ = 390 nm = 3.90 × 10⁻⁷ m.
Problem-stipulated, exact as printed (T8, part 8.6). -/
noncomputable def ledWavelength : ℝ := 3.90e-7

/-- LED illumination power, P = 50 mW = 0.050 J s⁻¹.
Problem-stipulated, exact as printed (T8, part 8.6). -/
noncomputable def ledPower : ℝ := 0.050

/-- Avogadro constant N_A = 6.02214076 × 10²³ mol⁻¹, an exact defining constant
of the SI (2019 revision).  Provenance: `trusted_general_law`. -/
noncomputable def avogadroConstant : ℝ := 6.02214076e23

/-- Planck constant h = 6.62607015 × 10⁻³⁴ J s, an exact defining constant of
the SI (2019 revision).  Provenance: `trusted_general_law`. -/
noncomputable def planckConstant : ℝ := 6.62607015e-34

/-- Speed of light in vacuum c = 299 792 458 m s⁻¹, an exact defining constant
of the SI.  Provenance: `trusted_general_law`. -/
noncomputable def speedOfLight : ℝ := 299792458

/-- Reacted electrons consumed per CO molecule formed: the acidic
half-equation of part 8.1 is CO₂ + 2H⁺ + 2e⁻ → CO + H₂O (carbon oxidation
state +IV → +II), so exactly two reacted electrons per product molecule.
Provenance: `problem_text` (part 8.1) via ordinary oxidation-state bookkeeping
(`trusted_general_law`). -/
noncomputable def electronsPerCO : ℝ := 2

/-- Exact SI prefix relation: one square metre in square nanometres,
1 m² = 10¹⁸ nm². -/
noncomputable def squareMetreInNm2 : ℝ := 1e18

/-- Exact time-unit relation: one hour in seconds, 1 h = 3600 s. -/
noncomputable def secondsPerHour : ℝ := 3600

/-- A sample of catalyst **1** loaded on crystalline C₃N₄, as specified in T8
parts 8.5–8.6.  The mass-fraction field binds the catalyst mass to the total
mixture mass (catalyst + support); the problem stipulates no other basis. -/
structure LoadedSample where
  /-- Mass of the C₃N₄ support in the sample (g). -/
  supportMass : ℝ
  /-- Mass of catalyst **1** in the sample (g). -/
  catalystMass : ℝ
  supportMass_pos : 0 < supportMass
  catalystMass_pos : 0 < catalystMass
  /-- The stipulated mass-fraction law ω_cat = m_cat / (m_cat + m_support). -/
  mass_fraction : catalystMass / (catalystMass + supportMass) = omegaCat

/-- Number of catalyst molecules in a loaded sample:
N = (m_cat / M_cat) · N_A. -/
noncomputable def catalystMolecules (s : LoadedSample) : ℝ :=
  s.catalystMass / molarMassCat * avogadroConstant

/-- Surface area of the sample's C₃N₄ support, in nm²:
A = S · m_support · 10¹⁸. -/
noncomputable def supportAreaNm2 (s : LoadedSample) : ℝ :=
  specificSurfaceArea * s.supportMass * squareMetreInNm2

/-- Catalyst surface density of a loaded sample, in molecules nm⁻² (the T8-8.5
quantity): the number of catalyst molecules divided by the support surface
area. -/
noncomputable def surfaceDensity (s : LoadedSample) : ℝ :=
  catalystMolecules s / supportAreaNm2 s

/-- The raw, unrounded catalyst surface density (molecules nm⁻²), derived
inline end to end from the problem-stipulated data — the T8-8.5 prerequisite,
whose policy is
`derive_in_answer_blind_run_or_use_problem_stated_fallback`:
N_cat = (ω_cat / (1 − ω_cat)) · N_A / (M_cat · S · 10¹⁸). -/
noncomputable def rawSurfaceDensity : ℝ :=
  omegaCat / (1 - omegaCat) * avogadroConstant /
    (molarMassCat * specificSurfaceArea * squareMetreInNm2)

/-- Energy of one 390 nm photon: E = h·c/λ (joules). -/
noncomputable def photonEnergy : ℝ :=
  planckConstant * speedOfLight / ledWavelength

/-- Number of photons incident on the sample per hour: the LED energy
delivered per hour divided by the single-photon energy,
P · 3600 / (h·c/λ). -/
noncomputable def incidentPhotonsPerHour : ℝ :=
  ledPower * secondsPerHour / photonEnergy

/-- CO molecules formed per hour by a loaded sample: TOF × (catalyst
molecules), from the problem's TOF definition. -/
noncomputable def coMoleculesPerHour (s : LoadedSample) : ℝ :=
  turnoverFrequency * catalystMolecules s

/-- Reacted electrons per hour for CO formation: two electrons per CO molecule
(part 8.1). -/
noncomputable def reactedElectronsPerHour (s : LoadedSample) : ℝ :=
  electronsPerCO * coMoleculesPerHour s

/-- Quantum yield for CO formation of a loaded sample, in %, by the problem's
own formula: φ = (reacted electrons)/(incident photons) · 100 %. -/
noncomputable def quantumYieldPercent (s : LoadedSample) : ℝ :=
  reactedElectronsPerHour s / incidentPhotonsPerHour * 100

/-- The raw, unrounded quantum yield for CO formation (%), derived end to end
from the problem-stipulated run with no intermediate rounding:
φ = 100 · (2 · TOF · N_cat · S · m_support · 10¹⁸) / (P · 3600 / (h·c/λ)),
with N_cat the inline-derived surface density `rawSurfaceDensity`. -/
noncomputable def rawQuantumYieldPercent : ℝ :=
  100 * (electronsPerCO * turnoverFrequency * rawSurfaceDensity *
    (specificSurfaceArea * sampleSupportMass * squareMetreInNm2)) /
      incidentPhotonsPerHour

/-- Problem-specific derivation specification for T8-8.6: (i) the inline
T8-8.5 prerequisite holds — every loaded sample obeying the stipulated
mass-fraction law has surface density equal to `rawSurfaceDensity`
(sample-size independence); and (ii) every such sample built on the stipulated
10 mg of C₃N₄ support has quantum yield equal to the raw closed-form
expression `rawQuantumYieldPercent`.  This is the governing relation: the
problem's φ formula fed by the TOF law, the two-electron stoichiometry of
part 8.1, the mass-fraction law, and the LED photon flux. -/
def QuantumYieldSpec : Prop :=
  (∀ s : LoadedSample, surfaceDensity s = rawSurfaceDensity) ∧
    ∀ s : LoadedSample, s.supportMass = sampleSupportMass →
      quantumYieldPercent s = rawQuantumYieldPercent

/-- Mass balance from the stipulated mass fraction: the catalyst-to-support
mass ratio equals ω_cat / (1 − ω_cat).  This is the algebraic heart of the raw
derivation, kept as a named step for the proof stage. -/
theorem catalyst_support_mass_ratio (s : LoadedSample) :
    s.catalystMass / s.supportMass = omegaCat / (1 - omegaCat) := by
  have h1 : (1 - omegaCat) ≠ 0 := by unfold omegaCat; norm_num
  have hsup : s.supportMass ≠ 0 := ne_of_gt s.supportMass_pos
  have hsum : s.catalystMass + s.supportMass ≠ 0 :=
    ne_of_gt (add_pos s.catalystMass_pos s.supportMass_pos)
  have h := s.mass_fraction
  rw [div_eq_iff hsum] at h
  rw [div_eq_div_iff hsup h1]
  linear_combination h

/-- Cross-multiplied form of `catalyst_support_mass_ratio`:
m_cat = m_support · ω_cat / (1 − ω_cat).  Target-local helper. -/
private theorem catalystMass_of_loaded (s : LoadedSample) :
    s.catalystMass = s.supportMass * (omegaCat / (1 - omegaCat)) := by
  have h := catalyst_support_mass_ratio s
  rw [div_eq_iff (ne_of_gt s.supportMass_pos)] at h
  rw [h]; ring

/-- The single-photon energy E = h·c/λ of the 390 nm LED is nonzero.
Target-local helper. -/
private theorem photonEnergy_ne : photonEnergy ≠ 0 := by
  unfold photonEnergy planckConstant speedOfLight ledWavelength
  norm_num

/-- The incident-photon rate P·3600/(h·c/λ) is nonzero.  Target-local
helper. -/
private theorem incidentPhotonsPerHour_ne : incidentPhotonsPerHour ≠ 0 := by
  unfold incidentPhotonsPerHour ledPower secondsPerHour
  exact div_ne_zero (by norm_num) photonEnergy_ne

/-- The inline T8-8.5 prerequisite: every loaded sample obeying the stipulated
mass-fraction law has catalyst surface density equal to the closed form
`rawSurfaceDensity` (sample-size independence).  Target-local helper. -/
private theorem surfaceDensity_eq_raw (s : LoadedSample) :
    surfaceDensity s = rawSurfaceDensity := by
  have hsup : s.supportMass ≠ 0 := ne_of_gt s.supportMass_pos
  have hM : molarMassCat ≠ 0 := by unfold molarMassCat; norm_num
  have hS : specificSurfaceArea ≠ 0 := by unfold specificSurfaceArea; norm_num
  have hnm : squareMetreInNm2 ≠ 0 := by unfold squareMetreInNm2; norm_num
  have h1 : (1 - omegaCat) ≠ 0 := by unfold omegaCat; norm_num
  unfold surfaceDensity catalystMolecules supportAreaNm2 rawSurfaceDensity
  rw [catalystMass_of_loaded s]
  field_simp

/-- The quantum yield of every loaded sample built on the stipulated 10 mg of
C₃N₄ support equals the closed-form `rawQuantumYieldPercent`.  Target-local
helper. -/
private theorem quantumYieldPercent_eq_raw (s : LoadedSample)
    (hmass : s.supportMass = sampleSupportMass) :
    quantumYieldPercent s = rawQuantumYieldPercent := by
  have hM : molarMassCat ≠ 0 := by unfold molarMassCat; norm_num
  have hS : specificSurfaceArea ≠ 0 := by unfold specificSurfaceArea; norm_num
  have hnm : squareMetreInNm2 ≠ 0 := by unfold squareMetreInNm2; norm_num
  have h1 : (1 - omegaCat) ≠ 0 := by unfold omegaCat; norm_num
  have hiph : incidentPhotonsPerHour ≠ 0 := incidentPhotonsPerHour_ne
  unfold quantumYieldPercent reactedElectronsPerHour coMoleculesPerHour
    catalystMolecules rawQuantumYieldPercent rawSurfaceDensity
  rw [catalystMass_of_loaded s, hmass]
  field_simp

/-- Certified enclosure of the raw quantum yield, evaluated end to end by
exact rational arithmetic from the stipulated constants:
77/40 = 1.925 ≤ φ < 1.935 = 387/200.  Target-local helper. -/
private theorem rawQuantumYieldPercent_bounds :
    (77 : ℝ) / 40 ≤ rawQuantumYieldPercent ∧
      rawQuantumYieldPercent < (387 : ℝ) / 200 := by
  unfold rawQuantumYieldPercent rawSurfaceDensity incidentPhotonsPerHour
    photonEnergy omegaCat avogadroConstant molarMassCat specificSurfaceArea
    sampleSupportMass turnoverFrequency ledWavelength ledPower planckConstant
    speedOfLight electronsPerCO squareMetreInNm2 secondsPerHour
  constructor <;> norm_num

/-- Raw result contract (answer-blind): the derivation specification holds, and
the raw quantum yield is certified to lie in the non-degenerate rational
enclosure (77/40, 387/200) = (1.925, 1.935) — the reporting half-cell of the
three-significant-figure quantum 0.01 %.  The raw value itself is the exact
expression `rawQuantumYieldPercent`
(= 18940872892793693114789369/9799408490625000000000000 ≈ 1.9328588 %), not a
rounded decimal. -/
theorem quantum_yield_raw :
    (IChO2026T8A6.QuantumYieldSpec) ∧
      (((77 : ℝ) / 40) ≤ (IChO2026T8A6.rawQuantumYieldPercent) ∧
        (IChO2026T8A6.rawQuantumYieldPercent) ≤ ((387 : ℝ) / 200)) := by
  refine ⟨?_, rawQuantumYieldPercent_bounds.1,
    le_of_lt rawQuantumYieldPercent_bounds.2⟩
  exact ⟨fun s => surfaceDensity_eq_raw s,
    fun s hmass => quantumYieldPercent_eq_raw s hmass⟩

/-- Reported result contract (answer-blind): at the predeclared project default
of three significant figures — quantum 0.01 % at this magnitude, ties away from
zero — the raw quantum yield is reported as 1.93 %. -/
theorem quantum_yield_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      (IChO2026T8A6.rawQuantumYieldPercent) ((193 : ℝ) / 100) ((1 : ℝ) / 100) := by
  have hb := rawQuantumYieldPercent_bounds
  have hpos : (0 : ℝ) ≤ rawQuantumYieldPercent :=
    le_trans (by norm_num) hb.1
  refine ⟨by norm_num, ⟨193, by norm_num⟩, ?_⟩
  rw [if_pos hpos]
  constructor
  · calc (193 : ℝ) / 100 - (1 / 100) / 2 = 77 / 40 := by norm_num
      _ ≤ rawQuantumYieldPercent := hb.1
  · calc rawQuantumYieldPercent < (387 : ℝ) / 200 := hb.2
      _ = (193 : ℝ) / 100 + (1 / 100) / 2 := by norm_num

/-- The solver-owned numeric submission, keeping the exact raw value separate
from the final reported value and recording the reporting quantum
explicitly. -/
noncomputable def submission : NumericSubmission where
  rawValue := rawQuantumYieldPercent
  reportedValue := 1.93
  reportingQuantum := 0.01

/-- The submission is valid: its raw value is the derived raw expression and
the reported value sits at the declared quantum. -/
theorem submission_valid :
    ValidNumericSubmission rawQuantumYieldPercent submission := by
  refine ⟨rfl, ?_⟩
  have e1 : submission.reportedValue = (193 : ℝ) / 100 := by
    show (1.93 : ℝ) = 193 / 100
    norm_num
  have e2 : submission.reportingQuantum = (1 : ℝ) / 100 := by
    show (0.01 : ℝ) = 1 / 100
    norm_num
  rw [e1, e2]
  exact quantum_yield_reported

end IChO2026T8A6
