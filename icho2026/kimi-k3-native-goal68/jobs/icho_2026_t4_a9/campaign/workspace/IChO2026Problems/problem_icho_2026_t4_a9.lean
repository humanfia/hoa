import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T4, subquestion 4.9 (`icho_2026_t4_a9`)

## Problem statement (official English problem materials, page Q4-3)

> The *Urtabulak* gas leak was ended by detonating a 30-kiloton in TNT
> equivalent underground nuclear explosion that collapsed the reservoir and
> sealed the leak. 1 ton of TNT equivalent is 4.184 GJ of energy.
>
> **4.9** Using the value from **4.4**, **calculate** the total number of
> fissions, TN, during the nuclear explosion. **Calculate** the mass, m, of
> enriched uranium used in the explosion (in kg), assuming it contained 90% by
> mass of the ²³⁵U isotope, and 33% of the ²³⁵U underwent fission.
> *If you did not get an answer for 4.4, use ΔE = 200 MeV.*

## Inputs and their grounding

Problem-stated (page Q4-3 / Q4-2), treated as exact printed data:

* yield of the explosion: 30 kilotons TNT equivalent;
* 1 ton of TNT equivalent = 4.184 GJ;
* enriched uranium is 90% ²³⁵U by mass and 33% of the ²³⁵U fissions;
* (part 4.4) BE(²³⁵U) = 7.59 MeV/nucleon, average BE(fission products)
  = 8.45 MeV/nucleon, free-neutron binding energy neglected.

Problem-stated (page Q4-1, part 4.1): the isotope ²³⁵U has mass
235.04 a.u. (g mol⁻¹ molar mass).

Derived inline below (no intermediate rounding, per the reporting policy):

* `deltaE_MeV_value`: the part-4.4 value ΔE = (8.45 − 7.59)·235 = 202.1 MeV.

Trusted general laws (exact SI/CODATA data not printed in the problem;
flagged as assumptions in `result.json`):

* 1 eV = 1.602176634 × 10⁻¹⁹ J (exact SI definition since 2019);
* Avogadro constant N_A = 6.02214076 × 10²³ mol⁻¹ (exact SI).

## Physical model used to combine the data

* Every fission releases ΔE, so TN = E_explosion / ΔE.
* The fissioned ²³⁵U atoms number TN, so the fissioned ²³⁵U mass is
  TN·M(²³⁵U)/N_A (molar mass in kg mol⁻¹ divided by N_A gives kg per atom).
* The fissioned ²³⁵U mass equals 33% of the total ²³⁵U mass, which in turn is
  90% of the enriched uranium mass:
  m = (TN·M(²³⁵U)/N_A) / (0.33 × 0.90).

## Requested outputs (three significant figures, half away from zero)

* TN = 3.876468179… × 10²⁴ fissions → **3.88 × 10²⁴ fissions** (quantum 10²²).
* m = 5.094137346… kg → **5.09 kg** (quantum 0.01 kg).
-/

namespace IChO2026T4A9

open IChO2026Chem.Reporting

/-! ### Exact problem data -/

/-- Explosive yield in tons of TNT equivalent: 30 kilotons. -/
noncomputable def yieldTonsTNT : ℝ := 30000

/-- Energy of one ton of TNT equivalent, in joules: 4.184 GJ. -/
noncomputable def joulesPerTonTNT : ℝ := 4.184 * 10 ^ 9

/-- Binding energy per nucleon of ²³⁵U (MeV/nucleon), part 4.4. -/
noncomputable def beU235 : ℝ := 7.59

/-- Average binding energy per nucleon of the fission products
(MeV/nucleon), part 4.4. -/
noncomputable def beFis : ℝ := 8.45

/-- Nucleon count of the fissioning system. Part 4.4 neglects the binding
energy of the free neutrons, so the released energy per fission is the
per-nucleon binding-energy change times the 235 nucleons that are bound on
both sides of the reaction. -/
noncomputable def nucleons : ℝ := 235

/-- Mass fraction of ²³⁵U in the enriched uranium. -/
noncomputable def enrichment : ℝ := 0.90

/-- Fraction of the ²³⁵U that underwent fission. -/
noncomputable def fissionFraction : ℝ := 0.33

/-- Molar mass of ²³⁵U in kg mol⁻¹ (235.04 a.u., part 4.1). -/
noncomputable def molarMassU235 : ℝ := 0.23504

/-! ### Trusted general constants (SI, exact; not printed in the problem) -/

/-- Joules per electronvolt (exact SI definition of the electronvolt). -/
noncomputable def joulesPerEV : ℝ := 1.602176634 * 10 ^ (-19 : ℤ)

/-- Avogadro constant, mol⁻¹ (exact SI). -/
noncomputable def avogadro : ℝ := 6.02214076 * 10 ^ 23

/-! ### Derived quantities -/

/-- Part 4.4 value, re-derived answer-blind:
ΔE = (BE(fis.) − BE(²³⁵U))·235 = 202.1 MeV per fission. -/
theorem deltaE_MeV_value : (beFis - beU235) * nucleons = 202.1 := by
  unfold beFis beU235 nucleons; norm_num

/-- Energy released per fission, expressed in MeV. -/
noncomputable def deltaE_MeV : ℝ := (beFis - beU235) * nucleons

/-- Total energy released by the explosion, in joules:
E = 30000 t × 4.184 × 10⁹ J t⁻¹ = 1.2552 × 10¹⁴ J. -/
noncomputable def explosionEnergy_J : ℝ := yieldTonsTNT * joulesPerTonTNT

theorem explosionEnergy_value : explosionEnergy_J = 1.2552 * 10 ^ 14 := by
  unfold explosionEnergy_J yieldTonsTNT joulesPerTonTNT; norm_num

/-- Total number of fissions during the explosion:
TN = E / (ΔE expressed in joules). -/
noncomputable def totalFissions : ℝ :=
  explosionEnergy_J / (deltaE_MeV * 10 ^ 6 * joulesPerEV)

/-- Mass of ²³⁵U that underwent fission, in kg:
m(²³⁵U fissioned) = TN·M(²³⁵U)/N_A. -/
noncomputable def massU235Fissioned : ℝ := totalFissions * molarMassU235 / avogadro

/-- Mass of enriched uranium used, in kg: the fissioned ²³⁵U is 33% of the
²³⁵U present, which is 90% of the enriched uranium:
m = TN·M(²³⁵U)/(N_A·0.33·0.90). -/
noncomputable def enrichedUraniumMass : ℝ := massU235Fissioned / (fissionFraction * enrichment)

/-! ### Numerical bounds establishing the three-significant-figure values

These inequalities are proved on the exact rational expressions that the
definitions unfold to; no intermediate rounding is used anywhere. -/

/-- 3.875 × 10²⁴ ≤ TN < 3.885 × 10²⁴, so TN rounds to 3.88 × 10²⁴ at three
significant figures. -/
theorem totalFissions_bounds :
    3.875 * 10 ^ 24 ≤ totalFissions ∧ totalFissions < 3.885 * 10 ^ 24 := by
  unfold totalFissions explosionEnergy_J deltaE_MeV yieldTonsTNT
    joulesPerTonTNT beFis beU235 nucleons joulesPerEV
  norm_num

/-- 5.085 ≤ m < 5.095, so m rounds to 5.09 kg at three significant figures. -/
theorem enrichedUraniumMass_bounds :
    5.085 ≤ enrichedUraniumMass ∧ enrichedUraniumMass < 5.095 := by
  unfold enrichedUraniumMass massU235Fissioned totalFissions
    explosionEnergy_J deltaE_MeV yieldTonsTNT joulesPerTonTNT beFis beU235
    nucleons joulesPerEV molarMassU235 avogadro fissionFraction enrichment
  norm_num

/-! ### Final reported answers under the project-wide reporting contract
(three significant figures, exact ties half away from zero). -/

/-- Reported total number of fissions: TN = 3.88 × 10²⁴ fissions
(quantum 10²² fissions). -/
noncomputable def totalFissionsSubmission : NumericSubmission where
  rawValue := totalFissions
  reportedValue := 3.88 * 10 ^ 24
  reportingQuantum := 10 ^ 22

/-- Reported mass of enriched uranium: m = 5.09 kg (quantum 0.01 kg). -/
noncomputable def enrichedUraniumMassSubmission : NumericSubmission where
  rawValue := enrichedUraniumMass
  reportedValue := 5.09
  reportingQuantum := 0.01

/-- The fission-count submission is valid: its raw value is the exact derived
expression and 3.88 × 10²⁴ is the nearest multiple of 10²². -/
theorem totalFissions_reported :
    ValidNumericSubmission totalFissions totalFissionsSubmission := by
  obtain ⟨hb1, hb2⟩ := totalFissions_bounds
  refine ⟨rfl, by norm_num [totalFissionsSubmission], ⟨388, ?_⟩, ?_⟩
  · norm_num [totalFissionsSubmission]
  · have hpos : 0 ≤ totalFissions := by unfold totalFissions; positivity
    have hpos' : 0 ≤ totalFissionsSubmission.rawValue := hpos
    rw [if_pos hpos']
    simp only [totalFissionsSubmission]
    have e1 : (3.88 * 10 ^ 24 : ℝ) - (10 : ℝ) ^ 22 / 2 = 3.875 * 10 ^ 24 := by norm_num
    have e2 : (3.88 * 10 ^ 24 : ℝ) + (10 : ℝ) ^ 22 / 2 = 3.885 * 10 ^ 24 := by norm_num
    rw [e1, e2]
    exact ⟨hb1, hb2⟩

/-- The enriched-uranium mass submission is valid: its raw value is the exact
derived expression and 5.09 kg is the nearest multiple of 0.01 kg. -/
theorem enrichedUraniumMass_reported :
    ValidNumericSubmission enrichedUraniumMass enrichedUraniumMassSubmission := by
  obtain ⟨hb1, hb2⟩ := enrichedUraniumMass_bounds
  refine ⟨rfl, by norm_num [enrichedUraniumMassSubmission], ⟨509, ?_⟩, ?_⟩
  · norm_num [enrichedUraniumMassSubmission]
  · have hpos : 0 ≤ enrichedUraniumMass := by
      unfold enrichedUraniumMass; positivity
    have hpos' : 0 ≤ enrichedUraniumMassSubmission.rawValue := hpos
    rw [if_pos hpos']
    simp only [enrichedUraniumMassSubmission]
    have e1 : (5.09 : ℝ) - 0.01 / 2 = 5.085 := by norm_num
    have e2 : (5.09 : ℝ) + 0.01 / 2 = 5.095 := by norm_num
    rw [e1, e2]
    exact ⟨hb1, hb2⟩

end IChO2026T4A9
