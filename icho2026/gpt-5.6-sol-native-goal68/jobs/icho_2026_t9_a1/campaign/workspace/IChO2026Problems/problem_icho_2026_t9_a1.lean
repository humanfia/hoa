import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026 T9-A1: molar mass of beta-cyclodextrin

The problem states that beta-cyclodextrin is a cyclic oligosaccharide made from
seven glucose units joined by alpha-1,4-glycosidic bonds, and stipulates
`M(glucose) = 180.16 g mol^-1`.  The periodic table supplied with the paper
gives `M(H) = 1.008 g mol^-1` and `M(O) = 16.00 g mol^-1`.

The chemistry law used below is the usual condensation accounting for a
glycosidic bond: each link removes one water molecule.  In a cyclic chain each
unit supplies one link to its successor, so seven units give seven links.
-/

namespace IChO2026Problems.ProblemIcho2026T9A1

open IChO2026Chem.Reporting

/-! ## Problem data -/

/-- The number of glucose-derived units in beta-CD, as stated in the problem. -/
def betaCDUnitCount : ℕ := 7

/-- Stipulated glucose molar mass, in `g mol^-1`. -/
noncomputable def glucoseMolarMass : ℝ := 18016 / 100

/-- Hydrogen atomic molar mass from the paper's periodic table, in `g mol^-1`. -/
noncomputable def hydrogenAtomicMolarMass : ℝ := 1008 / 1000

/-- Oxygen atomic molar mass from the paper's periodic table, in `g mol^-1`. -/
noncomputable def oxygenAtomicMolarMass : ℝ := 16

/-! ## Chemical and cyclic-structure accounting -/

/-- A water molecule contains two hydrogen atoms and one oxygen atom. -/
noncomputable def waterMolarMass : ℝ :=
  2 * hydrogenAtomicMolarMass + oxygenAtomicMolarMass

/-- The successor of a unit in the seven-membered cyclic oligosaccharide. -/
def betaCDNextUnit (i : Fin 7) : Fin 7 := i + 1

/-- The directed glycosidic links around beta-CD's ring.  A link is indexed by
its source unit and ends at the next unit around the cycle. -/
def betaCDRingBonds : Finset (Fin 7 × Fin 7) :=
  Finset.univ.image (fun i => (i, betaCDNextUnit i))

/-- A cyclic chain of seven units has seven distinct glycosidic links. -/
theorem beta_cd_has_seven_glycosidic_bonds : betaCDRingBonds.card = 7 := by
  have hinjective : Set.InjOn
      (fun i : Fin 7 => (i, betaCDNextUnit i)) (Finset.univ : Finset (Fin 7)) := by
    intro i _ j _ hij
    exact congrArg Prod.fst hij
  rw [betaCDRingBonds, Finset.card_image_iff.mpr hinjective]
  simp

/-- Condensation mass balance: begin with `unitCount` monomers and remove one
water molecule for each bond formed. -/
noncomputable def condensationProductMolarMass
    (unitMass waterMass : ℝ) (unitCount bondCount : ℕ) : ℝ :=
  unitCount * unitMass - bondCount * waterMass

/-- Exact molar-mass expression for beta-CD, before final display rounding. -/
noncomputable def betaCDRawMolarMass : ℝ :=
  condensationProductMolarMass glucoseMolarMass waterMolarMass
    betaCDUnitCount betaCDRingBonds.card

/-! ## Exact calculation and requested report -/

/-- The source atomic masses give `M(H2O) = 18.016 g mol^-1`. -/
theorem water_molar_mass_exact : waterMolarMass = 2252 / 125 := by
  norm_num [waterMolarMass, hydrogenAtomicMolarMass, oxygenAtomicMolarMass]

/-- The unrounded source-based result is `1135.008 g mol^-1`. -/
theorem beta_cd_raw_molar_mass : betaCDRawMolarMass = 141876 / 125 := by
  rw [betaCDRawMolarMass, beta_cd_has_seven_glycosidic_bonds]
  norm_num [condensationProductMolarMass, betaCDUnitCount, glucoseMolarMass,
    waterMolarMass, hydrogenAtomicMolarMass, oxygenAtomicMolarMass]

/-- Three significant figures at this magnitude means a last-place quantum of
`10 g mol^-1`; scientific notation makes the trailing zero unambiguous. -/
noncomputable def betaCDSubmission : NumericSubmission where
  rawValue := 141876 / 125
  reportedValue := 1140
  reportingQuantum := 10

/-- `1135.008` rounds to `1140 = 1.14 * 10^3` under the fixed nearest-value,
half-away-from-zero reporting rule. -/
theorem beta_cd_three_significant_figures :
    ValidNumericSubmission betaCDRawMolarMass betaCDSubmission := by
  constructor
  · norm_num [betaCDSubmission, beta_cd_raw_molar_mass]
  · norm_num [ReportsAtQuantum, betaCDSubmission]
    exact ⟨114, by norm_num⟩

/-- Final combined result: exact raw value and valid requested display. -/
theorem beta_cd_molar_mass_answer :
    betaCDRawMolarMass = 141876 / 125 ∧
      betaCDSubmission.reportedValue = 1140 ∧
      ValidNumericSubmission betaCDRawMolarMass betaCDSubmission := by
  exact ⟨beta_cd_raw_molar_mass, rfl, beta_cd_three_significant_figures⟩

#print axioms beta_cd_has_seven_glycosidic_bonds
#print axioms water_molar_mass_exact
#print axioms beta_cd_raw_molar_mass
#print axioms beta_cd_three_significant_figures
#print axioms beta_cd_molar_mass_answer

end IChO2026Problems.ProblemIcho2026T9A1
