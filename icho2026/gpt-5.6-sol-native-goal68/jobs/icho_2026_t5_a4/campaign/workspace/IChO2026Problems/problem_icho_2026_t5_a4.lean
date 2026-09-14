import IChO2026Chem.Reporting

/-!
# IChO 2026 T5-A4: identifying the iodine-containing addition reagent

The problem data are kept separate from the derived chemistry arithmetic.
The preceding part is derived inline: three reductive-ozonolysis products mean
two carbon-carbon double bonds, and the fragment construction of cardiolipin
then turns the stated total of 255 bonds into an 18-carbon fatty acid.

For part 5.4, `IodineHalogenReagent` is the finite chemical interpretation of
"reacts in similar way with iodine": an iodine-containing diatomic halogen or
interhalogen adds once to each C=C bond.  The theorem
`compound_x_formula` proves that the displayed iodine mass fraction uniquely
selects IBr from that domain.
-/

namespace IChO2026Problems.ProblemIChO2026T5A4

open IChO2026Chem.Reporting

noncomputable section

/-! ## Formula records and problem data -/

/-- Atom counts sufficient for every molecular formula used in this part. -/
structure MolecularFormula where
  carbon : ℕ := 0
  hydrogen : ℕ := 0
  oxygen : ℕ := 0
  fluorine : ℕ := 0
  chlorine : ℕ := 0
  bromine : ℕ := 0
  iodine : ℕ := 0
  phosphorus : ℕ := 0
  deriving DecidableEq, Repr

namespace ProblemData

/-- Printed number of distinct equimolar reductive-ozonolysis products. -/
def ozonolysisProductCount : ℕ := 3

/-- Printed total number of sigma and pi bonds in non-ionised PL1. -/
def pl1BondCount : ℕ := 255

/-- Printed iodine uptake, in grams per 100 g fatty acid. -/
def iodineUptakeShown : ℝ := 1810 / 10

/-- Last displayed quantum of the iodine-uptake measurement. -/
def iodineUptakeQuantum : ℝ := 1 / 10

/-- Printed iodine mass percentage of the adduct. -/
def adductIodinePercentShown : ℝ := 3657 / 100

/-- Last displayed quantum of the iodine mass percentage. -/
def adductIodinePercentQuantum : ℝ := 1 / 100

end ProblemData

/-! ## Inline derivation of the fatty acid from part 5.3 -/

/-- Cutting an acyclic chain at each of `doubleBondCount` distinct C=C bonds
gives `doubleBondCount + 1` fragments.  With the source's three different
equimolar products, the acid therefore contains two C=C bonds. -/
theorem fattyAcid_doubleBondCount
    (doubleBondCount : ℕ)
    (hcleavage : ProblemData.ozonolysisProductCount = doubleBondCount + 1) :
    doubleBondCount = 2 := by
  norm_num [ProblemData.ozonolysisProductCount] at hcleavage
  omega

/-- Formula law for an acyclic monocarboxylic fatty acid: CnH(2n-2d)O2,
where `d` is its number of carbon-carbon double bonds. -/
def acyclicFattyAcidFormula
    (carbonCount doubleBondCount : ℕ) : MolecularFormula where
  carbon := carbonCount
  hydrogen := 2 * carbonCount - 2 * doubleBondCount
  oxygen := 2

/-- Formula of an acyclic monocarboxylic fatty acid with two C=C bonds.
The two double bonds follow from the source's three equimolar reductive-
ozonolysis products (a chain cut at two distinct C=C bonds has three pieces). -/
def dieneFattyAcidFormula (carbonCount : ℕ) : MolecularFormula :=
  acyclicFattyAcidFormula carbonCount 2

/-- Formula of non-ionised PL1 after condensing three glycerols, two phosphoric
acids, and four identical diene fatty acids, with eight waters eliminated.
Thus C = 9 + 4n, H = 8n - 2, O = 17, and P = 2. -/
def pl1FormulaFromDiene (carbonCount : ℕ) : MolecularFormula where
  carbon := 9 + 4 * carbonCount
  hydrogen := 8 * carbonCount - 2
  oxygen := 17
  phosphorus := 2

/-- For a neutral CHOP formula, half the sum of ordinary valences counts all
sigma and pi bonds (bond order): C 4, H 1, O 2, P 5. -/
def totalBondOrder (f : MolecularFormula) : ℕ :=
  (4 * f.carbon + f.hydrogen + 2 * f.oxygen + 5 * f.phosphorus) / 2

/-- The fragment-derived PL1 formula has `39 + 12n` total sigma/pi bonds. -/
theorem pl1_totalBondOrder (carbonCount : ℕ) (hcarbon : 1 ≤ carbonCount) :
    totalBondOrder (pl1FormulaFromDiene carbonCount) = 39 + 12 * carbonCount := by
  simp [totalBondOrder, pl1FormulaFromDiene]
  omega

/-- The printed 255-bond constraint uniquely fixes 18 carbons in the fatty
acid; this is the dependency on part 5.3, proved rather than assumed. -/
theorem fattyAcid_carbonCount
    (carbonCount : ℕ) (hcarbon : 1 ≤ carbonCount)
    (hbonds : totalBondOrder (pl1FormulaFromDiene carbonCount) =
      ProblemData.pl1BondCount) :
    carbonCount = 18 := by
  rw [pl1_totalBondOrder carbonCount hcarbon] at hbonds
  norm_num [ProblemData.pl1BondCount] at hbonds
  omega

/-- Molecular formula of the fatty acid required by the source constraints. -/
theorem fattyAcid_formula_from_source
    (carbonCount : ℕ) (hcarbon : 1 ≤ carbonCount)
    (hbonds : totalBondOrder (pl1FormulaFromDiene carbonCount) =
      ProblemData.pl1BondCount) :
    dieneFattyAcidFormula carbonCount =
      { carbon := 18, hydrogen := 32, oxygen := 2 } := by
  have hc : carbonCount = 18 :=
    fattyAcid_carbonCount carbonCount hcarbon hbonds
  subst carbonCount
  rfl

/-- Combined previous-part dependency: the ozonolysis observation and the
255-bond constraint together prove C18H32O2 without assuming that result. -/
theorem fattyAcid_formula_from_all_source_constraints
    (carbonCount doubleBondCount : ℕ) (hcarbon : 1 ≤ carbonCount)
    (hcleavage : ProblemData.ozonolysisProductCount = doubleBondCount + 1)
    (hbonds : totalBondOrder (pl1FormulaFromDiene carbonCount) =
      ProblemData.pl1BondCount) :
    acyclicFattyAcidFormula carbonCount doubleBondCount =
      { carbon := 18, hydrogen := 32, oxygen := 2 } := by
  have hd : doubleBondCount = 2 :=
    fattyAcid_doubleBondCount doubleBondCount hcleavage
  subst doubleBondCount
  exact fattyAcid_formula_from_source carbonCount hcarbon hbonds

/-! ## Exact molar-mass and addition arithmetic -/

-- Atomic masses printed in the periodic table supplied with the problem PDF.
def atomicMassH : ℝ := 1008 / 1000
def atomicMassC : ℝ := 1201 / 100
def atomicMassO : ℝ := 16
def atomicMassF : ℝ := 19
def atomicMassCl : ℝ := 3545 / 100
def atomicMassBr : ℝ := 799 / 10
def atomicMassI : ℝ := 1269 / 10

/-- Molar mass of C18H32O2 in g mol^-1. -/
def fattyAcidMolarMass : ℝ :=
  18 * atomicMassC + 32 * atomicMassH + 2 * atomicMassO

theorem fattyAcidMolarMass_exact :
    fattyAcidMolarMass = 70109 / 250 := by
  norm_num [fattyAcidMolarMass, atomicMassC, atomicMassH, atomicMassO]

/-- A diene consumes two moles of I2 per mole of acid.  This is the iodine mass
consumed by 100 g of the fatty acid. -/
def iodineUptakePer100 : ℝ :=
  (100 / fattyAcidMolarMass) * 2 * (2 * atomicMassI)

/-- Independent consistency check against the printed 181.0 g iodine uptake,
using the mandated half-last-place measurement interval. -/
theorem iodineUptake_matches_source :
    ConsistentMeasurement iodineUptakePer100
      ProblemData.iodineUptakeShown ProblemData.iodineUptakeQuantum := by
  norm_num [ConsistentMeasurement, iodineUptakePer100,
    fattyAcidMolarMass, atomicMassC, atomicMassH, atomicMassO, atomicMassI,
    ProblemData.iodineUptakeShown, ProblemData.iodineUptakeQuantum,
    abs_of_nonneg, abs_of_nonpos]

/-- Iodine-containing diatomic halogens/interhalogens that can undergo the
same electrophilic addition pattern as I2. -/
inductive IodineHalogenReagent
  | iodineFluoride
  | iodineChloride
  | iodineBromide
  | iodine
  deriving DecidableEq, Repr

def reagentFormula : IodineHalogenReagent → MolecularFormula
  | .iodineFluoride => { fluorine := 1, iodine := 1 }
  | .iodineChloride => { chlorine := 1, iodine := 1 }
  | .iodineBromide => { bromine := 1, iodine := 1 }
  | .iodine => { iodine := 2 }

/-- The requested molecular formula IBr as an atom-count record. -/
def iodineMonobromideFormula : MolecularFormula :=
  { bromine := 1, iodine := 1 }

def reagentMolarMass : IodineHalogenReagent → ℝ
  | .iodineFluoride => atomicMassI + atomicMassF
  | .iodineChloride => atomicMassI + atomicMassCl
  | .iodineBromide => atomicMassI + atomicMassBr
  | .iodine => 2 * atomicMassI

def iodineAtomsPerReagent : IodineHalogenReagent → ℕ
  | .iodineFluoride => 1
  | .iodineChloride => 1
  | .iodineBromide => 1
  | .iodine => 2

/-- Iodine mass percentage after two reagent molecules add to the two C=C
bonds of one C18H32O2 molecule. -/
def adductIodineMassPercent (x : IodineHalogenReagent) : ℝ :=
  100 * (2 * (iodineAtomsPerReagent x : ℝ) * atomicMassI) /
    (fattyAcidMolarMass + 2 * reagentMolarMass x)

/-- IBr predicts 36.5687...%, which lies in the source interval
[36.565%, 36.575%] represented by `ConsistentMeasurement`. -/
theorem iodineBromide_matches_source :
    ConsistentMeasurement
      (adductIodineMassPercent .iodineBromide)
      ProblemData.adductIodinePercentShown
      ProblemData.adductIodinePercentQuantum := by
  norm_num [ConsistentMeasurement, adductIodineMassPercent,
    iodineAtomsPerReagent, reagentMolarMass, fattyAcidMolarMass,
    atomicMassC, atomicMassH, atomicMassO, atomicMassBr, atomicMassI,
    ProblemData.adductIodinePercentShown,
    ProblemData.adductIodinePercentQuantum, abs_of_nonneg, abs_of_nonpos]

/-- Among iodine-containing diatomic halogen reagents, the measured adduct
percentage uniquely selects iodine monobromide. -/
theorem iodineReagent_unique
    (x : IodineHalogenReagent)
    (hmeasurement : ConsistentMeasurement
      (adductIodineMassPercent x)
      ProblemData.adductIodinePercentShown
      ProblemData.adductIodinePercentQuantum) :
    x = .iodineBromide := by
  cases x with
  | iodineFluoride =>
    norm_num [ConsistentMeasurement, adductIodineMassPercent,
      iodineAtomsPerReagent, reagentMolarMass, fattyAcidMolarMass,
      atomicMassC, atomicMassH, atomicMassO, atomicMassF, atomicMassCl,
      atomicMassBr, atomicMassI, ProblemData.adductIodinePercentShown,
      ProblemData.adductIodinePercentQuantum, abs_of_nonneg, abs_of_nonpos]
      at hmeasurement
  | iodineChloride =>
    norm_num [ConsistentMeasurement, adductIodineMassPercent,
      iodineAtomsPerReagent, reagentMolarMass, fattyAcidMolarMass,
      atomicMassC, atomicMassH, atomicMassO, atomicMassF, atomicMassCl,
      atomicMassBr, atomicMassI, ProblemData.adductIodinePercentShown,
      ProblemData.adductIodinePercentQuantum, abs_of_nonneg, abs_of_nonpos]
      at hmeasurement
  | iodineBromide => rfl
  | iodine =>
    norm_num [ConsistentMeasurement, adductIodineMassPercent,
      iodineAtomsPerReagent, reagentMolarMass, fattyAcidMolarMass,
      atomicMassC, atomicMassH, atomicMassO, atomicMassF, atomicMassCl,
      atomicMassBr, atomicMassI, ProblemData.adductIodinePercentShown,
      ProblemData.adductIodinePercentQuantum, abs_of_nonneg, abs_of_nonpos]
      at hmeasurement

/-- **Requested output (T5-A4).** Any source-consistent iodine-containing
halogen addition reagent has molecular formula IBr. -/
theorem compound_x_formula
    (x : IodineHalogenReagent)
    (hmeasurement : ConsistentMeasurement
      (adductIodineMassPercent x)
      ProblemData.adductIodinePercentShown
      ProblemData.adductIodinePercentQuantum) :
    reagentFormula x = iodineMonobromideFormula := by
  rw [iodineReagent_unique x hmeasurement]
  rfl

#print axioms fattyAcid_formula_from_source
#print axioms fattyAcid_formula_from_all_source_constraints
#print axioms iodineUptake_matches_source
#print axioms iodineBromide_matches_source
#print axioms iodineReagent_unique
#print axioms compound_x_formula

end

end IChO2026Problems.ProblemIChO2026T5A4
