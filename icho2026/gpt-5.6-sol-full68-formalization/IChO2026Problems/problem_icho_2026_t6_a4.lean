import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T6, part A4: positive-mode mass spectrum

The problem supplies cyclo[48]carbon (`C₄₈`), the molecular formula
`C₄₀H₃₄N₂O₃` of macrocycle E, the observed integer `m/z` values, positive-ion
electrospray conditions, and a no-fragmentation instruction.  This file models
an observed ion as a whole-number assembly of intact `C₄₈` and E components,
together with added protons.  Consequently, the no-fragmentation condition is
carried by the `intact_formula` equality rather than by an unconstrained flag.

The atomic masses below are the integer mass numbers required by the problem.
The corresponding isotope identities were checked in the pinned offline
AME2020 subset; the source instruction to use integer masses overrides the
nonintegral exact isotope masses.
-/

namespace IChO2026Problems.ProblemIcho2026T6A4

/-- Element counts needed for every formula occurring in this subproblem. -/
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

namespace MolecularFormula

/-- Componentwise addition of molecular formulae. -/
def add (x y : MolecularFormula) : MolecularFormula where
  carbon := x.carbon + y.carbon
  hydrogen := x.hydrogen + y.hydrogen
  nitrogen := x.nitrogen + y.nitrogen
  oxygen := x.oxygen + y.oxygen

/-- `scale n f` is the formula of `n` intact copies of `f`. -/
def scale (n : ℕ) (f : MolecularFormula) : MolecularFormula where
  carbon := n * f.carbon
  hydrogen := n * f.hydrogen
  nitrogen := n * f.nitrogen
  oxygen := n * f.oxygen

end MolecularFormula

/-- The source-requested integer atomic-mass convention: H = 1, C = 12,
N = 14, and O = 16. -/
structure IntegerAtomicMassTable where
  hydrogen : ℕ
  carbon : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

def integerAtomicMasses : IntegerAtomicMassTable where
  hydrogen := 1
  carbon := 12
  nitrogen := 14
  oxygen := 16

/-- Nominal molecular mass in integer daltons under the convention requested
by the problem. -/
def integerMass (f : MolecularFormula) : ℕ :=
  integerAtomicMasses.carbon * f.carbon +
  integerAtomicMasses.hydrogen * f.hydrogen +
  integerAtomicMasses.nitrogen * f.nitrogen +
  integerAtomicMasses.oxygen * f.oxygen

/-- Dataset identity for the four isotope-mass lookups used only to audit the
integer mass-number convention. -/
def offlineChemistryDatasetSha256 : String :=
  "11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5"

def carbon12RecordSha256 : String :=
  "2c212258b787c2459da3b2f29c00882f3d8183c37528ace98a83ece308a2decc"

def hydrogen1RecordSha256 : String :=
  "32ec098d6ab9366a09311d83b4923d0f0120b126eeaacb7cfa4bbd0fa1497ff8"

def nitrogen14RecordSha256 : String :=
  "2512d93a1393f4bca3ad7f9d94c35cd9bd7179d99d84b4dd258cbd63b95503ba"

def oxygen16RecordSha256 : String :=
  "e3c31feaf7f8262947f9ffa8f4047dfd5f5c123ff0c136cab1f0fcca919e9c69"

/-- Formula of the carbon nanoring explicitly shown on page Q6-2. -/
def cyclo48Formula : MolecularFormula where
  carbon := 48
  hydrogen := 0
  nitrogen := 0
  oxygen := 0

/-- Formula printed underneath macrocycle E on page Q6-2. -/
def macrocycleEFormula : MolecularFormula where
  carbon := 40
  hydrogen := 34
  nitrogen := 2
  oxygen := 3

/-- Formula contribution of one added proton at the integer-mass resolution
requested in the question. -/
def protonFormula : MolecularFormula where
  carbon := 0
  hydrogen := 1
  nitrogen := 0
  oxygen := 0

/-- Additive formula of an intact assembly.  Catenation is noncovalent, so no
atoms are subtracted when the intact components are assembled. -/
def assembledFormula (cyclo48Count macrocycleECount addedProtonCount : ℕ) :
    MolecularFormula :=
  MolecularFormula.add
    (MolecularFormula.scale cyclo48Count cyclo48Formula)
    (MolecularFormula.add
      (MolecularFormula.scale macrocycleECount macrocycleEFormula)
      (MolecularFormula.scale addedProtonCount protonFormula))

/-- A positive ion whose elemental formula is explicitly accounted for by
whole `C₄₈` rings, whole macrocycles E, and added protons.  The last field is
the formal no-fragmentation ledger. -/
structure IntactAssemblyIon where
  formula : MolecularFormula
  cyclo48Count : ℕ
  macrocycleECount : ℕ
  addedProtonCount : ℕ
  positiveCharge : ℕ
  positiveCharge_pos : 0 < positiveCharge
  intact_formula :
    formula = assembledFormula cyclo48Count macrocycleECount addedProtonCount

/-- Construct the protonated positive-mode ion of an intact assembly. -/
def protonatedAssembly
    (cyclo48Count macrocycleECount charge : ℕ) (hcharge : 0 < charge) :
    IntactAssemblyIon where
  formula := assembledFormula cyclo48Count macrocycleECount charge
  cyclo48Count := cyclo48Count
  macrocycleECount := macrocycleECount
  addedProtonCount := charge
  positiveCharge := charge
  positiveCharge_pos := hcharge
  intact_formula := rfl

/-- Exact integer `m/z` relation, written without natural-number division. -/
def HasMz (ion : IntactAssemblyIon) (mz : ℕ) : Prop :=
  integerMass ion.formula = mz * ion.positiveCharge

/-- The four peaks printed in the current subquestion. -/
def observedPeaks : Finset ℕ := {591, 783, 879, 1174}

/-- A candidate accounts for an actually printed peak. -/
def AccountsForObservedPeak (ion : IntactAssemblyIon) (mz : ℕ) : Prop :=
  mz ∈ observedPeaks ∧ HasMz ion mz

/-- The free protonated macrocycle corresponding to the worked `m/z = 591`
example mentioned in the source. -/
def ion591 : IntactAssemblyIon := protonatedAssembly 0 1 1 (by norm_num)

def ion591Formula : MolecularFormula where
  carbon := 40
  hydrogen := 35
  nitrogen := 2
  oxygen := 3

/-- Source calibration: intact E plus one proton has nominal mass and charge
giving `m/z = 591`. -/
def Ion591ExampleSpec : Prop :=
  ion591.formula = ion591Formula ∧
  ion591.cyclo48Count = 0 ∧
  ion591.macrocycleECount = 1 ∧
  ion591.addedProtonCount = 1 ∧
  ion591.positiveCharge = 1 ∧
  integerMass ion591.formula = 591 ∧
  AccountsForObservedPeak ion591 591

theorem ion591_example : Ion591ExampleSpec := by
  norm_num [Ion591ExampleSpec, ion591, ion591Formula, protonatedAssembly,
    assembledFormula, MolecularFormula.add, MolecularFormula.scale,
    cyclo48Formula, macrocycleEFormula, protonFormula, integerMass,
    integerAtomicMasses, AccountsForObservedPeak, observedPeaks, HasMz]

/-- Proposed identity at `m/z = 783`: one C₄₈ ring, three intact E
macrocycles, and three added protons, with charge `3+`. -/
def ion783 : IntactAssemblyIon := protonatedAssembly 1 3 3 (by norm_num)

def ion783Formula : MolecularFormula where
  carbon := 168
  hydrogen := 105
  nitrogen := 6
  oxygen := 9

/-- Proposed identity at `m/z = 879`: one C₄₈ ring, two intact E
macrocycles, and two added protons, with charge `2+`. -/
def ion879 : IntactAssemblyIon := protonatedAssembly 1 2 2 (by norm_num)

def ion879Formula : MolecularFormula where
  carbon := 128
  hydrogen := 70
  nitrogen := 4
  oxygen := 6

/-- Proposed identity at `m/z = 1174`: the same one-C₄₈/three-E neutral
catenane core as the 783 ion, but with two added protons and charge `2+`. -/
def ion1174 : IntactAssemblyIon := protonatedAssembly 1 3 2 (by norm_num)

def ion1174Formula : MolecularFormula where
  carbon := 168
  hydrogen := 104
  nitrogen := 6
  oxygen := 9

/-- Full source-to-output specification for the ion at `m/z = 783`. -/
def Ion783Identity : Prop :=
  ion783.cyclo48Count = 1 ∧
  ion783.macrocycleECount = 3 ∧
  ion783.addedProtonCount = 3 ∧
  ion783.positiveCharge = 3 ∧
  ion783.formula = ion783Formula ∧
  integerMass ion783.formula = 2349 ∧
  AccountsForObservedPeak ion783 783

/-- Full source-to-output specification for the ion at `m/z = 879`. -/
def Ion879Identity : Prop :=
  ion879.cyclo48Count = 1 ∧
  ion879.macrocycleECount = 2 ∧
  ion879.addedProtonCount = 2 ∧
  ion879.positiveCharge = 2 ∧
  ion879.formula = ion879Formula ∧
  integerMass ion879.formula = 1758 ∧
  AccountsForObservedPeak ion879 879

/-- Full source-to-output specification for the ion at `m/z = 1174`. -/
def Ion1174Identity : Prop :=
  ion1174.cyclo48Count = 1 ∧
  ion1174.macrocycleECount = 3 ∧
  ion1174.addedProtonCount = 2 ∧
  ion1174.positiveCharge = 2 ∧
  ion1174.formula = ion1174Formula ∧
  integerMass ion1174.formula = 2348 ∧
  AccountsForObservedPeak ion1174 1174

/-- The neutral one-C₄₈/three-E assembly has nominal integer mass 2346. -/
theorem threeMacrocycleCatenane_neutralMass :
    integerMass (assembledFormula 1 3 0) = 2346 := by
  norm_num [integerMass, assembledFormula, MolecularFormula.add,
    MolecularFormula.scale, integerAtomicMasses, cyclo48Formula,
    macrocycleEFormula, protonFormula]

/-- The neutral one-C₄₈/two-E assembly has nominal integer mass 1756. -/
theorem twoMacrocycleCatenane_neutralMass :
    integerMass (assembledFormula 1 2 0) = 1756 := by
  norm_num [integerMass, assembledFormula, MolecularFormula.add,
    MolecularFormula.scale, integerAtomicMasses, cyclo48Formula,
    macrocycleEFormula, protonFormula]

/-- Once the one-C₄₈ and `3+` protonation/charge case is selected, the 783
mass equation characterizes the number of intact E macrocycles. -/
theorem macrocycleCount_of_mz783
    (eCount : ℕ)
    (hMass : integerMass (assembledFormula 1 eCount 3) = 783 * 3) :
    eCount = 3 := by
  norm_num [integerMass, assembledFormula, MolecularFormula.add,
    MolecularFormula.scale, integerAtomicMasses, cyclo48Formula,
    macrocycleEFormula, protonFormula] at hMass
  omega

/-- Once the one-C₄₈ and `2+` protonation/charge case is selected, the 879
mass equation characterizes the number of intact E macrocycles. -/
theorem macrocycleCount_of_mz879
    (eCount : ℕ)
    (hMass : integerMass (assembledFormula 1 eCount 2) = 879 * 2) :
    eCount = 2 := by
  norm_num [integerMass, assembledFormula, MolecularFormula.add,
    MolecularFormula.scale, integerAtomicMasses, cyclo48Formula,
    macrocycleEFormula, protonFormula] at hMass
  omega

/-- The 1174 mass equation independently recovers three intact E
macrocycles in the one-C₄₈, `2+` case. -/
theorem macrocycleCount_of_mz1174
    (eCount : ℕ)
    (hMass : integerMass (assembledFormula 1 eCount 2) = 1174 * 2) :
    eCount = 3 := by
  norm_num [integerMass, assembledFormula, MolecularFormula.add,
    MolecularFormula.scale, integerAtomicMasses, cyclo48Formula,
    macrocycleEFormula, protonFormula] at hMass
  omega

/-- Requested-output carrier for `ion_783`. -/
theorem ion783_identity : Ion783Identity := by
  norm_num [Ion783Identity, ion783, ion783Formula, protonatedAssembly,
    assembledFormula, MolecularFormula.add, MolecularFormula.scale,
    cyclo48Formula, macrocycleEFormula, protonFormula, integerMass,
    integerAtomicMasses, AccountsForObservedPeak, observedPeaks, HasMz]

/-- Requested-output carrier for `ion_879`. -/
theorem ion879_identity : Ion879Identity := by
  norm_num [Ion879Identity, ion879, ion879Formula, protonatedAssembly,
    assembledFormula, MolecularFormula.add, MolecularFormula.scale,
    cyclo48Formula, macrocycleEFormula, protonFormula, integerMass,
    integerAtomicMasses, AccountsForObservedPeak, observedPeaks, HasMz]

/-- Requested-output carrier for `ion_1174`. -/
theorem ion1174_identity : Ion1174Identity := by
  norm_num [Ion1174Identity, ion1174, ion1174Formula, protonatedAssembly,
    assembledFormula, MolecularFormula.add, MolecularFormula.scale,
    cyclo48Formula, macrocycleEFormula, protonFormula, integerMass,
    integerAtomicMasses, AccountsForObservedPeak, observedPeaks, HasMz]

/-- The 783 and 1174 candidates have the same intact catenane core; only their
protonation and positive charge states differ. -/
def SameNeutralAssemblyCore (x y : IntactAssemblyIon) : Prop :=
  x.cyclo48Count = y.cyclo48Count ∧
  x.macrocycleECount = y.macrocycleECount ∧
  assembledFormula x.cyclo48Count x.macrocycleECount 0 =
    assembledFormula y.cyclo48Count y.macrocycleECount 0

theorem ion783_ion1174_sameNeutralAssembly :
    SameNeutralAssemblyCore ion783 ion1174 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Aggregate raw symbolic solve contract.  Each conjunct retains component,
formula, charge, mass, observed-peak, and no-fragmentation information. -/
def RawResult : Prop :=
  Ion783Identity ∧ Ion879Identity ∧ Ion1174Identity

/-- Exact-symbolic reporting does not round or otherwise weaken any identity. -/
def ReportedResult : Prop :=
  Ion783Identity ∧ Ion879Identity ∧ Ion1174Identity

theorem raw_result : RawResult := by
  exact ⟨ion783_identity, ion879_identity, ion1174_identity⟩

theorem reported_result : ReportedResult := by
  exact ⟨ion783_identity, ion879_identity, ion1174_identity⟩

end IChO2026Problems.ProblemIcho2026T6A4
