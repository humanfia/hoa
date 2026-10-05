import Mathlib

/-!
# IChO 2026 T6-A4: positive-mode mass spectrum of catenated cyclo[48]carbon

The source depicts cyclo[48]carbon (`C₄₈`) and macrocycle `E`, whose printed
formula is `C₄₀H₃₄N₂O₃`.  Catenation is an interlocking of intact rings, so
the atom ledger for a candidate containing `n` copies of `E` is the component
sum `C₄₈ + n E`; no covalent condensation loss is inserted.  Positive ions are
then represented by explicit added protons and an explicit charge.

The three requested outputs below are concrete compatible candidates.  Their
specifications check the intact component ledger, charged molecular formula,
integer nominal mass, and exact mass-to-charge equation.  No premise assumes
one of the requested identities, and no global uniqueness claim is made: the
problem asks to *suggest* the identities rather than enumerate all possible
positive-mode adduct chemistry.
-/

namespace IChO2026Problems
namespace ProblemIChO2026T6A4

/-- Atom counts for the four elements occurring in the printed macrocycle
formula and in cyclo[48]carbon. -/
@[ext]
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

namespace MolecularFormula

/-- Component-wise formula addition. -/
def add (a b : MolecularFormula) : MolecularFormula where
  carbon := a.carbon + b.carbon
  hydrogen := a.hydrogen + b.hydrogen
  nitrogen := a.nitrogen + b.nitrogen
  oxygen := a.oxygen + b.oxygen

/-- `n` intact copies of one molecular component. -/
def scale (n : ℕ) (a : MolecularFormula) : MolecularFormula where
  carbon := n * a.carbon
  hydrogen := n * a.hydrogen
  nitrogen := n * a.nitrogen
  oxygen := n * a.oxygen

/-- The formula contribution of one added proton at the contest's integer-mass
resolution.  Electron masses are outside that explicitly requested model. -/
def proton : MolecularFormula where
  carbon := 0
  hydrogen := 1
  nitrogen := 0
  oxygen := 0

end MolecularFormula

/-- Formula read from the structure labelled `E` on source image T6 page 2. -/
def macrocycleE : MolecularFormula where
  carbon := 40
  hydrogen := 34
  nitrogen := 2
  oxygen := 3

/-- Formula of the all-carbon ring identified in the source as cyclo[48]carbon. -/
def cyclo48Carbon : MolecularFormula where
  carbon := 48
  hydrogen := 0
  nitrogen := 0
  oxygen := 0

/-- The intact, unfragmented atom ledger for one cyclo[48]carbon ring catenated
with `n` copies of macrocycle `E`. -/
def catenaneNeutralFormula (n : ℕ) : MolecularFormula :=
  MolecularFormula.add cyclo48Carbon (MolecularFormula.scale n macrocycleE)

/-- The contest's integer atomic-mass convention: C = 12, H = 1, N = 14,
O = 16. -/
def integerNominalMass (f : MolecularFormula) : ℕ :=
  12 * f.carbon + f.hydrogen + 14 * f.nitrogen + 16 * f.oxygen

/-- A positive-mode ion, keeping the uncharged whole assembly, proton adducts,
and observed charge as distinct data. -/
structure PositiveIon where
  neutralFormula : MolecularFormula
  addedProtons : ℕ
  charge : ℕ
  charge_pos : 0 < charge

/-- Molecular formula after including every proton adduct. -/
def PositiveIon.chargedFormula (ion : PositiveIon) : MolecularFormula :=
  MolecularFormula.add ion.neutralFormula
    (MolecularFormula.scale ion.addedProtons MolecularFormula.proton)

/-- Integer nominal mass of the complete ion. -/
def PositiveIon.nominalMass (ion : PositiveIon) : ℕ :=
  integerNominalMass ion.chargedFormula

/-- Exact integral `m/z` relation, written without truncating natural-number
division. -/
def HasMassToCharge (ion : PositiveIon) (peak : ℕ) : Prop :=
  ion.nominalMass = peak * ion.charge

/-- A whole protonated catenane candidate built from the two source-depicted
components.  Its construction is open in the number of macrocycles, proton
adducts, and positive charge; it is not an answer-shaped finite domain. -/
def catenaneIon (macrocycles protons charge : ℕ) (hcharge : 0 < charge) :
    PositiveIon where
  neutralFormula := catenaneNeutralFormula macrocycles
  addedProtons := protons
  charge := charge
  charge_pos := hcharge

/-- Transparent no-fragmentation/component-accounting specification for a
candidate ion. -/
def IsWholeCatenaneIon (ion : PositiveIon)
    (macrocycles protons charge : ℕ) : Prop :=
  ion.neutralFormula = catenaneNeutralFormula macrocycles ∧
  ion.addedProtons = protons ∧
  ion.charge = charge

/-- The `m/z = 591` calibration candidate obtained from intact `E` plus one
proton, included because the source says this peak is supplied as an example. -/
def example591Ion : PositiveIon where
  neutralFormula := macrocycleE
  addedProtons := 1
  charge := 1
  charge_pos := by decide

/-- The example candidate checks the printed formula and the adopted integer
mass convention before either is used for the requested ions. -/
def Example591Calibration : Prop :=
  example591Ion.chargedFormula =
      { carbon := 40, hydrogen := 35, nitrogen := 2, oxygen := 3 } ∧
  example591Ion.nominalMass = 591 ∧
  HasMassToCharge example591Ion 591

theorem example591_calibration : Example591Calibration := by
  unfold Example591Calibration HasMassToCharge
  decide

/-- Candidate carrier for the peak at `m/z = 783`: one C₄₈ ring interlocked
with three copies of `E`, triply protonated and triply charged. -/
def ion783Carrier : PositiveIon := catenaneIon 3 3 3 (by decide)

/-- Candidate carrier for the peak at `m/z = 879`: one C₄₈ ring interlocked
with two copies of `E`, doubly protonated and doubly charged. -/
def ion879Carrier : PositiveIon := catenaneIon 2 2 2 (by decide)

/-- Candidate carrier for the peak at `m/z = 1174`: one C₄₈ ring interlocked
with three copies of `E`, doubly protonated and doubly charged. -/
def ion1174Carrier : PositiveIon := catenaneIon 3 2 2 (by decide)

/-- Complete source-to-candidate derivation specification for `m/z = 783`.
The ion formula is C₁₆₈H₁₀₅N₆O₉³⁺ and its integer mass is 2349. -/
def Ion783Identity : Prop :=
  IsWholeCatenaneIon ion783Carrier 3 3 3 ∧
  ion783Carrier.neutralFormula =
      { carbon := 168, hydrogen := 102, nitrogen := 6, oxygen := 9 } ∧
  ion783Carrier.chargedFormula =
      { carbon := 168, hydrogen := 105, nitrogen := 6, oxygen := 9 } ∧
  ion783Carrier.nominalMass = 2349 ∧
  HasMassToCharge ion783Carrier 783

/-- Complete source-to-candidate derivation specification for `m/z = 879`.
The ion formula is C₁₂₈H₇₀N₄O₆²⁺ and its integer mass is 1758. -/
def Ion879Identity : Prop :=
  IsWholeCatenaneIon ion879Carrier 2 2 2 ∧
  ion879Carrier.neutralFormula =
      { carbon := 128, hydrogen := 68, nitrogen := 4, oxygen := 6 } ∧
  ion879Carrier.chargedFormula =
      { carbon := 128, hydrogen := 70, nitrogen := 4, oxygen := 6 } ∧
  ion879Carrier.nominalMass = 1758 ∧
  HasMassToCharge ion879Carrier 879

/-- Complete source-to-candidate derivation specification for `m/z = 1174`.
The ion formula is C₁₆₈H₁₀₄N₆O₉²⁺ and its integer mass is 2348. -/
def Ion1174Identity : Prop :=
  IsWholeCatenaneIon ion1174Carrier 3 2 2 ∧
  ion1174Carrier.neutralFormula =
      { carbon := 168, hydrogen := 102, nitrogen := 6, oxygen := 9 } ∧
  ion1174Carrier.chargedFormula =
      { carbon := 168, hydrogen := 104, nitrogen := 6, oxygen := 9 } ∧
  ion1174Carrier.nominalMass = 2348 ∧
  HasMassToCharge ion1174Carrier 1174

theorem ion_783_identity : Ion783Identity := by
  unfold Ion783Identity IsWholeCatenaneIon HasMassToCharge
  decide

theorem ion_879_identity : Ion879Identity := by
  unfold Ion879Identity IsWholeCatenaneIon HasMassToCharge
  decide

theorem ion_1174_identity : Ion1174Identity := by
  unfold Ion1174Identity IsWholeCatenaneIon HasMassToCharge
  decide

/-- Raw answer-blind result proposition.  Conjunct order follows the immutable
requested-output order: 783, 879, then 1174. -/
def RawResult : Prop :=
  Ion783Identity ∧ Ion879Identity ∧ Ion1174Identity

/-- Exact-symbolic reporting proposition.  Because every requested output is a
formula rather than a scalar measurement, reporting introduces no rounding or
tolerance and preserves the full raw identity specifications. -/
def ReportedResult : Prop :=
  Ion783Identity ∧ Ion879Identity ∧ Ion1174Identity

theorem raw_result : RawResult := by
  exact ⟨ion_783_identity, ion_879_identity, ion_1174_identity⟩

theorem reported_result : ReportedResult := by
  exact ⟨ion_783_identity, ion_879_identity, ion_1174_identity⟩

end ProblemIChO2026T6A4
end IChO2026Problems
