import Mathlib
import CRNT.Basic.Reaction

/-!
# IChO 2026, theory problem 8.1

The problem asks for the reduction half-equation taking carbon dioxide to
carbon monoxide in acidic medium.  The concrete displayed equation is kept
separate from its specification.  Its coefficients are checked against atom,
charge, electron-transfer, and canonical no-cancellation ledgers, and a
uniqueness statement says that these source-derived constraints determine the
candidate.
-/

namespace IChO2026Problems.T8A1

open scoped BigOperators

/-- Atoms whose inventories can change among the species used to balance the
requested acidic half-equation. -/
inductive Atom
  | hydrogen
  | carbon
  | oxygen
  deriving DecidableEq, Fintype

/-- The complete species domain used for this half-equation: the two species
named by the problem and the conventional acidic-medium balancing species. -/
inductive Species
  | carbonDioxide
  | proton
  | electron
  | carbonMonoxide
  | water
  deriving DecidableEq, Fintype

/-- A molecular formula over the three atoms relevant to this question. -/
structure Formula where
  hydrogen : ℕ
  carbon : ℕ
  oxygen : ℕ
  deriving DecidableEq

namespace Formula

/-- Number of atoms of the selected element in a formula. -/
def count (f : Formula) : Atom → ℕ
  | .hydrogen => f.hydrogen
  | .carbon => f.carbon
  | .oxygen => f.oxygen

end Formula

/-- Formula data for every member of the source-derived species domain. -/
def formula : Species → Formula
  | .carbonDioxide => ⟨0, 1, 2⟩
  | .proton => ⟨1, 0, 0⟩
  | .electron => ⟨0, 0, 0⟩
  | .carbonMonoxide => ⟨0, 1, 1⟩
  | .water => ⟨2, 0, 1⟩

/-- Net electric charge of each species, in elementary-charge units. -/
def charge : Species → ℤ
  | .carbonDioxide => 0
  | .proton => 1
  | .electron => -1
  | .carbonMonoxide => 0
  | .water => 0

/-- Permitted provenance tags for the finite species-domain construction. -/
inductive Provenance
  | problemText
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq

/-- Provenance split for the named transformation species and the
acidic-half-reaction balancing species. -/
structure DomainProvenance where
  transformationSpecies : Provenance
  balancingSpecies : Provenance
  deriving DecidableEq

/-- `CO₂` and `CO` come from the problem text; `H⁺`, `e⁻`, and `H₂O` come from
the standard acidic-medium half-reaction balancing convention. -/
def halfEquationDomainProvenance : DomainProvenance :=
  { transformationSpecies := .problemText
    balancingSpecies := .trustedGeneralLaw }

/-- Total inventory of an atom in one side of a reaction. -/
def atomInventory (c : CRNT.Complex Species) (a : Atom) : ℕ :=
  ∑ s : Species, c s * (formula s).count a

/-- Total charge in one side of a reaction, in elementary-charge units. -/
def chargeInventory (c : CRNT.Complex Species) : ℤ :=
  ∑ s : Species, (c s : ℤ) * charge s

/-- Every relevant atomic inventory is conserved. -/
def AtomBalanced (r : CRNT.Reaction Species) : Prop :=
  ∀ a : Atom, atomInventory r.source a = atomInventory r.target a

/-- Total electric charge is conserved. -/
def ChargeBalanced (r : CRNT.Reaction Species) : Prop :=
  chargeInventory r.source = chargeInventory r.target

/-- A canonical half-equation has no unchanged species written on both sides.
This removes arbitrary common summands without imposing any coefficient bound. -/
def NoSpeciesCancellation (r : CRNT.Reaction Species) : Prop :=
  ∀ s : Species, r.source s = 0 ∨ r.target s = 0

/-- The source-stated direction and unit normalization: one carbon dioxide is
consumed to form one carbon monoxide. -/
def RepresentsUnitCO2ToCO (r : CRNT.Reaction Species) : Prop :=
  r.source .carbonDioxide = 1 ∧ r.target .carbonMonoxide = 1

/-- Net number of electrons consumed by a half-equation. -/
def netElectronsConsumed (r : CRNT.Reaction Species) : ℤ :=
  (r.source .electron : ℤ) - (r.target .electron : ℤ)

/-- The usual oxidation number of oxygen in both oxides occurring here. -/
def usualOxygenOxidationNumber : ℤ := -2

/-- In a neutral carbon oxide, charge balance determines carbon's oxidation
number from the number of ordinary oxide oxygens. -/
def carbonOxidationNumberInNeutralOxide (oxygenAtoms : ℕ) : ℤ :=
  -((oxygenAtoms : ℤ) * usualOxygenOxidationNumber)

/-- Carbon oxidation number in the source species `CO₂`. -/
def carbonOxidationNumberCO2 : ℤ :=
  carbonOxidationNumberInNeutralOxide (formula .carbonDioxide).oxygen

/-- Carbon oxidation number in the product species `CO`. -/
def carbonOxidationNumberCO : ℤ :=
  carbonOxidationNumberInNeutralOxide (formula .carbonMonoxide).oxygen

/-- Electron-transfer ledger for the unit carbon reduction. -/
def CarbonReductionElectronBalanced (r : CRNT.Reaction Species) : Prop :=
  netElectronsConsumed r = carbonOxidationNumberCO2 - carbonOxidationNumberCO

/-- Full source-to-Lean specification of a canonical acidic-medium reduction
half-equation from one `CO₂` to one `CO`. -/
def IsAcidicCO2ToCOHalfEquation (r : CRNT.Reaction Species) : Prop :=
  RepresentsUnitCO2ToCO r ∧
  AtomBalanced r ∧
  ChargeBalanced r ∧
  NoSpeciesCancellation r ∧
  0 < netElectronsConsumed r ∧
  CarbonReductionElectronBalanced r

/-- Reactant complex of the submitted equation. -/
def submittedReactants : CRNT.Complex Species
  | .carbonDioxide => 1
  | .proton => 2
  | .electron => 2
  | .carbonMonoxide => 0
  | .water => 0

/-- Product complex of the submitted equation. -/
def submittedProducts : CRNT.Complex Species
  | .carbonDioxide => 0
  | .proton => 0
  | .electron => 0
  | .carbonMonoxide => 1
  | .water => 1

/-- Candidate output corresponding to
`CO₂ + 2 H⁺ + 2 e⁻ → CO + H₂O`. -/
def submittedHalfEquation : CRNT.Reaction Species where
  source := submittedReactants
  target := submittedProducts

/-- The oxidation-number calculation gives a two-electron carbon reduction. -/
theorem carbonOxidationStateDrop :
    carbonOxidationNumberCO2 = 4 ∧
    carbonOxidationNumberCO = 2 ∧
    carbonOxidationNumberCO2 - carbonOxidationNumberCO = 2 := by
  norm_num [carbonOxidationNumberCO2, carbonOxidationNumberCO,
    carbonOxidationNumberInNeutralOxide, usualOxygenOxidationNumber, formula]

/-- The submitted equation satisfies every atom, charge, direction,
canonicality, and electron-transfer obligation. -/
theorem submittedHalfEquation_meets_specification :
    IsAcidicCO2ToCOHalfEquation submittedHalfEquation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [RepresentsUnitCO2ToCO, submittedHalfEquation, submittedReactants,
      submittedProducts]
  · intro a
    cases a <;> native_decide
  · unfold ChargeBalanced
    native_decide
  · intro s
    cases s <;>
      simp [submittedHalfEquation, submittedReactants, submittedProducts]
  · norm_num [netElectronsConsumed, submittedHalfEquation, submittedReactants,
      submittedProducts]
  · norm_num [CarbonReductionElectronBalanced, netElectronsConsumed,
      submittedHalfEquation, submittedReactants, submittedProducts,
      carbonOxidationNumberCO2, carbonOxidationNumberCO,
      carbonOxidationNumberInNeutralOxide, usualOxygenOxidationNumber, formula]

/-- The constraints determine the submitted coefficients without a finite
coefficient search bound. -/
theorem acidicCO2ToCOHalfEquation_unique
    (r : CRNT.Reaction Species)
    (hr : IsAcidicCO2ToCOHalfEquation r) :
    r = submittedHalfEquation := by
  rcases hr with
    ⟨⟨hsourceCO2, htargetCO⟩, hatom, _, hcanonical, _, helectron⟩
  have species_univ : (Finset.univ : Finset Species) =
      { .carbonDioxide, .proton, .electron, .carbonMonoxide, .water } := by
    native_decide
  have hhydrogen := hatom .hydrogen
  have hoxygen := hatom .oxygen
  simp [atomInventory, species_univ, formula, Formula.count] at hhydrogen hoxygen
  norm_num [CarbonReductionElectronBalanced, netElectronsConsumed,
    carbonOxidationNumberCO2, carbonOxidationNumberCO,
    carbonOxidationNumberInNeutralOxide, usualOxygenOxidationNumber,
    formula] at helectron

  have htargetCO2 : r.target .carbonDioxide = 0 := by
    rcases hcanonical .carbonDioxide with hsource | htarget
    · omega
    · exact htarget
  have hsourceCO : r.source .carbonMonoxide = 0 := by
    rcases hcanonical .carbonMonoxide with hsource | htarget
    · exact hsource
    · omega

  have hsourceWater : r.source .water = 0 := by
    rcases hcanonical .water with hsource | htarget
    · exact hsource
    · omega
  have htargetWater : r.target .water = 1 := by
    omega

  have htargetProton : r.target .proton = 0 := by
    rcases hcanonical .proton with hsource | htarget
    · omega
    · exact htarget
  have hsourceProton : r.source .proton = 2 := by
    omega

  have htargetElectron : r.target .electron = 0 := by
    rcases hcanonical .electron with hsource | htarget
    · omega
    · exact htarget
  have hsourceElectron : r.source .electron = 2 := by
    omega

  have hsource : r.source = submittedReactants := by
    funext s
    cases s <;>
      simp [submittedReactants, hsourceCO2,
        hsourceProton, hsourceElectron, hsourceCO, hsourceWater]
  have htarget : r.target = submittedProducts := by
    funext s
    cases s <;>
      simp [submittedProducts, htargetCO2,
        htargetProton, htargetElectron, htargetCO, htargetWater]
  cases r with
  | mk source target =>
      change source = submittedReactants at hsource
      change target = submittedProducts at htarget
      subst source
      subst target
      rfl

/-- Exact symbolic result contract for the requested output. -/
def HalfEquationResult : Prop :=
  IsAcidicCO2ToCOHalfEquation submittedHalfEquation ∧
  ∀ r : CRNT.Reaction Species,
    IsAcidicCO2ToCOHalfEquation r → r = submittedHalfEquation

/-- Requested half-equation output, with existence/specification and uniqueness
kept distinct from the concrete candidate definition. -/
theorem halfEquation : HalfEquationResult := by
  exact ⟨submittedHalfEquation_meets_specification,
    fun r hr => acidicCO2ToCOHalfEquation_unique r hr⟩

end IChO2026Problems.T8A1
