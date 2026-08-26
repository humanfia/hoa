import ChemistryLib.Foundations.Concentration
import ChemistryLib.ReactionNetwork.Stoichiometry

/-!
# Coarse coupling stoichiometry adapter

This module instantiates the released ChemistryLib amount, quantity,
concentration, complex, reaction-network, and stoichiometry APIs for the coarse
bookkeeping reaction

`growing chain + incoming residue → extended chain`.

The three species deliberately omit coupling reagents and byproducts.  The
conservation result below tracks only residue count with weights `n`, `1`, and
`n + 1`; it is neither a molecular-mass conservation claim nor a complete
amide-coupling mechanism.

Source references:

* Sanitized sequence contract (`afps2017.sequence.contract:question`).
* Mijalis et al., Nature Chemical Biology (2017),
  DOI `10.1038/nchembio.2318` (`afps2017.main:DOI-10.1038/nchembio.2318`).
* Public Supplementary Information
  (`afps2017.supplement:sha256-f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e`).
-/

namespace AFPS2017.Sequence

/-- Species retained by the coarse coupling bookkeeping model. -/
inductive CouplingSpecies : Type where
  | growingChain
  | incomingResidue
  | extendedChain

/-- The reactant and product complexes of the coarse coupling reaction. -/
inductive CouplingComplexId : Type where
  | reactants
  | product

/-- The single reaction represented by the coarse coupling model. -/
inductive CouplingReactionId : Type where
  | amideFormation

private instance : DecidableEq CouplingSpecies
  | .growingChain, .growingChain => isTrue rfl
  | .growingChain, .incomingResidue => isFalse (by simp)
  | .growingChain, .extendedChain => isFalse (by simp)
  | .incomingResidue, .growingChain => isFalse (by simp)
  | .incomingResidue, .incomingResidue => isTrue rfl
  | .incomingResidue, .extendedChain => isFalse (by simp)
  | .extendedChain, .growingChain => isFalse (by simp)
  | .extendedChain, .incomingResidue => isFalse (by simp)
  | .extendedChain, .extendedChain => isTrue rfl

private instance : Fintype CouplingSpecies where
  elems := {.growingChain, .incomingResidue, .extendedChain}
  complete := by
    intro species
    cases species <;> simp

/-- Species-indexed coupling amounts, using ChemistryLib's amount domain. -/
abbrev CouplingAmounts : Type :=
  CouplingSpecies → ChemistryLib.Foundations.Amount

/-- Species-indexed coupling concentrations, using ChemistryLib's profile type. -/
abbrev CouplingConcentrations : Type :=
  ChemistryLib.Foundations.ConcentrationProfile CouplingSpecies

/-- Forget an amount's nonnegativity witness while retaining its dimension. -/
def couplingAmountQuantity (amount : ChemistryLib.Foundations.Amount) :
    ChemistryLib.Units.Quantity
      ChemistryLib.Units.ChemicalDimension.amountOfSubstance :=
  amount.1

/-- The two ChemistryLib complexes of the coarse coupling network. -/
noncomputable def couplingComplex :
    CouplingComplexId → ChemistryLib.Complex CouplingSpecies
  | .reactants =>
      Finsupp.single .growingChain 1 + Finsupp.single .incomingResidue 1
  | .product => Finsupp.single .extendedChain 1

/-- Form the pointwise amount-concentration profile at a common volume. -/
noncomputable def couplingConcentrations
    (amounts : CouplingSpecies → ChemistryLib.Foundations.Amount)
    (volume : ChemistryLib.Foundations.Volume) :
    ChemistryLib.Foundations.ConcentrationProfile CouplingSpecies :=
  ChemistryLib.Foundations.concentrationProfile amounts volume

/-- Coupling concentrations use ChemistryLib's amount-over-volume operation. -/
theorem couplingConcentrations_apply
    (amounts : CouplingSpecies → ChemistryLib.Foundations.Amount)
    (volume : ChemistryLib.Foundations.Volume)
    (species : CouplingSpecies) :
    couplingConcentrations amounts volume species =
      ChemistryLib.Foundations.amountConcentration (amounts species) volume :=
  rfl

/-- The coarse coupling reaction as a released ChemistryLib reaction network. -/
noncomputable def couplingNetwork :
    ChemistryLib.ReactionNetwork
      CouplingSpecies CouplingComplexId CouplingReactionId where
  complex := couplingComplex
  source
    | .amideFormation => .reactants
  target
    | .amideFormation => .product

/-- The coarse reaction produces one extended-chain bookkeeping unit. -/
theorem coupling_reactionVector_extendedChain :
    couplingNetwork.reactionVector .amideFormation .extendedChain = (1 : ℝ) := by
  simp [ChemistryLib.ReactionNetwork.reactionVector,
    ChemistryLib.ReactionNetwork.product, ChemistryLib.ReactionNetwork.reactant,
    couplingNetwork, couplingComplex]

/-- The coarse reaction consumes one growing-chain bookkeeping unit. -/
theorem coupling_reactionVector_growingChain :
    couplingNetwork.reactionVector .amideFormation .growingChain = (-1 : ℝ) := by
  simp [ChemistryLib.ReactionNetwork.reactionVector,
    ChemistryLib.ReactionNetwork.product, ChemistryLib.ReactionNetwork.reactant,
    couplingNetwork, couplingComplex]

/-- The coarse reaction consumes one incoming-residue bookkeeping unit. -/
theorem coupling_reactionVector_incomingResidue :
    couplingNetwork.reactionVector .amideFormation .incomingResidue = (-1 : ℝ) := by
  simp [ChemistryLib.ReactionNetwork.reactionVector,
    ChemistryLib.ReactionNetwork.product, ChemistryLib.ReactionNetwork.reactant,
    couplingNetwork, couplingComplex]

/-- Residue-count weights for an `n`-residue chain, one incoming residue, and
the resulting `(n + 1)`-residue chain. -/
def residueCountWeight : Nat → CouplingSpecies → ℝ
  | n, .growingChain => n
  | _, .incomingResidue => 1
  | n, .extendedChain => n + 1

/-- Coarse residue count is conserved by the bookkeeping reaction. -/
theorem coupling_residueCount_conservation (n : Nat) :
    couplingNetwork.IsConservationLaw (residueCountWeight n) := by
  intro reaction
  cases reaction
  rw [show (Finset.univ : Finset CouplingSpecies) =
      {.growingChain, .incomingResidue, .extendedChain} by
    ext species
    cases species <;> simp]
  simp [ChemistryLib.ReactionNetwork.reactionVector,
    ChemistryLib.ReactionNetwork.product, ChemistryLib.ReactionNetwork.reactant,
    couplingNetwork, couplingComplex, residueCountWeight]

/-- A stoichiometric-matrix entry is its reaction-vector coordinate. -/
theorem coupling_stoichiometricMatrix_apply (species : CouplingSpecies) :
    couplingNetwork.stoichiometricMatrix species .amideFormation =
      couplingNetwork.reactionVector .amideFormation species :=
  rfl

end AFPS2017.Sequence
