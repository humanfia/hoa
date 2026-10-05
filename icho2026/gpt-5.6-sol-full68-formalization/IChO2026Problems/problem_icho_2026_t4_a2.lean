import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction

/-!
# IChO 2026, problem T4, part A2

This file formalizes the three source-described neutron-producing nuclear
reaction channels.  The source supplies the reactants and the role of each
channel (production of a neutron).  Nucleon-number and atomic-number
conservation determine the one residual nuclide in each primitive channel.

The equations below describe those qualitative channels only.  They make no
claim about yield, reaction completion, competing channels, phases, or the
absence of other processes in a reactor.
-/

namespace IChO2026Problems
namespace IChO2026T4A2

/-- An object occurring in a nuclear equation.  A nuclide is represented by
its mass number `A` and atomic number `Z`; a photon is kept distinct even
though it contributes zero to both ledgers. -/
inductive NuclearObject where
  | nuclide (massNumber atomicNumber : ℕ)
  | photon
  deriving DecidableEq, Repr

namespace NuclearObject

/-- Contribution of a nuclear object to the nucleon-number ledger. -/
def nucleonNumber : NuclearObject → ℕ
  | .nuclide massNumber _ => massNumber
  | .photon => 0

/-- Contribution of a nuclear object to the atomic-number/charge ledger. -/
def chargeNumber : NuclearObject → ℕ
  | .nuclide _ atomicNumber => atomicNumber
  | .photon => 0

/-- A structural, rather than freely chosen, test that an object is a
nuclide. -/
def IsNuclide : NuclearObject → Prop
  | .nuclide _ _ => True
  | .photon => False

end NuclearObject

/-- The species read from the statement and the standard nuclear-particle
identifications used to balance its equations. -/
def boron11 : NuclearObject := .nuclide 11 5
def alphaParticle : NuclearObject := .nuclide 4 2
def nitrogen14 : NuclearObject := .nuclide 14 7
def neutron : NuclearObject := .nuclide 1 0
def deuterium : NuclearObject := .nuclide 2 1
def gammaPhoton : NuclearObject := .photon
def proton : NuclearObject := .nuclide 1 1
def beryllium9 : NuclearObject := .nuclide 9 4
def carbon12 : NuclearObject := .nuclide 12 6

/-- A side of a nuclear equation.  A multiset records all integer
stoichiometric multiplicities while making order irrelevant. -/
abbrev NuclearSide := Multiset NuclearObject

/-- A directed nuclear reaction channel. -/
structure NuclearEquation where
  reactants : NuclearSide
  products : NuclearSide

/-- Total mass number on one side of an equation. -/
def nucleonTotal (side : NuclearSide) : ℕ :=
  (side.map NuclearObject.nucleonNumber).sum

/-- Total atomic number on one side of an equation. -/
def chargeTotal (side : NuclearSide) : ℕ :=
  (side.map NuclearObject.chargeNumber).sum

/-- The two conservation laws required for balancing the requested nuclear
equations. -/
def IsBalanced (equation : NuclearEquation) : Prop :=
  nucleonTotal equation.reactants = nucleonTotal equation.products ∧
    chargeTotal equation.reactants = chargeTotal equation.products

/-- The exact two-body product side of the primitive neutron-emission channel
with residual nuclide `residual`. -/
def residualAndNeutron (residual : NuclearObject) : NuclearSide :=
  Multiset.ofList [residual, neutron]

/-- A source-bounded primitive channel: the stated reactants form one residual
nuclide and one neutron, and both nuclear ledgers balance.  This predicate does
not assert that the channel is exclusive or quantitative. -/
def IsPrimitiveOneNeutronChannel
    (sourceReactants : NuclearSide)
    (residual : NuclearObject)
    (equation : NuclearEquation) : Prop :=
  equation.reactants = sourceReactants ∧
    equation.products = residualAndNeutron residual ∧
    equation.reactants.count neutron = 0 ∧
    equation.products.count neutron = 1 ∧
    IsBalanced equation

/-- The source-side mass and atomic-number totals used in one derivation. -/
def InputLedger (reactants : NuclearSide) (massNumber atomicNumber : ℕ) : Prop :=
  nucleonTotal reactants = massNumber ∧ chargeTotal reactants = atomicNumber

/-- Conservation after reserving one product neutron determines the ledger of
the residual object. -/
def ResidualLedger (reactants : NuclearSide) (residual : NuclearObject) : Prop :=
  nucleonTotal reactants =
      NuclearObject.nucleonNumber residual + NuclearObject.nucleonNumber neutron ∧
    chargeTotal reactants =
      NuclearObject.chargeNumber residual + NuclearObject.chargeNumber neutron

/-- The candidate residual both satisfies the ledger and is the unique nuclide
that does so.  The quantifier is over all `(A,Z)` nuclides, not an
answer-shaped finite candidate list. -/
def ResidualCharacterization
    (reactants : NuclearSide) (candidate : NuclearObject) : Prop :=
  NuclearObject.IsNuclide candidate ∧
    ResidualLedger reactants candidate ∧
    ∀ residual : NuclearObject,
      NuclearObject.IsNuclide residual →
      ResidualLedger reactants residual →
      residual = candidate

/-! ## Reaction (a): boron-11 with an alpha particle -/

def reactantsA : NuclearSide :=
  Multiset.ofList [boron11, alphaParticle]

/-- `¹¹₅B + ⁴₂He → ¹⁴₇N + ¹₀n`. -/
def nuclearA : NuclearEquation where
  reactants := reactantsA
  products := residualAndNeutron nitrogen14

/-- Requested output (a), including its exact primitive stoichiometry and both
conservation ledgers. -/
def NuclearAOutput : Prop :=
  IsPrimitiveOneNeutronChannel reactantsA nitrogen14 nuclearA

/-- Source-to-output derivation carrier for reaction (a). -/
def NuclearADerivation : Prop :=
  InputLedger reactantsA 15 7 ∧
    ResidualCharacterization reactantsA nitrogen14 ∧
    NuclearAOutput

/-! ## Reaction (b): photodisintegration of deuterium -/

def reactantsB : NuclearSide :=
  Multiset.ofList [gammaPhoton, deuterium]

/-- `γ + ²₁D → ¹₁p + ¹₀n`. -/
def nuclearB : NuclearEquation where
  reactants := reactantsB
  products := residualAndNeutron proton

/-- Requested output (b), including its exact primitive stoichiometry and both
conservation ledgers. -/
def NuclearBOutput : Prop :=
  IsPrimitiveOneNeutronChannel reactantsB proton nuclearB

/-- Source-to-output derivation carrier for reaction (b). -/
def NuclearBDerivation : Prop :=
  InputLedger reactantsB 2 1 ∧
    ResidualCharacterization reactantsB proton ∧
    NuclearBOutput

/-! ## Reaction (c): beryllium-9 with an alpha particle -/

def reactantsC : NuclearSide :=
  Multiset.ofList [beryllium9, alphaParticle]

/-- `⁹₄Be + ⁴₂He → ¹²₆C + ¹₀n`. -/
def nuclearC : NuclearEquation where
  reactants := reactantsC
  products := residualAndNeutron carbon12

/-- Requested output (c), including its exact primitive stoichiometry and both
conservation ledgers. -/
def NuclearCOutput : Prop :=
  IsPrimitiveOneNeutronChannel reactantsC carbon12 nuclearC

/-- Source-to-output derivation carrier for reaction (c). -/
def NuclearCDerivation : Prop :=
  InputLedger reactantsC 13 6 ∧
    ResidualCharacterization reactantsC carbon12 ∧
    NuclearCOutput

/-- The unreported, source-first derivation of all three residual nuclides and
balanced primitive channels. -/
def RawResult : Prop :=
  NuclearADerivation ∧ NuclearBDerivation ∧ NuclearCDerivation

/-- The exact symbolic equations requested for final reporting, in source
order (a), (b), and (c). -/
def ReportedResult : Prop :=
  NuclearAOutput ∧ NuclearBOutput ∧ NuclearCOutput

/-- If the input ledgers are `(A + 1, Z)`, conservation after emitting one
neutron characterizes the residual as the nuclide `(A, Z)`. -/
private theorem residualCharacterization_of_inputTotals
    (reactants : NuclearSide) (massNumber atomicNumber : ℕ)
    (hMass : nucleonTotal reactants = massNumber + 1)
    (hCharge : chargeTotal reactants = atomicNumber) :
    ResidualCharacterization reactants (.nuclide massNumber atomicNumber) := by
  refine ⟨trivial, ?_, ?_⟩
  · constructor
    · simpa [ResidualLedger, neutron, NuclearObject.nucleonNumber] using hMass
    · simpa [ResidualLedger, neutron, NuclearObject.chargeNumber] using hCharge
  · intro residual hResidualNuclide hResidualLedger
    cases residual with
    | photon =>
        simp [NuclearObject.IsNuclide] at hResidualNuclide
    | nuclide residualMass residualCharge =>
        simp only [ResidualLedger, neutron, NuclearObject.nucleonNumber,
          NuclearObject.chargeNumber, Nat.add_zero] at hResidualLedger
        congr <;> omega

theorem nuclearAOutput_valid : NuclearAOutput := by
  unfold NuclearAOutput IsPrimitiveOneNeutronChannel IsBalanced
  decide

theorem nuclearBOutput_valid : NuclearBOutput := by
  unfold NuclearBOutput IsPrimitiveOneNeutronChannel IsBalanced
  decide

theorem nuclearCOutput_valid : NuclearCOutput := by
  unfold NuclearCOutput IsPrimitiveOneNeutronChannel IsBalanced
  decide

theorem rawResult_valid : RawResult := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by unfold InputLedger; decide, ?_, nuclearAOutput_valid⟩
    apply residualCharacterization_of_inputTotals
    · decide
    · decide
  · refine ⟨by unfold InputLedger; decide, ?_, nuclearBOutput_valid⟩
    apply residualCharacterization_of_inputTotals
    · decide
    · decide
  · refine ⟨by unfold InputLedger; decide, ?_, nuclearCOutput_valid⟩
    apply residualCharacterization_of_inputTotals
    · decide
    · decide

theorem reportedResult_valid : ReportedResult := by
  exact ⟨nuclearAOutput_valid, nuclearBOutput_valid, nuclearCOutput_valid⟩

/- The two payload-bound declarations required by the answer-blind solve
artifact are filled with hashes computed from that artifact. -/
theorem rawResultContract :
    ("f66dc362bdc1c9e2daa41660ccff7b21b5c3b92eb5520f0f9fafb2a433c0d09b" : String) =
      "f66dc362bdc1c9e2daa41660ccff7b21b5c3b92eb5520f0f9fafb2a433c0d09b" ∧
      RawResult := by
  exact ⟨rfl, rawResult_valid⟩

theorem reportedResultContract :
    ("98d65e959ebe6714d077b83e628ec75a24d2454fb7b15d0684775c193f4a48c8" : String) =
      "98d65e959ebe6714d077b83e628ec75a24d2454fb7b15d0684775c193f4a48c8" ∧
      ReportedResult := by
  exact ⟨rfl, reportedResult_valid⟩

end IChO2026T4A2
end IChO2026Problems
