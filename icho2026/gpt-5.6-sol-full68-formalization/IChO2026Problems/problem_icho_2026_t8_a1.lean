import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T8-A1: acidic reduction of carbon dioxide to carbon monoxide

The source asks for the reduction half-equation for `CO₂ → CO` in acidic
medium.  The reaction below is not assumed as a hypothesis.  Instead, the
source fixes the directed `CO₂`/`CO` skeleton and the conventional primitive
normalization, while the standard acidic half-equation species (`H⁺`, `e⁻`,
and `H₂O`) form the rest of the finite species domain.  Atom and formal-charge
balance then determine their coefficients.

The atmospheric gas phase and catalyst label belong to the shared context but
do not alter the balancing calculation.  They are nevertheless retained in
`problemContext`.
-/

namespace IChO2026Problems.ProblemIChO2026T8A1

open scoped BigOperators

/-- Elements occurring in the source formulas and in the acidic balancing
species. -/
inductive Element
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Fintype

/-- The complete finite species domain used to balance this half-equation.
`carbonDioxide` and `carbonMonoxide` come from the problem text; proton,
electron, and water are the standard balancing species for acidic medium. -/
inductive Species
  | carbonDioxide
  | proton
  | electron
  | carbonMonoxide
  | water
  deriving DecidableEq, Fintype

/-- Source categories allowed by the answer-blind candidate-domain policy. -/
inductive FactProvenance
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq

/-- Provenance of every member of the finite balancing-species domain. -/
def speciesDomainProvenance : Species → FactProvenance
  | .carbonDioxide => .problemText
  | .carbonMonoxide => .problemText
  | .proton => .trustedGeneralLaw
  | .electron => .trustedGeneralLaw
  | .water => .trustedGeneralLaw

/-- Physical phases mentioned explicitly in the shared source context. -/
inductive Phase
  | solid
  | liquid
  | gas
  | aqueous
  deriving DecidableEq

/-- Media relevant to the standard redox half-equation convention. -/
inductive ReactionMedium
  | acidic
  | neutral
  | basic
  deriving DecidableEq

/-- Activation modes needed to retain the shared statement's description of
the conversion as photocatalytic without representing it by a free Boolean. -/
inductive ReductionMode
  | photocatalytic
  | thermal
  | electrochemical
  deriving DecidableEq

/-- Source-side context for the requested half-equation.  The phase field says
that the environmental feedstock discussed in the preamble is gaseous; it does
not add an unstated phase label to every species in the written equation. -/
structure ProblemContext where
  atmosphericSpecies : Species
  atmosphericPhase : Phase
  reductionReactant : Species
  reductionProduct : Species
  medium : ReactionMedium
  mode : ReductionMode
  catalystLabel : ℕ
  deriving DecidableEq

/-- The data printed in the shared context and current question. -/
def problemContext : ProblemContext where
  atmosphericSpecies := .carbonDioxide
  atmosphericPhase := .gas
  reductionReactant := .carbonDioxide
  reductionProduct := .carbonMonoxide
  medium := .acidic
  mode := .photocatalytic
  catalystLabel := 1

/-- A proposition exposing, independently of the candidate equation, all
context fields used from the source. -/
def MatchesSourceContext (ctx : ProblemContext) : Prop :=
  ctx.atmosphericSpecies = .carbonDioxide ∧
  ctx.atmosphericPhase = .gas ∧
  ctx.reductionReactant = .carbonDioxide ∧
  ctx.reductionProduct = .carbonMonoxide ∧
  ctx.medium = .acidic ∧
  ctx.mode = .photocatalytic ∧
  ctx.catalystLabel = 1

/-- Number of atoms of an element in one formula unit of a species.  These
values unpack exactly the formulas `CO₂`, `CO`, `H⁺`, `e⁻`, and `H₂O`. -/
def atomCount : Species → Element → ℕ
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .hydrogen => 0
  | .carbonDioxide, .oxygen => 2
  | .proton, .carbon => 0
  | .proton, .hydrogen => 1
  | .proton, .oxygen => 0
  | .electron, _ => 0
  | .carbonMonoxide, .carbon => 1
  | .carbonMonoxide, .hydrogen => 0
  | .carbonMonoxide, .oxygen => 1
  | .water, .carbon => 0
  | .water, .hydrogen => 2
  | .water, .oxygen => 1

/-- Formal charge of one formula unit of each balancing species. -/
def formalCharge : Species → ℤ
  | .proton => 1
  | .electron => -1
  | .carbonDioxide | .carbonMonoxide | .water => 0

/-- Total count of an element on one side of an equation. -/
def atomsInComplex (c : CRNT.Complex Species) (e : Element) : ℕ :=
  ∑ s : Species, c s * atomCount s e

/-- Total formal charge on one side of an equation. -/
def chargeInComplex (c : CRNT.Complex Species) : ℤ :=
  ∑ s : Species, (c s : ℤ) * formalCharge s

/-- Every represented element is conserved by the reaction. -/
def AtomBalanced (r : CRNT.Reaction Species) : Prop :=
  ∀ e : Element, atomsInComplex r.source e = atomsInComplex r.target e

/-- Net formal charge is conserved by the reaction. -/
def ChargeBalanced (r : CRNT.Reaction Species) : Prop :=
  chargeInComplex r.source = chargeInComplex r.target

/-- The written half-equation has already had every common species cancelled.
This rules out adding arbitrary spectator copies to both sides. -/
def IsReduced (r : CRNT.Reaction Species) : Prop :=
  ∀ s : Species, r.source s = 0 ∨ r.target s = 0

/-- Candidate-independent specification supplied to the balancing derivation.

The coefficient-one constraints normalize the displayed `CO₂ → CO` skeleton;
they do not state any of the requested auxiliary coefficients. -/
def IsAcidicCO2ToCOHalfEquation
    (ctx : ProblemContext) (r : CRNT.Reaction Species) : Prop :=
  MatchesSourceContext ctx ∧
  r.source ctx.reductionReactant = 1 ∧
  r.target ctx.reductionProduct = 1 ∧
  IsReduced r ∧
  AtomBalanced r ∧
  ChargeBalanced r

/-- The exact coefficient ledger requested by the question.  It is used only
as a conclusion of the balancing theorem, never as an input premise. -/
def HasCO2ReductionCoefficients (r : CRNT.Reaction Species) : Prop :=
  r.source .carbonDioxide = 1 ∧
  r.source .proton = 2 ∧
  r.source .electron = 2 ∧
  r.source .carbonMonoxide = 0 ∧
  r.source .water = 0 ∧
  r.target .carbonDioxide = 0 ∧
  r.target .proton = 0 ∧
  r.target .electron = 0 ∧
  r.target .carbonMonoxide = 1 ∧
  r.target .water = 1

/-- Concrete output carrier for
`CO₂ + 2 H⁺ + 2 e⁻ → CO + H₂O`. -/
def halfEquation : CRNT.Reaction Species where
  source
    | .carbonDioxide => 1
    | .proton => 2
    | .electron => 2
    | .carbonMonoxide => 0
    | .water => 0
  target
    | .carbonDioxide => 0
    | .proton => 0
    | .electron => 0
    | .carbonMonoxide => 1
    | .water => 1

/-- Human-readable exact-symbolic rendering of `halfEquation`.  The reaction
object and its balance theorems, not this string alone, carry the semantics. -/
def halfEquationDisplay : String := "CO₂ + 2 H⁺ + 2 e⁻ → CO + H₂O"

/-- Explicit enumeration of the closed balancing-species domain, used to
evaluate the finite atom and charge ledgers. -/
private theorem species_univ :
    (Finset.univ : Finset Species) =
      {.carbonDioxide, .proton, .electron, .carbonMonoxide, .water} := by
  decide

/-- The source context data are represented faithfully. -/
theorem problemContext_matchesSource : MatchesSourceContext problemContext := by
  simp [MatchesSourceContext, problemContext]

/-- Atom and charge conservation force all auxiliary coefficients, including
the two-electron count, for any equation satisfying the source-first spec. -/
theorem derive_halfEquation_coefficients
    {r : CRNT.Reaction Species}
    (h : IsAcidicCO2ToCOHalfEquation problemContext r) :
    HasCO2ReductionCoefficients r := by
  rcases h with ⟨_, hCO2_source, hCO_target, hReduced, hAtoms, hCharge⟩
  change r.source .carbonDioxide = 1 at hCO2_source
  change r.target .carbonMonoxide = 1 at hCO_target

  have hCO2_target : r.target .carbonDioxide = 0 := by
    rcases hReduced .carbonDioxide with hzero | hzero
    · omega
    · exact hzero
  have hCO_source : r.source .carbonMonoxide = 0 := by
    rcases hReduced .carbonMonoxide with hzero | hzero
    · exact hzero
    · omega

  have hOxygen := hAtoms .oxygen
  simp [atomsInComplex, species_univ, atomCount] at hOxygen
  have hWater_source : r.source .water = 0 := by
    rcases hReduced .water with hzero | hzero
    · exact hzero
    · omega
  have hWater_target : r.target .water = 1 := by
    omega

  have hHydrogen := hAtoms .hydrogen
  simp [atomsInComplex, species_univ, atomCount] at hHydrogen
  have hProton_target : r.target .proton = 0 := by
    rcases hReduced .proton with hzero | hzero
    · omega
    · exact hzero
  have hProton_source : r.source .proton = 2 := by
    omega

  simp [ChargeBalanced, chargeInComplex, species_univ, formalCharge,
    hProton_source, hProton_target] at hCharge
  have hElectron_target : r.target .electron = 0 := by
    rcases hReduced .electron with hzero | hzero
    · omega
    · exact hzero
  have hElectron_source : r.source .electron = 2 := by
    omega

  exact ⟨hCO2_source, hProton_source, hElectron_source, hCO_source,
    hWater_source, hCO2_target, hProton_target, hElectron_target,
    hCO_target, hWater_target⟩

/-- The submitted reaction satisfies the candidate-independent specification. -/
theorem halfEquation_specification :
    IsAcidicCO2ToCOHalfEquation problemContext halfEquation := by
  refine ⟨problemContext_matchesSource, rfl, rfl, ?_, ?_, ?_⟩
  · intro s
    cases s <;> simp [halfEquation]
  · intro e
    cases e <;>
      simp [atomsInComplex, species_univ, halfEquation, atomCount]
  · simp [ChargeBalanced, chargeInComplex, species_univ, halfEquation,
      formalCharge]

/-- Primitive atom- and charge-balanced equations in this source-derived
species domain are unique. -/
theorem halfEquation_unique
    {r : CRNT.Reaction Species}
    (h : IsAcidicCO2ToCOHalfEquation problemContext r) :
    r = halfEquation := by
  rcases derive_halfEquation_coefficients h with
    ⟨hCO2s, hPs, hEs, hCOs, hWs, hCO2t, hPt, hEt, hCOt, hWt⟩
  cases r with
  | mk source target =>
      have hSource : source = halfEquation.source := by
        funext s
        cases s <;> simp [halfEquation] <;> assumption
      have hTarget : target = halfEquation.target := by
        funext s
        cases s <;> simp [halfEquation] <;> assumption
      cases hSource
      cases hTarget
      rfl

/-- Problem-specific raw symbolic result proposition. -/
def HalfEquationRawResult : Prop :=
  IsAcidicCO2ToCOHalfEquation problemContext halfEquation ∧
  ∀ r : CRNT.Reaction Species,
    IsAcidicCO2ToCOHalfEquation problemContext r →
      HasCO2ReductionCoefficients r

/-- Problem-specific exact reported-result proposition.  It exposes both the
full coefficient ledger and uniqueness of the displayed primitive equation. -/
def HalfEquationReportedResult : Prop :=
  IsAcidicCO2ToCOHalfEquation problemContext halfEquation ∧
  HasCO2ReductionCoefficients halfEquation ∧
  ∀ r : CRNT.Reaction Species,
    IsAcidicCO2ToCOHalfEquation problemContext r → r = halfEquation

/-- Raw answer-blind result contract. -/
theorem halfEquation_raw_result : HalfEquationRawResult := by
  refine ⟨halfEquation_specification, ?_⟩
  intro r hr
  exact derive_halfEquation_coefficients hr

/-- Reported exact-symbolic answer-blind result contract. -/
theorem halfEquation_reported_result : HalfEquationReportedResult := by
  refine ⟨halfEquation_specification, ?_, ?_⟩
  · exact derive_halfEquation_coefficients halfEquation_specification
  · intro r hr
    exact halfEquation_unique hr

end IChO2026Problems.ProblemIChO2026T8A1
