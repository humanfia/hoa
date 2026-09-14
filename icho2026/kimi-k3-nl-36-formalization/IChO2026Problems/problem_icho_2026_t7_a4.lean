import IChO2026Chem
import CRNT.Basic.Reaction

/-!
# IChO 2026, problem T7, part A4

The problem depicts compound `3` as a tertiary amine with two hydroxyethyl
substituents and one methyl substituent, and states that its aqueous solution
removes carbon dioxide.  This file records the corresponding reversible
bicarbonate-forming equation.  Atom and charge conservation, the image-derived
assembly of compound `3`, and cancellation of the carbonic-acid intermediate
are kept as explicit proof obligations.
-/

namespace IChO2026Problems.Icho2026T7A4

/-- Elements needed for the molecular formulae in T7-A4. -/
inductive Atom
  | carbon
  | hydrogen
  | nitrogen
  | oxygen
  deriving DecidableEq, Fintype, Repr

/-- Phases explicitly relevant to the aqueous scrubbing context. -/
inductive Phase
  | aqueous
  | liquid
  deriving DecidableEq, Fintype, Repr

/--
The source-first component ledger for the skeletal drawing of compound `3`.
One hydroxyethyl entry represents `HO-CH₂-CH₂-` attached to nitrogen.
-/
inductive Compound3Component
  | hydroxyethyl
  | methyl
  | tertiaryNitrogenCenter
  deriving DecidableEq, Fintype, Repr

/-- Multiplicities read from the drawing of compound `3` on `T7_page-2.png`. -/
def componentMultiplicity : Compound3Component → ℕ
  | .hydroxyethyl => 2
  | .methyl => 1
  | .tertiaryNitrogenCenter => 1

/-- Atom ledger for one visually distinct component of compound `3`. -/
def componentAtomCount : Compound3Component → Atom → ℕ
  | .hydroxyethyl, .carbon => 2
  | .hydroxyethyl, .hydrogen => 5
  | .hydroxyethyl, .oxygen => 1
  | .methyl, .carbon => 1
  | .methyl, .hydrogen => 3
  | .tertiaryNitrogenCenter, .nitrogen => 1
  | _, _ => 0

/-- Recombination of all components in the displayed structure of compound `3`. -/
def compound3AtomCount (a : Atom) : ℕ :=
  ∑ c : Compound3Component, componentMultiplicity c * componentAtomCount c a

/--
The three substituent bonds at nitrogen are supplied by two hydroxyethyl groups
and one methyl group; hence the depicted neutral amine has no N-H bond.
-/
def compound3NitrogenSubstituentCount : ℕ :=
  componentMultiplicity .hydroxyethyl + componentMultiplicity .methyl

/-- Species needed by the requested net equation and its aqueous mechanism. -/
inductive Species
  | compound3
  | carbonDioxide
  | water
  | carbonicAcid
  | protonatedCompound3
  | bicarbonate
  deriving DecidableEq, Fintype, Repr

/-- Molecular atom counts for every species in the finite reaction domain. -/
def atomCount : Species → Atom → ℕ
  | .compound3, a => compound3AtomCount a
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .oxygen => 2
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | .carbonicAcid, .carbon => 1
  | .carbonicAcid, .hydrogen => 2
  | .carbonicAcid, .oxygen => 3
  | .protonatedCompound3, .carbon => 5
  | .protonatedCompound3, .hydrogen => 14
  | .protonatedCompound3, .nitrogen => 1
  | .protonatedCompound3, .oxygen => 2
  | .bicarbonate, .carbon => 1
  | .bicarbonate, .hydrogen => 1
  | .bicarbonate, .oxygen => 3
  | _, _ => 0

/-- Formal charge of each species in integer elementary-charge units. -/
def formalCharge : Species → ℤ
  | .protonatedCompound3 => 1
  | .bicarbonate => -1
  | _ => 0

/-- Phase assignment inside the aqueous reaction equation. -/
def speciesPhase : Species → Phase
  | .water => .liquid
  | _ => .aqueous

/-- The reaction medium stated in the problem. -/
def reactionMedium : Phase := .aqueous

/-- Reactant complex `compound 3 + CO₂ + H₂O`, with unit coefficients. -/
def scrubberReactants : CRNT.Complex Species
  | .compound3 => 1
  | .carbonDioxide => 1
  | .water => 1
  | _ => 0

/-- Product complex `protonated compound 3 + HCO₃⁻`, with unit coefficients. -/
def scrubberProducts : CRNT.Complex Species
  | .protonatedCompound3 => 1
  | .bicarbonate => 1
  | _ => 0

/-- Hydration of dissolved carbon dioxide to the bookkeeping intermediate. -/
def carbonDioxideHydration : CRNT.Reaction Species where
  source := fun
    | .carbonDioxide => 1
    | .water => 1
    | _ => 0
  target := fun
    | .carbonicAcid => 1
    | _ => 0

/-- Proton transfer from carbonic acid to the depicted tertiary amine. -/
def tertiaryAmineProtonTransfer : CRNT.Reaction Species where
  source := fun
    | .compound3 => 1
    | .carbonicAcid => 1
    | _ => 0
  target := fun
    | .protonatedCompound3 => 1
    | .bicarbonate => 1
    | _ => 0

/-!
The chemistry bridge represented by the preceding two carriers is the
base-catalysed hydration mechanism for aqueous tertiary amines.  It is stated
with the reversible net equation in Section 2.1, Equation (1), of:
Zhang et al., *Molecules* 2019, 24, 1009,
doi:10.3390/molecules24061009 (PMCID: PMC6470649).
-/

/-- Forward direction of the requested net scrubbing equation. -/
def co2ScrubbingForward : CRNT.Reaction Species where
  source := scrubberReactants
  target := scrubberProducts

/-- A reversible equation is represented by both mutually inverse directions. -/
structure ReversibleEquation (S : Type) where
  forward : CRNT.Reaction S
  reverse : CRNT.Reaction S
  reverse_source : reverse.source = forward.target
  reverse_target : reverse.target = forward.source

/--
Candidate exact equation:
`(HOCH₂CH₂)₂NCH₃ + CO₂ + H₂O ⇌ [(HOCH₂CH₂)₂NHCH₃]⁺ + HCO₃⁻`.
-/
def co2ScrubbingEquation : ReversibleEquation Species where
  forward := co2ScrubbingForward
  reverse := {
    source := scrubberProducts
    target := scrubberReactants
  }
  reverse_source := rfl
  reverse_target := rfl

/-- Total number of atoms of element `a` in a stoichiometric complex. -/
def complexAtomCount (c : CRNT.Complex Species) (a : Atom) : ℕ :=
  ∑ s : Species, c s * atomCount s a

/-- Total formal charge of a stoichiometric complex. -/
def complexCharge (c : CRNT.Complex Species) : ℤ :=
  ∑ s : Species, (c s : ℤ) * formalCharge s

/-- Element-by-element conservation for a directed reaction. -/
def AtomBalanced (r : CRNT.Reaction Species) : Prop :=
  ∀ a : Atom, complexAtomCount r.source a = complexAtomCount r.target a

/-- Conservation of total formal charge for a directed reaction. -/
def ChargeBalanced (r : CRNT.Reaction Species) : Prop :=
  complexCharge r.source = complexCharge r.target

/-- The net stoichiometric vector is the sum of the two mechanism vectors. -/
def IsNetOf
    (first second net : CRNT.Reaction Species) : Prop :=
  ∀ s : Species,
    net.vector s = first.vector s + second.vector s

/--
Nontrivial image-accounting carrier: the displayed assembly is
`2 × C₂H₅O + 1 × CH₃ + 1 × N = C₅H₁₃NO₂`, with three carbon
substituents and no hydrogen attached to nitrogen.
-/
def Compound3ImageAccounting : Prop :=
  componentMultiplicity .hydroxyethyl = 2 ∧
  componentMultiplicity .methyl = 1 ∧
  componentMultiplicity .tertiaryNitrogenCenter = 1 ∧
  compound3NitrogenSubstituentCount = 3 ∧
  componentAtomCount .tertiaryNitrogenCenter .hydrogen = 0 ∧
  atomCount .compound3 .carbon = 5 ∧
  atomCount .compound3 .hydrogen = 13 ∧
  atomCount .compound3 .nitrogen = 1 ∧
  atomCount .compound3 .oxygen = 2

/-- The aqueous phase facts used to interpret the depicted scrubber. -/
def AqueousScrubbingContext : Prop :=
  reactionMedium = .aqueous ∧
  speciesPhase .compound3 = .aqueous ∧
  speciesPhase .carbonDioxide = .aqueous ∧
  speciesPhase .water = .liquid ∧
  speciesPhase .protonatedCompound3 = .aqueous ∧
  speciesPhase .bicarbonate = .aqueous

/--
Full source-to-Lean specification of the requested equation.  Function
equalities fix all coefficients on the finite species domain, while the last
three conjuncts require atom balance, charge balance, and cancellation of the
carbonic-acid intermediate in the two-step aqueous mechanism.
-/
def ReactionEquationSpec (eqn : ReversibleEquation Species) : Prop :=
  Compound3ImageAccounting ∧
  AqueousScrubbingContext ∧
  eqn.forward.source = scrubberReactants ∧
  eqn.forward.target = scrubberProducts ∧
  eqn.reverse.source = scrubberProducts ∧
  eqn.reverse.target = scrubberReactants ∧
  AtomBalanced eqn.forward ∧
  ChargeBalanced eqn.forward ∧
  IsNetOf carbonDioxideHydration tertiaryAmineProtonTransfer eqn.forward ∧
  eqn.forward.vector .carbonicAcid = 0

/-- Raw exact-symbolic result contract for T7-A4. -/
def ReactionEquationRawResult : Prop :=
  ReactionEquationSpec co2ScrubbingEquation

/--
Reported exact-symbolic result contract.  The conjuncts expose the printed
1:1:1 ⇌ 1:1 coefficients in source order in addition to the raw contract.
-/
def ReactionEquationReportedResult : Prop :=
  ReactionEquationRawResult ∧
  co2ScrubbingEquation.forward.source .compound3 = 1 ∧
  co2ScrubbingEquation.forward.source .carbonDioxide = 1 ∧
  co2ScrubbingEquation.forward.source .water = 1 ∧
  co2ScrubbingEquation.forward.target .protonatedCompound3 = 1 ∧
  co2ScrubbingEquation.forward.target .bicarbonate = 1

/-- The assembled structure shown for compound `3` has formula `C₅H₁₃NO₂`. -/
theorem compound3_image_accounting : Compound3ImageAccounting := by
  unfold Compound3ImageAccounting
  decide

/-- Both elementary aqueous steps conserve every represented atom and charge. -/
theorem mechanism_is_balanced :
    AtomBalanced carbonDioxideHydration ∧
      ChargeBalanced carbonDioxideHydration ∧
      AtomBalanced tertiaryAmineProtonTransfer ∧
      ChargeBalanced tertiaryAmineProtonTransfer := by
  unfold AtomBalanced ChargeBalanced
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    cases a <;> decide
  · decide
  · intro a
    cases a <;> decide
  · decide

/-- The exact candidate is the balanced net of hydration and proton transfer. -/
theorem reaction_equation_raw : ReactionEquationRawResult := by
  unfold ReactionEquationRawResult ReactionEquationSpec
  refine ⟨compound3_image_accounting, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · unfold AqueousScrubbingContext
    decide
  · intro a
    cases a <;> decide
  · unfold ChargeBalanced
    decide
  · intro s
    cases s <;>
      norm_num [CRNT.Reaction.vector, co2ScrubbingEquation,
        co2ScrubbingForward, scrubberReactants, scrubberProducts,
        carbonDioxideHydration, tertiaryAmineProtonTransfer]
  · norm_num [CRNT.Reaction.vector, co2ScrubbingEquation,
      co2ScrubbingForward, scrubberReactants, scrubberProducts]

/-- Exact symbolic reporting introduces no rounding or loss of coefficients. -/
theorem reaction_equation_reported : ReactionEquationReportedResult := by
  exact ⟨reaction_equation_raw, rfl, rfl, rfl, rfl, rfl⟩

end IChO2026Problems.Icho2026T7A4
