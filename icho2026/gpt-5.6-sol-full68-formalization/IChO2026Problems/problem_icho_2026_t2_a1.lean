import Mathlib
import CRNT.Basic.Reaction

/-!
# IChO 2026, problem T2-A1

The problem asks for the overall redox equation obtained when malonic acid is
oxidised to carbon dioxide and bromate is reduced to bromide.  The cerium(IV)
species is catalytic, while potassium and sulfate are spectators.  We model
the two balanced half-reactions, their cancellation, and the resulting
primitive whole-number net ionic equation.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T2A1

/-- Elements occurring in the supplied chemicals, the ionic intermediates, or
the products relevant to T2-A1. -/
inductive Element
  | carbon
  | hydrogen
  | oxygen
  | bromine
  | cerium
  | potassium
  | sulfur
  deriving DecidableEq, Fintype, Repr

/-- Source-named compounds and the species needed to write the acidic
half-reactions.  No phase is asserted because the question does not request
phase labels. -/
inductive Species
  | potassiumBromate
  | malonicAcid
  | ceriumIVSulfate
  | sulfuricAcid
  | bromate
  | carbonDioxide
  | bromide
  | water
  | ceriumIV
  | ceriumIII
  | potassium
  | sulfate
  | hydrogenIon
  | electron
  deriving DecidableEq, Fintype, Repr

/-- Number of atoms of an element in one formula unit of a species.  In
particular, `malonicAcid` represents `CH₂(COOH)₂ = C₃H₄O₄`. -/
def atomCount : Species → Element → ℕ
  | .potassiumBromate, .potassium => 1
  | .potassiumBromate, .bromine => 1
  | .potassiumBromate, .oxygen => 3
  | .malonicAcid, .carbon => 3
  | .malonicAcid, .hydrogen => 4
  | .malonicAcid, .oxygen => 4
  | .ceriumIVSulfate, .cerium => 1
  | .ceriumIVSulfate, .sulfur => 2
  | .ceriumIVSulfate, .oxygen => 8
  | .sulfuricAcid, .hydrogen => 2
  | .sulfuricAcid, .sulfur => 1
  | .sulfuricAcid, .oxygen => 4
  | .bromate, .bromine => 1
  | .bromate, .oxygen => 3
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .oxygen => 2
  | .bromide, .bromine => 1
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | .ceriumIV, .cerium => 1
  | .ceriumIII, .cerium => 1
  | .potassium, .potassium => 1
  | .sulfate, .sulfur => 1
  | .sulfate, .oxygen => 4
  | .hydrogenIon, .hydrogen => 1
  | _, _ => 0

/-- Formal electric charge, in elementary-charge units, of each modeled
species or formula unit. -/
def formalCharge : Species → ℤ
  | .bromate => -1
  | .bromide => -1
  | .ceriumIV => 4
  | .ceriumIII => 3
  | .potassium => 1
  | .sulfate => -2
  | .hydrogenIon => 1
  | .electron => -1
  | _ => 0

/-- The four chemicals explicitly stated to be mixed. -/
def suppliedChemicals : Finset Species :=
  { .potassiumBromate, .malonicAcid, .ceriumIVSulfate, .sulfuricAcid }

/-- Cerium oxidation states identified by the source's oscillation diagram. -/
def oscillatingCeriumSpecies : Finset Species := { .ceriumIV, .ceriumIII }

/-- The finite material domain of the requested net equation.  It is obtained
from the stipulated reactants and terminal redox products, with water as the
acidic-medium balancing species. -/
def overallMaterialDomain : Finset Species :=
  { .malonicAcid, .bromate, .carbonDioxide, .bromide, .water }

/-- Total atoms of element `e` in a CRNT complex. -/
def atomTotal (c : CRNT.Complex Species) (e : Element) : ℕ :=
  ∑ s : Species, c s * atomCount s e

/-- Total formal charge of a CRNT complex. -/
def chargeTotal (c : CRNT.Complex Species) : ℤ :=
  ∑ s : Species, (c s : ℤ) * formalCharge s

/-- Every element is conserved by a reaction. -/
def AtomBalanced (r : CRNT.Reaction Species) : Prop :=
  ∀ e : Element, atomTotal r.source e = atomTotal r.target e

/-- Total formal charge is conserved by a reaction. -/
def ChargeBalanced (r : CRNT.Reaction Species) : Prop :=
  chargeTotal r.source = chargeTotal r.target

/-- Oxidation half-reaction in acidic bookkeeping form:
`C₃H₄O₄ + 2 H₂O ⟶ 3 CO₂ + 8 H⁺ + 8 e⁻`. -/
def malonicOxidationHalfReaction : CRNT.Reaction Species where
  source
    | .malonicAcid => 1
    | .water => 2
    | _ => 0
  target
    | .carbonDioxide => 3
    | .hydrogenIon => 8
    | .electron => 8
    | _ => 0

/-- Reduction half-reaction in acidic bookkeeping form:
`BrO₃⁻ + 6 H⁺ + 6 e⁻ ⟶ Br⁻ + 3 H₂O`. -/
def bromateReductionHalfReaction : CRNT.Reaction Species where
  source
    | .bromate => 1
    | .hydrogenIon => 6
    | .electron => 6
    | _ => 0
  target
    | .bromide => 1
    | .water => 3
    | _ => 0

/-- Both stipulated redox transformations conserve every modeled element and
charge. -/
def HalfReactionLedgerSpec : Prop :=
  AtomBalanced malonicOxidationHalfReaction ∧
    ChargeBalanced malonicOxidationHalfReaction ∧
    AtomBalanced bromateReductionHalfReaction ∧
    ChargeBalanced bromateReductionHalfReaction

theorem halfReactionLedgers : HalfReactionLedgerSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    cases e <;> native_decide
  · change chargeTotal malonicOxidationHalfReaction.source =
      chargeTotal malonicOxidationHalfReaction.target
    native_decide
  · intro e
    cases e <;> native_decide
  · change chargeTotal bromateReductionHalfReaction.source =
      chargeTotal bromateReductionHalfReaction.target
    native_decide

/-- Coefficients of the five species in the net ionic equation. -/
structure OverallCoefficients where
  malonicAcid : ℕ
  bromate : ℕ
  carbonDioxide : ℕ
  bromide : ℕ
  water : ℕ
  deriving DecidableEq, Repr

/-- The primitive candidate obtained by matching the `8 e⁻` oxidation and
`6 e⁻` reduction half-reactions and then balancing atoms. -/
def derivedCoefficients : OverallCoefficients where
  malonicAcid := 3
  bromate := 4
  carbonDioxide := 9
  bromide := 4
  water := 6

/-- The element-by-element coefficient equations for the stipulated material
domain, in the order C, H, O, Br. -/
def CoefficientAtomLedger (c : OverallCoefficients) : Prop :=
  3 * c.malonicAcid = c.carbonDioxide ∧
    4 * c.malonicAcid = 2 * c.water ∧
    4 * c.malonicAcid + 3 * c.bromate =
      2 * c.carbonDioxide + c.water ∧
    c.bromate = c.bromide

/-- Charge balance for the two ionic species in the net equation. -/
def CoefficientChargeLedger (c : OverallCoefficients) : Prop :=
  -(c.bromate : ℤ) = -(c.bromide : ℤ)

/-- Matching the electrons produced and consumed by the two half-reactions. -/
def ElectronTransferLedger (c : OverallCoefficients) : Prop :=
  8 * c.malonicAcid = 6 * c.bromate

/-- Positive primitive whole-number coefficients are the standard
normalization of a balanced chemical equation. -/
def PrimitivePositive (c : OverallCoefficients) : Prop :=
  0 < c.malonicAcid ∧
    0 < c.bromate ∧
    0 < c.carbonDioxide ∧
    0 < c.bromide ∧
    0 < c.water ∧
    Nat.Coprime c.malonicAcid c.bromate

/-- Complete algebraic specification used to derive the coefficient tuple. -/
def OverallCoefficientSpec (c : OverallCoefficients) : Prop :=
  CoefficientAtomLedger c ∧
    CoefficientChargeLedger c ∧
    ElectronTransferLedger c ∧
    PrimitivePositive c

theorem derivedCoefficients_spec : OverallCoefficientSpec derivedCoefficients := by
  norm_num [OverallCoefficientSpec, CoefficientAtomLedger,
    CoefficientChargeLedger, ElectronTransferLedger, PrimitivePositive,
    derivedCoefficients, Nat.Coprime]

/-- The atom, charge, and primitive-normalization constraints determine the
reported coefficient tuple rather than assuming it as a premise. -/
theorem overallCoefficients_unique
    (c : OverallCoefficients) (h : OverallCoefficientSpec c) :
    c = derivedCoefficients := by
  rcases h with ⟨hatoms, _hcharge, helectrons, hpositive⟩
  rcases hatoms with ⟨hcarbon, hhydrogen, _hoxygen, hbromine⟩
  rcases hpositive with ⟨ha_pos, _hb_pos, _hco2_pos, _hbr_pos, _hwater_pos, hab_coprime⟩
  have ha_three_dvd : 3 ∣ c.malonicAcid := by
    omega
  obtain ⟨k, ha_eq⟩ := ha_three_dvd
  have hb_eq : c.bromate = 4 * k := by
    omega
  have hk_dvd_a : k ∣ c.malonicAcid := by
    refine ⟨3, ?_⟩
    omega
  have hk_dvd_b : k ∣ c.bromate := by
    refine ⟨4, ?_⟩
    omega
  have hk : k = 1 := Nat.eq_one_of_dvd_coprimes hab_coprime hk_dvd_a hk_dvd_b
  cases c
  simp only [derivedCoefficients, OverallCoefficients.mk.injEq]
  dsimp only at *
  omega

/-- Turn any coefficient tuple into a net reaction over the source-derived
five-species material domain. -/
def reactionFromCoefficients (c : OverallCoefficients) : CRNT.Reaction Species where
  source
    | .malonicAcid => c.malonicAcid
    | .bromate => c.bromate
    | _ => 0
  target
    | .carbonDioxide => c.carbonDioxide
    | .bromide => c.bromide
    | .water => c.water
    | _ => 0

/-- Candidate net ionic equation:
`3 C₃H₄O₄ + 4 BrO₃⁻ ⟶ 9 CO₂ + 4 Br⁻ + 6 H₂O`. -/
def overallBZReaction : CRNT.Reaction Species :=
  reactionFromCoefficients derivedCoefficients

/-- The common terms cancelled after adding three oxidation and four reduction
half-reactions: `6 H₂O + 24 H⁺ + 24 e⁻`. -/
def cancellationComplex : CRNT.Complex Species
  | .water => 6
  | .hydrogenIon => 24
  | .electron => 24
  | _ => 0

/-- Reactant side obtained by adding three oxidation half-reactions and four
reduction half-reactions. -/
def combinedHalfReactionSource : CRNT.Complex Species :=
  CRNT.Complex.add
    (CRNT.Complex.smul 3 malonicOxidationHalfReaction.source)
    (CRNT.Complex.smul 4 bromateReductionHalfReaction.source)

/-- Product side obtained by adding three oxidation half-reactions and four
reduction half-reactions. -/
def combinedHalfReactionTarget : CRNT.Complex Species :=
  CRNT.Complex.add
    (CRNT.Complex.smul 3 malonicOxidationHalfReaction.target)
    (CRNT.Complex.smul 4 bromateReductionHalfReaction.target)

/-- The summed half-reactions are the net equation with the same explicit
complex added to each side; this is the source-to-net cancellation bridge. -/
def HalfReactionCancellationSpec : Prop :=
  combinedHalfReactionSource =
      CRNT.Complex.add overallBZReaction.source cancellationComplex ∧
    combinedHalfReactionTarget =
      CRNT.Complex.add overallBZReaction.target cancellationComplex

theorem halfReactionCancellation : HalfReactionCancellationSpec := by
  constructor <;> funext s <;> cases s <;> rfl

/-- Ce(IV)/Ce(III), potassium, sulfate, acid, and electrons have no net
stoichiometric coefficient.  This records the source statement that Ce(IV) is
a catalyst and the counterions/acid are not consumed by the net ionic redox
reaction. -/
def CatalystAndSpectatorCancellation (r : CRNT.Reaction Species) : Prop :=
  r.source .ceriumIV = r.target .ceriumIV ∧
    r.source .ceriumIII = r.target .ceriumIII ∧
    r.source .potassium = r.target .potassium ∧
    r.source .sulfate = r.target .sulfate ∧
    r.source .hydrogenIon = r.target .hydrogenIon ∧
    r.source .electron = r.target .electron

/-- A reaction satisfies the requested overall-equation contract when it comes
from source-derived primitive coefficients, conserves atoms and charge, and
has no net catalyst or spectator consumption. -/
def IsOverallBZEquation (r : CRNT.Reaction Species) : Prop :=
  ∃ c : OverallCoefficients,
    OverallCoefficientSpec c ∧
      r = reactionFromCoefficients c ∧
      AtomBalanced r ∧
      ChargeBalanced r ∧
      CatalystAndSpectatorCancellation r

/-- Raw symbolic solve result.  It retains the half-reaction derivation rather
than reducing the answer to a preselected displayed string. -/
def BalancedBZEquationRawResult : Prop :=
  HalfReactionLedgerSpec ∧
    HalfReactionCancellationSpec ∧
    IsOverallBZEquation overallBZReaction

/-- Exact display boundary for the requested symbolic equation. -/
def ExactDisplayedEquation (r : CRNT.Reaction Species) : Prop :=
  r.source .malonicAcid = 3 ∧
    r.source .bromate = 4 ∧
    r.target .carbonDioxide = 9 ∧
    r.target .bromide = 4 ∧
    r.target .water = 6

/-- Reported symbolic result.  Because the problem requests an exact formula,
there is no numerical rounding layer. -/
def BalancedBZEquationReportedResult : Prop :=
  BalancedBZEquationRawResult ∧ ExactDisplayedEquation overallBZReaction

theorem balanced_bz_equation_raw : BalancedBZEquationRawResult := by
  refine ⟨halfReactionLedgers, halfReactionCancellation, ?_⟩
  refine ⟨derivedCoefficients, derivedCoefficients_spec, rfl, ?_, ?_, ?_⟩
  · intro e
    cases e <;> native_decide
  · change chargeTotal overallBZReaction.source = chargeTotal overallBZReaction.target
    native_decide
  · norm_num [CatalystAndSpectatorCancellation, overallBZReaction,
      reactionFromCoefficients]

/-- Lean carrier for requested output `balanced_bz_equation`. -/
theorem balanced_bz_equation_reported : BalancedBZEquationReportedResult := by
  refine ⟨balanced_bz_equation_raw, ?_⟩
  norm_num [ExactDisplayedEquation, overallBZReaction, reactionFromCoefficients,
    derivedCoefficients]

end ProblemIcho2026T2A1
end IChO2026Problems
