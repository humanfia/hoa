import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, theory problem 2, part 1

The problem asks for the overall net ionic equation when malonic acid is
oxidised to carbon dioxide and bromate is reduced to bromide, with Ce(IV)
acting catalytically.  The concrete equation below is kept separate from its
specification: the main result requires it to be the unique primitive,
atom-balanced and charge-balanced reaction having the source-stated roles.

The `proton` and `electron` constructors are equation-bookkeeping entities.
They make the acidic half-reaction derivation explicit.  `ceriumIV` records the
catalyst named in the problem.  All three must cancel from the reduced overall
equation; this is derived rather than inserted as a coefficient premise.
-/

open scoped BigOperators

namespace IChO2026Problems
namespace ProblemIChO2026T2A1

open CRNT

/-- Elements needed to audit the stated BZ transformation and its Ce catalyst. -/
inductive Element
  | hydrogen
  | carbon
  | oxygen
  | bromine
  | cerium
  deriving DecidableEq, Fintype, Repr

/-- Chemical species and internal entities needed for the two acidic
half-reactions and their reduced overall reaction. -/
inductive Entity
  | bromate
  | malonicAcid
  | bromide
  | carbonDioxide
  | water
  | proton
  | electron
  | ceriumIV
  deriving DecidableEq, Fintype, Repr

/-- Explicit enumeration bridge for coefficient-ledger computations. -/
private theorem entity_univ :
    (Finset.univ : Finset Entity) =
      { .bromate, .malonicAcid, .bromide, .carbonDioxide,
        .water, .proton, .electron, .ceriumIV } := by
  decide

/-- Expand a finite sum over the eight equation entities. -/
private theorem sum_entity {M : Type*} [AddCommMonoid M] (f : Entity → M) :
    ∑ s : Entity, f s =
      f .bromate +
        (f .malonicAcid +
          (f .bromide +
            (f .carbonDioxide +
              (f .water + (f .proton + (f .electron + f .ceriumIV)))))) := by
  rw [entity_univ]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]

/-- Formula and formal-charge data for one equation entity. -/
structure EntityData where
  atomCount : Element → ℕ
  formalCharge : ℤ

/-- Source-stated molecular formulae, together with the usual bookkeeping
formulae for water, proton, electron, and the named Ce(IV) catalyst. -/
def entityData : Entity → EntityData
  | .bromate =>
      { atomCount := fun e => match e with
          | .oxygen => 3
          | .bromine => 1
          | _ => 0
        formalCharge := -1 }
  | .malonicAcid =>
      { atomCount := fun e => match e with
          | .hydrogen => 4
          | .carbon => 3
          | .oxygen => 4
          | _ => 0
        formalCharge := 0 }
  | .bromide =>
      { atomCount := fun e => match e with
          | .bromine => 1
          | _ => 0
        formalCharge := -1 }
  | .carbonDioxide =>
      { atomCount := fun e => match e with
          | .carbon => 1
          | .oxygen => 2
          | _ => 0
        formalCharge := 0 }
  | .water =>
      { atomCount := fun e => match e with
          | .hydrogen => 2
          | .oxygen => 1
          | _ => 0
        formalCharge := 0 }
  | .proton =>
      { atomCount := fun e => match e with
          | .hydrogen => 1
          | _ => 0
        formalCharge := 1 }
  | .electron =>
      { atomCount := fun _ => 0
        formalCharge := -1 }
  | .ceriumIV =>
      { atomCount := fun e => match e with
          | .cerium => 1
          | _ => 0
        formalCharge := 4 }

/-- Number of atoms of `e` in one entity `s`. -/
def atomCount (s : Entity) (e : Element) : ℕ :=
  (entityData s).atomCount e

/-- Formal charge of one entity. -/
def formalCharge (s : Entity) : ℤ :=
  (entityData s).formalCharge

/-- Total number of atoms of an element on one side of an equation. -/
def totalAtoms (c : Complex Entity) (e : Element) : ℕ :=
  ∑ s : Entity, c s * atomCount s e

/-- Total formal charge on one side of an equation. -/
def totalCharge (c : Complex Entity) : ℤ :=
  ∑ s : Entity, (c s : ℤ) * formalCharge s

/-- Every audited element is conserved by a reaction. -/
def AtomBalanced (r : Reaction Entity) : Prop :=
  ∀ e : Element, totalAtoms r.source e = totalAtoms r.target e

/-- Net formal charge is conserved by a reaction. -/
def ChargeBalanced (r : Reaction Entity) : Prop :=
  totalCharge r.source = totalCharge r.target

/-- A reaction has had every entity occurring on both sides cancelled. -/
def NetReduced (r : Reaction Entity) : Prop :=
  ∀ s : Entity, r.source s = 0 ∨ r.target s = 0

/-- Electrons are internal redox bookkeeping and Ce(IV) is returned because it
is a catalyst.  Their coefficients therefore agree before net cancellation. -/
def InternalEntitiesCancel (r : Reaction Entity) : Prop :=
  r.source .electron = r.target .electron ∧
    r.source .ceriumIV = r.target .ceriumIV

/-- The directions explicitly stipulated by the question.  Water and proton
are intentionally not assigned to a side here; atom and charge balance decide
their net coefficients. -/
def HasStatedConversionRoles (r : Reaction Entity) : Prop :=
  0 < r.source .bromate ∧ r.target .bromate = 0 ∧
    0 < r.source .malonicAcid ∧ r.target .malonicAcid = 0 ∧
    r.source .bromide = 0 ∧ 0 < r.target .bromide ∧
    r.source .carbonDioxide = 0 ∧ 0 < r.target .carbonDioxide

/-- A primitive equation is normalized against multiplication of all
coefficients by a common positive factor. -/
def HasPrimitiveReactantCoefficients (r : Reaction Entity) : Prop :=
  Nat.Coprime (r.source .bromate) (r.source .malonicAcid)

/-- Complete source-derived specification of an admissible overall equation. -/
def IsAdmissibleOverallReaction (r : Reaction Entity) : Prop :=
  r.Nontrivial ∧
    HasStatedConversionRoles r ∧
    AtomBalanced r ∧
    ChargeBalanced r ∧
    InternalEntitiesCancel r ∧
    NetReduced r ∧
    HasPrimitiveReactantCoefficients r

/-- Candidate net equation
`4 BrO₃⁻ + 3 CH₂(COOH)₂ → 4 Br⁻ + 9 CO₂ + 6 H₂O`. -/
def balancedBZReaction : Reaction Entity where
  source
    | .bromate => 4
    | .malonicAcid => 3
    | _ => 0
  target
    | .bromide => 4
    | .carbonDioxide => 9
    | .water => 6
    | _ => 0

/-- Oxidation half-reaction normalized to one malonic-acid molecule:
`CH₂(COOH)₂ + 2 H₂O → 3 CO₂ + 8 H⁺ + 8 e⁻`. -/
def malonicAcidOxidation : Reaction Entity where
  source
    | .malonicAcid => 1
    | .water => 2
    | _ => 0
  target
    | .carbonDioxide => 3
    | .proton => 8
    | .electron => 8
    | _ => 0

/-- Reduction half-reaction normalized to one bromate ion:
`BrO₃⁻ + 6 H⁺ + 6 e⁻ → Br⁻ + 3 H₂O`. -/
def bromateReduction : Reaction Entity where
  source
    | .bromate => 1
    | .proton => 6
    | .electron => 6
    | _ => 0
  target
    | .bromide => 1
    | .water => 3
    | _ => 0

/-- Both atom and charge conservation for a half-reaction. -/
def IsBalancedHalfReaction (r : Reaction Entity) : Prop :=
  AtomBalanced r ∧ ChargeBalanced r

/-- Scale and add two reactions without cancelling common entities. -/
def combineScaled (m n : ℕ) (r₁ r₂ : Reaction Entity) : Reaction Entity where
  source := Complex.add (Complex.smul m r₁.source) (Complex.smul n r₂.source)
  target := Complex.add (Complex.smul m r₁.target) (Complex.smul n r₂.target)

/-- Cancel the common coefficient of each entity from both sides. -/
def cancelCommon (r : Reaction Entity) : Reaction Entity where
  source := fun s => r.source s - min (r.source s) (r.target s)
  target := fun s => r.target s - min (r.source s) (r.target s)

/-- Three malonic-acid oxidation events and four bromate-reduction events,
before cancelling protons, electrons, and water. -/
def combinedHalfReactions : Reaction Entity :=
  combineScaled 3 4 malonicAcidOxidation bromateReduction

/-- The result of cancelling the combined half-reactions. -/
def derivedOverallReaction : Reaction Entity :=
  cancelCommon combinedHalfReactions

/-- Positive scale factors match the electrons produced by oxidation and
consumed by reduction. -/
def ElectronTransfersMatch (oxidationScale reductionScale : ℕ) : Prop :=
  0 < oxidationScale ∧ 0 < reductionScale ∧
    oxidationScale * malonicAcidOxidation.target .electron =
      reductionScale * bromateReduction.source .electron

/-- The two source-derived half-reactions separately conserve atoms and charge. -/
theorem half_reactions_balanced :
    IsBalancedHalfReaction malonicAcidOxidation ∧
      IsBalancedHalfReaction bromateReduction := by
  constructor
  · constructor
    · intro e
      cases e <;>
        norm_num [AtomBalanced, totalAtoms, atomCount, entityData, malonicAcidOxidation,
          sum_entity]
    · norm_num [ChargeBalanced, totalCharge, formalCharge, entityData,
        malonicAcidOxidation, sum_entity]
  · constructor
    · intro e
      cases e <;>
        norm_num [AtomBalanced, totalAtoms, atomCount, entityData, bromateReduction,
          sum_entity]
    · norm_num [ChargeBalanced, totalCharge, formalCharge, entityData,
        bromateReduction, sum_entity]

/-- `3` and `4` are the least positive scales matching the 8 and 6 electron
transfers of the normalized half-reactions. -/
theorem electron_transfer_scales_primitive :
    ElectronTransfersMatch 3 4 ∧
      ∀ m n : ℕ, ElectronTransfersMatch m n → 3 ≤ m ∧ 4 ≤ n := by
  constructor
  · norm_num [ElectronTransfersMatch, malonicAcidOxidation, bromateReduction]
  · intro m n h
    change 0 < m ∧ 0 < n ∧ m * 8 = n * 6 at h
    omega

/-- Cancelling the least common electron transfer gives the candidate overall
equation, rather than assuming its coefficients as a premise. -/
theorem half_reactions_derive_overall :
    derivedOverallReaction = balancedBZReaction := by
  decide

/-- Net stoichiometric coefficient, positive for production and negative for
consumption. -/
def netCoefficient (r : Reaction Entity) (s : Entity) : ℤ :=
  (r.target s : ℤ) - (r.source s : ℤ)

/-- Exact coefficient-level rendering of the requested displayed equation. -/
def HasDisplayedBZCoefficients (r : Reaction Entity) : Prop :=
  r.source .bromate = 4 ∧
    r.source .malonicAcid = 3 ∧
    r.source .bromide = 0 ∧
    r.source .carbonDioxide = 0 ∧
    r.source .water = 0 ∧
    r.source .proton = 0 ∧
    r.source .electron = 0 ∧
    r.source .ceriumIV = 0 ∧
    r.target .bromate = 0 ∧
    r.target .malonicAcid = 0 ∧
    r.target .bromide = 4 ∧
    r.target .carbonDioxide = 9 ∧
    r.target .water = 6 ∧
    r.target .proton = 0 ∧
    r.target .electron = 0 ∧
    r.target .ceriumIV = 0

/-- Raw symbolic result contract: the half-reaction construction yields an
admissible equation, and the primitive source-derived constraints uniquely
determine that equation. -/
def BalancedBZEquationRaw : Prop :=
  derivedOverallReaction = balancedBZReaction ∧
    IsAdmissibleOverallReaction balancedBZReaction ∧
    ∀ r : Reaction Entity,
      IsAdmissibleOverallReaction r → r = balancedBZReaction

/-- Reported symbolic result contract.  Exact-symbolic reporting introduces no
rounding; it expands the raw result into every displayed coefficient and makes
the zero net Ce(IV) coefficient explicit. -/
def BalancedBZEquationReported : Prop :=
  BalancedBZEquationRaw ∧
    HasDisplayedBZCoefficients balancedBZReaction ∧
    netCoefficient balancedBZReaction .ceriumIV = 0

/-- Source-derived raw result for T2-A1. -/
theorem balanced_bz_equation_raw : BalancedBZEquationRaw := by
  refine ⟨half_reactions_derive_overall, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have h' := congrFun h Entity.bromate
      norm_num [balancedBZReaction] at h'
    · norm_num [HasStatedConversionRoles, balancedBZReaction]
    · intro e
      cases e <;>
        norm_num [AtomBalanced, totalAtoms, atomCount, entityData, balancedBZReaction,
          sum_entity]
    · norm_num [ChargeBalanced, totalCharge, formalCharge, entityData,
        balancedBZReaction, sum_entity]
    · norm_num [InternalEntitiesCancel, balancedBZReaction]
    · intro s
      cases s <;> norm_num [NetReduced, balancedBZReaction]
    · norm_num [HasPrimitiveReactantCoefficients, balancedBZReaction]
  · intro r hr
    rcases hr with ⟨_, hroles, hatoms, hcharge, hinternal, hreduced, hprimitive⟩
    rcases hroles with
      ⟨hbromate_pos, hbromate_target, hmalonic_pos, hmalonic_target,
        hbromide_source, hbromide_pos, hcarbon_source, hcarbon_pos⟩
    rcases hinternal with ⟨helectron_cancel, hcerium_cancel⟩
    have helectron_source : r.source .electron = 0 := by
      rcases hreduced .electron with h | h
      · exact h
      · omega
    have helectron_target : r.target .electron = 0 := by
      omega
    have hcerium_source : r.source .ceriumIV = 0 := by
      rcases hreduced .ceriumIV with h | h
      · exact h
      · omega
    have hcerium_target : r.target .ceriumIV = 0 := by
      omega
    have hbromine := hatoms .bromine
    simp [totalAtoms, atomCount, entityData, sum_entity] at hbromine
    have hcarbon := hatoms .carbon
    simp [totalAtoms, atomCount, entityData, sum_entity] at hcarbon
    have hhydrogen := hatoms .hydrogen
    simp [totalAtoms, atomCount, entityData, sum_entity] at hhydrogen
    have hoxygen := hatoms .oxygen
    simp [totalAtoms, atomCount, entityData, sum_entity] at hoxygen
    simp [ChargeBalanced, totalCharge, formalCharge, entityData, sum_entity] at hcharge
    have hbromate_eq_bromide : r.source .bromate = r.target .bromide := by
      omega
    have hcarbon_eq : r.target .carbonDioxide = 3 * r.source .malonicAcid := by
      omega
    have hproton_eq : r.source .proton = r.target .proton := by
      omega
    have hproton_source : r.source .proton = 0 := by
      rcases hreduced .proton with h | h
      · exact h
      · omega
    have hproton_target : r.target .proton = 0 := by
      omega
    have hwater_source : r.source .water = 0 := by
      rcases hreduced .water with h | h
      · exact h
      · exfalso
        omega
    have hwater_target : r.target .water = 2 * r.source .malonicAcid := by
      omega
    have hreactant_ratio :
        3 * r.source .bromate = 4 * r.source .malonicAcid := by
      omega
    have hfour_dvd_bromate : 4 ∣ r.source .bromate := by
      apply (show Nat.Coprime 4 3 by norm_num).dvd_of_dvd_mul_right
      rw [Nat.mul_comm (r.source .bromate) 3, hreactant_ratio]
      exact Nat.dvd_mul_right 4 (r.source .malonicAcid)
    obtain ⟨k, hk⟩ := hfour_dvd_bromate
    have hmalonic_eq : r.source .malonicAcid = 3 * k := by
      omega
    have hk_dvd_bromate : k ∣ r.source .bromate := by
      refine ⟨4, ?_⟩
      omega
    have hk_dvd_malonic : k ∣ r.source .malonicAcid := by
      refine ⟨3, ?_⟩
      omega
    have hk_one : k = 1 :=
      Nat.eq_one_of_dvd_coprimes hprimitive hk_dvd_bromate hk_dvd_malonic
    have hbromate_source_value : r.source .bromate = 4 := by
      omega
    have hmalonic_source_value : r.source .malonicAcid = 3 := by
      omega
    have hbromide_target_value : r.target .bromide = 4 := by
      omega
    have hcarbon_target_value : r.target .carbonDioxide = 9 := by
      omega
    have hwater_target_value : r.target .water = 6 := by
      omega
    cases r with
    | mk source target =>
        rw [Reaction.mk.injEq]
        constructor
        · funext s
          cases s <;> simp_all [balancedBZReaction]
        · funext s
          cases s <;> simp_all [balancedBZReaction]

/-- Exact-symbolic reported result for T2-A1. -/
theorem balanced_bz_equation_reported : BalancedBZEquationReported := by
  refine ⟨balanced_bz_equation_raw, ?_, ?_⟩
  · norm_num [HasDisplayedBZCoefficients, balancedBZReaction]
  · norm_num [netCoefficient, balancedBZReaction]

end ProblemIChO2026T2A1
end IChO2026Problems
