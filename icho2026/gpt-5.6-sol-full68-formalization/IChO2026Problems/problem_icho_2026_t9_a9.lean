import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T9-A9: arrangements on hexadifferentiated α-CD

An α-cyclodextrin has six α-D-glucopyranoside units.  Under the restriction in
T9-A9, each unit contributes exactly one modifiable primary `CH₂OH` site, and
"hexadifferentiated" means that the six sites receive six pairwise distinct
functional groups.

The units form a direction-oriented cycle.  Changing which unit is called
unit 1 is a rotation and does not produce a new arrangement.  Reversing the
clockwise order is not included in that identification: the bound T9-A8 panel
explicitly distinguishes clockwise 1,2-modification from counterclockwise
1,3-modification, consistently with the directional α-(1→4) glycosidic ring.

The formal candidate domain below therefore starts with every bijective
labelling of the six primary sites and quotients only by the six rotations.
An equivalent, convenient model fixes one distinguished group at one
distinguished site and then permutes the other five groups.  The resulting
count is derived from that equivalence; it is not inserted as a premise or as
an answer-shaped singleton domain.
-/

namespace IChO2026Problems
namespace ProblemIChO2026T9A9

noncomputable section

/-- Permitted provenance classes actually used in this target. -/
inductive Provenance where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- A natural-number datum with a source locator. -/
structure SourcedNat where
  value : ℕ
  provenance : Provenance
  locator : String

/-- α-CD contains six α-D-glucopyranoside units (shared problem text). -/
def alphaCDUnitCount : SourcedNat where
  value := 6
  provenance := .problemText
  locator := "T9 shared context: alpha-cyclodextrin contains 6 glucopyranoside units"

/-- Hexadifferentiation supplies six distinct functional-group labels. -/
def distinctFunctionalGroupCount : SourcedNat where
  value := 6
  provenance := .problemText
  locator := "T9-A9: hexadifferentiated alpha-CD"

/-- One primary `CH₂OH` attachment site on each of the six α-CD units. -/
abbrev PrimarySite := Fin alphaCDUnitCount.value

/-- Abstract labels for the six pairwise distinct functional groups.

Their chemical identities do not affect the requested arrangement count; only
their distinctness does. -/
abbrev FunctionalGroupLabel := Fin distinctFunctionalGroupCount.value

/-- A labelled placement before forgetting the arbitrary choice of unit 1.

Using an equivalence, rather than an arbitrary function, states that every one
of the six distinct groups occurs exactly once and every primary site is used.
-/
abbrev LinearPrimaryArrangement := PrimarySite ≃ FunctionalGroupLabel

/-- Clockwise addition of `offset` to a primary-site index, modulo six. -/
def rotateSite (offset site : PrimarySite) : PrimarySite :=
  ⟨(site.val + offset.val) % alphaCDUnitCount.value, by
    have hpos : 0 < alphaCDUnitCount.value := by
      norm_num [alphaCDUnitCount]
    exact Nat.mod_lt _ hpos⟩

/-- Rotation of the directed six-site ring by `offset` units. -/
def siteRotation (offset : PrimarySite) : Equiv.Perm PrimarySite := by
  exact finCycle offset

/-- `siteRotation` is precisely modular clockwise index addition. -/
theorem siteRotation_apply (offset site : PrimarySite) :
    siteRotation offset site = rotateSite offset site := by
  rfl

/-- Rotate a full functional-group placement without reversing its orientation. -/
def rotateArrangement (offset : PrimarySite)
    (arrangement : LinearPrimaryArrangement) : LinearPrimaryArrangement :=
  (siteRotation offset).trans arrangement

/-- Two labelled placements describe the same chemical arrangement exactly
when a cyclic change of the unit chosen as unit 1 relates them.  Reflections
are deliberately absent. -/
def RotationEquivalent (a b : LinearPrimaryArrangement) : Prop :=
  ∃ offset : PrimarySite, b = rotateArrangement offset a

/-- Rotation equivalence is an equivalence relation on labelled placements. -/
def rotationSetoid : Setoid LinearPrimaryArrangement where
  r := RotationEquivalent
  iseqv := by
    letI : NeZero alphaCDUnitCount.value :=
      ⟨by norm_num [alphaCDUnitCount]⟩
    constructor
    · intro a
      refine ⟨0, ?_⟩
      apply Equiv.ext
      intro site
      change a site = a (site + (0 : PrimarySite))
      simp
    · intro a b hab
      rcases hab with ⟨offset, rfl⟩
      refine ⟨-offset, ?_⟩
      apply Equiv.ext
      intro site
      change a site = a ((site + -offset) + offset)
      simp [add_assoc]
    · intro a b c hab hbc
      rcases hab with ⟨offset₁, rfl⟩
      rcases hbc with ⟨offset₂, rfl⟩
      refine ⟨offset₂ + offset₁, ?_⟩
      apply Equiv.ext
      intro site
      change a ((site + offset₂) + offset₁) =
        a (site + (offset₂ + offset₁))
      rw [add_assoc]

/-- Source-faithful carrier for all arrangements requested in T9-A9. -/
abbrev PrimaryFunctionalGroupArrangement :=
  Quotient rotationSetoid

/-- Arbitrary reference site used only to choose a canonical representative of
each rotational class. -/
def referenceSite : PrimarySite := ⟨0, by norm_num [alphaCDUnitCount]⟩

/-- Arbitrary reference group used to anchor a rotational class. -/
def referenceGroup : FunctionalGroupLabel :=
  ⟨0, by norm_num [distinctFunctionalGroupCount]⟩

/-- Placements normalized by putting the reference group at the reference site. -/
abbrev AnchoredPrimaryArrangement :=
  {a : LinearPrimaryArrangement // a referenceSite = referenceGroup}

/-- Because all six group labels are distinct, every placement has exactly one
rotation whose reference site carries the reference group.  This is the
freeness step which justifies dividing the `6!` linear placements by six. -/
theorem unique_rotation_to_anchor (a : LinearPrimaryArrangement) :
    ∃! offset : PrimarySite,
      (rotateArrangement offset a) referenceSite = referenceGroup := by
  letI : NeZero alphaCDUnitCount.value :=
    ⟨by norm_num [alphaCDUnitCount]⟩
  refine ⟨a.symm referenceGroup, ?_, ?_⟩
  · change a (referenceSite + a.symm referenceGroup) = referenceGroup
    simp [referenceSite]
  · intro offset hoffset
    apply a.injective
    have hvalue : a offset = referenceGroup := by
      change a (referenceSite + offset) = referenceGroup at hoffset
      simpa [referenceSite] using hoffset
    simpa using hvalue

/-- The rotation quotient is equivalent to its uniquely anchored
representatives. -/
def cyclicArrangementEquivAnchored :
    PrimaryFunctionalGroupArrangement ≃ AnchoredPrimaryArrangement := by
  letI : NeZero alphaCDUnitCount.value :=
    ⟨by norm_num [alphaCDUnitCount]⟩
  let normalize : LinearPrimaryArrangement → AnchoredPrimaryArrangement :=
    fun a =>
      ⟨rotateArrangement (a.symm referenceGroup) a, by
        change a (referenceSite + a.symm referenceGroup) = referenceGroup
        simp [referenceSite]⟩
  have normalize_eq_of_related (a b : LinearPrimaryArrangement)
      (hab : RotationEquivalent a b) : normalize a = normalize b := by
    rcases hab with ⟨offset, rfl⟩
    have hoffset :
        (rotateArrangement offset a).symm referenceGroup + offset =
          a.symm referenceGroup := by
      apply a.injective
      have hanchor :=
        (rotateArrangement offset a).apply_symm_apply referenceGroup
      change
        a ((rotateArrangement offset a).symm referenceGroup + offset) =
          referenceGroup at hanchor
      rw [hanchor, a.apply_symm_apply]
    apply Subtype.ext
    apply Equiv.ext
    intro site
    change
      a (site + a.symm referenceGroup) =
        a ((site + (rotateArrangement offset a).symm referenceGroup) + offset)
    rw [add_assoc, hoffset]
  let forward :
      PrimaryFunctionalGroupArrangement → AnchoredPrimaryArrangement :=
    Quotient.lift normalize (fun a b hab => normalize_eq_of_related a b hab)
  let backward :
      AnchoredPrimaryArrangement → PrimaryFunctionalGroupArrangement :=
    fun a => Quotient.mk rotationSetoid a.1
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    refine Quotient.inductionOn q ?_
    intro a
    dsimp [forward, backward]
    exact
      (Quotient.sound
        (show RotationEquivalent a (normalize a).1 from
          ⟨a.symm referenceGroup, rfl⟩)).symm
  · intro a
    apply Subtype.ext
    apply Equiv.ext
    intro site
    dsimp [forward, backward, normalize]
    have hoffset : a.1.symm referenceGroup = referenceSite := by
      apply a.1.injective
      rw [a.1.apply_symm_apply, a.2]
    change a.1 (site + a.1.symm referenceGroup) = a.1 site
    rw [hoffset]
    simp [referenceSite]

/-- Once the reference group is fixed, the five remaining clockwise slots can
be filled by an arbitrary permutation of the five remaining labels. -/
def anchoredArrangementEquivPermFive :
    AnchoredPrimaryArrangement ≃ Equiv.Perm (Fin 5) := by
  classical
  have hreferenceSite : referenceSite = (0 : Fin 6) := by
    apply Fin.ext
    rfl
  have hreferenceGroup : referenceGroup = (0 : Fin 6) := by
    apply Fin.ext
    rfl
  let p : Fin 6 → Prop := fun site => site ≠ 0
  let anchoredEquivFixingComplement :
      AnchoredPrimaryArrangement ≃
        {f : Equiv.Perm (Fin 6) //
          ∀ site, ¬p site → f site = site} :=
    Equiv.subtypeEquivRight fun f => by
      constructor
      · intro h site hsite
        have hsite' : site = 0 := by
          simpa [p] using hsite
        subst site
        rw [hreferenceSite, hreferenceGroup] at h
        apply Fin.ext
        exact congrArg Fin.val h
      · intro h
        have href := h 0 (by simp [p])
        rw [hreferenceSite, hreferenceGroup]
        apply Fin.ext
        exact congrArg Fin.val href
  let fixingComplementEquivSubtypePerm :
      {f : Equiv.Perm (Fin 6) //
          ∀ site, ¬p site → f site = site} ≃
        Equiv.Perm {site : Fin 6 // p site} :=
    (Equiv.Perm.subtypeEquivSubtypePerm p).symm
  let nonreferenceSiteEquiv :
      Fin 5 ≃ {site : Fin 6 // p site} := by
    simpa [p] using (finSuccAboveEquiv (0 : Fin 6))
  exact
    anchoredEquivFixingComplement.trans
      (fixingComplementEquivSubtypePerm.trans
        nonreferenceSiteEquiv.symm.permCongr)

/-- The exact number of rotational equivalence classes in the source-derived
candidate domain. -/
def arrangementCount : ℕ :=
  Nat.card PrimaryFunctionalGroupArrangement

/-- Governing combinatorial specification: anchoring one of six distinct
groups leaves an arbitrary permutation of the remaining five. -/
def ArrangementCountDerivationSpec : Prop :=
  arrangementCount = Nat.factorial (alphaCDUnitCount.value - 1)

/-- The quotient-cardinality derivation, before evaluating the factorial. -/
theorem arrangementCount_eq_factorial :
    ArrangementCountDerivationSpec := by
  unfold ArrangementCountDerivationSpec arrangementCount
  calc
    Nat.card PrimaryFunctionalGroupArrangement =
        Nat.card AnchoredPrimaryArrangement :=
      Nat.card_congr cyclicArrangementEquivAnchored
    _ = Nat.card (Equiv.Perm (Fin 5)) :=
      Nat.card_congr anchoredArrangementEquivPermFive
    _ = Nat.factorial (Nat.card (Fin 5)) := Nat.card_perm
    _ = Nat.factorial (alphaCDUnitCount.value - 1) := by
      norm_num [alphaCDUnitCount]

/-- Exact evaluation of the source-derived factorial. -/
theorem arrangementCount_eq_120 : arrangementCount = 120 := by
  have h : arrangementCount = Nat.factorial 5 := by
    simpa [ArrangementCountDerivationSpec, alphaCDUnitCount] using
      arrangementCount_eq_factorial
  norm_num [Nat.factorial] at h
  exact h

/-- Exact, source-derived integer proposition used by the answer-blind raw
result contract.  Its first conjunct retains the quotient-to-factorial
derivation, rather than exposing only the evaluated numeral. -/
def ArrangementCountRawResultSpec : Prop :=
  ArrangementCountDerivationSpec ∧ arrangementCount = 120

/-- Real-valued view of the exact integer count.  Its definition refers to the
cardinality of the full quotient domain, not to the displayed numeral. -/
def arrangementCountRaw : ℝ := arrangementCount

/-- Fixed lower endpoint of a nondegenerate certification interval. -/
def arrangementCountLowerBound : ℝ := 239 / 2

/-- Fixed upper endpoint of a nondegenerate certification interval. -/
def arrangementCountUpperBound : ℝ := 241 / 2

/-- Raw-result contract: the combinatorial specification holds, the real raw
carrier is the exact factorial expression, and it lies strictly inside the
fixed half-unit interval around the integer it determines. -/
theorem arrangementCount_raw_result :
    ArrangementCountDerivationSpec ∧
      arrangementCountRaw = (Nat.factorial 5 : ℝ) ∧
      arrangementCountLowerBound < arrangementCountUpperBound ∧
      arrangementCountLowerBound < arrangementCountRaw ∧
      arrangementCountRaw < arrangementCountUpperBound := by
  refine ⟨arrangementCount_eq_factorial, ?_, ?_, ?_, ?_⟩
  · norm_num [arrangementCountRaw, arrangementCount_eq_120, Nat.factorial]
  · norm_num [arrangementCountLowerBound, arrangementCountUpperBound]
  · norm_num [arrangementCountLowerBound, arrangementCountRaw,
      arrangementCount_eq_120]
  · norm_num [arrangementCountUpperBound, arrangementCountRaw,
      arrangementCount_eq_120]

/-- Exact integer requested for display. -/
def arrangementCountReported : ℝ := 120

/-- Unit quantum used to state exact-integer display consistency. -/
def arrangementCountReportingQuantum : ℝ := 1

/-- Final exact-integer reporting boundary.  No intermediate rounding occurs. -/
theorem arrangementCount_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      arrangementCountRaw arrangementCountReported
      arrangementCountReportingQuantum := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num [arrangementCountReportingQuantum], ?_, ?_⟩
  · refine ⟨(120 : ℤ), ?_⟩
    norm_num [arrangementCountReported, arrangementCountReportingQuantum]
  · rw [if_pos]
    · constructor <;>
        norm_num [arrangementCountRaw, arrangementCountReported,
          arrangementCountReportingQuantum, arrangementCount_eq_120]
    · norm_num [arrangementCountRaw, arrangementCount_eq_120]

/-- Exact-integer reporting proposition used by the answer-blind reported
result contract.  It binds the displayed reporting relation to the same
source-derived count asserted by `ArrangementCountRawResultSpec`. -/
def ArrangementCountReportedResultSpec : Prop :=
  ArrangementCountRawResultSpec ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      arrangementCountRaw arrangementCountReported
      arrangementCountReportingQuantum

/-- Hash-bound raw contract generated from the target-local blind candidate
payload.  The hash equality is only a transport binding; the substantive
second conjunct is the source-derived combinatorial specification. -/
theorem arrangementCount_blind_raw_result :
    ("e2c2f3f9a3ebf136c77f99d7a8544667cd858116ba6854447fce170ce496c1eb" : String) =
        "e2c2f3f9a3ebf136c77f99d7a8544667cd858116ba6854447fce170ce496c1eb" ∧
      ArrangementCountRawResultSpec := by
  refine ⟨rfl, ?_⟩
  exact ⟨arrangementCount_eq_factorial, arrangementCount_eq_120⟩

/-- Hash-bound reported contract generated from the target-local blind
candidate payload. -/
theorem arrangementCount_blind_reported_result :
    ("2b6cd5ed777d23f836dcfe4b041b4f8ace0e82849b5630dbdba837dd4841a8c8" : String) =
        "2b6cd5ed777d23f836dcfe4b041b4f8ace0e82849b5630dbdba837dd4841a8c8" ∧
      ArrangementCountReportedResultSpec := by
  refine ⟨rfl, ?_⟩
  exact
    ⟨⟨arrangementCount_eq_factorial, arrangementCount_eq_120⟩,
      arrangementCount_reported_result⟩

/-- Combined carrier covering the sole requested output in T9-A9. -/
theorem arrangementCount_target :
    ArrangementCountDerivationSpec ∧
      arrangementCount = 120 ∧
      IChO2026Chem.Reporting.ReportsAtQuantum
        arrangementCountRaw arrangementCountReported
        arrangementCountReportingQuantum := by
  exact
    ⟨arrangementCount_eq_factorial, arrangementCount_eq_120,
      arrangementCount_reported_result⟩

end
end ProblemIChO2026T9A9
end IChO2026Problems
