import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T9-A9

The source asks for every arrangement of the functional groups on a
hexadifferentiated α-cyclodextrin, under the restriction that only the six
primary `CH₂OH` sites are modified.

## Assumption/target split

The problem text and page-4 template supply six glucose units in a directed
cycle and one primary site on each unit.  “Hexadifferentiated” is represented
by six distinct functional-group labels.  A labeled placement is consequently
a bijection between these two six-element types.  Since the ring has no
distinguished starting unit, placements differing by a cyclic rotation are
identified.  Reflections are not identified: the shared source explicitly
distinguishes clockwise from counterclockwise modification.

The requested target is the cardinality of that quotient.  No reaction,
measurement, unit, approximation, or previous-part result is used.
-/

namespace IChO2026Problems.T9A9

/-- The six primary `CH₂OH` sites visible on the α-CD template.
Provenance: problem text and `T9_page-4.png`. -/
abbrev AlphaCDPrimarySite := Fin 6

/-- Six mutually distinct labels, one for each functional group in a
hexadifferentiated product.  Provenance: “hexadifferentiated” in the problem
text. -/
abbrev FunctionalGroupLabel := Fin 6

/-- Before accounting for the cyclic symmetry, an arrangement assigns every
distinct functional group to exactly one primary site. -/
abbrev LabeledPrimaryArrangement :=
  AlphaCDPrimarySite ≃ FunctionalGroupLabel

/-- Move a primary site clockwise by `offset` units.  Addition on `Fin 6` is
modular, so this includes the visible cross-boundary bond from unit 6 back to
unit 1. -/
def rotatePosition
    (offset site : AlphaCDPrimarySite) : AlphaCDPrimarySite :=
  site + offset

/-- Rotate an entire labeled placement clockwise.  This is precomposition by
the permutation `site ↦ site + offset` of the six primary sites. -/
def rotateArrangement
    (offset : AlphaCDPrimarySite) (a : LabeledPrimaryArrangement) :
    LabeledPrimaryArrangement :=
  (Equiv.addRight offset).trans a

@[simp]
theorem rotateArrangement_apply
    (offset : AlphaCDPrimarySite) (a : LabeledPrimaryArrangement)
    (site : AlphaCDPrimarySite) :
    rotateArrangement offset a site = a (rotatePosition offset site) :=
  rfl

/-- The cyclic group of primary-site offsets acts on labeled placements by
clockwise rotation. -/
instance cyclicAddAction :
    AddAction AlphaCDPrimarySite LabeledPrimaryArrangement where
  vadd := rotateArrangement
  zero_vadd a := by
    apply Equiv.ext
    intro site
    change a (site + 0) = a site
    rw [add_zero]
  add_vadd first second a := by
    apply Equiv.ext
    intro site
    change a (site + (first + second)) = a ((site + first) + second)
    exact congrArg a (add_assoc site first second).symm

/-- Two labeled placements describe the same oriented cyclic arrangement when
one is obtained from the other by a rotation.  No reflection clause is
present, preserving the source's clockwise/counterclockwise distinction. -/
def CyclicallyEquivalent
    (a b : LabeledPrimaryArrangement) : Prop :=
  ∃ offset : AlphaCDPrimarySite, ∀ site : AlphaCDPrimarySite,
    b site = a (rotatePosition offset site)

/-- The source-level rotation relation is the orbit relation for the cyclic
offset action. -/
theorem cyclicallyEquivalent_iff_orbitRel
    (a b : LabeledPrimaryArrangement) :
    CyclicallyEquivalent a b ↔
      AddAction.orbitRel AlphaCDPrimarySite LabeledPrimaryArrangement a b := by
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨offset, h⟩
    refine ⟨-offset, ?_⟩
    apply Equiv.ext
    intro site
    change b (site + -offset) = a site
    rw [h (site + -offset)]
    simp [rotatePosition, add_assoc]
  · rintro ⟨offset, h⟩
    refine ⟨-offset, ?_⟩
    intro site
    have hs := congrArg
      (fun arrangement : LabeledPrimaryArrangement => arrangement (site + -offset)) h
    change b ((site + -offset) + offset) = a (site + -offset) at hs
    simpa [rotatePosition, add_assoc] using hs

/-- Cyclic rotation is an equivalence relation on labeled placements. -/
def cyclicRotationSetoid : Setoid LabeledPrimaryArrangement where
  r := CyclicallyEquivalent
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      refine ⟨0, ?_⟩
      intro site
      simp [rotatePosition]
    · intro a b hab
      exact (cyclicallyEquivalent_iff_orbitRel b a).2 <|
        Setoid.symm' (AddAction.orbitRel
          AlphaCDPrimarySite LabeledPrimaryArrangement) <|
          (cyclicallyEquivalent_iff_orbitRel a b).1 hab
    · intro a b c hab hbc
      exact (cyclicallyEquivalent_iff_orbitRel a c).2 <|
        Setoid.trans' (AddAction.orbitRel
          AlphaCDPrimarySite LabeledPrimaryArrangement)
          ((cyclicallyEquivalent_iff_orbitRel a b).1 hab)
          ((cyclicallyEquivalent_iff_orbitRel b c).1 hbc)

/-- The source-level arrangements: labeled placements modulo choice of the
starting glucose unit. -/
abbrev CyclicPrimaryArrangement :=
  Quotient cyclicRotationSetoid

/-- The quotient used in the statement is canonically the orbit quotient for
the cyclic offset action. -/
noncomputable def cyclicPrimaryArrangementEquivOrbit :
    CyclicPrimaryArrangement ≃
      Quotient (AddAction.orbitRel
        AlphaCDPrimarySite LabeledPrimaryArrangement) :=
  Quotient.congrRight fun a b => cyclicallyEquivalent_iff_orbitRel a b

/-- No nonzero cyclic offset fixes a labeled placement: evaluating a fixed
placement at site zero and using injectivity recovers the offset. -/
theorem cyclicAddAction_stabilizer_eq_bot
    (a : LabeledPrimaryArrangement) :
    AddAction.stabilizer AlphaCDPrimarySite a = ⊥ := by
  apply le_antisymm
  · intro offset hoffset
    have haction : offset +ᵥ a = a :=
      (AddAction.mem_stabilizer_iff).1 hoffset
    have hzero : rotateArrangement offset a 0 = a 0 :=
      congrArg
        (fun arrangement : LabeledPrimaryArrangement => arrangement 0) haction
    have hoffset_zero : offset = 0 :=
      a.injective (by simpa [rotatePosition] using hzero)
    simp [hoffset_zero]
  · exact bot_le

noncomputable instance cyclicPrimaryArrangementFintype :
    Fintype CyclicPrimaryArrangement :=
  Fintype.ofFinite CyclicPrimaryArrangement

/-- The exact, unrounded output carrier requested in T9-A9. -/
noncomputable def arrangementCount : ℕ :=
  Fintype.card CyclicPrimaryArrangement

/-- Source carrier: the α-CD template has exactly six eligible primary sites. -/
theorem alphaCDPrimarySite_card :
    Fintype.card AlphaCDPrimarySite = 6 := by
  simp [AlphaCDPrimarySite]

/-- Source carrier: hexadifferentiation supplies six distinct group labels. -/
theorem functionalGroupLabel_card :
    Fintype.card FunctionalGroupLabel = 6 := by
  simp [FunctionalGroupLabel]

/-- All labeled placements are permutations, hence are counted by `6!`. -/
theorem labeledPrimaryArrangement_card :
    Fintype.card LabeledPrimaryArrangement = Nat.factorial 6 := by
  simpa [LabeledPrimaryArrangement, AlphaCDPrimarySite,
    FunctionalGroupLabel] using
    (Fintype.card_equiv (Equiv.refl (Fin 6)))

/-- Because all six labels are distinct, the rotation action is free.  Thus
each quotient class has six labeled representatives. -/
theorem cyclicClass_cardinality_ledger :
    arrangementCount * 6 = Fintype.card LabeledPrimaryArrangement := by
  classical
  letI : Fintype
      (Quotient (AddAction.orbitRel
        AlphaCDPrimarySite LabeledPrimaryArrangement)) :=
    Fintype.ofFinite _
  have hdecomposition :
      Fintype.card LabeledPrimaryArrangement =
        Fintype.card
            (Quotient (AddAction.orbitRel
              AlphaCDPrimarySite LabeledPrimaryArrangement)) *
          Fintype.card AlphaCDPrimarySite := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr <|
      AddAction.selfEquivOrbitsQuotientProd
        (α := AlphaCDPrimarySite) (β := LabeledPrimaryArrangement)
        cyclicAddAction_stabilizer_eq_bot
  have hquotient :
      arrangementCount =
        Fintype.card
          (Quotient (AddAction.orbitRel
            AlphaCDPrimarySite LabeledPrimaryArrangement)) := by
    unfold arrangementCount
    exact Fintype.card_congr cyclicPrimaryArrangementEquivOrbit
  calc
    arrangementCount * 6 =
        Fintype.card
            (Quotient (AddAction.orbitRel
              AlphaCDPrimarySite LabeledPrimaryArrangement)) *
          Fintype.card AlphaCDPrimarySite := by
            rw [hquotient, alphaCDPrimarySite_card]
    _ = Fintype.card LabeledPrimaryArrangement := hdecomposition.symm

/-- Dividing the `6!` labeled placements into the six-element rotation classes
leaves `5!` oriented cyclic arrangements. -/
theorem arrangementCount_eq_factorial_five :
    arrangementCount = Nat.factorial 5 := by
  refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6) ?_
  calc
    arrangementCount * 6 = Fintype.card LabeledPrimaryArrangement :=
      cyclicClass_cardinality_ledger
    _ = Nat.factorial 6 := labeledPrimaryArrangement_card
    _ = Nat.factorial 5 * 6 := by norm_num [Nat.factorial]

/-- Raw answer-blind result proposition.  It records the source cardinalities,
the permutation ledger, the rotation-orbit ledger, and the un-evaluated
factorial result. -/
def RawArrangementResult : Prop :=
  Fintype.card AlphaCDPrimarySite = 6 ∧
    Fintype.card FunctionalGroupLabel = 6 ∧
    Fintype.card LabeledPrimaryArrangement = Nat.factorial 6 ∧
    arrangementCount * 6 = Nat.factorial 6 ∧
    arrangementCount = Nat.factorial 5

theorem rawArrangementResult : RawArrangementResult := by
  exact ⟨alphaCDPrimarySite_card, functionalGroupLabel_card,
    labeledPrimaryArrangement_card,
    cyclicClass_cardinality_ledger.trans labeledPrimaryArrangement_card,
    arrangementCount_eq_factorial_five⟩

/-- Exact-integer reporting proposition for the sole requested output. -/
def ReportedArrangementResult : Prop :=
  arrangementCount = 120

theorem reportedArrangementResult : ReportedArrangementResult := by
  unfold ReportedArrangementResult
  rw [arrangementCount_eq_factorial_five]
  norm_num [Nat.factorial]

/-- Hash-bound solve-phase contract for the raw result carrier. -/
theorem rawResultContract :
    ("1b363153f9d31ff45598d149fd3f19007d4dd6535fbc8f85d592801f86d9736b" : String) =
        "1b363153f9d31ff45598d149fd3f19007d4dd6535fbc8f85d592801f86d9736b" ∧
      IChO2026Problems.T9A9.RawArrangementResult := by
  exact ⟨rfl, rawArrangementResult⟩

/-- Hash-bound solve-phase contract for the exact displayed integer. -/
theorem reportedResultContract :
    ("87599e9efc51370b5d2e9912c579a1c4908421f31aaa034147aef715647263bc" : String) =
        "87599e9efc51370b5d2e9912c579a1c4908421f31aaa034147aef715647263bc" ∧
      IChO2026Problems.T9A9.ReportedArrangementResult := by
  exact ⟨rfl, reportedArrangementResult⟩

end IChO2026Problems.T9A9
