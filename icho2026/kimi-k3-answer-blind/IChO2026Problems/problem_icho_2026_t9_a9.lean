/-
Copyright (c) 2026 Archon answer-blind IChO formalization project. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon chemistry-formalize agent
-/
import IChO2026Chem

/-!
# IChO 2026, Problem T9, subquestion 9.9 (target `icho_2026_t9_a9`)

**Problem.** (Sealed problem bundle: T9 page 5, question 9.9, with the shared context
of T9 pages 1–4.) α-Cyclodextrin (α-CD) is the cyclic α(1→4)-linked hexasaccharide of
α-D-glucopyranose: 6 glucopyranose units, hence 6 primary (C6) `CH2OH` groups and 12
secondary hydroxy groups — the T9 page 4 template for intermediate **N** draws six
numbered boxes (units 1–6) for the primary substituents around the ring and one
`(OBn)12` box for the secondary rim. A *hexadifferentiated* α-CD (compound **S** of
question 9.8) carries six *different* functional groups, one at each unit's primary
`CH2OH` position; question 9.9 stipulates that only the `CH2OH` groups have been
modified, so the six primary positions are the only sites that can differ between
units.

**Requested output.** `arrangement_count`: the number of all possible arrangements of
the functional groups on a hexadifferentiated α-CD (exact integer).

**Derivation.**
(i) *Positions and groups.* There are six primary sites on the macrocycle and six
distinct functional groups; an arrangement is a bijection from sites to groups,
giving `6! = 720` raw assignments (`card_arrangement`).
(ii) *Symmetry of the macrocycle.* The α(1→4)-linked all-D-glucose ring is chiral and
its two rims are inequivalent (the modified primary `CH2OH` rim versus the unmodified
secondary `OH` rim), so the symmetry group acting on the six sites is the cyclic
group `C₆` of rotations; reflections are *not* symmetries — a reflection would invert
every glucose stereocentre and interchange the two rims. (Consistent with the
directed templates of T9 page 4, where clockwise and counterclockwise modifications
are distinguished.) Two assignments therefore describe the same molecule iff they
differ by a rotation (`SameOrbit`, `arrangementSetoid`).
(iii) *Free action and count.* Because all six groups are distinct, no nontrivial
rotation fixes an assignment: a rotation fixing a bijection fixes every site, hence
is zero (`Arrangement.rotate_eq_self_iff`). Every orbit has exactly 6 elements, so
the number of arrangements is `720 / 6 = 120`. Equivalently, every rotation orbit
contains exactly one arrangement with group 0 at site 0 (`quotientEquivFixedZero`),
and those normal forms are counted fiberwise: `720 = 6 · (count of normal forms)`,
whence `120` (`card_fixedZero`, `arrangementCount_eq`).

No atomic weights or empirical-registry bridges are needed; the count follows from
the problem-stated six α-D-glucopyranose units (shared context), the
hexadifferentiation hypothesis (six distinct groups at the six primary positions,
question text), and the chirality of the α(1→4)-linked D-glucose ring (trusted
general law: the symmetry group of a homochiral cyclic oligosaccharide acting on its
primary positions is the cyclic rotation group).
-/

namespace IChO2026Problems.Icho2026T9A9

/-! ## The α-CD macrocycle as a directed 6-site ring -/

/-- Primary-site (C6 `CH2OH`) positions on the α-CD macrocycle. α-CD has 6
α-D-glucopyranose units (shared problem context) joined by α(1→4)-glycosidic bonds,
so the primary sites form a directed 6-cycle: translations `x ↦ x + t` are exactly
the rotational symmetries of the macrocycle, while reflections are not symmetries
because the all-D-glucose ring is chiral and the primary/secondary rims differ.
Index `k` models printed unit `k + 1` of the T9 page 4 template. -/
abbrev Site := ZMod 6

/-- The six distinct functional groups of a hexadifferentiated α-CD (question text:
"hexadifferentiated" means six *different* groups, and only the `CH2OH` groups have
been modified). The abstract index `g : Fin 6` stands for one of the six different
groups; distinct indices denote distinct groups. -/
abbrev FunctionalGroup := Fin 6

/-- α-CD has 6 glucopyranose units (shared problem context), hence 6 primary
`CH2OH` sites. -/
theorem card_site : Fintype.card Site = 6 := ZMod.card 6

/-- A hexadifferentiated α-CD carries six distinct functional groups. -/
theorem card_functionalGroup : Fintype.card FunctionalGroup = 6 := Fintype.card_fin 6

/-! ## Arrangements and the rotational symmetry of the macrocycle -/

/-- An arrangement of the functional groups on a hexadifferentiated α-CD: a bijection
from the six primary sites to the six distinct functional groups — each unit's
`CH2OH` carries exactly one group and each group appears exactly once
(hexadifferentiation). -/
abbrev Arrangement : Type := Site ≃ FunctionalGroup

/-- Extensionality for arrangements: two arrangements agreeing at every primary
site are equal. Stated directly for `Arrangement` (rather than via the generic
`Equiv`/`Equiv.Perm` extensionality lemmas) so that the function coercions in the
hypothesis are the `Site ≃ FunctionalGroup` ones; this matters because
`ZMod 6 ≡ Fin 6` definitionally, so `Arrangement` is also definitionally an
`Equiv.Perm (ZMod 6)` and the generic `ext` lemmas can pin the coercion to the
`Equiv.Perm` spelling. -/
@[ext]
theorem Arrangement.ext {a b : Arrangement} (h : ∀ s : Site, a s = b s) : a = b :=
  Equiv.ext h

/-- Rotating the macrocycle template by `t` units: after rotation, site `s` carries
the group that was at site `s + t`. Translations by `t : ZMod 6` are exactly the
rotational symmetries of the ring. -/
def Arrangement.rotate (a : Arrangement) (t : Site) : Arrangement where
  toFun s := a (s + t)
  invFun g := a.symm g - t
  left_inv s := by simp
  right_inv g := by simp

@[simp]
theorem Arrangement.rotate_apply (a : Arrangement) (t s : Site) :
    a.rotate t s = a (s + t) := rfl

/-- Rotation by zero does nothing. -/
theorem Arrangement.rotate_zero (a : Arrangement) : a.rotate 0 = a := by
  apply Arrangement.ext
  intro s
  rw [Arrangement.rotate_apply, add_zero]

/-- Rotations compose by adding the rotation parameters. -/
theorem Arrangement.rotate_rotate (a : Arrangement) (t t' : Site) :
    (a.rotate t).rotate t' = a.rotate (t + t') := by
  apply Arrangement.ext
  intro s
  simp only [Arrangement.rotate_apply]
  congr 1
  ac_rfl

/-- The rotation action is free: a rotation that fixes an arrangement fixes every
site (the bijection can be cancelled), and is therefore zero. This is where
hexadifferentiation — all six groups distinct — enters the count. -/
theorem Arrangement.rotate_eq_self_iff (a : Arrangement) (t : Site) :
    a.rotate t = a ↔ t = 0 := by
  constructor
  · intro h
    have happ : a (0 + t) = a 0 := by
      have h2 : ∀ s : Site, a.rotate t s = a s := fun s => by rw [h]
      have h3 := h2 0
      rwa [Arrangement.rotate_apply] at h3
    have h4 : (0 : Site) + t = 0 := a.injective happ
    simpa using h4
  · rintro rfl
    exact a.rotate_zero

/-- Two arrangements describe the same molecule iff they are related by a rotation of
the macrocycle: rotations of the template are the only symmetries of the chiral
α(1→4)-linked all-D-glucose ring. -/
def SameOrbit (a b : Arrangement) : Prop := ∃ t : Site, b = a.rotate t

theorem sameOrbit_refl (a : Arrangement) : SameOrbit a a := ⟨0, (a.rotate_zero).symm⟩

theorem sameOrbit_symm {a b : Arrangement} (h : SameOrbit a b) : SameOrbit b a := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨-t, by rw [Arrangement.rotate_rotate]; simp [Arrangement.rotate_zero]⟩

theorem sameOrbit_trans {a b c : Arrangement} (hab : SameOrbit a b)
    (hbc : SameOrbit b c) : SameOrbit a c := by
  obtain ⟨t, rfl⟩ := hab
  obtain ⟨t', rfl⟩ := hbc
  exact ⟨t + t', Arrangement.rotate_rotate a t t'⟩

/-- Rotation equivalence of arrangements: the equivalence relation whose classes are
the distinct molecules. -/
def arrangementSetoid : Setoid Arrangement where
  r := SameOrbit
  iseqv := ⟨sameOrbit_refl, sameOrbit_symm, sameOrbit_trans⟩

/-- The quotient of arrangements by rotation carries a Fintype structure. Classical,
because decidability of the orbit relation is irrelevant to the count. -/
noncomputable instance arrangementQuotientFintype :
    Fintype (Quotient arrangementSetoid) := by
  classical exact Quotient.fintype arrangementSetoid

/-- The number of distinct arrangements of the six functional groups on a
hexadifferentiated α-CD: the number of rotation orbits of arrangements, i.e. the
number of equivalence classes of `SameOrbit`. -/
noncomputable def arrangementCount : ℕ := Fintype.card (Quotient arrangementSetoid)

/-! ## Raw assignment count: `6! = 720` -/

/-- There are `6! = 720` raw assignments of six distinct groups to the six primary
sites (bijections between two 6-element types). -/
theorem card_arrangement : Fintype.card Arrangement = 720 := by
  have e : Site ≃ FunctionalGroup := Fintype.equivOfCardEq (by simp [ZMod.card])
  rw [Fintype.card_equiv e, ZMod.card 6]
  rfl
/-! ## Normal forms: arrangements with group 0 at site 0 -/

/-- The rotation that brings group 0 to site 0: rotate by the site at which group 0
currently sits. -/
def normalize (a : Arrangement) : Arrangement := a.rotate (a.symm 0)

theorem normalize_def (a : Arrangement) : normalize a = a.rotate (a.symm 0) := rfl

/-- The normal form indeed places group 0 at site 0. -/
@[simp]
theorem normalize_apply_zero (a : Arrangement) : normalize a 0 = 0 := by
  rw [normalize_def, Arrangement.rotate_apply, zero_add, Equiv.apply_symm_apply]

/-- Auxiliary computation: the site where group 0 sits after rotating by `t`. -/
theorem normalize_symm_zero_of_rotate (a : Arrangement) (t : Site) :
    (a.rotate t).symm 0 = a.symm 0 - t := by
  have key : (a.rotate t) (a.symm 0 - t) = 0 := by
    rw [Arrangement.rotate_apply, sub_add_cancel, Equiv.apply_symm_apply]
  exact ((a.rotate t).apply_eq_iff_eq_symm_apply.mp key).symm

/-- Rotating an arrangement does not change its normal form: `normalize` is constant
on rotation orbits. -/
theorem normalize_rotate (a : Arrangement) (t : Site) :
    normalize (a.rotate t) = normalize a := by
  apply Arrangement.ext
  intro s
  simp only [normalize_def, Arrangement.rotate_apply, normalize_symm_zero_of_rotate]
  congr 1
  abel

/-- The molecules (rotation orbits of arrangements) are in bijection with the
arrangements that place group 0 at site 0: every orbit has a unique such
representative. Uniqueness uses freeness in the special form "the rotation bringing
group 0 to site 0 is uniquely determined". -/
def quotientEquivFixedZero :
    Quotient arrangementSetoid ≃ { a : Arrangement // a 0 = 0 } where
  toFun q := q.liftOn' (fun a => ⟨normalize a, normalize_apply_zero a⟩)
    (fun a b hab => by
      obtain ⟨t, rfl⟩ := hab
      exact Subtype.ext (normalize_rotate a t).symm)
  invFun a := Quotient.mk'' a.val
  left_inv q := by
    refine q.ind' fun a => ?_
    show Quotient.mk'' (normalize a) = Quotient.mk'' a
    rw [Quotient.eq'']
    exact ⟨-(a.symm 0), by
      rw [normalize_def, Arrangement.rotate_rotate]
      simp [Arrangement.rotate_zero]⟩
  right_inv a := by
    obtain ⟨a, h⟩ := a
    apply Subtype.ext
    show normalize a = a
    have h0 : a.symm 0 = 0 := by
      have h2 := a.symm_apply_apply 0
      rwa [h] at h2
    rw [normalize_def, h0, Arrangement.rotate_zero]

/-- The number of rotation orbits equals the number of arrangements with group 0
fixed at site 0. -/
theorem arrangementCount_eq_card_fixedZero :
    arrangementCount = Fintype.card { a : Arrangement // a 0 = 0 } :=
  Fintype.card_congr quotientEquivFixedZero

/-! ## Fiberwise count of the normal forms -/

/-- Post-composing an arrangement twice with the swap of groups `0` and `g` returns
the original arrangement. -/
theorem Arrangement.trans_swap_swap (a : Arrangement) (g : FunctionalGroup) :
    (a.trans (Equiv.swap 0 g)).trans (Equiv.swap 0 g) = a := by
  apply Arrangement.ext
  intro s
  show (Equiv.swap 0 g) ((Equiv.swap 0 g) (a s)) = a s
  exact Equiv.swap_apply_self 0 g _

/-- The fibers of the evaluation-at-site-0 map are all equivalent: postcomposition
with the swap of `0` and `g` sends fiber `g` to fiber `0`. -/
def fiberEquiv (g : FunctionalGroup) :
    { a : Arrangement // a 0 = g } ≃ { a : Arrangement // a 0 = 0 } where
  toFun a := ⟨a.val.trans (Equiv.swap 0 g), by
    show (Equiv.swap 0 g) (a.val 0) = 0
    rw [a.property]
    exact Equiv.swap_apply_right 0 g⟩
  invFun a := ⟨a.val.trans (Equiv.swap 0 g), by
    show (Equiv.swap 0 g) (a.val 0) = g
    rw [a.property]
    exact Equiv.swap_apply_left 0 g⟩
  left_inv a := Subtype.ext (Arrangement.trans_swap_swap a.val g)
  right_inv a := Subtype.ext (Arrangement.trans_swap_swap a.val g)

/-- The number of arrangements with group 0 fixed at site 0 is 120: the six fibers of
evaluation at site 0 all have the same cardinality, and `720 = 6 · 120`. Equivalently
the five remaining distinct groups can be assigned arbitrarily to the five remaining
sites: `5! = 120`. -/
theorem card_fixedZero : Fintype.card { a : Arrangement // a 0 = 0 } = 120 := by
  classical
  have key : ∀ g : FunctionalGroup,
      Fintype.card { a : Arrangement // a 0 = g } =
        Fintype.card { a : Arrangement // a 0 = 0 } :=
    fun g => Fintype.card_congr (fiberEquiv g)
  have h2 := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset Arrangement)) (t := (Finset.univ : Finset FunctionalGroup))
    (f := fun a => a 0) (fun a _ => by simp)
  rw [Finset.card_univ, card_arrangement] at h2
  rw [Finset.sum_congr rfl (fun g _ => (Fintype.card_subtype _).symm)] at h2
  rw [Finset.sum_const_nat (fun g _ => key g)] at h2
  rw [Finset.card_univ, card_functionalGroup] at h2
  omega

/-- **Main result.** The number of all possible arrangements of the functional groups
on a hexadifferentiated α-CD is exactly `120`. -/
theorem arrangementCount_eq : arrangementCount = 120 := by
  rw [arrangementCount_eq_card_fixedZero]
  exact card_fixedZero

/-! ## Raw and reported result specifications -/

/-- The raw derived quantity as a real number: the exact integer count of
arrangements, exposed as the cardinality of the rotation-orbit quotient (the
governing combinatorial relation), not as a stipulated numeral. -/
noncomputable def arrangementCountReal : ℝ := (arrangementCount : ℝ)

theorem arrangementCountReal_eq : arrangementCountReal = 120 := by
  rw [arrangementCountReal, arrangementCount_eq]
  norm_num

/-- Certified non-degenerate enclosure of the raw count: the cell `(119, 121)`
contains exactly one integer, the raw count 120. -/
theorem arrangementCountReal_interval :
    (119 : ℝ) < arrangementCountReal ∧ arrangementCountReal < 121 := by
  rw [arrangementCountReal_eq]
  exact ⟨by norm_num, by norm_num⟩

/-- Exact-integer reporting of the count on the unit lattice (reporting quantum 1;
the source reporting policy for `arrangement_count` is `exact_integer`). -/
theorem reportsAtQuantum_arrangementCount :
    IChO2026Chem.Reporting.ReportsAtQuantum arrangementCountReal 120 1 := by
  rw [arrangementCountReal_eq]
  refine ⟨one_pos, ⟨120, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num : (0 : ℝ) ≤ 120)]
  exact ⟨by norm_num, by norm_num⟩

/-- Raw derivation spec for the requested output `arrangement_count`, before any
reporting rounding: the source data (α-CD has 6 units, hence 6 primary sites; six
distinct functional groups), the governing combinatorial relation (`6! = 720` raw
assignments), freeness of the rotation action (hexadifferentiation: all groups
distinct), the orbit/normal-form bijection, the normal-form count `120`, the orbit
count `120`, and the certified non-degenerate enclosure `(119, 121)`. -/
def RawResultSpec : Prop :=
  Fintype.card Site = 6
  ∧ Fintype.card FunctionalGroup = 6
  ∧ Fintype.card Arrangement = 720
  ∧ (∀ (a : Arrangement) (t : Site), a.rotate t = a ↔ t = 0)
  ∧ Nonempty (Quotient arrangementSetoid ≃ { a : Arrangement // a 0 = 0 })
  ∧ Fintype.card { a : Arrangement // a 0 = 0 } = 120
  ∧ arrangementCount = 120
  ∧ ((119 : ℝ) < arrangementCountReal ∧ arrangementCountReal < 121)

/-- Reported (final) spec: the count reported as the exact integer 120 (integer
lattice, reporting quantum 1; `exact_integer` policy for this output), equal to the
raw count. -/
def ReportedResultSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum arrangementCountReal 120 1
  ∧ arrangementCountReal = 120
  ∧ arrangementCount = 120

/-- Raw result certificate: binds the answer-blind raw-role payload digest to
`RawResultSpec`. -/
theorem rawResultCertificate :
    ("5fee6b59d59b49a053139ffaa35c95e950cb3d6626dec301bdeb88d5fd166261" : String)
      = "5fee6b59d59b49a053139ffaa35c95e950cb3d6626dec301bdeb88d5fd166261"
      ∧ RawResultSpec :=
  ⟨rfl, card_site, card_functionalGroup, card_arrangement,
    fun a t => Arrangement.rotate_eq_self_iff a t, ⟨quotientEquivFixedZero⟩,
    card_fixedZero, arrangementCount_eq, arrangementCountReal_interval⟩

/-- Reported result certificate: binds the answer-blind reported-role payload digest
to `ReportedResultSpec`. -/
theorem reportedResultCertificate :
    ("001004f12f1b80f70995a32e16a467e209badf6dc99a3abd244ce9bbb97b9133" : String)
      = "001004f12f1b80f70995a32e16a467e209badf6dc99a3abd244ce9bbb97b9133"
      ∧ ReportedResultSpec :=
  ⟨rfl, reportsAtQuantum_arrangementCount, arrangementCountReal_eq, arrangementCount_eq⟩

end IChO2026Problems.Icho2026T9A9
