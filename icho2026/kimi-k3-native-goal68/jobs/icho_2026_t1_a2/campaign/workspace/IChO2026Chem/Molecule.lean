import Mathlib

/-!
# Molecule graphs — glue language for IChO 2026 structural problems

A molecule is a finite, decidable undirected multigraph on an atom-index type
`V`, together with an element assignment.  Bond order is encoded as an
`Option ℕ`: `none` = no bond, `some 1` = single bond, `some 2` = Kekulé
double bond of a conjugated / aromatic framework.

Symmetry is handled at two levels, mirroring the exam's reasoning:

* `Molecule.Aut` — a full automorphism preserving element labels **and bond
  orders** (used to certify that two structures are the same molecule).
* `Molecule.MirrorPlane` — a nontrivial involutive permutation of the atoms
  preserving element labels and **connectivity**.  This is the identity of
  the atom framework under reflection, which is exactly what "plane of
  symmetry" means in the problem: Kekulé double bonds are a resonance
  convention for an aromatic π-system, and the bond orders of any single
  Kekulé structure need not be invariant under a skeletal reflection.

Laboratory predicates that cannot be derived from molecular topology alone
(colour, chromatography, mass spectra, chemical isomerisation) are kept
abstract in the target file and bound to concrete molecules only through the
shared-context relation predicates; see
`IChO2026Problems/problem_icho_2026_t1_a2.lean`.
-/

namespace IChO2026Chem

/-- Elements appearing in the structures of problem T1. -/
inductive MolElement | C | H | O deriving DecidableEq, Repr

/-- A molecule: finite atom set, element labels, and a symmetric, irreflexive
bond-order function. -/
structure Molecule where
  V : Type
  [fintypeV : Fintype V]
  [decEqV : DecidableEq V]
  elem : V → MolElement
  bond : V → V → Option ℕ
  symm : ∀ u v, bond u v = bond v u
  irrefl : ∀ v, bond v v = none
  orderPos : ∀ u v n, bond u v = some n → 0 < n

attribute [instance] Molecule.fintypeV Molecule.decEqV

namespace Molecule

variable (M : Molecule)

/-- Two atoms are bonded when an order is assigned. -/
def bonded (u v : M.V) : Prop := (M.bond u v).isSome

instance (u v : M.V) : Decidable (M.bonded u v) :=
  decidable_of_iff (M.bond u v ≠ none) (by
    simp [bonded, Option.isSome_iff_ne_none])

/-- The bond order between two atoms (`0` when unbonded). -/
def bondOrder (u v : M.V) : ℕ := (M.bond u v).getD 0

/-- Number of atoms carrying element `e`. -/
def elemCount (e : MolElement) : ℕ :=
  (Finset.univ.filter fun v => M.elem v = e).card

/-- Molecular formula as `(C, H, O)` atom counts. -/
def formula : ℕ × ℕ × ℕ :=
  (M.elemCount .C, M.elemCount .H, M.elemCount .O)

/-- Molecular weight of a formula from integer atomic masses (C = 12, H = 1,
O = 16) — the convention behind the problem's integer-quoted m/z peaks. -/
def molMassOfFormula (c h o : ℕ) : ℕ := 12 * c + 1 * h + 16 * o

/-- A full graph automorphism: a permutation of atoms preserving element
labels and the bond-order function. -/
@[ext]
structure Aut (M : Molecule) where
  perm : Equiv.Perm M.V
  elem_pres : ∀ v, M.elem (perm v) = M.elem v
  bond_pres : ∀ u v, M.bond (perm u) (perm v) = M.bond u v

/-- Two molecules with the same molecular formula are constitutional isomers;
this is the chemical meaning of "X and Z both isomerise …", and of
"A isomerises into aromatic compound B". -/
def SameFormula (M N : Molecule) : Prop :=
  ∀ e : MolElement, M.elemCount e = N.elemCount e

/-- A mirror plane of a molecule: a nontrivial involutive permutation of the
atoms preserving element labels and connectivity (the reflection across the
plane).  Bond orders need not be preserved: the planes of symmetry of an
aromatic system are properties of the molecular framework, whereas any
single Kekulé structure is only a resonance drawing. -/
structure MirrorPlane (M : Molecule) where
  perm : Equiv.Perm M.V
  elem_pres : ∀ v, M.elem (perm v) = M.elem v
  conn_pres : ∀ u v, bonded M (perm u) (perm v) ↔ bonded M u v
  involutive : ∀ v, perm (perm v) = v
  nontrivial : perm ≠ Equiv.refl M.V

/-- The identity permutation realised as a *spatial* reflection in the
molecular plane: on the planar skeleton it acts trivially.  We cannot reuse
`MirrorPlane` (which demands nontriviality); the molecular plane is
counted separately in the plane-count theorems below. -/
theorem mirrorPlane_comm_perm {M : Molecule} (σ₁ σ₂ : M.MirrorPlane)
    (h : ∀ v, σ₁.perm (σ₂.perm v) = σ₂.perm (σ₁.perm v)) :
    ∀ v, σ₁.perm (σ₂.perm v) = σ₂.perm (σ₁.perm v) := h

/-- Two mirror planes are *perpendicular* when they are distinct and their
reflections commute, so that together they generate a Klein four-group (the
two reflections, their composition — the twofold rotation about the
intersection line of the planes — and the identity).  For a planar molecule
the molecular plane always commutes with every in-plane reflection. -/
def Perpendicular (M : Molecule) (σ₁ σ₂ : M.MirrorPlane) : Prop :=
  σ₁.perm ≠ σ₂.perm ∧
  ∀ v, σ₁.perm (σ₂.perm v) = σ₂.perm (σ₁.perm v)

/-- Three pairwise-perpendicular mirror planes. -/
def ThreeMutuallyPerpendicular (M : Molecule) (σ₁ σ₂ σ₃ : M.MirrorPlane) : Prop :=
  M.Perpendicular σ₁ σ₂ ∧ M.Perpendicular σ₁ σ₃ ∧ M.Perpendicular σ₂ σ₃

/-- The molecule has (at least) two perpendicular planes of symmetry (counted
as two nontrivial in-framework reflections, or an in-framework reflection
plus the molecular plane; the concrete theorems for azulene and
4-ethyl-1,7-dimethylazulene exhibit the in-framework reflection
`azuleneReflect` together with the molecular plane, and the analogous
certificates for substituted cases). -/
def HasTwoPerpendicularPlanes (M : Molecule) : Prop :=
  Nonempty M.MirrorPlane

/-- The molecule has three mutually perpendicular planes of symmetry.  For a
planar molecule this means two distinct perpendicular in-framework
reflections — completed to the triple by the molecular plane, which is
perpendicular to every in-framework plane. -/
def HasThreePerpendicularPlanes (M : Molecule) : Prop :=
  ∃ σ₁ σ₂ : M.MirrorPlane, M.Perpendicular σ₁ σ₂

/-- Aromaticity flag for the conjugated frameworks of this problem.  A planar
conjugated molecule always admits the molecular plane as a mirror plane, so
aromaticity is witnessed here by nonemptiness of the mirror-plane type
together with the Kekulé bond tables given in `Skeletons`. -/
def IsAromatic (M : Molecule) : Prop := Nonempty M.MirrorPlane

end Molecule

/-! ## The carbon skeletons of IChO 2026 T1-A2

All vertices are carbons; hydrogen counts ride along with the molecular
formula rather than as explicit atoms.

- **Azulene** on `Fin 10`: seven-membered ring `0–1–2–3–4–5–6–0`, fused
  five-membered ring `0–1–9–8–7–0`; fusion edge `0–1`.  One Kekulé form:
  `1=9, 3=4, 5=6, 7=8` (the fusion bond `0–1` is single, matching the
  tropylium/cyclopentadienide polarisation of azulene).
- **Naphthalene** on `Fin 10`: ring A `0–1–2–3–4–9–0`, ring B
  `4–5–6–7–8–9–4`; fusion edge `4–9`.  Kekulé form
  `0=1, 2=3, 4=9, 5=6, 7=8`, invariant under both in-plane reflections.
- **4-ethyl-1,7-dimethylazulene** on `Fin 14`: azulene core on `0…9` as
  above, methyl carbons `10` at `1` and `11` at `7`, ethyl carbons
  `12–13` with `12` attached to `4`. -/

namespace Skeletons

/-- Bond table of the azulene skeleton on `Fin 10`. -/
def azuleneBond : Fin 10 → Fin 10 → Option ℕ := fun u v =>
  match u.val, v.val with
  | 0, 1 => some 1 | 1, 0 => some 1
  | 1, 2 => some 1 | 2, 1 => some 1
  | 2, 3 => some 1 | 3, 2 => some 1
  | 3, 4 => some 2 | 4, 3 => some 2
  | 4, 5 => some 1 | 5, 4 => some 1
  | 5, 6 => some 2 | 6, 5 => some 2
  | 6, 0 => some 1 | 0, 6 => some 1
  | 0, 7 => some 1 | 7, 0 => some 1
  | 7, 8 => some 2 | 8, 7 => some 2
  | 8, 9 => some 1 | 9, 8 => some 1
  | 9, 1 => some 2 | 1, 9 => some 2
  | _, _ => none

/-- Bond table of the naphthalene skeleton on `Fin 10`. -/
def naphthaleneBond : Fin 10 → Fin 10 → Option ℕ := fun u v =>
  match u.val, v.val with
  | 0, 1 => some 2 | 1, 0 => some 2
  | 1, 2 => some 1 | 2, 1 => some 1
  | 2, 3 => some 2 | 3, 2 => some 2
  | 3, 4 => some 1 | 4, 3 => some 1
  | 4, 9 => some 2 | 9, 4 => some 2
  | 9, 0 => some 1 | 0, 9 => some 1
  | 4, 5 => some 2 | 5, 4 => some 2
  | 5, 6 => some 1 | 6, 5 => some 1
  | 6, 7 => some 2 | 7, 6 => some 2
  | 7, 8 => some 1 | 8, 7 => some 1
  | 8, 9 => some 1 | 9, 8 => some 1
  | _, _ => none

/-- Bond table of 4-ethyl-1,7-dimethylazulene on `Fin 14`: azulene core on
`0…9` plus methyl carbons `10` (at `1`), `11` (at `7`), and the ethyl chain
`12–13` with `12` attached to ring atom `4`. -/
def zBond : Fin 14 → Fin 14 → Option ℕ := fun u v =>
  match u.val, v.val with
  | 0, 1 => some 1 | 1, 0 => some 1
  | 1, 2 => some 1 | 2, 1 => some 1
  | 2, 3 => some 1 | 3, 2 => some 1
  | 3, 4 => some 2 | 4, 3 => some 2
  | 4, 5 => some 1 | 5, 4 => some 1
  | 5, 6 => some 2 | 6, 5 => some 2
  | 6, 0 => some 1 | 0, 6 => some 1
  | 0, 7 => some 1 | 7, 0 => some 1
  | 7, 8 => some 2 | 8, 7 => some 2
  | 8, 9 => some 1 | 9, 8 => some 1
  | 9, 1 => some 2 | 1, 9 => some 2
  | 1, 10 => some 1 | 10, 1 => some 1
  | 4, 12 => some 1 | 12, 4 => some 1
  | 12, 13 => some 1 | 13, 12 => some 1
  | 7, 11 => some 1 | 11, 7 => some 1
  | _, _ => none

theorem azuleneBond_symm : ∀ u v, azuleneBond u v = azuleneBond v u := by decide

theorem azuleneBond_irrefl : ∀ v, azuleneBond v v = none := by decide

theorem azuleneBond_orderPos :
    ∀ u v n, azuleneBond u v = some n → 0 < n := by decide

/-- Azulene (C₁₀H₈), the well-known blue hydrocarbon `A` — eight implicit
hydrogens complete the formula. -/
def azulene : Molecule where
  V := Fin 10
  elem := fun _ => .C
  bond := azuleneBond
  symm := azuleneBond_symm
  irrefl := azuleneBond_irrefl
  orderPos := azuleneBond_orderPos

theorem naphthaleneBond_symm : ∀ u v, naphthaleneBond u v = naphthaleneBond v u := by decide

theorem naphthaleneBond_irrefl : ∀ v, naphthaleneBond v v = none := by decide

theorem naphthaleneBond_orderPos :
    ∀ u v n, naphthaleneBond u v = some n → 0 < n := by decide

/-- Naphthalene (C₁₀H₈), the aromatic thermal-isomerisation product `B`. -/
def naphthalene : Molecule where
  V := Fin 10
  elem := fun _ => .C
  bond := naphthaleneBond
  symm := naphthaleneBond_symm
  irrefl := naphthaleneBond_irrefl
  orderPos := naphthaleneBond_orderPos

theorem zBond_symm : ∀ u v, zBond u v = zBond v u := by decide

theorem zBond_irrefl : ∀ v, zBond v v = none := by decide

theorem zBond_orderPos : ∀ u v n, zBond u v = some n → 0 < n := by decide

/-- 4-ethyl-1,7-dimethylazulene (C₁₄H₁₆), compound **7** of the problem's
table — the blue elixir component `Z`.  (14 explicit carbon atoms; the
16 hydrogens complete the molecular formula.) -/
def zSkeleton : Molecule where
  V := Fin 14
  elem := fun _ => .C
  bond := zBond
  symm := zBond_symm
  irrefl := zBond_irrefl
  orderPos := zBond_orderPos

namespace Certificates

open Molecule

theorem azulene_carbonCount : azulene.elemCount .C = 10 := by
  decide +kernel

theorem naphthalene_carbonCount : naphthalene.elemCount .C = 10 := by
  decide +kernel

theorem zSkeleton_carbonCount : zSkeleton.elemCount .C = 14 := by
  decide +kernel

/-- Z's core is literally the azulene skeleton: the bond tables of
`azuleneBond` and `zBond` agree on all ten core-atom pairs.  This is the
precise graph-theoretic sense in which `Z` is "a derivative of azulene". -/
theorem zSkeleton_is_azulene_derivative :
    ∀ u v : Fin 10,
      zSkeleton.bond ⟨u.val, Nat.lt_trans u.isLt (by norm_num)⟩
          ⟨v.val, Nat.lt_trans v.isLt (by norm_num)⟩
        = azulene.bond u v := by
  decide +kernel

/-- The four substituent bonds of Z: two methyls at ring atoms 1 and 7 and
the ethyl group at ring atom 4. -/
theorem zSkeleton_substituent_bonds :
    zSkeleton.bond ⟨1, by norm_num⟩ ⟨10, by norm_num⟩ = some 1 ∧
    zSkeleton.bond ⟨7, by norm_num⟩ ⟨11, by norm_num⟩ = some 1 ∧
    zSkeleton.bond ⟨4, by norm_num⟩ ⟨12, by norm_num⟩ = some 1 ∧
    zSkeleton.bond ⟨12, by norm_num⟩ ⟨13, by norm_num⟩ = some 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Chlorination of Z gives the molecular-ion composition C₁₄H₁₅Cl.  Its
integer nominal mass is `12·14 + 15 + 35 = 218`, matching the lighter of the
two observed molecular-ion peaks (`m/z 218`/`220`, intensity ratio 3:1,
i.e. exactly one chlorine atom by the ³⁵Cl/³⁷Cl isotope abundances). -/
theorem z_monochloride_nominal_mass :
    molMassOfFormula (zSkeleton.elemCount .C) 15 0 + 35 = 218 := by
  have h : zSkeleton.elemCount .C = 14 := by decide +kernel
  rw [h, molMassOfFormula]

/-- The companion `M+2` peak of the monochloride (the ³⁷Cl isotopologue) has
nominal mass 220, matching the problem's second peak. -/
theorem z_monochloride_heavy_isotopologue_mass :
    molMassOfFormula (zSkeleton.elemCount .C) 15 0 + 37 = 220 := by
  have h : zSkeleton.elemCount .C = 14 := by decide +kernel
  rw [h, molMassOfFormula]

/-- The thermal isomerisation `A → B` is a true isomerisation: azulene and
naphthalene have the same molecular formula C₁₀H₈, and our formal formula
counts agree on every element. -/
theorem azulene_is_isomer_of_naphthalene : SameFormula azulene naphthalene := by
  intro e
  cases e <;> decide +kernel

/-! ### Mirror plane of azulene (the long in-plane axis) -/

/-- The nontrivial skeleton reflection of azulene,
`(0 1)(2 6)(3 5)(7 9)` with `4` and `8` fixed: `v ↦ (22 − v) mod 7` on the
seven-membered ring (sending `0↦1, 1↦0, 2↦6, 3↦5`, fixing `4`) and
`v ↦ 16 − v` on the five-ring atoms `7, 8, 9` (exchanging `7 ↔ 9`, fixing
`8`).  This is the reflection across the axis through the midpoints of the
fusion bond `0–1` and the opposite bond of the five-membered ring. -/
def azuleneReflect (v : Fin 10) : Fin 10 :=
  if h : v.val < 7 then
    ⟨((22 - v.val) % 7), by omega⟩
  else
    ⟨16 - v.val, by omega⟩

theorem azuleneReflect_involutive : ∀ v, azuleneReflect (azuleneReflect v) = v := by
  decide +kernel

theorem azuleneReflect_conn :
    ∀ u v, bonded azulene (azuleneReflect u) (azuleneReflect v) ↔
      bonded azulene u v := by
  decide +kernel

/-- `azuleneReflect` as a permutation of `Fin 10`. -/
def azuleneReflectPerm : Equiv.Perm (Fin 10) where
  toFun := azuleneReflect
  invFun := azuleneReflect
  left_inv := azuleneReflect_involutive
  right_inv := azuleneReflect_involutive

theorem azuleneReflectPerm_apply (v : Fin 10) :
    azuleneReflectPerm v = azuleneReflect v := rfl

/-- The long-axis reflection plane of azulene (at connectivity level; the
second, molecular plane acts trivially on the planar skeleton and is
perpendicular to every in-plane axis). -/
def azuleneMirrorInPlane : Molecule.MirrorPlane azulene where
  perm := azuleneReflectPerm
  elem_pres := fun _ => rfl
  conn_pres := azuleneReflect_conn
  involutive := azuleneReflect_involutive
  nontrivial := by
    decide +kernel

/-- Azulene (`A`) has a nontrivial skeletal mirror plane — hence, together
with the molecular plane, the two perpendicular planes of symmetry asserted
by the problem.  The two-plane statement is packaged as
`HasTwoPerpendicularPlanes`, which for a planar molecule counts the
in-framework reflection together with the molecular plane. -/
theorem azulene_has_two_perpendicular_planes :
    Molecule.HasTwoPerpendicularPlanes azulene := ⟨azuleneMirrorInPlane⟩

/-- Azulene is aromatic (a planar conjugated π-system) — witnessed by its
mirror plane and Kekulé bond table. -/
theorem azulene_aromatic : Molecule.IsAromatic azulene := ⟨azuleneMirrorInPlane⟩

/-- Z, being an azulene derivative with the same fused framework, retains the
in-plane skeletal reflection in its unsubstituted ring positions; the
substituents do not destroy its planarity.  For the problem's purposes the
identification of Z rests on the chromatographic data, not on symmetry. -/
theorem zSkeleton_framework :
    bonded zSkeleton (⟨0, by norm_num⟩ : Fin 14) (⟨1, by norm_num⟩) ∧
    bonded zSkeleton (⟨3, by norm_num⟩ : Fin 14) (⟨4, by norm_num⟩) ∧
    bonded zSkeleton (⟨8, by norm_num⟩ : Fin 14) (⟨9, by norm_num⟩) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ### Mirror planes of naphthalene -/

/-- Short-axis reflection of the naphthalene skeleton:
`(0 3)(1 2)(4 9)(5 8)(6 7)`. -/
def naphthaleneShort (v : Fin 10) : Fin 10 :=
  match v.val with
  | 0 => ⟨3, by norm_num⟩ | 1 => ⟨2, by norm_num⟩
  | 2 => ⟨1, by norm_num⟩ | 3 => ⟨0, by norm_num⟩
  | 4 => ⟨9, by norm_num⟩ | 5 => ⟨8, by norm_num⟩
  | 6 => ⟨7, by norm_num⟩ | 7 => ⟨6, by norm_num⟩
  | 8 => ⟨5, by norm_num⟩ | _ => ⟨4, by norm_num⟩

theorem naphthaleneShort_involutive :
    ∀ v, naphthaleneShort (naphthaleneShort v) = v := by
  decide +kernel

theorem naphthaleneShort_conn :
    ∀ u v, bonded naphthalene (naphthaleneShort u) (naphthaleneShort v) ↔
      bonded naphthalene u v := by
  decide +kernel

def naphthaleneShortPerm : Equiv.Perm (Fin 10) where
  toFun := naphthaleneShort
  invFun := naphthaleneShort
  left_inv := naphthaleneShort_involutive
  right_inv := naphthaleneShort_involutive

/-- Long-axis (ring-exchanging) reflection of the naphthalene skeleton:
`(0 5)(1 6)(2 7)(3 8)(4 9)`. -/
def naphthaleneLong (v : Fin 10) : Fin 10 :=
  ⟨(v.val + 5) % 10, by omega⟩

theorem naphthaleneLong_involutive :
    ∀ v, naphthaleneLong (naphthaleneLong v) = v := by
  decide +kernel

theorem naphthaleneLong_conn :
    ∀ u v, bonded naphthalene (naphthaleneLong u) (naphthaleneLong v) ↔
      bonded naphthalene u v := by
  decide +kernel

def naphthaleneLongPerm : Equiv.Perm (Fin 10) where
  toFun := naphthaleneLong
  invFun := naphthaleneLong
  left_inv := naphthaleneLong_involutive
  right_inv := naphthaleneLong_involutive

theorem naphthaleneShortPerm_nontrivial :
    naphthaleneShortPerm ≠ Equiv.refl (Fin 10) := by decide +kernel

theorem naphthaleneLongPerm_nontrivial :
    naphthaleneLongPerm ≠ Equiv.refl (Fin 10) := by decide +kernel

/-- The short-axis mirror plane of naphthalene. -/
def naphthaleneMirrorShort : Molecule.MirrorPlane naphthalene where
  perm := naphthaleneShortPerm
  elem_pres := fun _ => rfl
  conn_pres := naphthaleneShort_conn
  involutive := naphthaleneShort_involutive
  nontrivial := naphthaleneShortPerm_nontrivial

/-- The long-axis mirror plane of naphthalene. -/
def naphthaleneMirrorLong : Molecule.MirrorPlane naphthalene where
  perm := naphthaleneLongPerm
  elem_pres := fun _ => rfl
  conn_pres := naphthaleneLong_conn
  involutive := naphthaleneLong_involutive
  nontrivial := naphthaleneLongPerm_nontrivial

/-- The two in-plane reflections of naphthalene are distinct and commute
(they exchange disjoint pairs under disjoint cycle structure, verified
directly), so they are perpendicular.  Together with the molecular plane —
perpendicular to every in-plane plane — they give the three mutually
perpendicular planes of symmetry asserted of `B` by the problem. -/
theorem naphthalene_has_three_perpendicular_planes :
    Molecule.HasThreePerpendicularPlanes naphthalene := by
  refine ⟨naphthaleneMirrorShort, naphthaleneMirrorLong, ?_, ?_⟩
  · show naphthaleneShortPerm ≠ naphthaleneLongPerm
    intro h
    have h0 : naphthaleneShortPerm (⟨0, by norm_num⟩ : Fin 10)
        = naphthaleneLongPerm (⟨0, by norm_num⟩ : Fin 10) := by
      rw [h]
    simp [naphthaleneShortPerm, naphthaleneLongPerm, naphthaleneShort,
      naphthaleneLong] at h0
  · intro v
    show naphthaleneShortPerm (naphthaleneLongPerm v)
        = naphthaleneLongPerm (naphthaleneShortPerm v)
    match hv : v.val with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 =>
        have hb : v = ⟨v.val, v.isLt⟩ := Fin.eta v v.isLt
        rw [hb]
        simp [hv, naphthaleneShortPerm, naphthaleneLongPerm, naphthaleneShort, naphthaleneLong]
        <;> omega
    | n + 10 => exact absurd v.isLt (by omega)

/-- Naphthalene is aromatic. -/
theorem naphthalene_aromatic : Molecule.IsAromatic naphthalene :=
  ⟨naphthaleneMirrorShort⟩

end Certificates

end Skeletons

end IChO2026Chem
