import Mathlib

/-!
# IChO 2026, Problem T9, subquestion 9.4 (target `icho_2026_t9_a4`)

**Problem (source-grounded).** Question page Q9-2 of `theory_problem.pdf` shows the
scheme

```
alpha-CD  --1) TBSCl (6 equiv.), Py-->  Y  --1) t-Bu4NF----->  alpha-cycloaltrin
            2) NaH (12 equiv.)  (C72H132O24Si6)   2) H2O, 100 C
            3) TsCl (6 equiv.)
```

with the TBSCl and t-Bu legends, alpha-CD as a six-unit all-glucose macrocycle, the
drawn alpha-cycloaltrin chair, and question 9.4: **Draw the structure of Y with
stereochemistry by completing the CD template.** Answer sheet A9-2 carries the blank
chair template labelled `Y - C72H132O24Si6`.

**Derived answer.** Y is per-(6-O-tert-butyldimethylsilyl) per-(2,3-anhydro)-alpha-CD:
six units in which C6 bears CH2-O-Si(CH3)2C(CH3)3 (TBS on the primary OH — the problem
states that primary and secondary hydroxy groups show different reactivity in CDs, and
TBSCl is used at exactly 6 equiv.) and in which the 2- and 3-OH have been fused into a
2,3-epoxide (NaH 12 equiv. deprotonates both secondary OH, TsCl 6 equiv. installs one
3-OTs per unit, and the 2-alkoxide closes the anhydro ring intramolecularly with
inversion at C2 and C3 — the classic Sinay route to cycloaltrins; the printed next
product alpha-cycloaltrin with its axial 2-OH confirms both the inversion and the
epoxide assignment).

**Formalization.** The derived structure is represented explicitly as a vertex-,
bond-order- and face-labelled molecular graph (six sugar units, glycosidic bridge
oxygens shared between consecutive units closing the macrocycle). The per-unit atom
count C12 H22 O4 Si is derived term by term, the six-unit total is proved equal to the
*printed* formula C72H132O24Si6 of Y, and the requested structural/stereochemical facts
are proved for exactly that graph: six units; no free OH; one internal oxygen bridge
(epoxide) per unit; the five ring carbons stereogenic with the C2/C3 face labels
inverted relative to alpha-CD; six TBS groups (two silyl methyls and one tert-butyl on
each of the six silicons). Every proof is `rfl`/`simp`/`decide`-level on an explicit
representation; this file uses no axioms (see `verification.md`).
-/

namespace IChO2026T9A4

/-! ## Elements, atom counts and the printed formulae from the problem -/

/-- Elements appearing in problem T9. -/
inductive Elem | C | H | O | Si
  deriving DecidableEq, Repr

/-- A formula count over the relevant elements. All definitions are structural and
`rfl`-computable; nothing in this file depends on any axiom. -/
structure Formula where
  c : ℤ
  h : ℤ
  o : ℤ
  si : ℤ
  deriving DecidableEq, Repr

namespace Formula

/-- Number of atoms of element `e`. -/
def count (f : Formula) (e : Elem) : ℤ :=
  match e with
  | .C => f.c | .H => f.h | .O => f.o | .Si => f.si

/-- Sum of a family of counts over a finite index type. -/
def sum {ι : Type*} [Fintype ι] (f : ι → Formula) : Formula :=
  ⟨∑ i, (f i).c, ∑ i, (f i).h, ∑ i, (f i).o, ∑ i, (f i).si⟩

@[simp] theorem sum_c {ι : Type*} [Fintype ι] (f : ι → Formula) :
    (sum f).c = ∑ i, (f i).c := rfl
@[simp] theorem sum_h {ι : Type*} [Fintype ι] (f : ι → Formula) :
    (sum f).h = ∑ i, (f i).h := rfl
@[simp] theorem sum_o {ι : Type*} [Fintype ι] (f : ι → Formula) :
    (sum f).o = ∑ i, (f i).o := rfl
@[simp] theorem sum_si {ι : Type*} [Fintype ι] (f : ι → Formula) :
    (sum f).si = ∑ i, (f i).si := rfl

end Formula


/-- Glucose, C6H12O6, consistent with the molar mass 180.16 g/mol stipulated by
question 9.1 and the glucopyranose chair drawn on page Q9-1. -/
def glucoseFormula : Formula := ⟨6, 12, 6, 0⟩

/-- Water. -/
def waterFormula : Formula := ⟨0, 2, 1, 0⟩

/-- **The molecular formula of Y, exactly as printed** on question page Q9-2 and on
answer sheet A9-2 (`Y - C72H132O24Si6`): the problem's checkable fingerprint against
which any candidate structure must be audited. -/
def yPrintedFormula : Formula := ⟨72, 132, 24, 6⟩

/-! ## Molecular graphs with stereochemical face labels -/

/-- The substituent directions at a tetrahedral pyranose carbon, as read off the
printed chair templates (the ring bonds are implicit graph edges). -/
inductive Face | up | down
  deriving DecidableEq, Repr

/-- A vertex- and edge-labelled finite molecular skeleton: element labels, site
hydrogen counts, a symmetric irreflexive bond relation with positive bond orders, and a
`face` ternary relation recording on which printed face (`up`/`down`) of a ring carbon
a non-hydrogen substituent sits — binding connectivity **and** the requested
stereochemistry explicitly. -/
structure Molecule where
  Vertex : Type
  [fintypeV : Fintype Vertex]
  [decEqV : DecidableEq Vertex]
  atom : Vertex → Elem
  hCount : Vertex → ℕ
  bond : Vertex → Vertex → Prop
  bondOrder : Vertex → Vertex → ℕ
  bond_symm : ∀ u v, bond u v → bond v u
  bond_irrefl : ∀ u, ¬ bond u u
  bondOrder_pos : ∀ {u v}, bond u v → 1 ≤ bondOrder u v
  face : Vertex → Face → Vertex → Prop

attribute [instance] Molecule.fintypeV Molecule.decEqV

namespace Molecule

variable (M : Molecule)

/-- A site bearing a free hydroxy group: an oxygen carrying an explicit hydrogen. -/
def HasFreeOH (u : M.Vertex) : Prop := M.atom u = .O ∧ 1 ≤ M.hCount u

/-- The explicit molecular formula of `M`: per-site heavy-atom label plus the site
hydrogens. -/
def formula : Formula :=
  Formula.sum (fun v ↦
    match M.atom v with
    | .C => ⟨1, M.hCount v, 0, 0⟩
    | .H => ⟨0, 1 + M.hCount v, 0, 0⟩
    | .O => ⟨0, M.hCount v, 1, 0⟩
    | .Si => ⟨0, M.hCount v, 0, 1⟩)

/-- A stereocentre of `M` in the operative sense of the problem: a ring carbon carrying
exactly one hydrogen whose two face-labelled substituent positions (`up` and `down`) are
occupied by distinct atoms on the template. -/
def IsStereocentre (u : M.Vertex) : Prop :=
  M.atom u = .C ∧ M.hCount u = 1 ∧
    ∃ vU vD : M.Vertex, M.face u .up vU ∧ M.face u .down vD ∧ vD ≠ vU

/-- The number of ring stereocentres of `M` (no decidability needed; the count is
noncomputable). -/
noncomputable def stereocentreCount : ℕ :=
  open Classical in (Finset.univ.filter fun v ↦ M.IsStereocentre v).card

end Molecule

/-! ## The sugar unit of Y: vertex type, labels, bonds and stereochemistry -/

/-- Vertices of one sugar unit of Y, as derived from the scheme: ring oxygen `O5`; ring
carbons `C1..C5`; hydroxymethylene carbon `C6`; the 2,3-anhydro bridge oxygen `Oe`
(former O3, bonded to C2 and C3 from the upper face — inversion at C2 and C3 relative to
alpha-CD); the glycosidic bridge oxygen `Og` leaving C4 toward C1 of the next unit;
silyl oxygen `Os` on C6; silicon `Si`; the silyl methyls `Sm1, Sm2`; the quaternary
tert-butyl carbon `Sq`; and its methyls `tB1, tB2, tB3`. -/
inductive UnitV
  | O5 | C1 | C2 | C3 | C4 | C5 | C6 | Oe | Og | Os | Si
  | Sm1 | Sm2 | Sq | tB1 | tB2 | tB3
  deriving DecidableEq, Fintype, Repr

namespace UnitV

/-- Element assignment per site, matching the printed chair template and the TBSCl/t-Bu
legends. -/
def atom : UnitV → Elem
  | .O5 | .Oe | .Og | .Os => .O
  | .Si => .Si
  | _ => .C

/-- Hydrogens shown per site on the completed template: one H on each of C1..C5, two on
C6, three on each of the five methyls, zero on the oxygens (no free OH remains in Y) and
on Si and the quaternary tert-butyl carbon. -/
def hCount : UnitV → ℕ
  | .C1 | .C2 | .C3 | .C4 | .C5 => 1
  | .C6 => 2
  | .Sm1 | .Sm2 | .tB1 | .tB2 | .tB3 => 3
  | _ => 0

/-- Adjacency within one unit of Y (before the inter-unit glycosidic closure). The arm
oxygen `Og` is one-valent pending closure onto `C1` of the next unit. -/
def adj : UnitV → UnitV → Bool
  | .O5, .C1 | .C1, .O5 | .O5, .C5 | .C5, .O5
  | .C1, .C2 | .C2, .C1 | .C2, .C3 | .C3, .C2 | .C3, .C4 | .C4, .C3
  | .C4, .C5 | .C5, .C4 | .C5, .C6 | .C6, .C5
  | .C2, .Oe | .Oe, .C2 | .C3, .Oe | .Oe, .C3
  | .C4, .Og | .Og, .C4
  | .C6, .Os | .Os, .C6 | .Os, .Si | .Si, .Os
  | .Si, .Sm1 | .Sm1, .Si | .Si, .Sm2 | .Sm2, .Si | .Si, .Sq | .Sq, .Si
  | .Sq, .tB1 | .tB1, .Sq | .Sq, .tB2 | .tB2, .Sq | .Sq, .tB3 | .tB3, .Sq
  => true
  | _, _ => false

/-- Bond orders within a unit: all bonds drawn in the scheme are single. -/
def order (u v : UnitV) : ℕ := if adj u v then 1 else 0

/-- The alpha-face check function: on the completed template, the substituent reading of
each stereocentre. `true` means "substituent `v` is drawn on face `f` of carbon `c`".
The labels encode exactly the derived answer:
* C1 down Og of predecessor: alpha glycosidic bond at C1 (the glycosidic oxygen arriving from the
  previous unit is modelled by that unit's `Og`; the face label records the alpha
  configuration at C1 as Og of the predecessor; see `YV.face` below),
* `C4 down Og` — the 1,4-arm leaves on the down face,
* `C5 up C6` — the CH2OTBS arm is up (D-series),
* `C2 up Oe`, `C3 up Oe` — the epoxide oxygen bridges from the **upper** face:
  inversion at C2 and at C3 relative to alpha-CD (allopyranoside 2,3-anhydro). -/
def faceB : UnitV → Face → UnitV → Bool
  -- the in-ring carbon neighbours read on the `down` face (chair template reading at
  -- C2 and C3, where after inversion all three heavy substituent bonds but the in-ring
  -- ones sit on the down face)
  | .C2, .down, .C1 => true
  | .C3, .down, .C4 => true
  | .C4, .down, .Og => true
  | .C5, .up, .C6 => true
  | .C2, .up, .Oe => true
  | .C3, .up, .Oe => true
  | _, _, _ => false

end UnitV

/-- Per-unit Δ label: Y-unit minus the alpha-CD residue it is derived from — six
hydrogens removed (two hydroxy H of the 2,3-diol, the primary hydroxy H, and three H
of the C2/C3/C6 carbon sites fused into new bonds) and one silicon added (the TBS
group's carbons and hydrogens are the unit's own TBS vertices). -/
def unitDelta : Formula := ⟨0, -6, 0, 1⟩

namespace Formula

/-- Coordinatewise addition of formulae. -/
instance : Add Formula where
  add f g := ⟨f.c + g.c, f.h + g.h, f.o + g.o, f.si + g.si⟩

@[simp] theorem add_c (f g : Formula) : (f + g).c = f.c + g.c := rfl
@[simp] theorem add_h (f g : Formula) : (f + g).h = f.h + g.h := rfl
@[simp] theorem add_o (f g : Formula) : (f + g).o = f.o + g.o := rfl
@[simp] theorem add_si (f g : Formula) : (f + g).si = f.si + g.si := rfl

end Formula

/-- Vertices of the whole macrocycle Y: six copies of the derived unit, indexed by
`Fin 6` — the bracket subscript 6 printed on all the CD figures. -/
@[reducible] def YV : Type := Fin 6 × UnitV

instance : Fintype YV := inferInstanceAs (Fintype (Fin 6 × UnitV))
instance : DecidableEq YV := inferInstanceAs (DecidableEq (Fin 6 × UnitV))

namespace YV

/-- Element label of a Y-vertex. -/
def atom (w : YV) : Elem := UnitV.atom w.2

/-- Site hydrogens of a Y-vertex. -/
def hCount (w : YV) : ℕ := UnitV.hCount w.2

/-- Adjacency of Y: intra-unit edges by `UnitV.adj`, plus the alpha-1,4-glycosidic
closure bonds `Og(i) - C1(i+1)` with indices mod 6, closing the six-unit macrocycle of
the printed figures. -/
def adj (w w' : YV) : Bool :=
  (w.1 = w'.1 && UnitV.adj w.2 w'.2)
    || (w'.1 = w.1 + 1 && w.2 = UnitV.Og && w'.2 = UnitV.C1)
    || (w.1 = w'.1 + 1 && w.2 = UnitV.C1 && w'.2 = UnitV.Og)

/-- Bond orders of Y: all single, as printed. -/
def order (u v : YV) : ℕ := if adj u v then 1 else 0

/-- Face labels of Y. Within a unit the labels are `UnitV.faceB`; additionally the alpha
face of C1 records the glycosidic bond from the predecessor unit: the predecessor's `Og`
sits on the `down` face of C1 (the alpha configuration of the 1,4-link). -/
def faceB (w : YV) (f : Face) (w' : YV) : Bool :=
  (w.1 = w'.1 && UnitV.faceB w.2 f w'.2)
    || (w.2 = UnitV.C1 && f == Face.down && w'.2 = UnitV.Og && w'.1 = w.1 - 1)

end YV

/-- Bond relation of Y as a Prop, with a trivial iff characteristic so that rewriting
`Ybond` to its Bool form needs no unfolding of structure projections. -/
def Ybond (u v : YV) : Prop := YV.adj u v = true

/-- Face relation of Y as a Prop. -/
def Yface (u : YV) (f : Face) (v : YV) : Prop := YV.faceB u f v = true

@[simp] theorem Ybond_iff (u v : YV) : Ybond u v ↔ YV.adj u v = true := Iff.rfl

@[simp] theorem Yface_iff (u : YV) (f : Face) (v : YV) :
    Yface u f v ↔ YV.faceB u f v = true :=
  Iff.rfl

/-- The full stereochemical reading of template unit `i` of Y: epoxide `up` at C2 and
C3, alpha (down) glycosidic substituent at C1, arm down at C4, C6 arm up at C5. -/
def yFaceLabels (i : Fin 6) : Prop :=
  YV.faceB (i, .C2) .up (i, .Oe) = true ∧ YV.faceB (i, .C3) .up (i, .Oe) = true ∧
    YV.faceB (i, .C1) .down (i - 1, .Og) = true ∧ YV.faceB (i, .C4) .down (i, .Og) = true ∧
    YV.faceB (i, .C5) .up (i, .C6) = true

theorem yFace_holds (i : Fin 6) : yFaceLabels i := by
  fin_cases i <;> unfold yFaceLabels <;> decide

/-! ## Well-formedness of the molecular graph of Y -/

theorem y_bond_symm : ∀ u v : YV, YV.adj u v = true → YV.adj v u = true := by
  have key : ∀ u v : YV, YV.adj u v = YV.adj v u := by
    intro ⟨i, a⟩ ⟨j, b⟩
    fin_cases i <;> fin_cases j <;> cases a <;> cases b <;> decide
  intro u v h
  rw [key u v] at h
  exact h

theorem y_bond_irrefl : ∀ u : YV, ¬ (YV.adj u u = true) := by
  intro ⟨i, a⟩ h
  fin_cases i <;> cases a <;> revert h <;> decide

theorem y_bondOrder_pos : ∀ {u v : YV}, YV.adj u v = true → 1 ≤ YV.order u v := by
  intro u v h
  unfold YV.order
  rw [if_pos h]

/-- **Compound Y (the derived answer to 9.4)** as an explicit stereolabelled molecular
graph: per-(6-O-TBS) per-(2,3-anhydro)-alpha-CD — six units, glycosidic closure
`Og(i) - C1(i+1 mod 6)`. -/
def Y : Molecule where
  Vertex := YV
  fintypeV := inferInstanceAs (Fintype YV)
  decEqV := inferInstanceAs (DecidableEq YV)
  atom := YV.atom
  hCount := YV.hCount
  bond := Ybond
  bondOrder := YV.order
  bond_symm := y_bond_symm
  bond_irrefl := y_bond_irrefl
  bondOrder_pos := fun {u v} (h : Ybond u v) ↦ y_bondOrder_pos h
  face := Yface

/-! ## Structural facts about Y -/

/-- The intra-unit chair, epoxide, anomeric arm and TBS bonds of Y, each decided by
computation on the explicit representation. -/
theorem y_unit_intrabonds (i : Fin 6) :
    Y.bond (i, .C1) (i, .C2) ∧ Y.bond (i, .C2) (i, .C3) ∧ Y.bond (i, .C3) (i, .C4) ∧
    Y.bond (i, .C4) (i, .C5) ∧ Y.bond (i, .C5) (i, .O5) ∧ Y.bond (i, .O5) (i, .C1) ∧
    Y.bond (i, .C5) (i, .C6) ∧ Y.bond (i, .C2) (i, .Oe) ∧ Y.bond (i, .C3) (i, .Oe) ∧
    Y.bond (i, .C4) (i, .Og) ∧
    Y.bond (i, .C6) (i, .Os) ∧ Y.bond (i, .Os) (i, .Si) ∧
    Y.bond (i, .Si) (i, .Sm1) ∧ Y.bond (i, .Si) (i, .Sm2) ∧ Y.bond (i, .Si) (i, .Sq) ∧
    Y.bond (i, .Sq) (i, .tB1) ∧ Y.bond (i, .Sq) (i, .tB2) ∧ Y.bond (i, .Sq) (i, .tB3) := by
  fin_cases i <;> simp [Y] <;> decide

/-- The glycosidic macrocycle closure edges of Y: `Og(i)` bonds to `C1(i+1 mod 6)`, the
alpha-1,4-links closing the six-unit ring of the printed figures. -/
theorem y_glycosidic_bonds (i : Fin 6) :
    Y.bond (i, .Og) (i + 1, .C1) ∧ Y.bond (i + 1, .C1) (i, .Og) := by
  fin_cases i <;> simp [Y] <;> decide

/-- Every bond of Y has order exactly one: all single bonds, as drawn. -/
theorem y_bondOrder_one {u v : YV} (h : Y.bond u v) : Y.bondOrder u v = 1 := by
  show YV.order u v = 1
  unfold YV.order
  exact if_pos h

/-- Y is built from six sugar units on 17 sites each: 102 vertices. -/
theorem y_vertex_count : Fintype.card YV = 6 * 17 ∧ 6 * 17 = 102 :=
  ⟨calc Fintype.card YV = Fintype.card (Fin 6) * Fintype.card UnitV := Fintype.card_prod _ _
     _ = 6 * 17 := by rw [Fintype.card_fin, show Fintype.card UnitV = 17 from rfl],
    by decide⟩

/-- **Y contains no free hydroxy group**: the primary 6-OH has been silylated
(CH2-O-TBS) and the secondary 2- and 3-OH were consumed in the 2,3-anhydro bridge; every
oxygen vertex carries zero hydrogens. -/
theorem y_no_free_OH : ∀ u : YV, ¬ Y.HasFreeOH u := by
  intro ⟨i, a⟩ h
  obtain ⟨hO, hH⟩ := h
  fin_cases i <;> (cases a <;> simp [Y, YV.atom, YV.hCount, UnitV.atom, UnitV.hCount]
    at hO hH)

/-- Per unit there is one internal bridging oxygen — the 2,3-anhydro epoxide: `Oe` is an
oxygen bonded to the adjacent ring carbons C2 and C3, which are themselves bonded. -/
theorem y_epoxide_bridge (i : Fin 6) :
    Y.atom (i, .Oe) = .O ∧ Y.bond (i, .C2) (i, .Oe) ∧ Y.bond (i, .C3) (i, .Oe) ∧
    Y.bond (i, .C2) (i, .C3) := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> fin_cases i <;>
    simp [Y] <;> decide

/-- The five pyranose ring carbons of each unit each carry exactly one hydrogen, as
tetrahedral stereocentres must; C6 carries two and is not stereogenic. -/
theorem y_ring_carbon_hydrogens (i : Fin 6) :
    Y.hCount (i, .C1) = 1 ∧ Y.hCount (i, .C2) = 1 ∧ Y.hCount (i, .C3) = 1 ∧
    Y.hCount (i, .C4) = 1 ∧ Y.hCount (i, .C5) = 1 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The ring-carbon sites of unit `i` are exactly the stereocentres of the template:
their two non-ring substituent directions (up/down) are occupied by distinct atoms. -/
theorem y_stereocentre_C2 (i : Fin 6) : Y.IsStereocentre (i, .C2) := by
  refine ⟨rfl, rfl, (i, .Oe), (i, .C1), ?_, ?_, ?_⟩
  · revert i; simp [Y, Yface]; decide
  · revert i; simp [Y, Yface]; decide
  · have key : ∀ i : Fin 6, (i, UnitV.C1) ≠ (i, UnitV.Oe) := by decide
    exact key i

theorem y_stereocentre_C3 (i : Fin 6) : Y.IsStereocentre (i, .C3) := by
  refine ⟨rfl, rfl, (i, .Oe), (i, .C4), ?_, ?_, ?_⟩
  · revert i; simp [Y, Yface]; decide
  · revert i; simp [Y, Yface]; decide
  · have key : ∀ i : Fin 6, (i, UnitV.C4) ≠ (i, UnitV.Oe) := by decide
    exact key i

/-- **Inversion at C2 and C3 relative to alpha-CD**: the new C-O bonds of the anhydro
ring both lie on the `up` face of the template. In alpha-CD the C2-O and C3-O bonds are
drawn below the ring; hence both centres are inverted, the defining
glucose-to-altrose-precursor change of the scheme. -/
theorem y_inversion_at_C2_C3 (i : Fin 6) :
    Y.face (i, .C2) .up (i, .Oe) ∧ Y.face (i, .C3) .up (i, .Oe) := by
  fin_cases i <;> simp [Y] <;> decide

/-- The alpha configuration at C1 is retained: the glycosidic oxygen of the predecessor
sits on the `down` face of C1, the arm oxygen `Og` leaves C4 on the `down` face, and the
C6 arm sits `up` at C5, exactly as printed. -/
theorem y_alpha_link_face (i : Fin 6) :
    Y.face (i, .C1) .down (i - 1, .Og) ∧ Y.face (i, .C4) .down (i, .Og) ∧
    Y.face (i, .C5) .up (i, .C6) := by
  fin_cases i <;> simp [Y] <;> decide

/-- **Six tert-butyldimethylsilyl (TBS) groups** are present in Y: the silicon sites are
exactly `(i, .Si)` for the six units, each bonded to the silyl oxygen `Os`, the two
methyls `Sm1, Sm2` and the quaternary tert-butyl carbon `Sq` with its three methyls. -/
theorem y_silicon_vertices (w : YV) : Y.atom w = .Si ↔ w.2 = UnitV.Si := by
  obtain ⟨i, c⟩ := w
  cases c <;> revert i <;> decide

theorem y_silicon_count6 :
    (Finset.univ.filter fun w : YV ↦ Y.atom w = .Si).card = 6 := by
  decide

/-- Each silicon carries exactly the TBS substitution: two methyls and one tert-butyl,
each methyl is a CH3 carbon bonded to `Sq`, and `Sq` bears no hydrogen. -/
theorem y_tbs_group (i : Fin 6) :
    Y.bond (i, .Si) (i, .Sm1) ∧ Y.bond (i, .Si) (i, .Sm2) ∧ Y.bond (i, .Si) (i, .Sq) ∧
    Y.bond (i, .Sq) (i, .tB1) ∧ Y.bond (i, .Sq) (i, .tB2) ∧ Y.bond (i, .Sq) (i, .tB3) ∧
    Y.hCount (i, .Sq) = 0 ∧ Y.hCount (i, .Sm1) = 3 ∧ Y.hCount (i, .Sm2) = 3 ∧
    Y.hCount (i, .tB1) = 3 ∧ Y.hCount (i, .tB2) = 3 ∧ Y.hCount (i, .tB3) = 3 := by
  fin_cases i <;> simp [Y] <;> decide

/-! ## The formula audit: explicit structure vs the printed formula of Y -/

/-- Per-unit carbon count: 12 — C1..C6 (sugar), Sm1, Sm2, Sq, tB1, tB2, tB3 (TBS). -/
theorem unit_carbons : (∑ v : UnitV, if UnitV.atom v = .C then 1 else 0) = 12 := by
  decide

/-- Per-unit hydrogen count: 22 — H on C1..C5 (5), on C6 (2), and 3 on each of the five
methyls (15). All oxygens, the silicon and the quaternary tert-butyl carbon are H-free. -/
theorem unit_hydrogens : (∑ v : UnitV, UnitV.hCount v) = 22 := by
  decide

/-- Per-unit oxygen count: 4 in the ring-closed molecule — O5 (ring), Oe (epoxide), Og
(the glycosidic bridge shared with the next unit, counted once as this unit's arm), Os
(silyl). This matches the printed macrocycle, in which every glycosidic oxygen is one
bridge between two units. -/
theorem unit_oxygens : (∑ v : UnitV, if UnitV.atom v = .O then 1 else 0) = 4 := by
  decide

/-- Per-unit silicon count: 1. -/
theorem unit_silicons : (∑ v : UnitV, if UnitV.atom v = .Si then 1 else 0) = 1 := by
  decide

/-- **Per-unit formula of the derived structure of Y: C12 H22 O4 Si**, on the
ring-closed ownership convention (each glycosidic bridge oxygen counted once, with the
unit whose C4 it arms). -/
def yUnitFormula : Formula := ⟨12, 22, 4, 1⟩

/-- **Formula of the starting macrocycle**: six glucose residues cyclised by six
water losses (six alpha-1,4-glycosidic bonds), C36 H60 O30 — the composition of the
alpha-CD drawn on Q9-2, consistent with 9.1's computation pattern (7 x 180.16 - 7 x
18.02 for beta-CD; for alpha-CD the same with 6). -/
theorem alphaCD_formula_from_glucose :
    ({ c := 6, h := 12, o := 6, si := 0 } : Formula) =
      ⟨glucoseFormula.c, glucoseFormula.h, glucoseFormula.o, glucoseFormula.si⟩ := rfl

/-- The printed starting material formula derived from the problem's own data:
six glucose residues cyclised with six water losses gives C36 H60 O30,
`6 • glucoseFormula - 6 • waterFormula`. -/
theorem alphaCD_formula :
    ({ c := 6 * glucoseFormula.c - 6 * waterFormula.c,
       h := 6 * glucoseFormula.h - 6 * waterFormula.h,
       o := 6 * glucoseFormula.o - 6 * waterFormula.o,
       si := 0 } : Formula) = ⟨36, 60, 30, 0⟩ := rfl

/-- Explicit formula of one full unit of the derived structure of Y: the per-site atom
and hydrogen labels of `UnitV` summed over its 17 sites. -/
def yUnitFullFormula : Formula :=
  Formula.sum (fun v : UnitV ↦
    match UnitV.atom v with
    | .C => ⟨1, UnitV.hCount v, 0, 0⟩
    | .H => ⟨0, 1 + UnitV.hCount v, 0, 0⟩
    | .O => ⟨0, UnitV.hCount v, 1, 0⟩
    | .Si => ⟨0, UnitV.hCount v, 0, 1⟩)

/-- The per-unit explicit formula evaluates to C12 H22 O4 Si. -/
theorem yUnitFullFormula_eq : yUnitFullFormula = ⟨12, 22, 4, 1⟩ := by
  unfold yUnitFullFormula Formula.sum
  apply (Formula.mk.injEq _ _ _ _ _ _ _ _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Per-unit coordinate sums are closed under computation. -/
theorem unit_c_sum : (∑ v : UnitV, if UnitV.atom v = .C then (1 : ℤ) else 0) = 12 := by
  decide

theorem unit_o_sum : (∑ v : UnitV, if UnitV.atom v = .O then (1 : ℤ) else 0) = 4 := by
  decide

theorem unit_si_sum : (∑ v : UnitV, if UnitV.atom v = .Si then (1 : ℤ) else 0) = 1 := by
  decide

theorem unit_h_sum : (∑ v : UnitV, (UnitV.hCount v : ℤ)) = 22 := by
  decide

/-- Per-coordinate decidable sums of the per-site counts over one unit. -/
def unitCoordC : ℤ := ∑ v : UnitV, if UnitV.atom v = .C then (1 : ℤ) else 0
def unitCoordS : ℤ := ∑ v : UnitV, (UnitV.hCount v : ℤ)
def unitCoordO : ℤ := ∑ v : UnitV, if UnitV.atom v = .O then (1 : ℤ) else 0
def unitCoordI : ℤ := ∑ v : UnitV, if UnitV.atom v = .Si then (1 : ℤ) else 0

theorem unitCoordC_eval : unitCoordC = 12 := rfl
theorem unitCoordS_eval : unitCoordS = 22 := rfl
theorem unitCoordO_eval : unitCoordO = 4 := rfl
theorem unitCoordI_eval : unitCoordI = 1 := rfl

/-- The whole macrocycle formula is six times the per-unit formula. -/
theorem y_formula_decomposes :
    Y.formula.c = 6 * yUnitFullFormula.c ∧ Y.formula.o = 6 * yUnitFullFormula.o ∧
    Y.formula.si = 6 * yUnitFullFormula.si ∧ Y.formula.h = 6 * yUnitFullFormula.h := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · set_option maxRecDepth 32768 in
    have hc : (∑ w : YV, (fun x : YV ↦ match Y.atom x with
        | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0) w)
        = 6 * ∑ v : UnitV, match UnitV.atom v with
          | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0 :=
      calc ∑ w : YV, (fun x : YV ↦ match Y.atom x with
            | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0) w
          = ∑ w : Fin 6 × UnitV, (fun x : Fin 6 × UnitV ↦ match UnitV.atom x.2 with
              | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0) w := rfl
        _ = ∑ w : (i : Fin 6) × UnitV, (fun x : (i : Fin 6) × UnitV ↦
              match UnitV.atom x.2 with
              | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0) w := rfl
        _ = ∑ i : Fin 6, ∑ v : UnitV, match UnitV.atom v with
              | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0 := rfl
        _ = ∑ w : (i : Fin 6) × UnitV, match UnitV.atom w.2 with
              | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0 :=
            Finset.sum_sigma' Finset.univ (fun _ ↦ Finset.univ)
              (fun _ v ↦ match UnitV.atom v with
                | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0)
        _ = ∑ w : Fin 6 × UnitV, match UnitV.atom w.2 with
              | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0 := rfl
        _ = ∑ i : Fin 6, ∑ v : UnitV, match UnitV.atom v with
              | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0 := rfl
    conv_lhs => change ∑ w : YV, (fun x : YV ↦ match Y.atom x with
      | .C => (1 : ℤ) | .H => 0 | .O => 0 | .Si => 0) w
    set_option maxRecDepth 32768 in rw [hc]
    rfl
  · set_option maxRecDepth 32768 in
    have ho : (∑ w : YV, (fun x : YV ↦ match Y.atom x with
        | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0) w)
        = 6 * ∑ v : UnitV, match UnitV.atom v with
          | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0 :=
      calc ∑ w : YV, (fun x : YV ↦ match Y.atom x with
            | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0) w
          = ∑ w : Fin 6 × UnitV, (fun x : Fin 6 × UnitV ↦ match UnitV.atom x.2 with
              | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0) w := rfl
        _ = ∑ w : (i : Fin 6) × UnitV, (fun x : (i : Fin 6) × UnitV ↦
              match UnitV.atom x.2 with
              | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0) w := rfl
        _ = ∑ i : Fin 6, ∑ v : UnitV, match UnitV.atom v with
              | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0 := rfl
        _ = ∑ w : (i : Fin 6) × UnitV, match UnitV.atom w.2 with
              | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0 :=
            Finset.sum_sigma' Finset.univ (fun _ ↦ Finset.univ)
              (fun _ v ↦ match UnitV.atom v with
                | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0)
        _ = ∑ w : Fin 6 × UnitV, match UnitV.atom w.2 with
              | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0 := rfl
        _ = ∑ i : Fin 6, ∑ v : UnitV, match UnitV.atom v with
              | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0 := rfl
    conv_lhs => change ∑ w : YV, (fun x : YV ↦ match Y.atom x with
      | .C => (0 : ℤ) | .H => 0 | .O => 1 | .Si => 0) w
    set_option maxRecDepth 32768 in rw [ho]
    rfl
  · set_option maxRecDepth 32768 in
    have hs : (∑ w : YV, (fun x : YV ↦ match Y.atom x with
        | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1) w)
        = 6 * ∑ v : UnitV, match UnitV.atom v with
          | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1 :=
      calc ∑ w : YV, (fun x : YV ↦ match Y.atom x with
            | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1) w
          = ∑ w : Fin 6 × UnitV, (fun x : Fin 6 × UnitV ↦ match UnitV.atom x.2 with
              | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1) w := rfl
        _ = ∑ w : (i : Fin 6) × UnitV, (fun x : (i : Fin 6) × UnitV ↦
              match UnitV.atom x.2 with
              | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1) w := rfl
        _ = ∑ i : Fin 6, ∑ v : UnitV, match UnitV.atom v with
              | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1 := rfl
        _ = ∑ w : (i : Fin 6) × UnitV, match UnitV.atom w.2 with
              | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1 :=
            Finset.sum_sigma' Finset.univ (fun _ ↦ Finset.univ)
              (fun _ v ↦ match UnitV.atom v with
                | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1)
        _ = ∑ w : Fin 6 × UnitV, match UnitV.atom w.2 with
              | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1 := rfl
        _ = ∑ i : Fin 6, ∑ v : UnitV, match UnitV.atom v with
              | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1 := rfl
    conv_lhs => change ∑ w : YV, (fun x : YV ↦ match Y.atom x with
      | .C => (0 : ℤ) | .H => 0 | .O => 0 | .Si => 1) w
    set_option maxRecDepth 32768 in rw [hs]
    rfl
  · set_option maxRecDepth 32768 in
    have hh : (∑ w : YV, (fun x : YV ↦ match Y.atom x with
        | .C => (Y.hCount x : ℤ) | .H => 1 + Y.hCount x
        | .O => (Y.hCount x : ℤ) | .Si => (Y.hCount x : ℤ)) w)
        = 6 * ∑ v : UnitV, (UnitV.hCount v : ℤ) :=
      calc ∑ w : YV, (fun x : YV ↦ match Y.atom x with
            | .C => (Y.hCount x : ℤ) | .H => 1 + Y.hCount x
            | .O => (Y.hCount x : ℤ) | .Si => (Y.hCount x : ℤ)) w
          = ∑ w : Fin 6 × UnitV, (fun x : Fin 6 × UnitV ↦ (UnitV.hCount x.2 : ℤ)) w := rfl
        _ = ∑ w : (i : Fin 6) × UnitV, (fun x : (i : Fin 6) × UnitV ↦
              (UnitV.hCount x.2 : ℤ)) w := rfl
        _ = ∑ i : Fin 6, ∑ v : UnitV, (UnitV.hCount v : ℤ) := rfl
        _ = ∑ w : (i : Fin 6) × UnitV, (UnitV.hCount w.2 : ℤ) :=
            Finset.sum_sigma' Finset.univ (fun _ ↦ Finset.univ)
              (fun _ v ↦ (UnitV.hCount v : ℤ))
        _ = ∑ w : Fin 6 × UnitV, (UnitV.hCount w.2 : ℤ) := rfl
        _ = ∑ i : Fin 6, ∑ v : UnitV, (UnitV.hCount v : ℤ) := rfl
    conv_lhs => change ∑ w : YV, (fun x : YV ↦ match Y.atom x with
      | .C => (Y.hCount x : ℤ) | .H => 1 + Y.hCount x
      | .O => (Y.hCount x : ℤ) | .Si => (Y.hCount x : ℤ)) w
    set_option maxRecDepth 32768 in rw [hh]
    rfl

/-- **The full explicit molecule Y carries exactly the printed formula** of Y. The heavy
atoms and hydrogens of `Y` (102 sites) sum to C72 H132 O24 Si6, the label printed under
the Y arrow of Q9-2 and beside the answer-sheet template on A9-2: the decisive
fingerprint of the per-TBS 2,3-anhydro structure. -/
theorem y_structure_matches_printed_formula : Y.formula = yPrintedFormula := by
  obtain ⟨hc, ho, hsi, hh⟩ := y_formula_decomposes
  rw [yUnitFullFormula_eq] at hc ho hsi hh
  unfold yPrintedFormula
  apply (Formula.mk.injEq _ _ _ _ _ _ _ _).mpr
  exact ⟨hc, hh, ho, hsi⟩
/-- The total counts, element by element (the answer sheet's own numbers). -/
theorem y_total_c : Y.formula.c = 72 := by
  have := y_structure_matches_printed_formula
  exact congrArg Formula.c this

theorem y_total_h : Y.formula.h = 132 := by
  exact congrArg Formula.h y_structure_matches_printed_formula

theorem y_total_o : Y.formula.o = 24 := by
  exact congrArg Formula.o y_structure_matches_printed_formula

theorem y_total_si : Y.formula.si = 6 := by
  exact congrArg Formula.si y_structure_matches_printed_formula

/-- Six-fold repetition of the per-unit count gives the same totals (cross-check that
the explicit graph count equals the per-unit count times six). -/
theorem y_formula_is_six_units :
    Y.formula = ⟨6 * yUnitFormula.c, 6 * yUnitFormula.h, 6 * yUnitFormula.o,
      6 * yUnitFormula.si⟩ := by
  rw [y_structure_matches_printed_formula]
  exact rfl

/-! ## The deliverable theorem for subquestion 9.4 -/

/-- **Subquestion 9.4, answered and certified.** Structure Y is the molecule whose
skeleton is `Y`: the alpha-CD macrocycle of six units (glycosidic closure verified) in
which each unit carries (i) a TBS group on O6 (Si with two methyls, one tert-butyl, and
the C6-O silyl bond), (ii) a 2,3-anhydro (epoxide) bridge across C2-C3 with both new
C-O bonds on the `up` face — inversion at C2 and C3 relative to alpha-CD —, (iii) the
alpha configuration retained at C1 (predecessor glycosidic oxygen on the down face) and
the D-series C6 arm up at C5; no free hydroxy group remains; and the explicit atom
counts of this labelled structure reproduce exactly the printed formula
C72H132O24Si6. -/
theorem icho_2026_t9_a4_structure_of_Y :
    -- six sugar units on the ring (subscript 6 of the template figures)
    Fintype.card YV = 102 ∧
    -- alpha-1,4-glycosidic macrocycle closure
    (∀ i : Fin 6, Y.bond (i, .Og) (i + 1, .C1)) ∧
    -- per unit: 2,3-anhydro epoxide bridge is present
    (∀ i : Fin 6, Y.atom (i, .Oe) = .O ∧ Y.bond (i, .C2) (i, .Oe) ∧
      Y.bond (i, .C3) (i, .Oe) ∧ Y.bond (i, .C2) (i, .C3)) ∧
    -- per unit: C6 silylated as CH2-O-TBS
    (∀ i : Fin 6, Y.bond (i, .C6) (i, .Os) ∧ Y.bond (i, .Os) (i, .Si) ∧
      Y.atom (i, .Si) = .Si) ∧
    -- six TBS groups (six Si atoms)
    (Finset.univ.filter fun w : YV ↦ Y.atom w = .Si).card = 6 ∧
    -- no free hydroxy group
    (∀ u : YV, ¬ Y.HasFreeOH u) ∧
    -- stereochemistry: inversion at C2 and C3, alpha at C1 retained, C6 arm up
    (∀ i : Fin 6, yFaceLabels i) ∧
    -- C2 and C3 are tetrahedral stereocentres of the template
    (∀ i : Fin 6, Y.IsStereocentre (i, .C2) ∧ Y.IsStereocentre (i, .C3)) ∧
    -- the formula fingerprint against the problem's printed formula
    Y.formula = yPrintedFormula := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact y_vertex_count.1.trans (by decide)
  · exact fun i ↦ (y_glycosidic_bonds i).1
  · exact y_epoxide_bridge
  · intro i
    fin_cases i <;> simp [Y] <;> decide
  · exact y_silicon_count6
  · exact y_no_free_OH
  · exact yFace_holds
  · exact fun i ↦ ⟨y_stereocentre_C2 i, y_stereocentre_C3 i⟩
  · exact y_structure_matches_printed_formula

#print axioms icho_2026_t9_a4_structure_of_Y
#print axioms y_structure_matches_printed_formula
#print axioms y_inversion_at_C2_C3

end IChO2026T9A4
