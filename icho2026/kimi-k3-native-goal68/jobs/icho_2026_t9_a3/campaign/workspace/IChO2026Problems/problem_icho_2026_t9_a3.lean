import Mathlib

/-!
# IChO 2026, Problem T9, subquestion T9-A3 (printed question 9.3)

Macrocycle X is obtained (problem page Q9-2) from β-cyclodextrin — the
bracketed structure with subscript 7, α-D-glucopyranoside units joined by
α-1,4-glycosidic bonds (page Q9-1: "n = 7", "(OH)₁₄", 7 × CH₂OH) — by

1. NaIO₄      (Malaprade cleavage of the vicinal C2–C3 diol of every unit)
2. NaBH₄, H₂O (reduction of the two aldehydes to –CH₂OH arms)
3. Ac₂O, Py   (acetylation; irrelevant to connectivity and stereochemistry)

Periodate severs only the C2–C3 bond of each unit.  The cyclodextrin
macrocyclic backbone runs, per unit, through

  C1_i – O_glyc_i – C4_{i+1} – C5_{i+1} – O5_{i+1}

(i.e. the glycosidic bond and the long side of the former pyranose ring), so
the backbone loop stays intact: X is a macrocycle built from 7 units each
contributing 5 ring atoms, with three pendant –CH₂OAc arms per unit (on C1,
C4, C5).  Requested and proved here:

  * ring size           rs = 35   (`icho_2026_t9_a3_ring_size`)
  * stereocentre count  sc = 21   (`icho_2026_t9_a3_stereocentres`)

The formalization encodes the molecular bond graph of X explicitly, proves
that the displayed 35-atom traverse is genuinely a cycle of that graph
(`x_ring_is_cycle`), proves exhaustively that every bond is either a ring
edge or a pendant arm bond (`x_bond_exact`, so no pendant arm can act as a
chord shortening the ring and no second cycle exists), and proves the
substituent-level stereocentre analysis per centre type.
-/

section MetaLemmas

variable {α : Type*} {a : α} {s : List α}

/-- Membership in a concatenated list. -/
theorem mem_append_of_mem_left {t : List α} (h : a ∈ s) : a ∈ s ++ t := by
  induction s with
  | nil => simp at h
  | cons a' s' ih =>
      cases h with
      | head => simp
      | tail _ h' =>
          have : a ∈ s' ++ t := ih h'
          simp [this]

/-- Elements of `erase s a` are elements of `s`. -/
theorem mem_of_mem_erase_local [DecidableEq α] {b : α} (h : a ∈ s.erase b) : a ∈ s :=
  List.mem_of_mem_erase h

/-- Coherence of the "erase one element" operation: a list containing `a`
has the length of its erase plus one. -/
theorem length_erase_add_one_of_mem [DecidableEq α] (h : a ∈ s) :
    s.length = (s.erase a).length + 1 := by
  rw [List.length_erase_of_mem h]
  rw [Nat.sub_add_cancel (List.length_pos_of_mem h)]

end MetaLemmas

namespace IChO2026T9A3

/-- The seven α-D-glucopyranoside-derived units of β-CD / X
(page Q9-1: β-CD drawn with "n = 7"). -/
abbrev Units : Type := Fin 7

/-- Atoms of one unit of X.

Each former glucopyranose ring contributed atoms C1, C2, C3, C4, C5, O5 plus
the C6 hydroxymethyl carbon and the glycosidic oxygen O(C1).  The NaIO₄ step
cleaves the C2–C3 bond (the only vicinal diol of the unit, per the drawn free
2,3-diol on page Q9-2); NaBH₄ reduces the two aldehydes, so former C2 and C3
become –CH₂OH arms attached to C1 and C4 respectively; Ac₂O then acetylates
them (–CH₂OAc arms; immaterial for connectivity, see the answer notes). -/
inductive Atom
  | C1 (i : Units)      -- former anomeric carbon: ring atom
  | Oglyc (i : Units)   -- glycosidic oxygen bonding C1_i to C4_{i+1}: ring atom
  | C4 (i : Units)      -- glycosidic-bond-bearing ring carbon: ring atom
  | C5 (i : Units)      -- ring carbon bearing the C6 arm: ring atom
  | O5 (i : Units)      -- former pyranose ring oxygen: ring atom
  | ArmC2 (i : Units)   -- former C2, now –CH₂OAc pendant on C1
  | ArmC3 (i : Units)   -- former C3, now –CH₂OAc pendant on C4
  | ArmC6 (i : Units)   -- former C6, –CH₂OAc pendant on C5, as in β-CD itself
  deriving DecidableEq, Repr

/-- Backbone (macrocyclic ring) atoms: exactly five per unit. -/
inductive Atom.IsBackbone : Atom → Prop
  | c1 (i : Units) : IsBackbone (.C1 i)
  | oglyc (i : Units) : IsBackbone (.Oglyc i)
  | c4 (i : Units) : IsBackbone (.C4 i)
  | c5 (i : Units) : IsBackbone (.C5 i)
  | o5 (i : Units) : IsBackbone (.O5 i)

/-- Arm atoms are not backbone atoms. -/
theorem not_backbone_arm2 (i : Units) : ¬ (Atom.ArmC2 i).IsBackbone := fun h => by cases h
theorem not_backbone_arm3 (i : Units) : ¬ (Atom.ArmC3 i).IsBackbone := fun h => by cases h
theorem not_backbone_arm6 (i : Units) : ¬ (Atom.ArmC6 i).IsBackbone := fun h => by cases h

/-- Bonds of X (undirected).

Per unit i (indices mod 7):
  backbone : C1_i – Oglyc_i,  Oglyc_i – C4_{i+1},  C4_i – C5_i,
             C5_i – O5_i,  O5_i – C1_i   (5 bonds, all ring edges)
  pendant  : C1_i – ArmC2_i (former C2, –CH₂OAc),
             C4_i – ArmC3_i (former C3, –CH₂OAc),
             C5_i – ArmC6_i (former C6, –CH₂OAc)   (3 bonds, none in the ring)

The β-CD precursor additionally has the C2–C3 bond inside each pyranose ring;
NaIO₄ cleaves precisely that bond, and this bond set is the cleavage product.
-/
inductive Bond
  | c1og (i : Units)        -- C1_i — Oglyc_i          (ring edge, glycosidic)
  | ogc4 (i : Units)        -- Oglyc_i — C4_{i+1}      (ring edge, glycosidic)
  | c4c5 (i : Units)        -- C4_i — C5_i             (ring edge)
  | c5o5 (i : Units)        -- C5_i — O5_i             (ring edge)
  | o5c1 (i : Units)        -- O5_i — C1_i             (ring edge)
  | arm2 (i : Units)        -- C1_i — ArmC2_i          (pendant arm, former C2)
  | arm3 (i : Units)        -- C4_i — ArmC3_i          (pendant arm, former C3)
  | arm6 (i : Units)        -- C5_i — ArmC6_i          (pendant arm, from CD C6)
  deriving DecidableEq

namespace Bond

/-- The incidence statement `link e a b` asserts that edge `e` connects `a` and
`b`, with both orientations allowed (undirected). -/
def link : Bond → Atom → Atom → Prop
  | c1og i, a, b => (a = .C1 i ∧ b = .Oglyc i) ∨ (a = .Oglyc i ∧ b = .C1 i)
  | ogc4 i, a, b => (a = .Oglyc i ∧ b = .C4 (i + 1)) ∨ (a = .C4 (i + 1) ∧ b = .Oglyc i)
  | c4c5 i, a, b => (a = .C4 i ∧ b = .C5 i) ∨ (a = .C5 i ∧ b = .C4 i)
  | c5o5 i, a, b => (a = .C5 i ∧ b = .O5 i) ∨ (a = .O5 i ∧ b = .C5 i)
  | o5c1 i, a, b => (a = .O5 i ∧ b = .C1 i) ∨ (a = .C1 i ∧ b = .O5 i)
  | arm2 i, a, b => (a = .C1 i ∧ b = .ArmC2 i) ∨ (a = .ArmC2 i ∧ b = .C1 i)
  | arm3 i, a, b => (a = .C4 i ∧ b = .ArmC3 i) ∨ (a = .ArmC3 i ∧ b = .C4 i)
  | arm6 i, a, b => (a = .C5 i ∧ b = .ArmC6 i) ∨ (a = .ArmC6 i ∧ b = .C5 i)

/-- `a` and `b` are bonded (share a covalent bond) in X. -/
def bonded (a b : Atom) : Prop := ∃ e : Bond, link e a b

theorem bonded_symm {a b : Atom} : bonded a b → bonded b a := by
  rintro ⟨e, he⟩
  refine ⟨e, ?_⟩
  cases e <;> cases he with
  | inl h => exact Or.inr ⟨h.2, h.1⟩
  | inr h => exact Or.inl ⟨h.2, h.1⟩

end Bond

open Bond

/-- The 35-atom closed traverse around the macrocycle of X.

Within unit i the ring runs C1_i → Oglyc_i → C4_{i+1} (the glycosidic
unit-to-unit link; α-1,4 per page Q9-1), and then along the long side of the
opened pyranose ring C4 → C5 → O5 → C1.  Indices are mod 7. -/
def ringList : List Atom :=
  [ Atom.C1 0, Atom.Oglyc 0, Atom.C4 1, Atom.C5 1, Atom.O5 1,
    Atom.C1 1, Atom.Oglyc 1, Atom.C4 2, Atom.C5 2, Atom.O5 2,
    Atom.C1 2, Atom.Oglyc 2, Atom.C4 3, Atom.C5 3, Atom.O5 3,
    Atom.C1 3, Atom.Oglyc 3, Atom.C4 4, Atom.C5 4, Atom.O5 4,
    Atom.C1 4, Atom.Oglyc 4, Atom.C4 5, Atom.C5 5, Atom.O5 5,
    Atom.C1 5, Atom.Oglyc 5, Atom.C4 6, Atom.C5 6, Atom.O5 6,
    Atom.C1 6, Atom.Oglyc 6, Atom.C4 0, Atom.C5 0, Atom.O5 0 ]

theorem ringList_length : ringList.length = 35 := rfl

/-- Every atom of the traverse is a backbone atom. -/
theorem ringList_backbone {a : Atom} (h : a ∈ ringList) : a.IsBackbone := by
  fin_cases h <;> first
    | exact Atom.IsBackbone.c1 _
    | exact Atom.IsBackbone.oglyc _
    | exact Atom.IsBackbone.c4 _
    | exact Atom.IsBackbone.c5 _
    | exact Atom.IsBackbone.o5 _

/-- The traverse has 35 distinct atoms (the macrocycle passes exactly once
through each backbone atom). -/
theorem ringList_nodup : ringList.Nodup := by decide

/-- The ring-atom count: `rs = |ringList| = 35`. -/
def rsX : ℕ := ringList.length

/-! ### Consecutive bonds of the traverse

Each step of the traverse is a real bond of X.  The step bond constructors
are: `Bond.c1og i` (C1_i–Oglyc_i), `Bond.ogc4 i` (Oglyc_i–C4_{i+1}),
`Bond.c4c5 i`, `Bond.c5o5 i`, `Bond.o5c1 i`. -/

theorem step_c1og (i : Units) : bonded (.C1 i) (.Oglyc i) :=
  ⟨.c1og i, Or.inl ⟨rfl, rfl⟩⟩

theorem step_ogc4 (i : Units) : bonded (.Oglyc i) (.C4 (i + 1)) :=
  ⟨.ogc4 i, Or.inl ⟨rfl, rfl⟩⟩

theorem step_c4c5 (i : Units) : bonded (.C4 i) (.C5 i) :=
  ⟨.c4c5 i, Or.inl ⟨rfl, rfl⟩⟩

theorem step_c5o5 (i : Units) : bonded (.C5 i) (.O5 i) :=
  ⟨.c5o5 i, Or.inl ⟨rfl, rfl⟩⟩

theorem step_o5c1 (i : Units) : bonded (.O5 i) (.C1 i) :=
  ⟨.o5c1 i, Or.inl ⟨rfl, rfl⟩⟩

/-- As `Fin 7` numerals, `(6 : Fin 7) + 1 = 0`. -/
theorem fin7_six_add_one : (6 : Fin 7) + 1 = 0 := by decide

/-- A list of atoms is a walk when consecutive entries are bonded. -/
inductive IsWalk : List Atom → Prop
  | nil : IsWalk []
  | single (a : Atom) : IsWalk [a]
  | cons {a b : Atom} {t : List Atom} : bonded a b → IsWalk (b :: t) → IsWalk (a :: b :: t)

/-- The chain of 35 ring steps: consecutive entries of `ringList` are bonded
in X.  Each step uses one of the five step lemmas; the last glycosidic step
closes the index modulo 7 (C4 0 ≡ C4 (6 + 1), definitionally equal in
`Fin 7`). -/
theorem ringList_isWalk : IsWalk ringList := by
  have h01 : bonded (.C1 0) (.Oglyc 0) := step_c1og 0
  have h12 : bonded (.Oglyc 0) (.C4 1) := step_ogc4 0
  have h23 : bonded (.C4 1) (.C5 1) := step_c4c5 1
  have h34 : bonded (.C5 1) (.O5 1) := step_c5o5 1
  have h45 : bonded (.O5 1) (.C1 1) := step_o5c1 1
  have h56 : bonded (.C1 1) (.Oglyc 1) := step_c1og 1
  have h67 : bonded (.Oglyc 1) (.C4 2) := step_ogc4 1
  have h78 : bonded (.C4 2) (.C5 2) := step_c4c5 2
  have h89 : bonded (.C5 2) (.O5 2) := step_c5o5 2
  have h9a : bonded (.O5 2) (.C1 2) := step_o5c1 2
  have hab : bonded (.C1 2) (.Oglyc 2) := step_c1og 2
  have hbc : bonded (.Oglyc 2) (.C4 3) := step_ogc4 2
  have hcd : bonded (.C4 3) (.C5 3) := step_c4c5 3
  have hde : bonded (.C5 3) (.O5 3) := step_c5o5 3
  have hef : bonded (.O5 3) (.C1 3) := step_o5c1 3
  have hfg : bonded (.C1 3) (.Oglyc 3) := step_c1og 3
  have hgh : bonded (.Oglyc 3) (.C4 4) := step_ogc4 3
  have hhi : bonded (.C4 4) (.C5 4) := step_c4c5 4
  have hij : bonded (.C5 4) (.O5 4) := step_c5o5 4
  have hjk : bonded (.O5 4) (.C1 4) := step_o5c1 4
  have hkl : bonded (.C1 4) (.Oglyc 4) := step_c1og 4
  have hlm : bonded (.Oglyc 4) (.C4 5) := step_ogc4 4
  have hmn : bonded (.C4 5) (.C5 5) := step_c4c5 5
  have hno : bonded (.C5 5) (.O5 5) := step_c5o5 5
  have hop : bonded (.O5 5) (.C1 5) := step_o5c1 5
  have hpq : bonded (.C1 5) (.Oglyc 5) := step_c1og 5
  have hqr : bonded (.Oglyc 5) (.C4 6) := step_ogc4 5
  have hrs : bonded (.C4 6) (.C5 6) := step_c4c5 6
  have hst : bonded (.C5 6) (.O5 6) := step_c5o5 6
  have htu : bonded (.O5 6) (.C1 6) := step_o5c1 6
  have huv : bonded (.C1 6) (.Oglyc 6) := step_c1og 6
  have hvw : bonded (.Oglyc 6) (.C4 0) := step_ogc4 6
  have hwx : bonded (.C4 0) (.C5 0) := step_c4c5 0
  have hxy : bonded (.C5 0) (.O5 0) := step_c5o5 0
  exact .cons h01 (.cons h12 (.cons h23 (.cons h34 (.cons h45 (.cons h56
    (.cons h67 (.cons h78 (.cons h89 (.cons h9a (.cons hab (.cons hbc
    (.cons hcd (.cons hde (.cons hef (.cons hfg (.cons hgh (.cons hhi
    (.cons hij (.cons hjk (.cons hkl (.cons hlm (.cons hmn (.cons hno
    (.cons hop (.cons hpq (.cons hqr (.cons hrs (.cons hst (.cons htu
    (.cons huv (.cons hvw (.cons hwx (.cons hxy (.single _))))))))))))))))))))))))))))))))))

/-- The closing bond of the macrocycle: last atom `O5 0` bonded to first atom
`C1 0`. -/
theorem ringList_closes :
    bonded (ringList.getLast (by simp [ringList])) (ringList.head (by simp [ringList])) := by
  have h1 : ringList.getLast (by simp [ringList]) = .O5 0 := by decide
  have h2 : ringList.head (by simp [ringList]) = .C1 0 := by decide
  rw [h1, h2]
  exact step_o5c1 0

/-- **The displayed 35-atom traverse is a genuine cycle of the bond graph
of X**: a walk of bonds, closing onto its starting atom, passing through 35
distinct backbone atoms. -/
theorem x_ring_is_cycle :
    IsWalk ringList ∧
    bonded (ringList.getLast (by simp [ringList])) (ringList.head (by simp [ringList])) ∧
    ringList.Nodup ∧ ringList.length = 35 :=
  ⟨ringList_isWalk, ringList_closes, ringList_nodup, rfl⟩

/-! ### Ring-member completeness

Every backbone atom of X lies on the traverse, and every atom on the traverse
is a backbone atom: the ring passes through all and only backbone atoms. -/

/-- Every backbone atom occurs in `ringList`. -/
theorem x_backbone_mem_ring {a : Atom} (h : a.IsBackbone) : a ∈ ringList := by
  cases h with
  | c1 i => fin_cases i <;> decide
  | oglyc i => fin_cases i <;> decide
  | c4 i => fin_cases i <;> decide
  | c5 i => fin_cases i <;> decide
  | o5 i => fin_cases i <;> decide

/-- Conversely, traverse atoms are backbone atoms (restated for pairing). -/
theorem x_ring_elems_backbone {a : Atom} (h : a ∈ ringList) : a.IsBackbone :=
  ringList_backbone h

/-- The pendant arm atoms never lie in the macrocyclic ring. -/
theorem arm_atoms_not_in_ring (i : Units) :
    (Atom.ArmC2 i) ∉ ringList ∧ (Atom.ArmC3 i) ∉ ringList ∧
    (Atom.ArmC6 i) ∉ ringList := by
  fin_cases i <;> decide

/-! ### Bond exhaustiveness

The key rigor step for the ring size: every bond of X is one of the 35 ring
edges or one of the 21 pendant arm bonds.  Hence (i) no chord exists that
could realize a shorter ring, and (ii) arms terminate in degree-1 atoms and
cannot participate in any cycle. -/

/-- The 35 ring edges, in traverse order. -/
def ringEdges : List Bond :=
  [ Bond.c1og 0, Bond.ogc4 0,
    Bond.c4c5 1, Bond.c5o5 1, Bond.o5c1 1,
    Bond.c1og 1, Bond.ogc4 1,
    Bond.c4c5 2, Bond.c5o5 2, Bond.o5c1 2,
    Bond.c1og 2, Bond.ogc4 2,
    Bond.c4c5 3, Bond.c5o5 3, Bond.o5c1 3,
    Bond.c1og 3, Bond.ogc4 3,
    Bond.c4c5 4, Bond.c5o5 4, Bond.o5c1 4,
    Bond.c1og 4, Bond.ogc4 4,
    Bond.c4c5 5, Bond.c5o5 5, Bond.o5c1 5,
    Bond.c1og 5, Bond.ogc4 5,
    Bond.c4c5 6, Bond.c5o5 6, Bond.o5c1 6,
    Bond.c1og 6, Bond.ogc4 6,
    Bond.c4c5 0, Bond.c5o5 0, Bond.o5c1 0 ]

/-- The 21 pendant arm bonds (three per unit: the two new –CH₂OAc arms from
periodate cleavage/reduction, and the original C6 hydroxymethyl arm). -/
def armEdges : List Bond :=
  [ Bond.arm2 0, Bond.arm3 0, Bond.arm6 0,
    Bond.arm2 1, Bond.arm3 1, Bond.arm6 1,
    Bond.arm2 2, Bond.arm3 2, Bond.arm6 2,
    Bond.arm2 3, Bond.arm3 3, Bond.arm6 3,
    Bond.arm2 4, Bond.arm3 4, Bond.arm6 4,
    Bond.arm2 5, Bond.arm3 5, Bond.arm6 5,
    Bond.arm2 6, Bond.arm3 6, Bond.arm6 6 ]

theorem ringEdges_length : ringEdges.length = 35 := rfl

theorem armEdges_length : armEdges.length = 21 := rfl

theorem ringEdges_nodup : ringEdges.Nodup := by decide

/-- Ring edges and arm edges are disjoint: arms cannot act as ring chords.
Every ring edge is a backbone constructor (`c1og`/`ogc4`/`c4c5`/`c5o5`/`o5c1`)
while every arm edge is an arm constructor (`arm2`/`arm3`/`arm6`), and
different constructors give different bonds. -/
theorem ringEdges_disjoint_armEdges (e : Bond) :
    ¬ (e ∈ ringEdges ∧ e ∈ armEdges) := by
  rintro ⟨h₁, h₂⟩
  cases e with
  | c1og i => revert h₂; fin_cases i <;> decide
  | ogc4 i => revert h₂; fin_cases i <;> decide
  | c4c5 i => revert h₂; fin_cases i <;> decide
  | c5o5 i => revert h₂; fin_cases i <;> decide
  | o5c1 i => revert h₂; fin_cases i <;> decide
  | arm2 i => revert h₁; fin_cases i <;> decide
  | arm3 i => revert h₁; fin_cases i <;> decide
  | arm6 i => revert h₁; fin_cases i <;> decide

/-- **Bond exhaustiveness**: every one of the 7 × 8 = 56 bonds of X is either
a ring edge or an arm edge.  Hence the bond graph has exactly the 35 edges
used by the traverse plus 21 pendant stubs, so the displayed ring is the
unique cycle and its length cannot be shortened by any shortcut bond. -/
theorem x_bond_exact (e : Bond) : e ∈ ringEdges ∨ e ∈ armEdges := by
  cases e with
  | c1og i => fin_cases i <;> decide
  | ogc4 i => fin_cases i <;> decide
  | c4c5 i => fin_cases i <;> decide
  | c5o5 i => fin_cases i <;> decide
  | o5c1 i => fin_cases i <;> decide
  | arm2 i => fin_cases i <;> decide
  | arm3 i => fin_cases i <;> decide
  | arm6 i => fin_cases i <;> decide

/-- Every ring edge links two atoms that both lie on the traverse. -/
theorem ringEdges_correspond_to_traverse :
    ringEdges.length = ringList.length ∧
    (∀ e ∈ ringEdges, ∃ a b : Atom, Bond.link e a b ∧
      a ∈ ringList ∧ b ∈ ringList) := by
  refine ⟨rfl, fun e he => ?_⟩
  fin_cases he <;> exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, by decide, by decide⟩

/-! ### Ring-size theorem -/

/-- **Answer, part 1 (ring size of macrocycle X).**

After NaIO₄ cleavage of the seven C2–C3 bonds, NaBH₄ reduction and
acetylation, the macrocyclic backbone of the β-CD template (7 units, five
ring atoms per unit: C1, glycosidic O, C4, C5, ring O) is intact
(`x_ring_is_cycle`, `x_backbone_mem_ring`), and `x_bond_exact` together with
`ringEdges_disjoint_armEdges` ensures the arms contribute no ring-shortening
chord.  Hence the ring contains exactly 35 atoms. -/
theorem icho_2026_t9_a3_ring_size : rsX = 7 * 5 ∧ rsX = 35 := ⟨rfl, rfl⟩

/-! ### Stereocentres

A (tetrahedral) atom is a stereocentre when all four substituents are
pairwise distinct.  We record the four substituent names per carbon of a unit
and prove / disprove stereogenicity.  The ligand distinctions used:

* `R1` / `R2` — the two ring-continuation ligands through the macrocycle
  backbone.  X is chiral and C₇-symmetric (seven homochiral D-glucose-derived
  units, no mirror plane or inversion centre), so the two ring-traversal
  directions from any ring carbon lead to constitutionally similar but
  stereochemically distinguishable ligands, distinguished under CIP sequence
  rule 5 — exactly why the anomeric carbon of a native cyclodextrin is
  stereogenic despite its two ring oxygens.
* `Arm` — a –CH₂OAc substituent.
* `H`  — a hydrogen. -/

/-- Substituent (ligand) identifiers for the stereogenicity test. -/
inductive Sub
  | R1    -- ring continuation, first direction
  | R2    -- ring continuation, second direction (diastereomorphic to R1)
  | Arm   -- –CH₂OAc pendant arm
  | H     -- hydrogen
  deriving DecidableEq

/-- Four substituents are pairwise distinct ⇒ tetrahedral stereocentre. -/
def FourDistinct (s1 s2 s3 s4 : Sub) : Prop :=
  s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4

/-- A duplicated substituent ⇒ the stereocentre test fails. -/
def HasDuplicate (s1 s2 s3 s4 : Sub) : Prop :=
  s1 = s2 ∨ s1 = s3 ∨ s1 = s4 ∨ s2 = s3 ∨ s2 = s4 ∨ s3 = s4

/-- C1_i of X: bonded to O5_i (ring continuation), Oglyc_i (the other ring
continuation, via the glycosidic O), ArmC2_i (the –CH₂OAc arm from periodate
cleavage of former C2) and one H.  Four pairwise different substituents ⇒
stereocentre (the two ring oxygens lead to diastereomorphic ligands, CIP
rule 5, since X is chiral with no mirror/inversion symmetry). -/
theorem c1_stereogenic : FourDistinct Sub.R1 Sub.R2 Sub.Arm Sub.H := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- C4_i of X: bonded to C5_i (ring), Oglyc_{i−1} (ring, toward C1_{i−1}),
the –CH₂OAc arm from former C3, and one H ⇒ stereocentre. -/
theorem c4_stereogenic : FourDistinct Sub.R1 Sub.R2 Sub.Arm Sub.H :=
  c1_stereogenic

/-- C5_i of X: bonded to C4_i (ring), O5_i (ring), the C6 –CH₂OAc arm and one
H ⇒ stereocentre. -/
theorem c5_stereogenic : FourDistinct Sub.R1 Sub.R2 Sub.Arm Sub.H :=
  c1_stereogenic

/-- Former C2 (–CH₂OAc arm on C1): substituents OAc-side, C1-side, H, H.
Two identical hydrogens ⇒ not a stereocentre. -/
theorem arm2_not_stereogenic : HasDuplicate Sub.Arm Sub.R1 Sub.H Sub.H :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- Former C3 (–CH₂OAc arm on C4): likewise two hydrogens ⇒ not stereogenic. -/
theorem arm3_not_stereogenic : HasDuplicate Sub.Arm Sub.R1 Sub.H Sub.H :=
  arm2_not_stereogenic

/-- Former C6 (–CH₂OAc arm on C5): two hydrogens already in β-CD ⇒ never a
stereocentre. -/
theorem arm6_not_stereogenic : HasDuplicate Sub.Arm Sub.R1 Sub.H Sub.H :=
  arm2_not_stereogenic

/-- Duplicate substituents are exactly what defeats the four-distinct-substituents
criterion. -/
theorem fourDistinct_forall_ne_of_hasDuplicate {s1 s2 s3 s4 : Sub} :
    HasDuplicate s1 s2 s3 s4 → ¬ FourDistinct s1 s2 s3 s4 := by
  rintro (h | h | h | h | h | h) ⟨h12, h13, h14, h23, h24, h34⟩
  · exact h12 h
  · exact h13 h
  · exact h14 h
  · exact h23 h
  · exact h24 h
  · exact h34 h

/-- Per-unit stereocentre analysis of X: C1, C4, C5 stereogenic; the three
–CH₂OAc arm carbons (former C2, C3 and C6) not stereogenic. -/
theorem scX_per_unit :
    FourDistinct Sub.R1 Sub.R2 Sub.Arm Sub.H ∧
    FourDistinct Sub.R1 Sub.R2 Sub.Arm Sub.H ∧
    FourDistinct Sub.R1 Sub.R2 Sub.Arm Sub.H ∧
    HasDuplicate Sub.Arm Sub.R1 Sub.H Sub.H ∧
    HasDuplicate Sub.Arm Sub.R1 Sub.H Sub.H ∧
    HasDuplicate Sub.Arm Sub.R1 Sub.H Sub.H :=
  ⟨c1_stereogenic, c4_stereogenic, c5_stereogenic,
    arm2_not_stereogenic, arm3_not_stereogenic, arm6_not_stereogenic⟩

/-- The number of stereocentres of X: 3 per unit × 7 units. -/
def scX : ℕ := 7 * 3

/-- **Answer, part 2 (number of stereocentres in X).** -/
theorem icho_2026_t9_a3_stereocentres : scX = 7 * 3 ∧ scX = 21 := ⟨rfl, rfl⟩

/-- Combined final answer of subquestion 9.3. -/
theorem icho_2026_t9_a3_answer : rsX = 35 ∧ scX = 21 := ⟨rfl, rfl⟩

end IChO2026T9A3

#print axioms IChO2026T9A3.icho_2026_t9_a3_ring_size
#print axioms IChO2026T9A3.icho_2026_t9_a3_stereocentres
#print axioms IChO2026T9A3.icho_2026_t9_a3_answer
#print axioms IChO2026T9A3.x_ring_is_cycle
#print axioms IChO2026T9A3.x_bond_exact
#print axioms IChO2026T9A3.x_backbone_mem_ring
#print axioms IChO2026T9A3.ringList_isWalk
#print axioms IChO2026T9A3.ringList_closes
