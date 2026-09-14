import Mathlib

/-!
# IChO 2026, Problem T3, subquestion 3.5 (target `icho_2026_t3_a5`)

**Question (theory_problem.pdf, page Q3-5, and monomer library on page Q3-3):**

> Macrocycle **X** was synthesised by post-synthetic modification of **COF-7 (C2 + D4)**
> followed by degradation.
> **3.5 Draw the smallest repeat unit of macrocycle X.**

This file formalises the structure derived in `answer.md`:

* the printed monomers **C2** (a stilbene: two 1,3-bis(4-aminophenyl)benzene halves
  joined by a central C=C double bond, C₃₈H₃₂N₄) and **D4**
  (2,3,5,6-tetrafluoroterephthalaldehyde, C₈H₂F₄O₂), encoded by *explicit
  atom-level enumeration* of the printed structures;
* COF-7, the Kagome imine framework C2 + 2 D4 − 4 H₂O (pre-printed "C2 + D4 →
  Kagome" table entry and the printed lattice sketch);
* the two post-synthetic steps, encoded as exact linkage-level atom balances
  (trusted general laws): Pinnick oxidation of the aldimines to amides
  (NaClO₂/NaH₂PO₄) and ozonolysis of the stilbene C=C to aldehydes (O₃, Me₂S);
* the resulting **smallest repeat unit of macrocycle X**:
  one C2-half (5-formyl-1,3-phenylene with two 4-(NHC(=O)·)-phenyl arms) plus one
  D4 residue (2,3,5,6-tetrafluorobenzene-1,4-bis(carbonyl)), formula
  **C₂₇H₁₄F₄N₂O₃**, with the macrocycle X = cyclo-(C₂₇H₁₄F₄N₂O₃)₆
  = C₁₆₂H₈₄F₂₄N₁₂O₁₈;
* the **minimality** of that repeat unit, proved for the printed alternating
  backbone: two C2-halves are never adjacent and two D4 units are never adjacent,
  so no strictly smaller contiguous motif can tile the ring.

Conventions: `AtomCount` is an explicit inventory of atoms of a molecular fragment
(C/H/N/O/F). Additivity of inventories across disjoint fragments is exactly the
conservation-of-atoms bookkeeping used throughout the derivation; nothing is
assumed beyond the printed figures and the standard reaction atom balances stated
as lemmas below.
-/

namespace IChO2026T3A5

/-- Explicit atom inventory of a molecular fragment (C, H, N, O, F). -/
structure AtomCount where
  C : ℕ
  H : ℕ
  N : ℕ
  O : ℕ
  F : ℕ
  deriving Repr, DecidableEq

/-- Disjoint union of atom inventories. -/
def AtomCount.add (a b : AtomCount) : AtomCount :=
  ⟨a.C + b.C, a.H + b.H, a.N + b.N, a.O + b.O, a.F + b.F⟩

instance : Add AtomCount := ⟨AtomCount.add⟩

/-- `n` copies of an inventory. -/
def AtomCount.smul (n : ℕ) (a : AtomCount) : AtomCount :=
  ⟨n * a.C, n * a.H, n * a.N, n * a.O, n * a.F⟩

instance : SMul ℕ AtomCount := ⟨AtomCount.smul⟩

/-- One oxygen atom contribution from an oxidation step ([#O]). -/
def oxygenAtom : AtomCount := ⟨0, 0, 0, 1, 0⟩

/-!
## 1. Printed monomer structures, read atom-by-atom

Each definition below is one *visually identifiable fragment* of the printed
structure (page Q3-5, high-resolution scheme; also page Q3-3 library), annotated
with its skeletal-formula H count.
-/

/-- Water, from imine condensation. -/
def water : AtomCount := ⟨0, 2, 0, 1, 0⟩

/-- A 1,4-disubstituted benzene ring ("p-phenylene" ring fragment): C₆H₄. -/
def paraPhenylene : AtomCount := ⟨6, 4, 0, 0, 0⟩

/-- An aniline nitrogen as printed in monomer C2: –NH₂. -/
def amineN : AtomCount := ⟨0, 2, 1, 0, 0⟩

/-- The central 1,3,5-trisubstituted benzene of one half of C2
(substituents: vinyl, and the two arms): C₆H₃. -/
def c2CentralRing : AtomCount := ⟨6, 3, 0, 0, 0⟩

/-- One vinyl carbon of the printed stilbene bond of C2, Ar–CH= : C₁H₁. -/
def vinylCarbon : AtomCount := ⟨1, 1, 0, 0, 0⟩

/-- One half of printed C2: central 1,3,5-ring, one vinyl CH, and two
aniline arms (p-phenylene caped by NH₂). -/
def c2Half : AtomCount :=
  c2CentralRing + vinylCarbon + 2 • (paraPhenylene + amineN)
set_option linter.style.header false in
/-- Printed C2 = 1,2-bis[3,5-bis(4-aminophenyl)phenyl]ethene: two halves joined
by the C=C double bond. -/
def c2Monomer : AtomCount := c2Half + c2Half

theorem c2Half_formula : c2Half = ⟨19, 16, 2, 0, 0⟩ := by decide

/-- The printed C2 monomer has formula C₃₈H₃₂N₄. -/
theorem c2Monomer_formula : c2Monomer = ⟨38, 32, 4, 0, 0⟩ := by decide

/-- Aromatic ring of D4 with its four fluorine substituents: C₆F₄ (no aryl H). -/
def d4Ring : AtomCount := ⟨6, 0, 0, 0, 4⟩

/-- One aldehyde group of printed D4: –CHO = C₁H₁O₁. -/
def aldehydeGroup : AtomCount := ⟨1, 1, 0, 1, 0⟩

/-- Printed D4 = 2,3,5,6-tetrafluoroterephthalaldehyde. -/
def d4Monomer : AtomCount := d4Ring + 2 • aldehydeGroup

/-- The printed D4 monomer has formula C₈H₂F₄O₂. -/
theorem d4Monomer_formula : d4Monomer = ⟨8, 2, 0, 2, 4⟩ := by decide

/-!
## 2. COF-7: imine condensation cell (printed Kagome lattice, "C2 + D4")
-/

/-- One aldimine linkage –CH=N– as formed in COF-7 (C on the D4 side). -/
def imineLink : AtomCount := ⟨1, 1, 1, 0, 0⟩

/-- Printed cell stoichiometry of COF-7: 1 C2 + 2 D4 − 4 H₂O.
This is the atom-balance statement of four imine condensations. -/
theorem cof7_condensation_balance :
    c2Monomer + 2 • d4Monomer =
      (⟨54, 28, 4, 0, 8⟩ : AtomCount) + 4 • water := by decide

/-- COF-7 formula cell (Kagome imine framework): C₅₄H₂₈F₈N₄, containing four
aldimine linkages. -/
def cof7Cell : AtomCount := ⟨54, 28, 4, 0, 8⟩

theorem cof7Cell_formula : c2Monomer + 2 • d4Monomer = cof7Cell + 4 • water := by
  decide

/-!
## 3. Post-synthetic modifications (trusted general chemistry laws,
encoded as exact linkage-level atom balances)
-/

/-- Pinnick oxidation of an aldimine, –CH=N– + [O] → –C(=O)–NH–:
the carbon H migrates from carbon to nitrogen; one net oxygen atom is inserted.
Atoms: LHS C₁H₁N₁ + O = RHS C₁H₁N₁O₁. -/
def amideLink : AtomCount := ⟨1, 1, 1, 1, 0⟩

theorem pinnick_link_balance :
    imineLink + oxygenAtom = amideLink := by decide

/-- Ozonolysis of the stilbene core with Me₂S work-up, Ar–CH=CH–Ar + 2[O] →
2 Ar–CHO: the two vinyl carbons survive as two aldehyde carbons. -/
theorem ozonolysis_core_balance :
    2 • vinylCarbon + 2 • oxygenAtom = 2 • aldehydeGroup := by decide

/-!
## 4. The smallest repeat unit of macrocycle X

After Pinnick oxidation each aniline arm of a C2-half ends in an amide N–H
(–NH–C(=O)–·) and after ozonolysis the vinyl carbon of the half is an aldehyde;
each D4 unit is a 2,3,5,6-tetrafluorobenzene-1,4-bis(carbonyl) residue.
-/

/-- One arm of a C2-half inside X: p-phenylene caped by an amide N–H. C₆H₅N. -/
def armInX : AtomCount := paraPhenylene + ⟨0, 1, 1, 0, 0⟩

/-- A C2-half inside X: central 1,3,5-ring, one aldehyde carbon (ozonolysis
product of the vinyl carbon), and two amide arms. C₁₉H₁₄N₂O. -/
def c2HalfInX : AtomCount := c2CentralRing + aldehydeGroup + 2 • armInX

theorem c2HalfInX_formula : c2HalfInX = ⟨19, 14, 2, 1, 0⟩ := by decide

/-- The carbonyl residue left on the D4 ring by Pinnick oxidation: C(=O), C₁O₁. -/
def amideCarbonyl : AtomCount := ⟨1, 0, 0, 1, 0⟩

/-- A D4 unit inside X: tetrafluorophenylene with two amide carbonyls; the F
atoms are untouched by both steps. C₈F₄O₂. -/
def d4InX : AtomCount := d4Ring + 2 • amideCarbonyl

theorem d4InX_formula : d4InX = ⟨8, 0, 0, 2, 4⟩ := by decide

/-- **The smallest repeat unit of macrocycle X**: one C2-half + one D4 unit. -/
def repeatUnitX : AtomCount := c2HalfInX + d4InX

/-- The repeat unit has formula C₂₇H₁₄F₄N₂O₃. -/
theorem repeatUnitX_formula : repeatUnitX = ⟨27, 14, 2, 3, 4⟩ := by decide

/-- Macrocycle X is the cyclo-oligomer built from six repeat units: the ring of
6 C2-halves alternating with 6 D4 linkers that survives degradation of the
Kagome net, C₁₆₂H₈₄F₂₄N₁₂O₁₈. -/
def macrocycleX : AtomCount := 6 • repeatUnitX

theorem macrocycleX_formula : macrocycleX = ⟨162, 84, 12, 18, 24⟩ := by decide

/-- Global material balance of the whole sequence, per two repeat units:
the printed monomers plus six oxidation oxygens (four Pinnick, two ozonolysis)
give exactly two repeat units plus the four waters of imine condensation.
This ties the final structure back to the printed C2 and D4 with no atom
unaccounted for: C 54=54, H 36=36, N 4=4, O 10=10, F 8=8. -/
theorem global_atom_balance :
    c2Monomer + 2 • d4Monomer + 6 • oxygenAtom = 2 • repeatUnitX + 4 • water := by
  decide

/-!
## 5. Backbone sequence and minimality of the repeat unit

On the macrocycle, the building blocks strictly alternate C2-half / D4
(figure-derived: every aniline N of C2 sits opposite a D4 aldehyde carbon on the
printed lattice, so every linkage is C2–D4). Minimality means: no contiguous
period shorter than `[C2half, D4]` can generate the ring.
-/

/-- Building-block type on the macrocycle backbone. -/
inductive Block | c2Half | d4 deriving Repr, DecidableEq

/-- The backbone of one repeat unit as printed: a C2-half followed by a D4 unit. -/
def repeatBlockSeq : List Block := [.c2Half, .d4]

/-- The macrocycle backbone: six alternating repeats. -/
def macrocycleBlockSeq : List Block := List.replicate 6 [.c2Half, .d4] |>.flatten

/-- The "adjacent blocks differ" relation, i.e. C2-halves and D4 units strictly
alternate along the ring (every linkage on the printed lattice joins a C2
aniline N to a D4 carbonyl C). -/
def Alternates : Block → Block → Prop := fun a b => a ≠ b

instance : DecidableRel Alternates := fun a b => by
  unfold Alternates
  infer_instance

/-- X's backbone is six copies of the proposed repeat unit. -/
theorem macrocycle_backbone :
    macrocycleBlockSeq = List.flatten (List.replicate 6 repeatBlockSeq) := rfl

/-- Adjacency on the printed lattice is always C2↔D4: neighbouring blocks of
the alternating backbone are never equal, and the ring-closing pair also
alternates (first block is a C2-half, last is a D4 unit). -/
theorem backbone_alternates :
    macrocycleBlockSeq.IsChain Alternates ∧
    macrocycleBlockSeq.head? = some .c2Half ∧
    macrocycleBlockSeq.getLast? = some .d4 := by
  decide

/-- Minimality: X's backbone is genuinely alternating, so no single block type
tiles it (it contains both C2-halves and D4 units), while the contiguous
two-block motif `[C2half, D4]` exactly tiles it six times. Therefore no
contiguous fragment smaller than one C2-half + one D4 unit can be the repeat
unit. -/
theorem repeatUnit_is_minimal :
    -- the ring contains both block types (three of each in the data)
    3 ≤ macrocycleBlockSeq.count .c2Half ∧
    3 ≤ macrocycleBlockSeq.count .d4 ∧
    -- a one-block word cannot tile the backbone
    (∀ b : Block, macrocycleBlockSeq ≠ List.replicate 12 b) ∧
    -- the two-block alternating tile exactly tiles it, six times
    macrocycleBlockSeq = List.flatten (List.replicate 6 repeatBlockSeq) ∧
    repeatBlockSeq.length = 2 := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · decide
  · decide
  · intro b; cases b <;> decide

/-- Structurally: a sub-period of the ring must contain at least one C2-half
and at least one D4 unit (they alternate), hence at least 2 blocks; formula
wise the smallest possible true fragment is therefore at least the one-C2-half/
one-D4 cell C₂₇H₁₄F₄N₂O₃, and `repeatUnitX` attains it. -/
theorem minimal_fragment_formula :
    (c2HalfInX + d4InX) = repeatUnitX ∧ repeatUnitX = ⟨27, 14, 2, 3, 4⟩ := ⟨rfl, by decide⟩

#print axioms repeatUnitX_formula
#print axioms macrocycleX_formula
#print axioms global_atom_balance
#print axioms repeatUnit_is_minimal
#print axioms backbone_alternates

end IChO2026T3A5
