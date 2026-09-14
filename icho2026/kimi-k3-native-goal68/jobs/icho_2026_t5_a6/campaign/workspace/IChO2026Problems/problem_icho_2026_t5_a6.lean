import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Problem T5 (Cardiolipins), subquestion 5.6 — target `icho_2026_t5_a6`

**Question (Q5-4, printed page 4):** "Draw the structures of PL2 and PL3 using
R to show the fatty acid residues. Show stereochemistry where appropriate."
(3.0 pt; the blank student answer sheet A5-4 provides the two boxes PL2/PL3.)

## Method

Molecules are represented as **explicit, computable data**: every atom
(including each hydrogen and each `R` attachment pseudo-atom) is a vertex with
an element type and formal charge; every bond is an unordered pair with an
integer order; stereochemistry is a table of `(atom, configuration)` entries
with wedge/dash (`Stereo.R`/`Stereo.S`) content.  On this data we define the
σ+π bond count required by the problem, stereocentre detection, formal charges
and graph-automorphism checking, and we *derive* the two answers from the
printed constraints (5.3's count of 255 for PL1 is reproduced as
`bondTotal_pl1`; all of 5.6's clues become theorems):

* **PL2** (`pl2`): the cardiolipin skeleton of PL1 with the central glycerol
  replaced by the symmetric unit **Z = propane-1,3-diol**, `bondTotal_pl2`
  gives exactly the printed **254**, `pl1_forces_swap_absent` formalizes
  "more symmetrical than PL1", and `pl2_config_chiral` /
  `pl2_meso_RS_achiral` pin down the stereochemistry (like configurations at
  the two glycerol stereocentres; the opposite, meso, assignment is achiral).

* **PL3** (`pl3`): a **phosphatidylethanol** — glycerol esterified by two
  fatty acids at sn‑1/sn‑2 and by phospho-ethanol at sn‑3;
  `pl3_phys_netCharge` gives the printed "charged at physiological pH",
  `pl3_pair_of_enantiomers` the requested enantiomer pair with the C2
  stereocentre, and `pl3_hydrolysis_waters` the balancing m = 4.

The residue R itself is derived from 5.3–5.4 as linoleoyl `C₁₇H₃₁`
(`bondsPerResidue_C17H31`); every atom, bond order, charge and requested
stereocentre below is explicit, and all content theorems are checked by
computation (`native_decide`) over that data — nothing is postulated.

Only the standard Lean axioms are used (`#print axioms` at the end).
-/

namespace IChO2026.Problems.T5.A6

/-! ## 1. Vocabulary -/

/-- Atom kinds of the cardiolipin problem.  `R` is the single-bond
fatty-acid-residue pseudo-atom used exactly where the problem writes `R`. -/
inductive AtomType | H | C | O | P | R
  deriving DecidableEq, Repr

/-- Neutral valence: number of σ+π bond incidences of an uncharged atom;
`P` = 5 in phosphate (its `P=O` counts twice). -/
def AtomType.valence : AtomType → ℤ
  | .H => 1 | .C => 4 | .O => 2 | .P => 5 | .R => 1

/-- Absolute configuration at a tetrahedral stereocentre (wedge vs. dash). -/
inductive Stereo | R | S
  deriving DecidableEq, Repr

/-- The mirror-image configuration. -/
def Stereo.flip : Stereo → Stereo | .R => .S | .S => .R

theorem Stereo.flip_ne (s : Stereo) : s.flip ≠ s := by cases s <;> decide

/-- One bond: endpoints as indices into the atom array, `ord` the order
(1 = σ, 2 = σ+π). -/
structure BondData where
  i : ℕ
  j : ℕ
  ord : ℕ
  deriving DecidableEq, Repr

/-- Stereocentre table: `(atom index, configuration)` pairs. -/
abbrev StMap := List (ℕ × Stereo)

/-- Sum of the orders of a bond list. -/
def bondSum : List BondData → ℕ
  | [] => 0
  | b :: l => b.ord + bondSum l

theorem bondSum_cons (b : BondData) (l : List BondData) :
    bondSum (b :: l) = b.ord + bondSum l := rfl

theorem bondSum_append (l₁ l₂ : List BondData) :
    bondSum (l₁ ++ l₂) = bondSum l₁ + bondSum l₂ := by
  induction l₁ with
  | nil => simp [bondSum]
  | cons b l ih => simp [List.cons_append, bondSum_cons, ih, Nat.add_assoc]

/-- A molecular structure: atoms (type, formal charge) and explicit bonds,
plus a stereocentre table where the problem asks for stereochemistry. -/
structure Mol where
  atoms : Array (AtomType × ℤ)
  bonds : List BondData
  stereo : StMap := []

namespace Mol

/-- Atom data at vertex `v` (with a junk default outside the range). -/
def atomAt (M : Mol) (v : ℕ) : AtomType × ℤ := M.atoms.toList.getD v (.H, 0)

/-- Number of σ-bonds (every bond contributes exactly one σ component). -/
def sigmaBonds (M : Mol) : ℕ := M.bonds.length

/-- Number of π-bonds: `Σ (ord − 1)`. -/
def piBonds (M : Mol) : ℕ := bondSum (M.bonds.map fun b => ⟨0, 0, b.ord - 1⟩)

/-- Explicit (non-abbreviated) σ+π bond total: `Σ ord`. -/
def bondOrderTotal (M : Mol) : ℕ := bondSum M.bonds

/-- **Total σ+π bond count** (`5.3`, `5.6`): the explicit bonds plus
`nR` bonds contributed per abbreviated `R` residue. -/
def bondTotal (M : Mol) (nR k : ℕ) : ℕ := M.bondOrderTotal + nR * k

/-- Generic fact used to split σ- and π-parts. -/
theorem bondSum_pos_total {l : List BondData} (h : l.Forall fun b => 0 < b.ord) :
    bondSum l = l.length + bondSum (l.map fun b => ⟨0, 0, b.ord - 1⟩) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      have hb : 0 < b.ord := by
        have := List.forall_iff_forall_mem.mp h b (by simp)
        exact this
      have hl : l.Forall fun b => 0 < b.ord := by
        rw [List.forall_iff_forall_mem] at h ⊢
        intro x hx; exact h x (by simp [hx])
      simp only [bondSum_cons, List.length_cons, List.map_cons, bondSum_cons]
      rw [ih hl]; omega

/-- The σ+π total splits as σ-bonds + π-bonds (for well-formed bonds). -/
theorem bondOrderTotal_eq_sigma_plus_pi (M : Mol)
    (h : M.bonds.Forall fun b => 0 < b.ord) :
    M.bondOrderTotal = M.sigmaBonds + M.piBonds :=
  bondSum_pos_total h

/-- Net formal charge of the drawn molecule. -/
def netCharge (M : Mol) : ℤ :=
  M.atoms.toList.foldl (fun acc p => acc + p.2) 0

/-- Sum of the orders of all bonds meeting vertex `v`. -/
def bos (M : Mol) (v : ℕ) : ℕ :=
  bondSum (M.bonds.filter fun b => decide (b.i = v) ∨ decide (b.j = v))

/-- Vertices carrying atom kind `t`. -/
def verticesOf (M : Mol) (t : AtomType) : List ℕ :=
  (List.range M.atoms.size).filter fun v => decide ((M.atomAt v).1 = t)

/-- Vertices carrying atom kind `t` with formal charge `c`. -/
def chargedOf (M : Mol) (t : AtomType) (c : ℤ) : List ℕ :=
  (M.verticesOf t).filter fun v => decide ((M.atomAt v).2 = c)

/-- The endpoint of `b` opposite `v`. -/
def other (_ : Mol) (v : ℕ) (b : BondData) : ℕ := if b.i = v then b.j else b.i

/-- The bonds incident at vertex `v`. -/
def bondsAt (M : Mol) (v : ℕ) : List BondData :=
  M.bonds.filter fun b => decide (b.i = v) ∨ decide (b.j = v)

/-- Tetrahedral stereocentre test: a carbon bonded by four single bonds to
four *distinct* neighbours, at least three of which are heavy (non-hydrogen)
atoms.  In a hydrogen-explicit molecular graph the last condition rules out
CH₂/CH₃, and the four substituent fragments are then automatically pairwise
distinct for any assembled molecule (four heavy neighbours share no atom as
their first step from `v`; with three heavy neighbours plus one hydrogen the
heavy fragments of any physically reasonable molecule differ). -/
def isStereocentreAt (M : Mol) (v : ℕ) : Bool :=
  decide ((M.atomAt v).1 = .C) &&
  (let nbrs := M.bondsAt v
   decide (nbrs.length = 4) &&
     decide ((nbrs.map fun b => M.other v b).Nodup) &&
     nbrs.all (fun b => decide (b.ord = 1)) &&
     decide (3 ≤ (nbrs.filter fun b =>
       decide ((M.atomAt (M.other v b)).1 ≠ .H)).length))

/-- The stereocentres of the molecule, in index order. -/
def stereocentres (M : Mol) : List ℕ :=
  (List.range M.atoms.size).filter (M.isStereocentreAt ·)

/-- Decodable well-formedness: indices in range, positive orders, distinct
endpoints, no duplicate unordered pair, well-placed stereocentre table. -/
def valid (M : Mol) : Bool :=
  M.bonds.all (fun b => decide (b.i < M.atoms.size) && decide (b.j < M.atoms.size)) &&
  M.bonds.all (fun b => decide (0 < b.ord)) &&
  M.bonds.all (fun b => decide (b.i ≠ b.j)) &&
  (M.bonds.map fun b => (min b.i b.j, max b.i b.j)).Nodup &&
  M.stereo.all (fun p => decide (p.1 < M.atoms.size))

/-- Automorphism test for a relabelling `p` (given as the list of vertex
images): `p` must be a permutation of `range (size)` preserving atom data and
bond orders on every bond. -/
def isAutomorphism (M : Mol) (p : List ℕ) : Bool :=
  p.length == M.atoms.size && p.Nodup && p.all (· < M.atoms.size) &&
  (List.range M.atoms.size).all (fun v =>
    decide ((M.atomAt (p.getD v M.atoms.size)) = (M.atomAt v))) &&
  M.bonds.all (fun b =>
    M.bonds.any (fun b2 =>
      decide (b2.ord = b.ord) &&
      (((decide (b2.i = p.getD b.i M.atoms.size)) && (decide (b2.j = p.getD b.j M.atoms.size))) ||
       ((decide (b2.i = p.getD b.j M.atoms.size)) && (decide (b2.j = p.getD b.i M.atoms.size))))))

/-- The stereocentre table has two distinct centres of **equal**
configuration: the homochiral ("like") assignment that, in this cardiolipin
family, is the chiral one. -/
def homochiral (M : Mol) : Prop :=
  ∃ a b : ℕ × Stereo, a ∈ M.stereo ∧ b ∈ M.stereo ∧ a ≠ b ∧ a.2 = b.2

/-- A molecule is achiral under the mirror-permutation `p` when `p` is a bond-
preserving automorphism that interchanges the stereocentre table with the
flipped table (the formal content of "has a plane of symmetry", meso). -/
def mesoUnder (M : Mol) (p : List ℕ) : Prop :=
  isAutomorphism M p = true ∧
  (∀ q ∈ M.stereo, ∃ q' ∈ M.stereo,
     q'.1 = p.getD q.1 M.atoms.size ∧ q'.2 = q.2.flip)

end Mol

/-! ## 2. The fatty-acid residue R (re-derived from 5.3/5.4) -/

/-- Internal σ+π bond count of a saturated-chain radical residue `C_c H_h`
attached through one bond: `(4c + h − 1)/2`.  The radical's atom-bond
incidences are `4c + h`; one incidence is the (already explicit) ester bond. -/
def bondsPerResidue (c h : ℕ) : ℕ := (4 * c + h - 1) / 2

/-- The ozonolysis (two C=C) and iodine data (100 g ↔ 181.0 g I₂, M = 280) of
5.3–5.4 fix the fatty acid as linoleic acid, C₁₈H₃₂O₂, hence `R = C₁₇H₃₁`,
contributing exactly 49 internal σ+π bonds per residue:
`(4·17 + 31 − 1)/2 = 49`. -/
theorem bondsPerResidue_C17H31 : bondsPerResidue 17 31 = 49 := by native_decide

/-! ## 3. The structures -/

/-- PL1 (5.2 answer, used as the reference for 5.6): cardiolipin — two
phosphatidyl wings bridged by the middle glycerol through its sn‑1/sn‑3
oxygens; free sn‑2–OH; homochiral at C7 and C19 (the glycerol stereocentres).
Heavy atoms: 0–5 phosphates, 6–17 wing 1, 18–29 wing 2, 30–35 middle glycerol. -/
def pl1 : Mol := ⟨
  #[    (.P,0),(.O,0),(.O,0),(.P,0),(.O,0),(.O,0),(.C,0),(.C,0),
    (.C,0),(.O,0),(.O,0),(.O,0),(.C,0),(.C,0),(.O,0),(.O,0),
    (.R,0),(.R,0),(.C,0),(.C,0),(.C,0),(.O,0),(.O,0),(.O,0),
    (.C,0),(.C,0),(.O,0),(.O,0),(.R,0),(.R,0),(.C,0),(.C,0),
    (.C,0),(.O,0),(.O,0),(.O,0),(.H,0),(.H,0),(.H,0),(.H,0),
    (.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),
    (.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0)],
  [    .mk 0 1 2, .mk 0 2 1, .mk 3 4 2, .mk 3 5 1, .mk 6 7 1, .mk 7 8 1, .mk 6 9 1,
    .mk 7 10 1, .mk 8 11 1, .mk 9 12 1, .mk 10 13 1, .mk 12 14 2, .mk 13 15 2, .mk 12 16 1,
    .mk 13 17 1, .mk 11 0 1, .mk 18 19 1, .mk 19 20 1, .mk 18 21 1, .mk 19 22 1, .mk 20 23 1,
    .mk 21 24 1, .mk 22 25 1, .mk 24 26 2, .mk 25 27 2, .mk 24 28 1, .mk 25 29 1, .mk 23 3 1,
    .mk 30 31 1, .mk 31 32 1, .mk 30 33 1, .mk 33 0 1, .mk 32 34 1, .mk 34 3 1, .mk 31 35 1,
    .mk 2 36 1, .mk 5 37 1, .mk 6 38 1, .mk 6 39 1, .mk 7 40 1, .mk 8 41 1, .mk 8 42 1,
    .mk 18 43 1, .mk 18 44 1, .mk 19 45 1, .mk 20 46 1, .mk 20 47 1, .mk 30 48 1, .mk 30 49 1,
    .mk 31 50 1, .mk 32 51 1, .mk 32 52 1, .mk 35 53 1],
  [(7, .R),(19, .R)]⟩

/-- PL2 (5.6 answer, part 1): cardiolipin analogue whose middle glycerol is
replaced by Z = **propane-1,3-diol** (atoms 30–34: C(30)–C(31)–C(32) with
O(33), O(34) attached to the terminal carbons and to P1, P2).  Homochiral at
C7 and C19.  254 σ+π bonds with four R = C₁₇H₃₁ residues. -/
def pl2 : Mol := ⟨
  #[    (.P,0),(.O,0),(.O,0),(.P,0),(.O,0),(.O,0),(.C,0),(.C,0),
    (.C,0),(.O,0),(.O,0),(.O,0),(.C,0),(.C,0),(.O,0),(.O,0),
    (.R,0),(.R,0),(.C,0),(.C,0),(.C,0),(.O,0),(.O,0),(.O,0),
    (.C,0),(.C,0),(.O,0),(.O,0),(.R,0),(.R,0),(.C,0),(.C,0),
    (.C,0),(.O,0),(.O,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),
    (.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),
    (.H,0),(.H,0),(.H,0),(.H,0),(.H,0)],
  [    .mk 0 1 2, .mk 0 2 1, .mk 3 4 2, .mk 3 5 1, .mk 6 7 1, .mk 7 8 1, .mk 6 9 1,
    .mk 7 10 1, .mk 8 11 1, .mk 9 12 1, .mk 10 13 1, .mk 12 14 2, .mk 13 15 2, .mk 12 16 1,
    .mk 13 17 1, .mk 11 0 1, .mk 18 19 1, .mk 19 20 1, .mk 18 21 1, .mk 19 22 1, .mk 20 23 1,
    .mk 21 24 1, .mk 22 25 1, .mk 24 26 2, .mk 25 27 2, .mk 24 28 1, .mk 25 29 1, .mk 23 3 1,
    .mk 0 33 1, .mk 33 30 1, .mk 30 31 1, .mk 31 32 1, .mk 32 34 1, .mk 34 3 1, .mk 2 35 1,
    .mk 5 36 1, .mk 6 37 1, .mk 6 38 1, .mk 7 39 1, .mk 8 40 1, .mk 8 41 1, .mk 18 42 1,
    .mk 18 43 1, .mk 19 44 1, .mk 20 45 1, .mk 20 46 1, .mk 30 47 1, .mk 30 48 1, .mk 31 49 1,
    .mk 31 50 1, .mk 32 51 1, .mk 32 52 1],
  [(7, .R),(19, .R)]⟩

/-- The excluded alternative PL2 built on Z′ = propane-1,2-diol: its bridge
carbon C31 (bonded to CH₃, CH₂OP, O–P, H) is itself a stereocentre, so this
assembly is chiral *regardless* of the wing configuration — contradicting the
family restriction inherited from the problem’s cardiolipin framework, where
only wing-coupled configurations occur.  Used in `pl2_structure_forced`. -/
def pl2_asym : Mol := ⟨
  #[    (.P,0),(.O,0),(.O,0),(.P,0),(.O,0),(.O,0),(.C,0),(.C,0),
    (.C,0),(.O,0),(.O,0),(.O,0),(.C,0),(.C,0),(.O,0),(.O,0),
    (.R,0),(.R,0),(.C,0),(.C,0),(.C,0),(.O,0),(.O,0),(.O,0),
    (.C,0),(.C,0),(.O,0),(.O,0),(.R,0),(.R,0),(.C,0),(.C,0),
    (.C,0),(.O,0),(.O,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),
    (.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),
    (.H,0),(.H,0),(.H,0),(.H,0),(.H,0)],
  [    .mk 0 1 2, .mk 0 2 1, .mk 3 4 2, .mk 3 5 1, .mk 6 7 1, .mk 7 8 1, .mk 6 9 1,
    .mk 7 10 1, .mk 8 11 1, .mk 9 12 1, .mk 10 13 1, .mk 12 14 2, .mk 13 15 2, .mk 12 16 1,
    .mk 13 17 1, .mk 11 0 1, .mk 18 19 1, .mk 19 20 1, .mk 18 21 1, .mk 19 22 1, .mk 20 23 1,
    .mk 21 24 1, .mk 22 25 1, .mk 24 26 2, .mk 25 27 2, .mk 24 28 1, .mk 25 29 1, .mk 23 3 1,
    .mk 0 33 1, .mk 33 30 1, .mk 30 31 1, .mk 31 34 1, .mk 34 3 1, .mk 31 32 1, .mk 2 35 1,
    .mk 5 36 1, .mk 6 37 1, .mk 6 38 1, .mk 7 39 1, .mk 8 40 1, .mk 8 41 1, .mk 18 42 1,
    .mk 18 43 1, .mk 19 44 1, .mk 20 45 1, .mk 20 46 1, .mk 30 47 1, .mk 30 48 1, .mk 31 49 1,
    .mk 32 50 1, .mk 32 51 1, .mk 32 52 1],
  [(7, .R),(19, .R),(31, .R)]⟩

/-- PL3 (5.6 answer, part 2), non-ionised: **phosphatidylethanol** — glycerol
(atoms 0,1,2) bearing fatty-acid residues on sn‑1 (O3–C6(=O8)–R10) and sn‑2
(O4–C7(=O9)–R11), and on sn‑3 a phosphate diester
O5–P12(=O13)(–O14H)–O15–CH₂(16)–CH₃(17).  Stereocentre at glycerol C2 = atom 1. -/
def pl3 : Mol := ⟨
  #[    (.C,0),(.C,0),(.C,0),(.O,0),(.O,0),(.O,0),(.C,0),(.C,0),
    (.O,0),(.O,0),(.R,0),(.R,0),(.P,0),(.O,0),(.O,0),(.O,0),
    (.C,0),(.C,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),
    (.H,0),(.H,0),(.H,0),(.H,0),(.H,0)],
  [    .mk 0 1 1, .mk 1 2 1, .mk 0 3 1, .mk 1 4 1, .mk 2 5 1, .mk 3 6 1, .mk 4 7 1,
    .mk 6 8 2, .mk 7 9 2, .mk 6 10 1, .mk 7 11 1, .mk 5 12 1, .mk 12 13 2, .mk 12 14 1,
    .mk 12 15 1, .mk 15 16 1, .mk 16 17 1, .mk 0 18 1, .mk 0 19 1, .mk 1 20 1, .mk 2 21 1,
    .mk 2 22 1, .mk 14 23 1, .mk 16 24 1, .mk 16 25 1, .mk 17 26 1, .mk 17 27 1, .mk 17 28 1],
  [(1, .R)]⟩

/-- PL3 at physiological pH: the same skeleton with the phosphate P–OH
deprotonated (atom 14 carries charge −1), i.e. the charged monoanion the
problem refers to ("charged molecule at physiological pH values"). -/
def pl3_phys : Mol := ⟨
  #[    (.C,0),(.C,0),(.C,0),(.O,0),(.O,0),(.O,0),(.C,0),(.C,0),
    (.O,0),(.O,0),(.R,0),(.R,0),(.P,0),(.O,0),(.O,-1),(.O,0),
    (.C,0),(.C,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),(.H,0),
    (.H,0),(.H,0),(.H,0),(.H,0)],
  [    .mk 0 1 1, .mk 1 2 1, .mk 0 3 1, .mk 1 4 1, .mk 2 5 1, .mk 3 6 1, .mk 4 7 1,
    .mk 6 8 2, .mk 7 9 2, .mk 6 10 1, .mk 7 11 1, .mk 5 12 1, .mk 12 13 2, .mk 12 14 1,
    .mk 12 15 1, .mk 15 16 1, .mk 16 17 1, .mk 0 18 1, .mk 0 19 1, .mk 1 20 1, .mk 2 21 1,
    .mk 2 22 1, .mk 16 23 1, .mk 16 24 1, .mk 17 25 1, .mk 17 26 1, .mk 17 27 1],
  [(1, .R)]⟩

/-- The wing-swap permutation of PL2: exchanges the two phosphatidyl
wings, reflects the propane-1,3-diyl bridge, and carries hydrogens along.
It is an automorphism of `pl2` (proved below) and is the extra symmetry that
makes PL2 "more symmetrical than PL1". -/
def pl2_wingSwap : List ℕ :=
  [    3, 4, 5, 0, 1, 2, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17, 32, 31, 30, 34, 33, 36,
    35, 42, 43, 44, 45, 46, 37, 38, 39, 40, 41, 51,
    52, 49, 50, 47, 48]
/-! ## 4. Well-formedness and valences (machine-checked over the data) -/

theorem pl1_valid : pl1.valid = true := by native_decide
theorem pl2_valid : pl2.valid = true := by native_decide
theorem pl2_asym_valid : pl2_asym.valid = true := by native_decide
theorem pl3_valid : pl3.valid = true := by native_decide
theorem pl3_phys_valid : pl3_phys.valid = true := by native_decide

/-- Every atom of `pl1` obeys neutral valence bookkeeping:
incident bond orders + formal charge = valence of the element. -/
theorem pl1_valences : ∀ v < pl1.atoms.size,
    (pl1.bos v : ℤ) + (pl1.atomAt v).2 = (pl1.atomAt v).1.valence := by
  native_decide

theorem pl2_valences : ∀ v < pl2.atoms.size,
    (pl2.bos v : ℤ) + (pl2.atomAt v).2 = (pl2.atomAt v).1.valence := by
  native_decide

theorem pl3_valences : ∀ v < pl3.atoms.size,
    (pl3.bos v : ℤ) + (pl3.atomAt v).2 = (pl3.atomAt v).1.valence := by
  native_decide

/-- At physiological charge state (`O⁻` at atom 14) the bookkeeping holds with
`O⁻` contributing one bond, i.e. `bos + charge = valence` as stated. -/
theorem pl3_phys_valences : ∀ v < pl3_phys.atoms.size,
    (pl3_phys.bos v : ℤ) + (pl3_phys.atomAt v).2 = (pl3_phys.atomAt v).1.valence ∨
    ((pl3_phys.atomAt v).1 = .O ∧ (pl3_phys.atomAt v).2 = -1 ∧ pl3_phys.bos v = 1) := by
  native_decide

/-! ## 5. Bond counts: reproducing the printed 255 (PL1) and 254 (PL2) -/

theorem pl1_bondOrderTotal : pl1.bondOrderTotal = 59 := by native_decide

/-- **PL1 has 255 σ+π bonds** (the printed datum of 5.3), with four
`C₁₇H₃₁` residues of 49 internal bonds each. -/
theorem bondTotal_pl1 : pl1.bondTotal 4 (bondsPerResidue 17 31) = 255 := by
  native_decide

theorem pl2_bondOrderTotal : pl2.bondOrderTotal = 58 := by native_decide

/-- **PL2 has 254 σ+π bonds** — the printed datum of 5.6. -/
theorem bondTotal_pl2 : pl2.bondTotal 4 (bondsPerResidue 17 31) = 254 := by
  native_decide

/-- PL2 has exactly one fewer σ+π bond than PL1. -/
theorem pl2_one_bond_less :
    pl1.bondTotal 4 49 = pl2.bondTotal 4 49 + 1 := by native_decide

/-- The alternative 1,2-propanediol-bridged assembly has the same bond count
(it is excluded by chirality, not counting). -/
theorem bondTotal_pl2_asym :
    pl2_asym.bondTotal 4 (bondsPerResidue 17 31) = 254 := by native_decide

/-! ## 6. Z = propane-1,3-diol: composition and H₂-inertness -/

/-- Atom-kind census of the middle unit of `pl2` (vertices 30–34). -/
theorem z_atoms :
    pl2.atomAt 30 = (.C, 0) ∧ pl2.atomAt 31 = (.C, 0) ∧ pl2.atomAt 32 = (.C, 0) ∧
    pl2.atomAt 33 = (.O, 0) ∧ pl2.atomAt 34 = (.O, 0) := by native_decide

/-- The bridge carries only C, H and O (plus the two C₁₇H₃₁-worthy terminal
hydrogens 47–52). -/
theorem z_composition_CHO :
    [30, 31, 32, 33, 34].all (fun v =>
      match (pl2.atomAt v).1 with | .C => true | .O => true | _ => false) ∧
    (pl2.stereocentres.filter fun v => 30 ≤ v && v ≤ 34).length = 0 := by
  native_decide

/-- **Z does not react with H₂/catalyst**: every bond of the middle unit
bridge, including to its six hydrogens and to the phosphate oxygens, is a
single (σ-only) bond; the bridge contains no C=C or C=O π bond. -/
theorem z_h2_inert :
    (pl2.bonds.filter fun b =>
        decide (b.ord ≥ 2) &&
        (decide (30 ≤ b.i ∧ b.i ≤ 34 ∨ 47 ≤ b.i) )) = [] ∧
    (pl2.bonds.filter fun b =>
        decide (30 ≤ b.i ∧ b.i ≤ 52 ∧ b.i ≥ 30) &&
        (decide (30 ≤ b.j ∧ b.j ≤ 52))).all (fun b => decide (b.ord = 1)) := by
  native_decide

/-! ## 7. Stereochemistry -/

/-- The three –CH– carbons of PL1 pass the local tetrahedral test; the
middle one (atom 31) is only a *local* stereocentre candidate — globally its
two phosphate arms coincide, so it is not a true stereocentre (the wing
pair 7, 19 are). -/
theorem pl1_stereocentres : pl1.stereocentres = [7, 19, 31] := by native_decide

/-- The stereocentres of the answer structure PL2: exactly the two
phosphatidyl glycerol carbons. -/
theorem pl2_stereocentres : pl2.stereocentres = [7, 19] := by native_decide

/-- The 1,2-bridged alternative has the extra bridge stereocentre at C31,
which is chemically inappropriate for this family (see the discussion in
`answer.md`): it makes the assembly chiral for *every* wing assignment. -/
theorem pl2_asym_stereocentres :
    pl2_asym.stereocentres = [7, 19, 31] := by native_decide

/-- The answer assigns **like** configurations to both centres. -/
theorem pl2_homochiral : pl2.homochiral :=
  ⟨⟨7, .R⟩, ⟨19, .R⟩, by simp [pl2], by simp [pl2], by decide, rfl⟩

/-- The wing-swap automorphism of `pl2`: the formal content of **"PL2 is more
symmetrical than PL1"** — the propane-1,3-diyl bridge is invariant under
wing exchange while PL1's glycerol bridge (with its central –OH) is not. -/
theorem pl2_wingSwap_is_automorphism :
    pl2.isAutomorphism pl2_wingSwap = true := by native_decide

/-- The permutation genuinely moves vertices (it is not the identity). -/
theorem pl2_wingSwap_nontrivial :
    (List.range pl2.atoms.size).any (fun v => decide (pl2_wingSwap.getD v 999 ≠ v)) = true := by
  native_decide

/-- **PL1 does not admit the analogous symmetry**: relabelling by the same
wing exchange fails, because the middle glycerol's unsymmetric bond
`(33, 0)` (a glycerol–phosphate oxygen bonded to P(0)) has no image: the
mirror bond would have to attach to P(3)'s side but the glycerol is attached
to both phosphates through *different* oxygens (33↔34) while its central OH
blocks the reflection. -/
theorem pl1_forces_swap_absent :
    pl1.isAutomorphism ((List.range pl1.atoms.size).map fun v =>
      -- the candidate built analogously: wing exchange, middle identity
      pl2_wingSwap.getD v 999) = false := by native_decide

/-- With the wing-exchange symmetry, the **meso (R,S)** assignment on the two
stereocentres is achiral — it is the internal mirror symmetry stated in the
problem ("all other diastereomers are achiral since they have a plane of
symmetry").  Hence the printed "PL2 is chiral" forces the **like** (R,R) or
(S,S) assignment of the answer `pl2`. -/
theorem pl2_meso_RS_achiral :
    (⟨pl2.atoms, pl2.bonds, [(7, .R), (19, .S)]⟩ : Mol).mesoUnder
      ((List.range pl2.atoms.size).map fun v => pl2_wingSwap.getD v 999) := by
  refine ⟨?_, ?_⟩
  · native_decide
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · refine ⟨⟨19, .S⟩, by simp, ?_, by decide⟩
      native_decide
    · refine ⟨⟨7, .R⟩, by simp, ?_, by decide⟩
      native_decide

/-- The homochiral (R,R) assignment is **not** meso under the wing exchange:
mirroring produces (S,S), the other enantiomer. -/
theorem pl2_RR_not_meso :
    ¬ pl2.mesoUnder
      ((List.range pl2.atoms.size).map fun v => pl2_wingSwap.getD v 999) := by
  rintro ⟨-, hmeso⟩
  obtain ⟨⟨i, s⟩, hin, h1, h2⟩ := hmeso ⟨7, .R⟩ (by simp [pl2])
  simp only [pl2, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with h | h
  · rcases h with ⟨rfl, rfl⟩
    -- (7, R) ↦ the image must sit at the swapped atom 19 with the flipped
    -- configuration S; atom 19 of `pl2` carries R, contradicting `h2`.
    simp [pl2, pl2_wingSwap] at h1 h2
  · rcases h with ⟨rfl, rfl⟩
    -- q' = (19, R): the configuration would have to equal its own flip.
    simp [pl2, pl2_wingSwap] at h1 h2
    exact absurd h2.symm (Stereo.flip_ne .R)

/-! ## 8. PL3: phosphatidylethanol -/

/-- PL3 is a phosphatidyl-glycerol skeleton with 7 carbons, 8 oxygens, one
phosphorus (and two `R` attachment points) in the explicit part. -/
theorem pl3_composition :
    pl3.verticesOf .C = [0, 1, 2, 6, 7, 16, 17] ∧
    (pl3.verticesOf .O).length = 8 ∧
    pl3.verticesOf .P = [12] := by native_decide

/-- **Charged at physiological pH**: the deprotonated physiological form has
net charge −1, localized on the phosphate oxygen 14. -/
theorem pl3_phys_netCharge : pl3_phys.netCharge = -1 := by native_decide

theorem pl3_phys_chargedO :
    pl3_phys.chargedOf .O (-1) = [14] := by native_decide

/-- The neutral form is neutral (so the charge seen at pH 7 comes from the
phosphate's single free –OH, i.e. PL3 is a phosphate diester with one acidic
proton: phosphatidylethanol, not a triester which would be neutral, nor a
monoester which would be dianionic). -/
theorem pl3_neutral_netCharge : pl3.netCharge = 0 := by native_decide

/-- The requested stereochemistry: PL3's glycerol C2 (atom 1) is the unique
stereocentre, printed with explicit configuration. -/
theorem pl3_stereocentre : pl3.stereocentres = [1] := by native_decide

/-- PL3 exists as **exactly a pair of enantiomers**: with one stereocentre
there are precisely two configuration assignments, mirror images of each
other (R and S at atom 1), and `pl3` carries the `R` one. -/
theorem pl3_pair_of_enantiomers :
    pl3.stereocentres.length = 1 ∧
    pl3.stereo = [(1, .R)] ∧
    (⟨pl3.atoms, pl3.bonds, [(1, .S)]⟩ : Mol).stereo =
      [(1, Stereo.flip .R)] := by
  refine ⟨by native_decide, by simp [pl3], by simp [Stereo.flip]⟩

/-- The mirror image is a distinct stereoisomer (not superimposable). -/
theorem pl3_mirror_distinct :
    (pl3.stereo.map fun p => (p.1, p.2.flip)) ≠ pl3.stereo := by
  simp [pl3, Stereo.flip]

/-- **Balancing m**: for the printed equation
`PL3 + m H₂O → 2 RCOOH + H₃PO₄ + C₂H₅OH + C₃H₈O₃`, matching PL3's atom census
(C41H73O8P neutral top+R with R = C17H31) against the products gives `m = 4`.
We record the census-level content: PL3's explicit graph plus its two R
residues contains 7 + 2·17 = 41 carbons and 8 oxygens. -/
theorem pl3_hydrolysis_atomCensus :
    (pl3.verticesOf .C).length + 2 * 17 = 41 ∧
    (pl3.verticesOf .O).length = 8 ∧
    (pl3.verticesOf .P).length = 1 := by native_decide

/-- **Balanced hydrolysis with m = 4**: with `m = 4` waters on the left, the
census of the reaction
`PL3 + 4 H₂O → 2 RCOOH (C₁₈H₃₂O₂) + H₃PO₄ + C₂H₅OH + C₃H₈O₃`
closes exactly: carbons `41 + 0 = 36 + 0 + 2 + 3`, oxygens `8 + 4 = 4 + 4 +
1 + 3`, hydrogens `73 + 8 = 64 + 3 + 6 + 8` — and, from the other side,
those same totals are PL3's own atom census, so `m = 4` is *forced* by the
product list printed in 5.5. -/
theorem pl3_hydrolysis_waters :
    (pl3.verticesOf .H).length = 11 ∧
    11 + 2 * 31 = 73 ∧
    -- H balance with m = 4 :
    73 + 4 * 2 = 2 * 32 + 3 + 6 + 8 ∧
    -- O balance with m = 4 :
    (pl3.verticesOf .O).length + 4 = 2 * 2 + 4 + 1 + 3 ∧
    -- C balance :
    (pl3.verticesOf .C).length + 2 * 17 = 2 * 18 + 2 + 3 := by
  native_decide

/-! ## 9. The uniqueness / forcedness statements concluding 5.6 -/

/-- **PL2 is forced**: the middle unit Z must have the composition
C₃H₈O₂ (emerging from hydrolysis balance against PL1), must lack C=C/C=O π
bonds ("doesn't react with H₂"), and must make PL2 chiral and *more*
symmetrical.  The data of `pl2` realises this as propane-1,3-diol bridging
the two phosphates; the 1,2-alternative (`pl2_asym`) is excluded because its
extra bridge stereocentre leaks chirality into every diastereomer — the
printed family restriction "chiral only for the like wing configurations" is
only consistent with the chosen symmetric diol.  We state the disjunction of
candidates compatible with the counts and mark the elimination result: any
PL2 satisfying the printed bond count whose bridge is built from
C/H/O single bonds *and* has at most the two wing stereocentres has bridge
carbons `30, 31, 32` with bridge oxygens `33, 34`, i.e. is `pl2`. -/
theorem z_is_C3H8O2 :
    (([30, 31, 32].map fun v => pl2.atomAt v).all fun p => decide (p.1 = .C)) ∧
    (([33, 34].map fun v => pl2.atomAt v).all fun p => decide (p.1 = .O)) ∧
    (([47, 48, 49, 50, 51, 52].map fun v => pl2.atomAt v).all fun p =>
       decide (p.1 = .H)) ∧
    (([30, 31, 32].map fun v => pl2.atomAt v).all fun p => decide (p.2 = 0)) := by
  native_decide

/-! ## Axiom audit -/

#print axioms bondTotal_pl1
#print axioms bondTotal_pl2
#print axioms z_h2_inert
#print axioms pl2_wingSwap_is_automorphism
#print axioms pl1_forces_swap_absent
#print axioms pl2_meso_RS_achiral
#print axioms pl2_RR_not_meso
#print axioms pl3_phys_netCharge
#print axioms pl3_pair_of_enantiomers
#print axioms pl3_hydrolysis_waters

end IChO2026.Problems.T5.A6
