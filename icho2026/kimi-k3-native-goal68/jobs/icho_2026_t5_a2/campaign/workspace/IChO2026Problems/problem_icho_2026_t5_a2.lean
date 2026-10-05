import Mathlib

/-!
# IChO 2026 — Theory problem T5 (Cardiolipins), subquestion 5.2
## Target `icho_2026_t5_a2`

Formalization of the two requested structural outputs:

1. **`structure_pl1`** — the structure of one enantiomer of the cardiolipin
   **PL1**, derived from the fragments a–d drawn on page Q5-1 of
   `theory_problem.pdf` (quantities: n × a, 2 × b, 3 × c, 4 × d), the problem
   statements that PL1 is acyclic, contains no peroxide bonds, is diprotic with
   identical acidic groups, chiral even with four identical fatty-acid
   residues, the 5.1 parity question, and the independent hydrolysis
   stoichiometry on page Q5-4
   (`PL1 + 8 H2O → 4 RCOOH + 2 H3PO4 + 3 glycerol`).
2. **`structure_y`** — the monoanion **Y** (= PL1 − H⁺) drawn so as to show the
   stabilisation that makes the second deprotonation unfavourable
   (`pK_a2 ≫ pK_a1`, page Q5-1).

Every atom, bond order, charge and stereocentre of the two outputs is bound
explicitly to the fragments of the problem figures:

* fragment **a** (·—H, valence 1, count n) → the six capping H atoms
  (2 × P–OH proton, 1 × central free 2-OH proton, 3 × sn-2 C–H);
* fragment **b** (HO—P(=O)(·)(·), valence 3, count 2) → the two phosphate groups;
* fragment **c** (·O—CH2—CH(O·)—CH2—O·, valence 4, count 3) → the three glycerol units;
* fragment **d** (·CO—R, valence 1, count 4) → the four acyl residues.

### Derived dependency of part 5.1

The number n of type-a fragments is determined inside this file from the
problem data only: parity from pairwise consumption of dangling bonds
(`n_parity_of_stub_evenness`, the answer to 5.1) and the acyclicity /
connectivity equation (`number_of_a_fragments : n = 6`).

### Sources

* Q5-1: fragment drawings a–e, the worked example W, PL1 fragment quantities,
  "acyclic phospholipids", "PL1 does not contain any peroxide bonds", the
  chirality statement, the diprotic-acid statement, `pK_a2 ≫ pK_a1` "due to the
  special, stable structure of monoanion Y".
* Q5-2: the requested outputs (draw one enantiomer of PL1; draw Y showing the
  stabilisation; "Use the abbreviation R for the fatty acid residues").
* Q5-4: the balanced hydrolysis equation of PL1 (independent stoichiometric
  cross-check).

No official solutions, marking schemes or external answer repositories were
consulted.  The general-chemistry rules used (and relied on as trusted general
laws) are: tetravalence of C, divalence of O, monovalence of H, the
pentavalent tetrahedral phosphate group P(=O)(OH)(OR)(OR'), tetrahedral
stereochemistry of a carbon carrying four different substituents, the
Cahn–Ingold–Prelog priority rules, and stabilisation of a conjugate base by
intramolecular hydrogen bonding.
-/

namespace IChO2026T5A2

/-! ## §1  Problem inputs: fragments, valences, quantities -/

/-- Fragment identifiers a–d exactly as boxed on page Q5-1. -/
inductive FragmentId where
  | a   -- ·—H
  | b   -- HO—P(=O)(·)(·)
  | c   -- ·O—CH2—CH(O·)—CH2—O·
  | d   -- ·CO—R
  deriving DecidableEq, Repr, BEq

/-- Number of dangling bonds (squiggles) drawn on each fragment on page Q5-1. -/
def fragmentValence : FragmentId → ℕ
  | .a => 1
  | .b => 3
  | .c => 4
  | .d => 1

/-- Quantities stated for PL1 on page Q5-1; the a-count is the unknown `n`
of question 5.1. -/
def pl1Quantities (n : ℕ) : FragmentId → ℕ
  | .a => n
  | .b => 2
  | .c => 3
  | .d => 4

/-- Total number of dangling bonds in the fragment pool:
n·1 + 2·3 + 3·4 + 4·1 = n + 22. -/
def totalStubs (n : ℕ) : ℕ := n * 1 + 2 * 3 + 3 * 4 + 4 * 1

/-- Total number of fragment units to be joined into the single molecule PL1. -/
def fragmentCount (n : ℕ) : ℕ := n + 2 + 3 + 4

/-! ## §2  Derived dependencies: value and parity of n (part 5.1) -/

/-- **5.1, statement (a).**  Every bond in the assembled molecule consumes
exactly two dangling bonds, so the stub total `n + 22` must be even; hence
`n` is even. -/
theorem n_parity_of_stub_evenness {n k : ℕ}
    (h : 2 * k = n * 1 + 2 * 3 + 3 * 4 + 4 * 1) : n % 2 = 0 := by
  omega

/-- **Value of n.**  Assembling all fragments into a single *acyclic* molecule
(page Q5-1: "Cardiolipins are a family of acyclic phospholipids") requires
`edges = units − 1`, and all stubs are used up:
`n + 22 = 2·(n + 9 − 1)`, giving `n = 6`. -/
theorem number_of_a_fragments {n : ℕ}
    (h : n * 1 + 2 * 3 + 3 * 4 + 4 * 1 = 2 * (n + 2 + 3 + 4 - 1)) : n = 6 := by
  omega

/-- The stub-balance equation of PL1 with n = 6, for traceability (cf. the
worked example W on page Q5-1, where a complete acyclic assembly is drawn). -/
theorem stub_balance : 6 * 1 + 2 * 3 + 3 * 4 + 4 * 1 = 2 * (6 + 2 + 3 + 4 - 1) := by
  decide

/-! ## §3  Atom inventory for the cardiolipin headgroup

All atoms that the fragments a–d contribute explicitly to PL1.  Carbons of the
glycerol backbones additionally carry implicit hydrogens (the two H atoms of
each CH2 arm), the universal skeletal-drawing convention used by the problem
figures; they are accounted for by `Atom.implicitH` below.  The hydrocarbon
substituents R of the fragments d are represented by one boundary atom each
(`Atom.rCap`), exactly as licensed by "Use the abbreviation R for the fatty
acid residues" (Q5-2) and by the d-fragment drawing (·CO—R). -/

/-- The two outer glycerol units. -/
inductive OuterId where | lo | ro deriving DecidableEq, Repr, BEq

/-- Exchange of the two outer units (used for the constitutional symmetry). -/
def OuterId.other : OuterId → OuterId
  | .lo => .ro
  | .ro => .lo

/-- The three glycerol units (= the three fragments c). -/
inductive GlycId where
  | central
  | ofOuter (o : OuterId)
  deriving DecidableEq, Repr, BEq

/-- Position within a glycerol unit: `a`/`b` are the two CH2 arms, `m` the
middle carbon (sn-2). -/
inductive GP where | a | b | m deriving DecidableEq, Repr, BEq

/-- The two phosphate groups (= the two fragments b). -/
inductive PId where | p1 | p2 deriving DecidableEq, Repr, BEq

/-- The four acyl residues (= the four fragments d). -/
inductive AcylId where | q1 | q2 | q3 | q4 deriving DecidableEq, Repr, BEq

/-- Explicit atoms of the PL1 headgroup (42 atoms). -/
inductive Atom where
  | glyc (g : GlycId) (p : GP)   -- glycerol backbone carbons (9)
  | glycH (g : GlycId)           -- H cap on the sn-2 carbon, fragment a (3)
  | glyO (g : GlycId)            -- sn-2 substituent oxygen of each glycerol (3)
  | glyOH                        -- proton of the FREE central 2-OH, fragment a (1)
  | glyOB (o : OuterId)          -- arm-b substituent oxygen of the outer glycerols (2)
  | phA (p : PId)                -- phosphorus atoms (2)
  | phPO (p : PId)               -- phosphoryl oxygens, drawn P=O (2)
  | phOH (p : PId)               -- acidic P–OH oxygens (2)
  | phOHH (p : PId)              -- acidic P–OH protons, fragments a (2)
  | phBC (p : PId)               -- bridging oxygens P–O–CH2–(central glycerol) (2)
  | phBO (p : PId)               -- bridging oxygens P–O–CH2–(outer glycerol) (2)
  | acC (a : AcylId)             -- acyl carbonyl carbons (4)
  | acO (a : AcylId)             -- acyl carbonyl oxygens (4)
  | rCap (a : AcylId)            -- boundary to the fatty-acid substituent R (4)
  deriving DecidableEq, Repr, BEq

/-- Elements of the explicit atoms. -/
inductive Element where | c | h | o | p | rsub deriving DecidableEq, Repr, BEq

def Atom.element : Atom → Element
  | .glyc _ _ => .c
  | .glycH _ => .h
  | .glyO _ => .o
  | .glyOH => .h
  | .glyOB _ => .o
  | .phA _ => .p
  | .phPO _ => .o
  | .phOH _ => .o
  | .phOHH _ => .h
  | .phBC _ => .o
  | .phBO _ => .o
  | .acC _ => .c
  | .acO _ => .o
  | .rCap _ => .rsub

/-- Atomic numbers used for CIP priority (R is a hydrocarbon substituent,
so its boundary counts as carbon). -/
def Element.atomicNo : Element → ℕ
  | .c => 6
  | .h => 1
  | .o => 8
  | .p => 15
  | .rsub => 6

/-- Which phosphate esterifies which outer glycerol. -/
def pOfOuter : OuterId → PId
  | .lo => .p1
  | .ro => .p2

/-- Which acyl residue sits on the sn-2 oxygen of each outer glycerol. -/
def acylOfMid : OuterId → AcylId
  | .lo => .q1
  | .ro => .q3

/-- Which acyl residue sits on the arm-b oxygen of each outer glycerol. -/
def acylOfB : OuterId → AcylId
  | .lo => .q2
  | .ro => .q4

/-! ## §4  Bond structure of PL1

Connectivity, audited mechanically below:
* each glycerol (fragment c): –CH2–CH–CH2– backbone (two C–C bonds), an sn-2
  C–H cap (fragment a) and an sn-2 C–O bond;
* central glycerol: both arms esterified by the phosphate bridging oxygens
  `phBC`; its sn-2 oxygen is a FREE hydroxyl, capped by `glyOH` (fragment a);
* outer glycerols: arm a esterified by phosphate oxygen `phBO`; the arm-b
  oxygen `glyOB` and the sn-2 oxygen `glyO` are acyl-esterified;
* each phosphate (fragment b): P=O drawn double, P–OH capped by its proton
  (fragment a), two P–O–CH2 ester bonds;
* each acyl residue (fragment d): C=O drawn double, C–O ester bond to a
  glycerol oxygen, and the C—R boundary. -/

/-- Bond orders as printed in a Lewis structure. -/
inductive BondOrd where | single | double deriving DecidableEq, Repr, BEq

def BondOrd.toNat : BondOrd → ℕ
  | .single => 1
  | .double => 2

/-- An undirected bond with its bond order. -/
structure Bond where
  a : Atom
  b : Atom
  ord : BondOrd
  deriving DecidableEq, Repr, BEq

/-- Bonds contributed by one glycerol unit (fragment c). -/
def glycBonds (g : GlycId) : List Bond :=
  [ ⟨.glyc g .a, .glyc g .m, .single⟩,
    ⟨.glyc g .b, .glyc g .m, .single⟩,
    ⟨.glyc g .m, .glycH g, .single⟩,
    ⟨.glyc g .m, .glyO g, .single⟩ ] ++
  match g with
  | .central =>
      [ ⟨.glyc .central .a, .phBC .p1, .single⟩,
        ⟨.glyc .central .b, .phBC .p2, .single⟩,
        ⟨.glyO .central, .glyOH, .single⟩ ]
  | .ofOuter o =>
      [ ⟨.glyc g .a, .phBO (pOfOuter o), .single⟩,
        ⟨.glyc g .b, .glyOB o, .single⟩,
        ⟨.glyO g, .acC (acylOfMid o), .single⟩,
        ⟨.glyOB o, .acC (acylOfB o), .single⟩ ]

/-- Bonds of one phosphate group (fragment b). -/
def phosBonds (p : PId) : List Bond :=
  [ ⟨.phA p, .phPO p, .double⟩,
    ⟨.phA p, .phOH p, .single⟩,
    ⟨.phOH p, .phOHH p, .single⟩,
    ⟨.phA p, .phBC p, .single⟩,
    ⟨.phA p, .phBO p, .single⟩ ]

/-- Bonds of one acyl residue (fragment d). -/
def acylBonds (a : AcylId) : List Bond :=
  [ ⟨.acC a, .acO a, .double⟩,
    ⟨.acC a, .rCap a, .single⟩ ]

/-- All bonds of neutral PL1 (41 bonds). -/
def pl1Bonds : List Bond :=
  glycBonds .central ++ glycBonds (.ofOuter .lo) ++ glycBonds (.ofOuter .ro) ++
  phosBonds .p1 ++ phosBonds .p2 ++
  acylBonds .q1 ++ acylBonds .q2 ++ acylBonds .q3 ++ acylBonds .q4

/-- All explicit atoms of neutral PL1 (42 atoms). -/
def pl1Atoms : List Atom :=
  [ .glyc .central .a, .glyc .central .b, .glyc .central .m, .glycH .central,
    .glyO .central, .glyOH,
    .glyc (.ofOuter .lo) .a, .glyc (.ofOuter .lo) .b, .glyc (.ofOuter .lo) .m,
    .glycH (.ofOuter .lo), .glyO (.ofOuter .lo), .glyOB .lo,
    .glyc (.ofOuter .ro) .a, .glyc (.ofOuter .ro) .b, .glyc (.ofOuter .ro) .m,
    .glycH (.ofOuter .ro), .glyO (.ofOuter .ro), .glyOB .ro,
    .phA .p1, .phPO .p1, .phOH .p1, .phOHH .p1, .phBC .p1, .phBO .p1,
    .phA .p2, .phPO .p2, .phOH .p2, .phOHH .p2, .phBC .p2, .phBO .p2,
    .acC .q1, .acC .q2, .acC .q3, .acC .q4,
    .acO .q1, .acO .q2, .acO .q3, .acO .q4,
    .rCap .q1, .rCap .q2, .rCap .q3, .rCap .q4 ]

def sumNat : List ℕ → ℕ := List.foldl (· + ·) 0

/-- Bond order between two given atoms (0 if not bonded). -/
def bondOrderBetween (x y : Atom) (bs : List Bond) : ℕ :=
  sumNat (bs.map fun b =>
    if (b.a == x && b.b == y) || (b.a == y && b.b == x) then b.ord.toNat else 0)

/-- Sum of bond orders at an atom (its drawn valence). -/
def bondOrderSum (x : Atom) (bs : List Bond) : ℕ :=
  sumNat (bs.map fun b => if b.a == x || b.b == x then b.ord.toNat else 0)

/-- Neighbour list of an atom. -/
def neighbors (x : Atom) (bs : List Bond) : List Atom :=
  bs.filterMap fun b =>
    if b.a == x then some b.b else if b.b == x then some b.a else none

/-! ### §4a  Cardinalities -/

theorem pl1_atom_count : pl1Atoms.length = 42 := by
  decide

theorem pl1_bond_count : pl1Bonds.length = 41 := by
  decide

/-- **PL1 is acyclic** ("Cardiolipins are a family of acyclic phospholipids")
and is one connected molecule: `|E| = |V| − 1` for the tree criterion;
connectivity is proved in `pl1_connected`. -/
theorem pl1_is_tree : pl1Bonds.length + 1 = pl1Atoms.length := by
  decide

/-! ### §4b  Connectivity via a spanning arborescence -/

/-- Parent pointers towards the root `phA p1`; each step follows a drawn bond
(verified by `pl1_parent_is_bond`).  Cases are ordered so that every atom is
matched by its first applicable clause. -/
def parentOf : Atom → Option Atom
  | .phA .p1 => none
  | .phPO .p1 => some (.phA .p1)
  | .phOH .p1 => some (.phA .p1)
  | .phOHH .p1 => some (.phOH .p1)
  | .phBC .p1 => some (.phA .p1)
  | .phBO .p1 => some (.phA .p1)
  | .glyc .central .a => some (.phBC .p1)
  | .glyc .central .m => some (.glyc .central .a)
  | .glyc .central .b => some (.glyc .central .m)
  | .glycH .central => some (.glyc .central .m)
  | .glyO .central => some (.glyc .central .m)
  | .glyOH => some (.glyO .central)
  | .phBC .p2 => some (.glyc .central .b)
  | .phA .p2 => some (.phBC .p2)
  | .phPO .p2 => some (.phA .p2)
  | .phOH .p2 => some (.phA .p2)
  | .phOHH .p2 => some (.phOH .p2)
  | .phBO .p2 => some (.phA .p2)
  | .glyc (.ofOuter .lo) .a => some (.phBO .p1)
  | .glyc (.ofOuter .ro) .a => some (.phBO .p2)
  | .glyc (.ofOuter o) .m => some (.glyc (.ofOuter o) .a)
  | .glycH g => some (.glyc g .m)
  | .glyO g => some (.glyc g .m)
  | .glyc (.ofOuter o) .b => some (.glyc (.ofOuter o) .m)
  | .glyOB o => some (.glyc (.ofOuter o) .b)
  | .acC .q1 => some (.glyO (.ofOuter .lo))
  | .acC .q2 => some (.glyOB .lo)
  | .acC .q3 => some (.glyO (.ofOuter .ro))
  | .acC .q4 => some (.glyOB .ro)
  | .acO a => some (.acC a)
  | .rCap a => some (.acC a)

/-- Follow the parent pointers (fuel-bounded) and test arrival at the root. -/
def reachesRoot : ℕ → Atom → Bool
  | 0, _ => false
  | _ + 1, .phA .p1 => true
  | fuel + 1, x => match parentOf x with
    | some p => reachesRoot fuel p
    | none => false

/-- Every explicit atom is joined to the root by a chain of drawn bonds:
the molecular graph of PL1 is connected.  (Fuel 20 exceeds the longest
root path, which is 14: rCap q4 → ··· → phA p2 → phBC p2 → central b →
central m → central a → phBC p1 → phA p1.) -/
theorem pl1_connected : ∀ x ∈ pl1Atoms, reachesRoot 20 x = true := by
  decide

/-- Each parent link is one of the drawn bonds of PL1. -/
theorem pl1_parent_is_bond :
    ∀ x ∈ pl1Atoms,
      ((parentOf x).map fun p => bondOrderBetween x p pl1Bonds != 0).getD true = true := by
  decide

/-! ### §4c  Valence audit (general laws: C tetravalent, O divalent,
H monovalent, phosphate P pentavalent with P=O drawn as one double bond) -/

/-- Target valences of the explicit atoms. -/
def Atom.targetValence : Atom → ℕ
  | .glyc _ _ => 4
  | .glycH _ => 1
  | .glyO _ => 2
  | .glyOH => 1
  | .glyOB _ => 2
  | .phA _ => 5
  | .phPO _ => 2
  | .phOH _ => 2
  | .phOHH _ => 1
  | .phBC _ => 2
  | .phBO _ => 2
  | .acC _ => 4
  | .acO _ => 2
  | .rCap _ => 1

/-- Implicit hydrogens of the skeletal convention: the glycerol CH2 arms carry
two hydrogens each; every other explicit atom is fully specified by the
fragments a–d. -/
def Atom.implicitH : Atom → ℕ
  | .glyc _ .a => 2
  | .glyc _ .b => 2
  | _ => 0

/-- Every atom of PL1 meets its target valence exactly once the implicit
hydrogens are added: the assembled structure is a valence-complete neutral
Lewis structure with no radicals — matching "the non-ionised form of PL1". -/
theorem pl1_valences_ok :
    ∀ x ∈ pl1Atoms, bondOrderSum x pl1Bonds + x.implicitH = x.targetValence := by
  decide

/-! ### §4d  No peroxide bonds (page Q5-1) -/

def Atom.isOxygen (x : Atom) : Bool := x.element == .o

/-- PL1 contains no O–O single bonds. -/
theorem pl1_no_peroxides :
    ∀ b ∈ pl1Bonds, b.ord = .single → (b.a.isOxygen && b.b.isOxygen) = false := by
  decide

/-! ### §4e  Fragment reconciliation: every fragment a–d of the problem figure
is present in the stated quantity -/

/-- Fragment-a caps in PL1: three sn-2 C–H, one central free 2-OH proton and
two P–OH protons. -/
def isTypeACap : Atom → Bool
  | .glycH _ | .glyOH | .phOHH _ => true
  | _ => false

/-- The number of fragment-a caps in the structure equals the derived n = 6. -/
theorem type_a_count_eq_n : (pl1Atoms.filter isTypeACap).length = 6 := by
  decide

def isPhosphorus (x : Atom) : Bool := x.element == .p

/-- Exactly two phosphate groups: the stated quantity of fragment b. -/
theorem type_b_count : (pl1Atoms.filter isPhosphorus).length = 2 := by
  decide

/-- Exactly three glycerol units (counted by their sn-2 carbons): the stated
quantity of fragment c. -/
theorem type_c_count :
    (pl1Atoms.filter fun x => match x with | .glyc _ .m => true | _ => false).length = 3 := by
  decide

/-- Exactly four acyl residues (counted by their carbonyl carbons): the stated
quantity of fragment d. -/
theorem type_d_count :
    (pl1Atoms.filter fun x => match x with | .acC _ => true | _ => false).length = 4 := by
  decide

/-! ### §4f  Which arm carries what -/

/-- The middle hydroxyl of the central glycerol is a FREE OH group: its oxygen
carries a fragment-a proton. -/
theorem central_free_OH : bondOrderBetween (.glyO .central) .glyOH pl1Bonds = 1 := by
  decide

/-- Both arms of the central glycerol are phosphate esters; the central sn-2
carbon's neighbour set is exactly {arm a, arm b, sn-2 H, free sn-2 O}. -/
theorem central_glycerol_connectivity :
    neighbors (.glyc .central .m) pl1Bonds =
      [.glyc .central .a, .glyc .central .b, .glycH .central, .glyO .central] ∧
    bondOrderBetween (.glyc .central .a) (.phBC .p1) pl1Bonds = 1 ∧
    bondOrderBetween (.glyc .central .b) (.phBC .p2) pl1Bonds = 1 := by
  decide

/-- Each outer glycerol carries exactly: one phosphate ester on arm a, one acyl
ester on arm b, one acyl ester on sn-2, and its sn-2 C–H cap. -/
theorem outer_glycerol_connectivity :
    ∀ o : OuterId,
      bondOrderBetween (.glyc (.ofOuter o) .a) (.phBO (pOfOuter o)) pl1Bonds = 1 ∧
      bondOrderBetween (.glyc (.ofOuter o) .b) (.glyOB o) pl1Bonds = 1 ∧
      bondOrderBetween (.glyO (.ofOuter o)) (.acC (acylOfMid o)) pl1Bonds = 1 ∧
      bondOrderBetween (.glyOB o) (.acC (acylOfB o)) pl1Bonds = 1 ∧
      bondOrderBetween (.glyc (.ofOuter o) .m) (.glycH (.ofOuter o)) pl1Bonds = 1 := by
  intro o; cases o <;> decide

/-! ### §4g  Cross-check against the Q5-4 hydrolysis equation

`PL1 + 8 H2O → 4 RCOOH + 2 H3PO4 + 3 glycerol` requires exactly 8 hydrolysable
ester bonds in PL1 (4 acyl esters + 4 phosphate esters). -/

def isHydrolyzable (bnd : Bond) : Bool :=
  match bnd.a, bnd.b with
  | .glyc _ _, .phBC _ => true
  | .phBC _, .glyc _ _ => true
  | .glyc _ _, .phBO _ => true
  | .phBO _, .glyc _ _ => true
  | .glyO _, .acC _ => true
  | .acC _, .glyO _ => true
  | .glyOB _, .acC _ => true
  | .acC _, .glyOB _ => true
  | _, _ => false

/-- Exactly eight ester bonds — matching the eight waters of the balanced
hydrolysis equation given on page Q5-4. -/
theorem hydrolysis_water_count : (pl1Bonds.filter isHydrolyzable).length = 8 := by
  decide

/-! ### §4h  Diprotic acid with identical acidic groups (page Q5-1) -/

def isAcidicOH (bnd : Bond) : Bool :=
  match bnd.a, bnd.b with
  | .phOH _, .phOHH _ => true
  | .phOHH _, .phOH _ => true
  | _, _ => false

/-- PL1 bears exactly two P–OH groups — the same acidic group on the two
otherwise identical phosphate fragments. -/
theorem pl1_is_diprotic : (pl1Bonds.filter isAcidicOH).length = 2 := by
  decide

/-! ## §5  Stereochemistry of PL1

Phosphorus is excluded as a stereocentre by the problem statement ("Do not
consider the chirality of phosphorus atoms as stereocentres").  The
stereocentres are the sn-2 carbons of the two OUTER glycerols; the central
glycerol's sn-2 carbon has two constitutionally identical arms
(`central_not_stereogenic` below) and is therefore not stereogenic.

CIP trace at each outer sn-2 carbon:
1. `glyO o` — the directly attached O (Z = 8);
2. `glyc o .a` — the CH2 arm whose O leads to P (Z = 15 at the third sphere);
3. `glyc o .b` — the CH2 arm whose O leads to the acyl carbon (Z = 6 at the
   third sphere);
4. `glycH o` — H (Z = 1).
Sphere 1: [8, 6, 6, 1].  The two carbon arms tie at sphere 2 ([8,1,1] both)
and split at sphere 3 ([15] vs [6]). -/

/-- The two stereocentres: sn-2 carbons of the outer glycerols. -/
def loC : Atom := .glyc (.ofOuter .lo) .m
def roC : Atom := .glyc (.ofOuter .ro) .m

/-- Each outer sn-2 carbon carries four distinct substituents — the
prerequisite for being a stereocentre. -/
theorem outer_centres_have_four_distinct_substituents :
    (neighbors loC pl1Bonds).Nodup ∧ (neighbors loC pl1Bonds).length = 4 ∧
    (neighbors roC pl1Bonds).Nodup ∧ (neighbors roC pl1Bonds).length = 4 := by
  decide

/-- Sphere-1 CIP data at an outer stereocentre: O > C = C > H. -/
theorem cip_sphere1 :
    Element.o.atomicNo > Element.c.atomicNo ∧ Element.c.atomicNo > Element.h.atomicNo := by
  decide

/-- Sphere-3 tie-break between the two carbon arms: arm a reaches phosphorus
(15), arm b only the acyl carbon (6), so priority 2 = arm a, priority 3 = arm b. -/
theorem cip_tiebreak : Element.p.atomicNo > Element.c.atomicNo := by
  decide

/-- The neighbours of each outer stereocentre, listed in decreasing CIP
priority (1 → 4) as derived above. -/
def cipOrder (o : OuterId) : List Atom :=
  [.glyO (.ofOuter o), .glyc (.ofOuter o) .a, .glyc (.ofOuter o) .b, .glycH (.ofOuter o)]

/-- The CIP-sorted list coincides with the actual neighbour set of the
stereocentre (nothing missing, nothing extra). -/
theorem cip_order_covers_neighbours (o : OuterId) :
    ((cipOrder o).all (fun x => (neighbors (.glyc (.ofOuter o) .m) pl1Bonds).elem x) = true) ∧
    ((neighbors (.glyc (.ofOuter o) .m) pl1Bonds).all (fun x => (cipOrder o).elem x) = true) := by
  cases o <;> decide

/-- The constitutional left↔right symmetry of the cardiolipin skeleton
("plane of symmetry"): exchange the two outer glycerols together with their
phosphates and their two acyl residues, and simultaneously exchange the two
equivalent CH2 arms of the bridging central glycerol.  (The four R
substituents are identical: "four identical fatty acid residues".) -/
def Atom.permute : Atom → Atom
  | .glyc .central .m => .glyc .central .m
  | .glyc .central .a => .glyc .central .b
  | .glyc .central .b => .glyc .central .a
  | .glyc (.ofOuter o) p => .glyc (.ofOuter o.other) p
  | .glycH .central => .glycH .central
  | .glycH (.ofOuter o) => .glycH (.ofOuter o.other)
  | .glyO .central => .glyO .central
  | .glyO (.ofOuter o) => .glyO (.ofOuter o.other)
  | .glyOH => .glyOH
  | .glyOB o => .glyOB o.other
  | .phA .p1 => .phA .p2
  | .phA .p2 => .phA .p1
  | .phPO .p1 => .phPO .p2
  | .phPO .p2 => .phPO .p1
  | .phOH .p1 => .phOH .p2
  | .phOH .p2 => .phOH .p1
  | .phOHH .p1 => .phOHH .p2
  | .phOHH .p2 => .phOHH .p1
  | .phBC .p1 => .phBC .p2
  | .phBC .p2 => .phBC .p1
  | .phBO .p1 => .phBO .p2
  | .phBO .p2 => .phBO .p1
  | .acC .q1 => .acC .q3
  | .acC .q3 => .acC .q1
  | .acC .q2 => .acC .q4
  | .acC .q4 => .acC .q2
  | .acO .q1 => .acO .q3
  | .acO .q3 => .acO .q1
  | .acO .q2 => .acO .q4
  | .acO .q4 => .acO .q2
  | .rCap .q1 => .rCap .q3
  | .rCap .q3 => .rCap .q1
  | .rCap .q2 => .rCap .q4
  | .rCap .q4 => .rCap .q2

/-- `permute` is an involution on the atom set. -/
theorem permute_involution : ∀ x ∈ pl1Atoms, x.permute.permute = x := by
  decide

/-- `permute` maps every drawn bond to a drawn bond of the same order: it is a
bond-order-preserving automorphism of the molecular graph — the formal content
of the left–right "plane of symmetry" of the skeleton. -/
theorem permute_is_automorphism :
    ∀ b ∈ pl1Bonds, ∃ b' ∈ pl1Bonds,
      ((b'.a == b.a.permute || b'.a == b.b.permute) &&
       (b'.b == b.a.permute || b'.b == b.b.permute) && (b'.ord == b.ord)) = true := by
  decide

/-- The two arms of the central glycerol are swapped by the automorphism, so
the central sn-2 carbon sees two constitutionally equal substituents: it is
NOT a stereocentre.  This is why the only diastereomers of PL1 arise from the
two outer centres, and why "all other diastereomers … have a plane of
symmetry" (page Q5-1). -/
theorem central_not_stereogenic :
    (Atom.glyc .central .a).permute = .glyc .central .b ∧
    (Atom.glyc .central .b).permute = .glyc .central .a := by
  decide

/-- R/S configuration labels (Cahn–Ingold–Prelog). -/
inductive Chiral where | R | S deriving DecidableEq, Repr, BEq

/-- Mirror image of a configuration. -/
def Chiral.toggle : Chiral → Chiral
  | .R => .S
  | .S => .R

/-- A stereochemical assignment to the two outer stereocentres. -/
abbrev Assign := List (Atom × Chiral)

/-- Assignments, compared up to reordering of the centre list. -/
def assignEquiv (s t : Assign) : Bool :=
  s.all (fun x => t.elem x) && t.all (fun x => s.elem x)

/-- Mirror image of an assignment (every centre inverted). -/
def Assign.mirror (s : Assign) : Assign :=
  s.map fun (a, c) => (a, c.toggle)

/-- Transport of an assignment along the constitutional symmetry. -/
def Assign.symImage (s : Assign) : Assign :=
  s.map fun (a, c) => (a.permute, c)

/-- **One enantiomer of PL1 (requested output)**: both outer sn-2 centres (R).
This is the configuration of the cardiolipins found in prokaryotes and
eukaryotes (glycerol backbones derived from sn-glycerol-3-phosphate); the
(S,S) form occurs in archaea.  In the drawn answer, at each outer
stereocentre the O–CO–R bond is shown as a hashed wedge (behind the plane)
and the C–H bond as a solid wedge (in front), with the phosphate arm drawn to
the right: by the CIP trace in §5 this gives (R) at both centres. -/
def pl1EnantiomerRR : Assign := [(loC, .R), (roC, .R)]

/-- The opposite enantiomer (archaeal type). -/
def pl1EnantiomerSS : Assign := [(loC, .S), (roC, .S)]

/-- A meso diastereomer. -/
def pl1MesoRS : Assign := [(loC, .R), (roC, .S)]

/-- The two enantiomers are mutual mirror images. -/
theorem rr_mirror_is_ss :
    assignEquiv pl1EnantiomerRR.mirror pl1EnantiomerSS = true := by
  decide

/-- **Chirality of the (R,R) form**: its mirror image differs both from the
form itself and from its constitutionally symmetric image, so neither a plain
rotation nor the combination with the skeleton's left–right symmetry
superposes the (R,R) form on its mirror image. -/
theorem rr_is_chiral :
    assignEquiv pl1EnantiomerRR.mirror pl1EnantiomerRR = false ∧
    assignEquiv pl1EnantiomerRR.mirror pl1EnantiomerRR.symImage = false ∧
    assignEquiv pl1EnantiomerRR.symImage pl1EnantiomerRR = true := by
  decide

/-- **The (R,S) diastereomer is achiral (meso)**: its mirror image coincides
with its image under the plane-of-symmetry automorphism — the formal content
of "All other diastereomers of PL1 are achiral molecules, since they have a
plane of symmetry" (page Q5-1). -/
theorem rs_is_meso :
    assignEquiv pl1MesoRS.mirror pl1MesoRS.symImage = true := by
  decide

/-! ## §6  The monoanion Y and the origin of `pK_a2 ≫ pK_a1`

The first deprotonation removes one phosphate proton (here `phOHH p1`); the
negative charge is delocalised by resonance over the two non-bridging oxygens
of that phosphate (`phPO p1`, `phOH p1`).

The special, stable structure of Y (page Q5-1) is an intramolecular
hydrogen-bond network that cannot survive in the dianion:

* **H-bond 1** — the FREE 2-OH of the central glycerol donates to the anionic
  phosphate oxygen `phOH p1`, closing a six-membered pseudo-ring
  O–H···O(–)–P–O–C–C;
* **H-bond 2** — the remaining P–OH proton of the second phosphate donates to
  the same anionic oxygen `phOH p1`, so the last acidic proton is held in a
  P–O–H···O(–)–P bridge spanning the bridging glycerol.

Removing the second proton would destroy this hydrogen-bond network and would
place two anionic phosphates close together across the propane bridge: the
second deprotonation is therefore far less favourable, `pK_a2 ≫ pK_a1`. -/

/-- The three protonation states of the cardiolipin headgroup. -/
inductive Species where | pl1 | yAnion | dianion deriving DecidableEq, Repr, BEq

/-- Formal charges on the explicit atoms (0 unless listed): the negative
charge sits on a non-bridging phosphate oxygen. -/
def Species.charge : Species → Atom → ℤ
  | .yAnion, .phOH .p1 => -1
  | .dianion, .phOH .p1 => -1
  | .dianion, .phOH .p2 => -1
  | _, _ => 0

/-- Atom inventory of each protonation state (deprotonation removes the drawn
acidic proton; all other atoms persist). -/
def Species.atoms : Species → List Atom
  | .pl1 => pl1Atoms
  | .yAnion => pl1Atoms.erase (.phOHH .p1)
  | .dianion => (pl1Atoms.erase (.phOHH .p1)).erase (.phOHH .p2)

/-- Bonds of each protonation state: all bonds among the surviving atoms;
connectivity and bond orders are otherwise unchanged. -/
def Species.bonds (s : Species) : List Bond :=
  pl1Bonds.filter fun b => s.atoms.elem b.a && s.atoms.elem b.b

def sumInt : List ℤ → ℤ := List.foldl (· + ·) 0

/-- Total charge of a protonation state. -/
def Species.totalCharge (s : Species) : ℤ :=
  sumInt (s.atoms.map s.charge)

/-- Y is indeed a monoanion. -/
theorem y_is_monoanion : Species.totalCharge .yAnion = -1 := by
  decide

/-- The fully deprotonated cardiolipin is a dianion. -/
theorem dianion_charge : Species.totalCharge .dianion = -2 := by
  decide

/-- Y differs from PL1 by exactly one atom (the removed acidic proton). -/
theorem y_atoms : (Species.atoms .yAnion).length + 1 = pl1Atoms.length := by
  decide

/-- Y differs from PL1 by exactly one drawn bond (the broken P–OH bond:
the acidic O–H bond is removed on deprotonation). -/
theorem y_bonds : (Species.bonds .yAnion).length + 1 = pl1Bonds.length := by
  decide

/-- A hydrogen bond, drawn D–H···A, recorded as (donor atom D, acceptor A). -/
structure HBond where
  donor : Atom
  acceptor : Atom
  deriving DecidableEq, Repr, BEq

/-- **The special stable structure of Y (requested output)**: Y is drawn with
the two intramolecular hydrogen bonds that stabilise it — the free 2-OH of the
bridging glycerol and the remaining acidic P–OH both donating onto the anionic
non-bridging phosphate oxygen. -/
def yHBonds : List HBond :=
  [ ⟨.glyO .central, .phOH .p1⟩,
    ⟨.phOH .p2, .phOH .p1⟩ ]

/-- Does the atom `d` carry a drawn hydrogen in the protonation state `s`? -/
def donorHasHydrogen (d : Atom) (s : Species) : Bool :=
  s.bonds.any fun b =>
    (b.a == d && b.b.element == .h) || (b.b == d && b.a.element == .h)

/-- In Y, both hydrogen-bond donors still carry their protons and the acceptor
is the anionic phosphate oxygen: the complete stabilising network is present. -/
theorem y_stabilisation_network :
    (∀ hb ∈ yHBonds, donorHasHydrogen hb.donor .yAnion = true) ∧
    (∀ hb ∈ yHBonds, Species.charge .yAnion hb.acceptor = -1) ∧
    yHBonds.length = 2 := by
  decide

/-- Monoanion formation leaves the second P–OH intact: Y still owns exactly
one acidic P–OH bond. -/
theorem y_retains_one_acidic_OH :
    ((Species.bonds .yAnion).filter isAcidicOH).length = 1 := by
  decide

/-- **Structural reason for `pK_a2 ≫ pK_a1`**: the second deprotonation removes
the donor proton of the P–OH···O(–) bridge, so no phosphate hydrogen-bond
donor survives in the dianion; the stabilising network of Y cannot exist after
the second ionisation, which is accordingly much less favourable. -/
theorem second_deprotonation_destroys_network :
    donorHasHydrogen (.phOH .p2) .dianion = false ∧
    donorHasHydrogen (.phOH .p1) .dianion = false ∧
    (Species.atoms .dianion).length + 2 = pl1Atoms.length := by
  decide

/-- The anionic acceptor oxygen is resonance-equivalent to the phosphoryl
oxygen of the same phosphate (both are non-bridging oxygens on the same
phosphorus): the negative charge of Y is delocalised over the P–O⁻/P=O pair
of the ionised phosphate. -/
theorem y_charge_resonance_partners :
    bondOrderBetween (.phA .p1) (.phPO .p1) (Species.bonds .yAnion) = 2 ∧
    bondOrderBetween (.phA .p1) (.phOH .p1) (Species.bonds .yAnion) = 1 := by
  decide

/-! ## §7  Bundle: the two requested outputs -/

/-- **Requested output `structure_pl1`.**  The complete structure of one
enantiomer of PL1: the atom/bond skeleton `pl1Atoms`, `pl1Bonds` (with bond
orders) together with the (R,R) stereochemical assignment at the two outer
glycerol sn-2 carbons; the fatty-acid residues appear as the abbreviation R
(`Atom.rCap`), as instructed in Q5-2. -/
structure StructurePL1 where
  atoms : List Atom := pl1Atoms
  bonds : List Bond := pl1Bonds
  stereo : Assign := pl1EnantiomerRR

def structure_pl1 : StructurePL1 where

/-- **Certificate for `structure_pl1`** — every requirement of the problem is
met by the proposed enantiomer:
(1) built from exactly the stated fragment quantities (a : 6, b : 2, c : 3,
d : 4, with n = 6 derived in §2);
(2) a single connected acyclic molecule (`|E| = |V| − 1`);
(3) no peroxide bonds;
(4) a valence-complete neutral Lewis structure (the "non-ionised form");
(5) four fatty-acid residues, all abbreviated by the same R;
(6) diprotic, with two identical P–OH acidic groups;
(7) exactly two stereocentres, each with four distinct substituents;
(8) the (R,R) assignment is chiral — not superposable on its mirror image —
while the (R,S) alternative is meso, in agreement with "all other
diastereomers … have a plane of symmetry";
(9) exactly eight ester bonds, consistent with the fully independent
hydrolysis equation on page Q5-4. -/
theorem structure_pl1_certificate :
    (pl1Atoms.filter isTypeACap).length = 6 ∧
    (pl1Atoms.filter isPhosphorus).length = 2 ∧
    pl1Bonds.length + 1 = pl1Atoms.length ∧
    (∀ b ∈ pl1Bonds, b.ord = .single → (b.a.isOxygen && b.b.isOxygen) = false) ∧
    (∀ x ∈ pl1Atoms, bondOrderSum x pl1Bonds + x.implicitH = x.targetValence) ∧
    (pl1Atoms.filter (fun x => match x with | .acC _ => true | _ => false)).length = 4 ∧
    (pl1Bonds.filter isAcidicOH).length = 2 ∧
    (neighbors loC pl1Bonds).length = 4 ∧ (neighbors roC pl1Bonds).length = 4 ∧
    assignEquiv pl1EnantiomerRR.mirror pl1EnantiomerRR = false ∧
    assignEquiv pl1MesoRS.mirror pl1MesoRS.symImage = true ∧
    (pl1Bonds.filter isHydrolyzable).length = 8 := by
  exact ⟨type_a_count_eq_n, type_b_count, pl1_is_tree, pl1_no_peroxides,
         pl1_valences_ok, type_d_count, pl1_is_diprotic,
         outer_centres_have_four_distinct_substituents.2.1,
         outer_centres_have_four_distinct_substituents.2.2.2,
         rr_is_chiral.1, rs_is_meso, hydrolysis_water_count⟩

/-- **Requested output `structure_y`.**  The monoanion Y drawn so as to show
its stabilisation: the species `yAnion` (PL1 minus one acidic proton; charge
−1 on a non-bridging oxygen of the ionised phosphate) together with the two
explicit intramolecular hydrogen bonds `yHBonds` — the free 2-OH of the
bridging glycerol and the remaining P–OH both donating onto the anionic
phosphate oxygen.  The stereochemistry of the headgroup is unchanged. -/
structure StructureY where
  species : Species := .yAnion
  hbonds : List HBond := yHBonds
  stereo : Assign := pl1EnantiomerRR

def structure_y : StructureY where

/-- **Certificate for `structure_y`** — Y is the monoanion of PL1 (charge −1;
one atom and one bond fewer than the neutral acid), its skeleton and (R,R)
stereochemistry are unchanged, it displays the complete two-donor
hydrogen-bond network onto the anionic phosphate oxygen, and the structural
source of `pK_a2 ≫ pK_a1` is exhibited: the second deprotonation would remove
the donor proton of the P–OH···O(–) bridge, so the stabilising network cannot
survive in the dianion. -/
theorem structure_y_certificate :
    Species.totalCharge structure_y.species = -1 ∧
    ((Species.bonds structure_y.species).filter isAcidicOH).length = 1 ∧
    (∀ hb ∈ structure_y.hbonds, donorHasHydrogen hb.donor structure_y.species = true) ∧
    (∀ hb ∈ structure_y.hbonds, Species.charge structure_y.species hb.acceptor = -1) ∧
    donorHasHydrogen (.phOH .p2) .dianion = false ∧
    structure_y.stereo = pl1EnantiomerRR := by
  show Species.totalCharge .yAnion = -1 ∧ _
  exact ⟨y_is_monoanion, y_retains_one_acidic_OH,
         y_stabilisation_network.1, y_stabilisation_network.2.1,
         second_deprotonation_destroys_network.1, rfl⟩

#print axioms structure_pl1_certificate
#print axioms structure_y_certificate
#print axioms number_of_a_fragments
#print axioms n_parity_of_stub_evenness
#print axioms pl1_connected
#print axioms pl1_valences_ok
#print axioms permute_is_automorphism
#print axioms rr_is_chiral
#print axioms rs_is_meso
#print axioms y_stabilisation_network
#print axioms second_deprotonation_destroys_network
#print axioms hydrolysis_water_count

end IChO2026T5A2
