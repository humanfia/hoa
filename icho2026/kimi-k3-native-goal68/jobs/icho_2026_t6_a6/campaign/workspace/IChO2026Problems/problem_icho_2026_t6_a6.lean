import Mathlib

/-!
# IChO 2026, Problem T6.6 (icho_2026_t6_a6): structures of M–R

Q6-4 of the official booklet shows the template synthesis of a porphyrin
nanobelt:

* toluene --(t-BuCl (2 equiv.), AlCl₃)--> M
* M --(1) NBS, (BzO)₂; 2) HMTA; 3) HCl, H₂O)--> N
* N --(1) dipyrromethane (shown), CF₃COOH; 2) DDQ; 3) Zn(OAc)₂)--> O
* O --NBS--> Q
* Q --(1) Pd⁰, PPh₃, CuI, (C₆H₁₃)₃Si–C≡CH; 2) n-Bu₄NF)--> R
* R + hexakis(4-(pyridin-4-yl)phenyl)benzene template --(PdCl₂, PPh₃, CuI)-->
  cyclo-trimer of porphyrin units (six P6 shown), Ar = 4-tert-butylphenyl.

and asks to draw the structures of M–R.

Because Lean has no graphics canvas, each requested structure is formalised as
an explicit connectivity model: atoms are labelled `Atom`s, bonds carry a
`BondOrder`, and the answers are propositions stating the full structural
specification (substitution pattern, bond multiplicities, metal coordination,
elemental counts).  Everything is discharged on finite, explicitly enumerated
structures by `decide`.  No `sorry`; no axioms beyond Lean's logical ones.
-/

namespace IChO2026T6A6

/-- Chemical elements occurring in this problem. -/
inductive Elem where
  | C | H | N | O | Zn | Br | Si
  deriving DecidableEq, Repr

/-- Bond orders used in skeletal drawings. -/
inductive BondOrder where
  | single | aromatic | doubleBond | triple
  deriving DecidableEq, Repr

/-- One atom: a unique label and its element.  Implicit hydrogens are computed
from bond orders, not stored. -/
structure Atom where
  id : String
  elem : Elem
  deriving DecidableEq, Repr

/-- A covalent bond between two labelled atoms. -/
structure Bond where
  a : String
  b : String
  order : BondOrder
  deriving DecidableEq, Repr

/-- A molecular structural model. -/
structure Mol where
  atoms : List Atom
  bonds : List Bond
  metal : Option Elem := none
  coordination : List String := []
  deriving Repr

/-- The molecule has a bond of order `o` between labels `x` and `y`. -/
def Mol.hasBond (m : Mol) (x y : String) (o : BondOrder) : Bool :=
  m.bonds.any (fun b => ((b.a == x && b.b == y) || (b.a == y && b.b == x)) && b.order == o)

/-- Number of atoms of a given element. -/
def Mol.count (m : Mol) (e : Elem) : Nat :=
  (m.atoms.filter (·.elem == e)).length

/-- Doubled sum of bond orders incident on `x` (aromatic contributes 3). -/
def Mol.doubleValenceSum (m : Mol) (x : String) : Nat :=
  m.bonds.foldl (fun acc b =>
    if b.a == x || b.b == x then
      acc + match b.order with
        | .single => 2 | .aromatic => 3 | .doubleBond => 4 | .triple => 6
    else acc) 0

/-- Implicit hydrogens of a carbon atom (skeletal-drawing convention: H tops
the doubled valence sum up to 8). -/
def Mol.implicitH (m : Mol) (x : String) : Nat :=
  let v := m.doubleValenceSum x
  if (m.atoms.find? (·.id == x)).map (·.elem) == some Elem.C then
    if 8 ≤ v then 0 else (8 - v) / 2
  else 0

/-- Atom `x` of element `e` is present. -/
def Mol.hasAtom (m : Mol) (x : String) (e : Elem) : Bool :=
  m.atoms.any (fun a => a.id == x && a.elem == e)

/-! ## Elementary motifs -/

def ringLabels (p : String) : List String :=
  ["1", "2", "3", "4", "5", "6"].map (fun i => p ++ i)

def ringAtoms (p : String) : List Atom :=
  (ringLabels p).map (fun x => ⟨x, Elem.C⟩)

def ringBonds (p : String) : List Bond :=
  match ringLabels p with
  | [a, b, c, d, e, f] =>
      [ ⟨a, b, .aromatic⟩, ⟨b, c, .aromatic⟩, ⟨c, d, .aromatic⟩,
        ⟨d, e, .aromatic⟩, ⟨e, f, .aromatic⟩, ⟨f, a, .aromatic⟩ ]
  | _ => []

/-- A tert-butyl group attached through central carbon `c` to ring atom `r`. -/
def tBuAtoms (c : String) : List Atom :=
  [⟨c, Elem.C⟩, ⟨c ++ "1", Elem.C⟩, ⟨c ++ "2", Elem.C⟩, ⟨c ++ "3", Elem.C⟩]

def tBuBonds (c r : String) : List Bond :=
  [ ⟨r, c, .single⟩, ⟨c, c ++ "1", .single⟩, ⟨c, c ++ "2", .single⟩,
    ⟨c, c ++ "3", .single⟩ ]

/-! ## M : 1-methyl-4-tert-butylbenzene

Friedel–Crafts alkylation of toluene with t-BuCl/AlCl₃: the para isomer is the
thermodynamic product, and the hint "M has four types of protons" matches para
(aromatic AA'BB' = two types, CH₃, C(CH₃)₃), excluding ortho.  m1 carries the
original toluene methyl (mMe); m4 (para) carries the new tert-butyl. -/

def M : Mol where
  atoms := ringAtoms "m" ++ [⟨"mMe", Elem.C⟩] ++ tBuAtoms "mB"
  bonds := ringBonds "m" ++ [⟨"m1", "mMe", .single⟩] ++ tBuBonds "mB" "m4"

theorem M_formula_counts :
    M.count Elem.C = 11 ∧ M.count Elem.N = 0 ∧ M.count Elem.Br = 0 := by
  decide

theorem M_para :
    M.hasBond "m1" "mMe" BondOrder.single = true ∧
    M.hasBond "m4" "mB" BondOrder.single = true ∧
    M.hasBond "m2" "mB" BondOrder.single = false := by
  decide

/-- The four proton environments: mMe (type 1), three equivalent tBu methyls
(type 2), aromatic m2/m6 (type 3), aromatic m3/m5 (type 4); mB and m1/m4 carry
no hydrogen. -/
theorem M_four_proton_types :
    M.implicitH "mB" = 0 ∧ M.implicitH "mB1" = 3 ∧ M.implicitH "mMe" = 3 ∧
    M.implicitH "m2" = 1 ∧ M.implicitH "m3" = 1 ∧
    M.implicitH "m1" = 0 ∧ M.implicitH "m4" = 0 := by
  decide

/-! ## N : 4-tert-butylbenzaldehyde

NBS/(BzO)₂ brominates the benzylic methyl of M (Wohl–Ziegler), HMTA with
aqueous acidic work-up (Sommelet) converts ArCH₂Br into ArCHO.  The methyl
carbon mMe of M becomes the formyl carbon: C=O double bond, one aldehydic H. -/

def N : Mol where
  atoms := ringAtoms "m" ++ [⟨"mMe", Elem.C⟩, ⟨"aldO", Elem.O⟩] ++ tBuAtoms "mB"
  bonds := ringBonds "m" ++ [⟨"m1", "mMe", .single⟩, ⟨"mMe", "aldO", .doubleBond⟩]
    ++ tBuBonds "mB" "m4"

theorem N_formula_counts :
    N.count Elem.C = 11 ∧ N.count Elem.O = 1 ∧ N.count Elem.Br = 0 := by
  decide

theorem N_aldehyde :
    N.hasBond "mMe" "aldO" BondOrder.doubleBond = true ∧
    N.implicitH "mMe" = 1 := by
  decide

/-! ## O : 5,15-bis(4-tert-butylphenyl)porphyrinato zinc(II)

Two equivalents of N condense with dipyrromethane (2+2 MacDonald), DDQ oxidises
to the porphyrin, Zn(OAc)₂ inserts Zn²⁺.  Aryl groups land at the two trans
meso positions (5,15) — the Ar placement drawn for P6.  Porphyrin skeleton:
meso carbons me5 (A|B), me10 (B|C), me15 (C|D), me20 (D|A); pyrrole rings A–D
with α-carbons a· and β-carbons b·, nitrogens nA..nD. -/

def porphAtoms : List Atom :=
  (["me5", "me10", "me15", "me20"]).map (⟨·, Elem.C⟩) ++
  (["aA1", "aA2", "bA1", "bA2",
    "aB1", "aB2", "bB1", "bB2",
    "aC1", "aC2", "bC1", "bC2",
    "aD1", "aD2", "bD1", "bD2"]).map (⟨·, Elem.C⟩) ++
  (["nA", "nB", "nC", "nD"]).map (⟨·, Elem.N⟩)

def porphBonds : List Bond :=
  [ ⟨"nA", "aA1", .aromatic⟩, ⟨"aA1", "bA1", .aromatic⟩, ⟨"bA1", "bA2", .aromatic⟩,
    ⟨"bA2", "aA2", .aromatic⟩, ⟨"aA2", "nA", .aromatic⟩ ] ++
  [ ⟨"nB", "aB1", .aromatic⟩, ⟨"aB1", "bB1", .aromatic⟩, ⟨"bB1", "bB2", .aromatic⟩,
    ⟨"bB2", "aB2", .aromatic⟩, ⟨"aB2", "nB", .aromatic⟩ ] ++
  [ ⟨"nC", "aC1", .aromatic⟩, ⟨"aC1", "bC1", .aromatic⟩, ⟨"bC1", "bC2", .aromatic⟩,
    ⟨"bC2", "aC2", .aromatic⟩, ⟨"aC2", "nC", .aromatic⟩ ] ++
  [ ⟨"nD", "aD1", .aromatic⟩, ⟨"aD1", "bD1", .aromatic⟩, ⟨"bD1", "bD2", .aromatic⟩,
    ⟨"bD2", "aD2", .aromatic⟩, ⟨"aD2", "nD", .aromatic⟩ ] ++
  [ ⟨"aA2", "me5", .aromatic⟩, ⟨"me5", "aB1", .aromatic⟩,
    ⟨"aB2", "me10", .aromatic⟩, ⟨"me10", "aC1", .aromatic⟩,
    ⟨"aC2", "me15", .aromatic⟩, ⟨"me15", "aD1", .aromatic⟩,
    ⟨"aD2", "me20", .aromatic⟩, ⟨"me20", "aA1", .aromatic⟩ ]

/-- 4-tert-butylphenyl arm attached through ring atom 1. -/
def arAtoms (ar : String) : List Atom :=
  ringAtoms (ar ++ "r") ++ tBuAtoms (ar ++ "B")

def arBonds (ar me : String) : List Bond :=
  ringBonds (ar ++ "r") ++ [⟨me, ar ++ "r1", .single⟩] ++
  tBuBonds (ar ++ "B") (ar ++ "r4")

theorem ar_ten_carbons : (arAtoms "x1").length = 10 := by decide

def O : Mol where
  atoms := porphAtoms ++ arAtoms "x1" ++ arAtoms "x2" ++ [⟨"zn", Elem.Zn⟩]
  bonds := porphBonds ++ arBonds "x1" "me5" ++ arBonds "x2" "me15"
  metal := some Elem.Zn
  coordination := ["nA", "nB", "nC", "nD"]

theorem O_counts :
    O.count Elem.C = 40 ∧ O.count Elem.N = 4 ∧ O.count Elem.Zn = 1 ∧
    O.count Elem.Br = 0 := by
  decide

/-- Ar groups sit at the 5,15 (trans) meso carbons; me10 and me20 keep their
hydrogens; Zn binds all four pyrrole nitrogens. -/
theorem O_trans_meso :
    O.hasBond "me5" "x1r1" BondOrder.single = true ∧
    O.hasBond "me15" "x2r1" BondOrder.single = true ∧
    O.implicitH "me10" = 1 ∧ O.implicitH "me20" = 1 ∧
    O.coordination = ["nA", "nB", "nC", "nD"] := by
  decide

/-! ## Q : β-tetrabromo-O

NBS brominates the four free β-positions — the β-carbons of rings B and D,
bB1/bB2/bD1/bD2, giving 2,3,17,18-tetrabromination (the four positions between
the two Ar-bearing meso edges, as required for the subsequent cross-couplings). -/

def Q : Mol where
  atoms := O.atoms ++ (["brB1", "brB2", "brD1", "brD2"]).map (⟨·, Elem.Br⟩)
  bonds := O.bonds ++
    [ ⟨"bB1", "brB1", .single⟩, ⟨"bB2", "brB2", .single⟩,
      ⟨"bD1", "brD1", .single⟩, ⟨"bD2", "brD2", .single⟩ ]
  metal := some Elem.Zn
  coordination := ["nA", "nB", "nC", "nD"]

theorem Q_counts :
    Q.count Elem.C = 40 ∧ Q.count Elem.N = 4 ∧ Q.count Elem.Br = 4 ∧
    Q.count Elem.Zn = 1 := by
  decide

theorem Q_beta_pattern :
    Q.hasBond "bB1" "brB1" BondOrder.single = true ∧
    Q.hasBond "bB2" "brB2" BondOrder.single = true ∧
    Q.hasBond "bD1" "brD1" BondOrder.single = true ∧
    Q.hasBond "bD2" "brD2" BondOrder.single = true ∧
    Q.hasBond "bA1" "brB1" BondOrder.single = false := by
  decide

/-! ## R : bis-ethynyl dibromo porphyrin

Pd⁰/PPh₃/CuI with (C₆H₁₃)₃Si–C≡CH replaces two of the four bromines (the pair
drawn along the P6 oligomer axis, labels bB2/bD2) with THS-protected ethynyls,
and step 2 (n-Bu₄NF) strips the THS groups to terminal alkynes.  The other two
bromines (bB1, bD1) survive into R and are consumed in the final
template-directed cyclooligomerisation to butadiyne edges.  Hence R carries
two terminal ethynyl groups and two β-bromines; no silicon remains. -/

def R : Mol where
  atoms := O.atoms ++ [⟨"brB1", Elem.Br⟩, ⟨"brD1", Elem.Br⟩] ++
    [⟨"tB1", Elem.C⟩, ⟨"tB2", Elem.C⟩, ⟨"tD1", Elem.C⟩, ⟨"tD2", Elem.C⟩]
  bonds := O.bonds ++
    [ ⟨"bB1", "brB1", .single⟩, ⟨"bD1", "brD1", .single⟩,
      ⟨"bB2", "tB1", .single⟩, ⟨"tB1", "tB2", .triple⟩,
      ⟨"bD2", "tD1", .single⟩, ⟨"tD1", "tD2", .triple⟩ ]
  metal := some Elem.Zn
  coordination := ["nA", "nB", "nC", "nD"]

theorem R_counts :
    R.count Elem.C = 44 ∧ R.count Elem.N = 4 ∧ R.count Elem.Br = 2 ∧
    R.count Elem.Zn = 1 ∧ R.count Elem.Si = 0 := by
  decide

theorem R_terminal_alkynes :
    R.hasBond "tB1" "tB2" BondOrder.triple = true ∧
    R.hasBond "tD1" "tD2" BondOrder.triple = true ∧
    R.hasBond "bB2" "tB1" BondOrder.single = true ∧
    R.hasBond "bD2" "tD1" BondOrder.single = true ∧
    R.implicitH "tB2" = 1 ∧ R.implicitH "tD2" = 1 ∧
    R.implicitH "tB1" = 0 ∧ R.implicitH "tD1" = 0 := by
  decide

/-! ## The hexafunctional template

The star drawn in the scheme is hexakis[4-(pyridin-4-yl)phenyl]benzene:
a central benzene bearing six 4-(pyridin-4-yl)phenyl arms; each pyridine
nitrogen sits para to the biaryl bond and is one of the six Zn-binding sites
in the belt picture.  Central ring tc1..tc6; arm i: phenylene tph<i>, pyridine
tpy<i> with N at position 4. -/

def armAtoms (i : Nat) : List Atom :=
  let ph := "tph" ++ toString i
  let py := "tpy" ++ toString i
  ringAtoms ph ++
    (["1", "2", "3", "5", "6"].map (fun k => ⟨py ++ k, Elem.C⟩)) ++
    [⟨py ++ "4", Elem.N⟩]

def armBonds (i : Nat) (c : String) : List Bond :=
  let ph := "tph" ++ toString i
  let py := "tpy" ++ toString i
  ringBonds ph ++
  [ ⟨py ++ "1", py ++ "2", .aromatic⟩, ⟨py ++ "2", py ++ "3", .aromatic⟩,
    ⟨py ++ "3", py ++ "4", .aromatic⟩, ⟨py ++ "4", py ++ "5", .aromatic⟩,
    ⟨py ++ "5", py ++ "6", .aromatic⟩, ⟨py ++ "6", py ++ "1", .aromatic⟩ ] ++
  [ ⟨c, ph ++ "1", .single⟩, ⟨ph ++ "4", py ++ "1", .single⟩ ]

def template : Mol where
  atoms := ringAtoms "tc" ++ (List.range' 1 6).flatMap armAtoms
  bonds := ringBonds "tc" ++
    (List.range' 1 6).flatMap (fun i => armBonds i ("tc" ++ toString i))

theorem template_six_arms :
    template.count Elem.N = 6 ∧ template.count Elem.C = 72 := by
  decide

theorem template_arm1_para :
    template.hasBond "tpy14" "tpy13" BondOrder.aromatic = true ∧
    template.hasBond "tpy14" "tpy15" BondOrder.aromatic = true ∧
    template.hasBond "tph14" "tpy11" BondOrder.single = true ∧
    template.hasAtom "tpy14" Elem.N = true := by
  decide

theorem template_six_binding_sites :
    (List.range' 1 6).all
      (fun i => template.hasAtom ("tpy" ++ toString i ++ "4") Elem.N) = true := by
  decide

/-! ## Final answer theorem -/

theorem icho_2026_t6_a6_structures :
    -- M = 1-methyl-4-tert-butylbenzene
    (M.count Elem.C = 11 ∧
     M.hasBond "m1" "mMe" BondOrder.single = true ∧
     M.hasBond "m4" "mB" BondOrder.single = true ∧
     M.implicitH "mMe" = 3 ∧ M.implicitH "mB" = 0) ∧
    -- N = 4-tert-butylbenzaldehyde
    (N.count Elem.O = 1 ∧
     N.hasBond "mMe" "aldO" BondOrder.doubleBond = true ∧
     N.implicitH "mMe" = 1 ∧
     N.hasBond "m4" "mB" BondOrder.single = true) ∧
    -- O = trans-5,15-bis(4-tert-butylphenyl)porphyrinato Zn(II)
    (O.count Elem.C = 40 ∧ O.count Elem.N = 4 ∧ O.count Elem.Zn = 1 ∧
     O.hasBond "me5" "x1r1" BondOrder.single = true ∧
     O.hasBond "me15" "x2r1" BondOrder.single = true ∧
     O.implicitH "me10" = 1 ∧ O.implicitH "me20" = 1 ∧
     O.coordination = ["nA", "nB", "nC", "nD"]) ∧
    -- Q = β-tetrabromo-O
    (Q.count Elem.Br = 4 ∧
     Q.hasBond "bB1" "brB1" BondOrder.single = true ∧
     Q.hasBond "bB2" "brB2" BondOrder.single = true ∧
     Q.hasBond "bD1" "brD1" BondOrder.single = true ∧
     Q.hasBond "bD2" "brD2" BondOrder.single = true) ∧
    -- R = bis(terminal-ethynyl) dibromo Zn porphyrin, silicon-free
    (R.count Elem.Br = 2 ∧ R.count Elem.C = 44 ∧ R.count Elem.Si = 0 ∧
     R.hasBond "tB1" "tB2" BondOrder.triple = true ∧
     R.hasBond "tD1" "tD2" BondOrder.triple = true ∧
     R.implicitH "tB2" = 1 ∧ R.implicitH "tD2" = 1 ∧
     R.hasBond "bB1" "brB1" BondOrder.single = true ∧
     R.hasBond "bD1" "brD1" BondOrder.single = true ∧
     R.coordination = ["nA", "nB", "nC", "nD"]) ∧
    -- template = hexakis[4-(pyridin-4-yl)phenyl]benzene
    (template.count Elem.N = 6 ∧ template.count Elem.C = 72 ∧
     template.hasBond "tph14" "tpy11" BondOrder.single = true) := by
  decide

#print axioms icho_2026_t6_a6_structures
#print axioms M_formula_counts
#print axioms M_four_proton_types
#print axioms N_aldehyde
#print axioms O_trans_meso
#print axioms Q_beta_pattern
#print axioms R_terminal_alkynes
#print axioms template_six_arms

end IChO2026T6A6
