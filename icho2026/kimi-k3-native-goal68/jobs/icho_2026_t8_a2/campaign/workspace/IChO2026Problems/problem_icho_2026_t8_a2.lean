import Mathlib

/-!
# IChO 2026, Problem T8 ("Recycling of Carbon Dioxide"), subquestion 8.2

**Draw the structures of 3-7.** (16.0 pt, problem page Q8-1 / `T8_page-1.png`)

## Problem data used (all from `T8_page-1.png`)

Sacrificial reductant **2** is drawn as the tertiary amine N(CH2CH2OH)3
(triethanolamine, TEOA, C6H15NO3, charge 0, no radicals).  The scheme printed
in the problem is

    2 --(-1e-)--> [3] --(-H+)--> [4] --(-1e-)--> [5] --(+H2O, -H+)--> 6 + 7

with the textual constraints

* "Species 3, 4, and 5 are short-lived ionic and radical intermediates";
* "7 yields a silver mirror with the [Ag(NH3)2]OH test" (Tollens' test:
  species **7** is an aldehyde).

## Derived structures (derivation in `answer.md`)

* 3 = [N(CH2CH2OH)3]+ radical cation, C6H15NO3, charge +1, one radical
* 4 = (HOCH2CH2)2N-CH(radical)-CH2OH, C6H14NO3, neutral radical
* 5 = [(HOCH2CH2)2N=CH-CH2OH]+ iminium ion, C6H14NO3, charge +1, closed shell
* 6 = HN(CH2CH2OH)2 diethanolamine, C4H11NO2, neutral closed shell
* 7 = HOCH2-CHO glycolaldehyde, C2H4O2, neutral closed shell (aldehyde)

## Representation

Each molecule is a `Molecule`: a list of explicit `Atom`s, each recording its
`Element`, its formal `charge` and its `radicals` (number of unpaired
electrons localised on that atom), together with the full list of explicit
bonds (two atom indices and a bond order).  Connectivity, bond orders,
charges and radical counts are therefore explicit data; nothing about the
target structures is assumed through a string equality.
-/

namespace IChO2026.T8.A2

/-- Elements occurring in species 2-7. -/
inductive Element
  | C | H | N | O
  deriving DecidableEq, Repr

/-- One explicit atom of a drawn structure: its element, formal charge, and
the number of unpaired electrons (radical dots) placed on it. -/
structure Atom where
  el : Element
  charge : Int := 0
  radicals : Nat := 0
  deriving DecidableEq, Repr

/-- A molecule: explicit atoms and explicit bonds.  Bond endpoints are indices
into the atom list and each bond carries its bond order (1 = single,
2 = double). -/
structure Molecule where
  atoms : List Atom
  bonds : List (Nat × Nat × Nat)
  deriving Repr

namespace Molecule

/-- Total formal charge of the species. -/
def charge (m : Molecule) : Int := (m.atoms.map Atom.charge).sum

/-- Total number of unpaired electrons in the species. -/
def radicals (m : Molecule) : Nat := (m.atoms.map Atom.radicals).sum

/-- Number of atoms of element `e`. -/
def count (m : Molecule) (e : Element) : Nat :=
  m.atoms.countP (fun a => decide (a.el = e))

/-- The bonds in which atom index `i` participates. -/
def bondsOf (m : Molecule) (i : Nat) : List (Nat × Nat × Nat) :=
  m.bonds.filter (fun b => b.1 = i || b.2.1 = i)

/-- The element of atom `i`, as a decidable check against `e`. -/
def elAt (m : Molecule) (i : Nat) (e : Element) : Bool :=
  (m.atoms[i]?).any (fun a => a.el == e)

/-- Atom `i` is an aldehyde (formyl) carbon: a carbon carrying both a double
bond to an oxygen and a single bond to a hydrogen.  This is the functional
group detected by the [Ag(NH3)2]OH (Tollens) silver-mirror test. -/
def isAldehydeCarbon (m : Molecule) (i : Nat) : Bool :=
  m.elAt i Element.C &&
  (m.bondsOf i).any (fun p => m.elAt (if p.1 = i then p.2.1 else p.1) Element.O &&
    (p.2.2 == 2)) &&
  (m.bondsOf i).any (fun p => m.elAt (if p.1 = i then p.2.1 else p.1) Element.H &&
    (p.2.2 == 1))

/-- The species contains a formyl (-CHO) group, the structural requirement
behind a positive Tollens (silver mirror) test.  Stated as a proposition
derived from the explicit connectivity data of the molecule. -/
def hasAldehyde (m : Molecule) : Prop :=
  (List.range m.atoms.length).filter (fun i => m.isAldehydeCarbon i) ≠ []

end Molecule

/-- **2**: triethanolamine, N(CH2CH2OH)3, 25 explicit atoms.
    Indexing: N(0); arm 1: C(1)-C(2)-O(3)-H(4); arm 2: C(5)-C(6)-O(7)-H(8);
    arm 3: C(9)-C(10)-O(11)-H(12); alpha-hydrogens H(13),H(14) on C(1),
    H(15),H(16) on C(5), H(17),H(18) on C(9); beta-hydrogens H(19),H(20) on
    C(2), H(21),H(22) on C(6), H(23),H(24) on C(10). -/
def teoa : Molecule where
  atoms :=
    [ ⟨.N, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩ ]
  bonds :=
    [ (0, 1, 1), (0, 5, 1), (0, 9, 1),
      (1, 2, 1), (2, 3, 1), (3, 4, 1),
      (5, 6, 1), (6, 7, 1), (7, 8, 1),
      (9, 10, 1), (10, 11, 1), (11, 12, 1),
      (1, 13, 1), (1, 14, 1), (5, 15, 1), (5, 16, 1),
      (9, 17, 1), (9, 18, 1), (2, 19, 1), (2, 20, 1),
      (6, 21, 1), (6, 22, 1), (10, 23, 1), (10, 24, 1) ]

/-- **3**: the TEOA radical cation -- one electron removed from **2**;
    connectivity unchanged, N carries charge +1 and the unpaired electron. -/
def teoaRadicalCation : Molecule where
  atoms :=
    [ ⟨.N, 1, 1⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩ ]
  bonds := teoa.bonds

/-- **4**: the neutral alpha-amino radical, 24 explicit atoms: the alpha-C-H
    proton of arm 1 of **3** removed as H+ (the bond C(1)-H of index 13 in
    **2**/**3** is gone and one alpha-H slot is removed); the radical moves
    to the alpha-carbon C(1).  Remaining H indices: 13 (alpha on C(1)),
    14,15 (alpha on C(5)), 16,17 (alpha on C(9)), 18,19 (beta on C(2)),
    20,21 (beta on C(6)), 22,23 (beta on C(10)). -/
def alphaAminoRadical : Molecule where
  atoms :=
    [ ⟨.N, 0, 0⟩,
      ⟨.C, 0, 1⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩ ]
  bonds :=
    [ (0, 1, 1), (0, 5, 1), (0, 9, 1),
      (1, 2, 1), (2, 3, 1), (3, 4, 1),
      (5, 6, 1), (6, 7, 1), (7, 8, 1),
      (9, 10, 1), (10, 11, 1), (11, 12, 1),
      (1, 13, 1), (5, 14, 1), (5, 15, 1), (9, 16, 1),
      (9, 17, 1), (2, 18, 1), (2, 19, 1), (6, 20, 1),
      (6, 21, 1), (10, 22, 1), (10, 23, 1) ]

/-- **5**: the iminium ion, 24 explicit atoms -- one electron removed from
    **4**; the N-C(1) bond order rises to 2, N becomes four-coordinate and
    carries the positive charge.  No radical remains. -/
def iminium : Molecule where
  atoms :=
    [ ⟨.N, 1, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩ ]
  bonds :=
    [ (0, 1, 2), (0, 5, 1), (0, 9, 1),
      (1, 2, 1), (2, 3, 1), (3, 4, 1),
      (5, 6, 1), (6, 7, 1), (7, 8, 1),
      (9, 10, 1), (10, 11, 1), (11, 12, 1),
      (1, 13, 1), (5, 14, 1), (5, 15, 1), (9, 16, 1),
      (9, 17, 1), (2, 18, 1), (2, 19, 1), (6, 20, 1),
      (6, 21, 1), (10, 22, 1), (10, 23, 1) ]

/-- **6**: diethanolamine, HN(CH2CH2OH)2, 18 explicit atoms.  N(0)-H(1);
    arm 1: C(2)-C(3)-O(4)-H(5); arm 2: C(6)-C(7)-O(8)-H(9); alpha-H's
    H(10),H(11) on C(2) and H(14),H(15) on C(6); beta-H's H(12),H(13) on
    C(3) and H(16),H(17) on C(7). -/
def deoa : Molecule where
  atoms :=
    [ ⟨.N, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.C, 0, 0⟩, ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩,
      ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩ ]
  bonds :=
    [ (0, 1, 1), (0, 2, 1), (0, 6, 1),
      (2, 3, 1), (3, 4, 1), (4, 5, 1),
      (6, 7, 1), (7, 8, 1), (8, 9, 1),
      (2, 10, 1), (2, 11, 1), (3, 12, 1), (3, 13, 1),
      (6, 14, 1), (6, 15, 1), (7, 16, 1), (7, 17, 1) ]

/-- **7**: glycolaldehyde, HOCH2-CHO, 8 explicit atoms.  Aldehyde carbon C(0)
    double bonded to O(1), single bonded to H(2) and to C(3); C(3)-O(4)-H(5);
    alpha-hydrogens H(6), H(7) on C(3). -/
def glycolaldehyde : Molecule where
  atoms :=
    [ ⟨.C, 0, 0⟩, ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.C, 0, 0⟩,
      ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩ ]
  bonds := [ (0, 1, 2), (0, 2, 1), (0, 3, 1), (3, 4, 1), (4, 5, 1),
             (3, 6, 1), (3, 7, 1) ]

/-- The proton released at the deprotonation/hydrolysis steps. -/
def proton : Molecule where
  atoms := [ ⟨.H, 1, 0⟩ ]
  bonds := []

/-- Water, consumed at the hydrolysis step 5 -> 6 + 7. -/
def water : Molecule where
  atoms := [ ⟨.O, 0, 0⟩, ⟨.H, 0, 0⟩, ⟨.H, 0, 0⟩ ]
  bonds := [ (0, 1, 1), (0, 2, 1) ]

/-- The formal electron of the -1e- arrows, represented in the standard
electron-balance convention: an H atom = proton + electron, so an electron is
modeled as an "H" of charge -1. -/
def electron : Molecule where
  atoms := [ ⟨.H, -1, 0⟩ ]
  bonds := []

/-- Composition of **2** (TEOA): C6H15NO3. -/
theorem teoa_atoms :
    teoa.count .C = 6 ∧ teoa.count .H = 15 ∧
    teoa.count .N = 1 ∧ teoa.count .O = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Composition of **3** = **2** - e-: unchanged C6H15NO3 skeleton. -/
theorem species3_atoms :
    teoaRadicalCation.count .C = 6 ∧ teoaRadicalCation.count .H = 15 ∧
    teoaRadicalCation.count .N = 1 ∧ teoaRadicalCation.count .O = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Composition of **4** = **3** - H+: C6H14NO3. -/
theorem species4_atoms :
    alphaAminoRadical.count .C = 6 ∧ alphaAminoRadical.count .H = 14 ∧
    alphaAminoRadical.count .N = 1 ∧ alphaAminoRadical.count .O = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Composition of **5** = **4** - e-: still C6H14NO3 (six carbons retained
    until hydrolysis). -/
theorem species5_atoms :
    iminium.count .C = 6 ∧ iminium.count .H = 14 ∧
    iminium.count .N = 1 ∧ iminium.count .O = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Composition of **6** (diethanolamine): C4H11NO2. -/
theorem species6_atoms :
    deoa.count .C = 4 ∧ deoa.count .H = 11 ∧
    deoa.count .N = 1 ∧ deoa.count .O = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Composition of **7** (glycolaldehyde): C2H4O2. -/
theorem species7_atoms :
    glycolaldehyde.count .C = 2 ∧ glycolaldehyde.count .H = 4 ∧
    glycolaldehyde.count .N = 0 ∧ glycolaldehyde.count .O = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **2** is neutral and closed-shell, as drawn on the problem page. -/
theorem species2_closed : teoa.charge = 0 ∧ teoa.radicals = 0 := ⟨rfl, rfl⟩

/-- **3** is the radical cation: charge +1, one unpaired electron. -/
theorem species3_charge_radical :
    teoaRadicalCation.charge = 1 ∧ teoaRadicalCation.radicals = 1 := ⟨rfl, rfl⟩

/-- **4** is the neutral radical: charge 0, one unpaired electron. -/
theorem species4_charge_radical :
    alphaAminoRadical.charge = 0 ∧ alphaAminoRadical.radicals = 1 := ⟨rfl, rfl⟩

/-- **5** is the closed-shell ion: charge +1, no unpaired electrons. -/
theorem species5_charge_radical :
    iminium.charge = 1 ∧ iminium.radicals = 0 := ⟨rfl, rfl⟩

/-- **6** and **7** are neutral, closed-shell products. -/
theorem species6_species7_closed :
    deoa.charge = 0 ∧ deoa.radicals = 0 ∧
    glycolaldehyde.charge = 0 ∧ glycolaldehyde.radicals = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Tollens constraint: **7** indeed carries a -CHO group (a specific carbon
    with a C=O double bond and a C-H single bond), so the silver-mirror
    statement is satisfied by glycolaldehyde and fixes the structure of
    **7**.  The aldehyde carbon is atom index 0 of `glycolaldehyde`. -/
theorem tollens_implies_aldehyde : glycolaldehyde.hasAldehyde := by
  unfold Molecule.hasAldehyde
  decide

/-- Step 2 -> 3, -1e-: atoms balance for every element (a bare electron
    carries no atoms). -/
theorem step1_atoms_balanced :
    ∀ e : Element, teoa.count e = teoaRadicalCation.count e := by
  intro e; cases e <;> rfl

/-- Step 2 -> 3, -1e-: charge balance (an electron of charge -1 leaves). -/
theorem step1_charge_balanced :
    teoa.charge = teoaRadicalCation.charge + electron.charge := rfl

/-- Step 3 -> 4, -H+: atoms balance for every element. -/
theorem step2_atoms_balanced :
    ∀ e : Element,
      teoaRadicalCation.count e = alphaAminoRadical.count e + proton.count e := by
  intro e; cases e <;> rfl

/-- Step 3 -> 4, -H+: charge balance. -/
theorem step2_charge_balanced :
    teoaRadicalCation.charge = alphaAminoRadical.charge + proton.charge := rfl

/-- Step 4 -> 5, -1e-: atoms balance for every element (a bare electron
    carries no atoms). -/
theorem step3_atoms_balanced :
    ∀ e : Element, alphaAminoRadical.count e = iminium.count e := by
  intro e; cases e <;> rfl

/-- Step 4 -> 5, -1e-: charge balance. -/
theorem step3_charge_balanced :
    alphaAminoRadical.charge = iminium.charge + electron.charge := rfl

/-- Step 5 + H2O -> 6 + 7 + H+: atoms balance for every element. -/
theorem step4_atoms_balanced :
    ∀ e : Element,
      iminium.count e + water.count e =
        deoa.count e + glycolaldehyde.count e + proton.count e := by
  intro e; cases e <;> rfl

/-- Step 5 + H2O -> 6 + 7 + H+: charge balance. -/
theorem step4_charge_balanced :
    iminium.charge + water.charge =
      deoa.charge + glycolaldehyde.charge + proton.charge := rfl

/-- The radical count: **3** carries the unpaired electron created at step 1,
    it is retained in **4**, and consumed at the second oxidation step. -/
theorem radical_fate_through_scheme :
    teoa.radicals + 1 = teoaRadicalCation.radicals ∧
    teoaRadicalCation.radicals = alphaAminoRadical.radicals ∧
    alphaAminoRadical.radicals = iminium.radicals + 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Net result: the sacrificial reductant is a two-electron donor.
    2 + H2O -> 6 + 7 + 2 H+ + 2 e-, the conjugate oxidation of the
    8.1 half-reaction CO2 + 2 H+ + 2 e- -> CO + H2O.  Atom balance counts
    the real atoms (electrons carry none); charge balance includes the two
    electrons of charge -1. -/
theorem overall_two_electron_donation :
    (∀ e : Element,
      teoa.count e + water.count e =
        deoa.count e + glycolaldehyde.count e + 2 * proton.count e) ∧
    (teoa.charge + water.charge =
      deoa.charge + glycolaldehyde.charge + 2 * proton.charge + 2 * electron.charge) :=
  ⟨by intro e; cases e <;> rfl, rfl⟩

end IChO2026.T8.A2
