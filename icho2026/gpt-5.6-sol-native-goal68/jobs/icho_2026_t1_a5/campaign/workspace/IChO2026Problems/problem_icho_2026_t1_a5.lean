import Mathlib

/-!
# IChO 2026, theory problem 1.5

The problem asks for drawings, so the answer below is represented as molecular
graphs rather than as names or strings.  Hydrogens are explicit.  Every atom
also carries formal-charge, radical, and tetrahedral-stereochemistry fields,
and every bond carries its order and geometrical-stereochemistry field.

The experimental percentages are treated as displayed measurements: 11.18%
and 49.98% mean the corresponding half-last-place intervals.  Atomic masses
are kept as exact integers in units of 0.001 u (C = 12010, H = 1008,
O = 15999); no intermediate rounding is used.
-/

namespace IChO2026Problems.T1A5

inductive Element
  | C | H | O
  deriving DecidableEq, BEq, Repr

inductive TetrahedralStereo
  | none | R | S
  deriving DecidableEq, BEq, Repr

inductive BondOrder
  | single | double | aromatic
  deriving DecidableEq, BEq, Repr

inductive BondStereo
  | none | E | Z
  deriving DecidableEq, BEq, Repr

structure Atom where
  element : Element
  formalCharge : Int
  radicalElectrons : Nat
  stereo : TetrahedralStereo
  deriving DecidableEq, BEq, Repr

structure Bond where
  a : Nat
  b : Nat
  order : BondOrder
  stereo : BondStereo
  deriving DecidableEq, BEq, Repr

structure Molecule where
  atoms : List Atom
  bonds : List Bond
  deriving DecidableEq, BEq, Repr

def neutral (e : Element) : Atom :=
  { element := e, formalCharge := 0, radicalElectrons := 0,
    stereo := TetrahedralStereo.none }

def sbond (a b : Nat) : Bond :=
  { a := a, b := b, order := BondOrder.single, stereo := BondStereo.none }

def dbond (a b : Nat) : Bond :=
  { a := a, b := b, order := BondOrder.double, stereo := BondStereo.none }

def abond (a b : Nat) : Bond :=
  { a := a, b := b, order := BondOrder.aromatic, stereo := BondStereo.none }

def aromaticRingBonds : List Bond :=
  [abond 0 1, abond 1 2, abond 2 3, abond 3 4, abond 4 5, abond 5 0]

def bondPair (b : Bond) : Nat × Nat :=
  if b.a ≤ b.b then (b.a, b.b) else (b.b, b.a)

def bondOrderAt (m : Molecule) (i j : Nat) : Option (BondOrder × BondStereo) :=
  (m.bonds.find? fun b => bondPair b = (min i j, max i j)).map
    fun b => (b.order, b.stereo)

def bondValenceUnits : BondOrder → Nat
  | BondOrder.single => 2
  | BondOrder.double => 4
  | BondOrder.aromatic => 3

def expectedValenceUnits : Element → Nat
  | Element.H => 2
  | Element.O => 4
  | Element.C => 8

def valenceUnitsAt (m : Molecule) (i : Nat) : Nat :=
  m.bonds.foldl (fun total b =>
    if b.a = i || b.b = i then total + bondValenceUnits b.order else total) 0

/-- A finite, simple molecular graph with ordinary neutral closed-shell
valences. Aromatic bond order is counted as 1.5 by using doubled units. -/
def validClosedShellMolecule (m : Molecule) : Bool :=
  let n := m.atoms.length
  m.bonds.all (fun b =>
      b.a < n && b.b < n && b.a != b.b && b.stereo == BondStereo.none) &&
    decide (m.bonds.map bondPair).Nodup &&
    (List.range n).all (fun i =>
      match m.atoms[i]? with
      | none => false
      | some a =>
          a.formalCharge == 0 && a.radicalElectrons == 0 &&
          a.stereo == TetrahedralStereo.none &&
          valenceUnitsAt m i == expectedValenceUnits a.element)

structure Formula where
  carbon : Nat
  hydrogen : Nat
  oxygen : Nat
  deriving DecidableEq, BEq, Repr

def countElement (m : Molecule) (e : Element) : Nat :=
  (m.atoms.filter fun a => a.element = e).length

def molecularFormula (m : Molecule) : Formula :=
  { carbon := countElement m Element.C
    hydrogen := countElement m Element.H
    oxygen := countElement m Element.O }

/-! ## E: the sixfold-symmetric alkylbenzene precursor -/

/-- Carbon count for a benzene bearing six identical straight saturated
substituents of chain length `k`; `k = 0` is benzene itself. -/
def precursorCarbonCount (k : Nat) : Nat := 6 + 6 * k

/-- Hydrogen count for the same C6-symmetric homologous family. -/
def precursorHydrogenCount (k : Nat) : Nat := 6 * (2 * k + 1)

def chainCarbonIndex (k site position : Nat) : Nat :=
  6 + site * k + position

def precursorHydrogenBase (k : Nat) : Nat :=
  precursorCarbonCount k

def siteHydrogenBase (k site : Nat) : Nat :=
  precursorHydrogenBase k + site * (2 * k + 1)

def precursorSubstituentBonds (k : Nat) : List Bond :=
  if k = 0 then
    (List.range 6).map fun site => sbond site (siteHydrogenBase k site)
  else
    (List.range 6).flatMap fun site =>
      [sbond site (chainCarbonIndex k site 0)] ++
      (List.range (k - 1)).map (fun j =>
        sbond (chainCarbonIndex k site j) (chainCarbonIndex k site (j + 1))) ++
      (List.range k).flatMap (fun j =>
        let hCount := if j + 1 = k then 3 else 2
        (List.range hCount).map fun q =>
          sbond (chainCarbonIndex k site j) (siteHydrogenBase k site + 2 * j + q))

/-- Complete molecular graph of the C6-symmetric peralkylbenzene homolog. -/
def symmetricPeralkylbenzene (k : Nat) : Molecule :=
  { atoms :=
      List.replicate (precursorCarbonCount k) (neutral Element.C) ++
      List.replicate (precursorHydrogenCount k) (neutral Element.H)
    bonds := aromaticRingBonds ++ precursorSubstituentBonds k }

/-- The structure identified for E: 1,2,3,4,5,6-hexamethylbenzene. -/
def structureE : Molecule := symmetricPeralkylbenzene 1

/- Exact integer comparisons equivalent to
   11.175% ≤ hydrogen mass percentage ≤ 11.185%. -/
def hydrogenDisplayCompatible (k : Nat) : Prop :=
  let c := precursorCarbonCount k
  let h := precursorHydrogenCount k
  let totalMass := 12010 * c + 1008 * h
  11175 * totalMass ≤ 100 * 1000 * 1008 * h ∧
    100 * 1000 * 1008 * h ≤ 11185 * totalMass

/-- The unrounded 11.18% measurement selects chain length one throughout the
unbounded homologous family; no finite search cutoff is used. -/
theorem hydrogen_percentage_selects_methyl (k : Nat)
    (h : hydrogenDisplayCompatible k) : k = 1 := by
  simp only [hydrogenDisplayCompatible, precursorCarbonCount,
    precursorHydrogenCount] at h
  omega

theorem structure_e_from_problem (k : Nat)
    (h : hydrogenDisplayCompatible k) :
    symmetricPeralkylbenzene k = structureE := by
  rw [hydrogen_percentage_selects_methyl k h]
  rfl

/-! ## F: graph-level oxidation of all six benzylic methyl groups -/

def oxidationBonds : List Bond :=
  (List.range 6).flatMap fun site =>
    [dbond (6 + site) (12 + site),
     sbond (6 + site) (18 + site),
     sbond (18 + site) (24 + site)]

/-- Standard exhaustive acidic-permanganate benzylic oxidation, specialized
to the canonical indexing of a sixfold arene.  The six ring atoms and six
benzylic carbons are retained, all benzylic hydrogens are removed, and each
benzylic carbon becomes `C(=O)OH`. -/
def oxidiseSixBenzylicGroups (m : Molecule) : Molecule :=
  { atoms := m.atoms.take 12 ++
      List.replicate 12 (neutral Element.O) ++
      List.replicate 6 (neutral Element.H)
    bonds := m.bonds.filter (fun b => b.a < 12 && b.b < 12) ++ oxidationBonds }

/-- The structure identified for F: benzene-1,2,3,4,5,6-hexacarboxylic acid,
also called mellitic acid. -/
def structureF : Molecule := oxidiseSixBenzylicGroups structureE

theorem structure_f_from_problem (k : Nat)
    (h : hydrogenDisplayCompatible k) :
    oxidiseSixBenzylicGroups (symmetricPeralkylbenzene k) = structureF := by
  rw [structure_e_from_problem k h]
  rfl

/-! ## G: dehydration to three adjacent cyclic anhydrides -/

/-- Retain the aromatic framework, carbonyl atoms, and one hydroxyl oxygen
from each adjacent pair (sites 0/1, 2/3, 4/5). -/
def retainedAfterTripleDehydration (old : Nat) : Option Nat :=
  if old < 18 then some old
  else if old = 18 then some 18
  else if old = 20 then some 19
  else if old = 22 then some 20
  else none

def retainAtom (m : Molecule) (old : Nat) : Option Atom :=
  match retainedAfterTripleDehydration old with
  | none => none
  | some _ => m.atoms[old]?

def retainBond (b : Bond) : Option Bond :=
  match retainedAfterTripleDehydration b.a, retainedAfterTripleDehydration b.b with
  | some a, some c => some { b with a := a, b := c }
  | _, _ => none

def anhydrideBridgeBonds : List Bond :=
  [sbond 7 18, sbond 9 19, sbond 11 20]

/-- Graph edit for loss of three water molecules from the six neighbouring
carboxyl groups.  The retained oxygens bridge carbonyl pairs 0/1, 2/3, 4/5. -/
def tripleAdjacentDehydration (m : Molecule) : Molecule :=
  { atoms := (List.range m.atoms.length).filterMap (retainAtom m)
    bonds := m.bonds.filterMap retainBond ++ anhydrideBridgeBonds }

/-- The structure identified for G: mellitic trianhydride. -/
def structureG : Molecule := tripleAdjacentDehydration structureF

def dehydrationFormula (waters : Nat) : Formula :=
  { carbon := 12, hydrogen := 6 - 2 * waters, oxygen := 12 - waters }

/- Exact integer comparisons equivalent to
   49.975% ≤ oxygen mass percentage ≤ 49.985%. -/
def oxygenDisplayCompatibleAfterDehydration (waters : Nat) : Prop :=
  let f := dehydrationFormula waters
  let oxygenMass := 15999 * f.oxygen
  let totalMass := 12010 * f.carbon + 1008 * f.hydrogen + oxygenMass
  49975 * totalMass ≤ 100 * 1000 * oxygenMass ∧
    100 * 1000 * oxygenMass ≤ 49985 * totalMass

/-- At most three waters can be lost from six acid hydrogens.  Within that
chemically imposed range, the displayed oxygen percentage uniquely selects
the trianhydride. -/
theorem oxygen_percentage_selects_three_waters (waters : Nat)
    (hBound : waters ≤ 3)
    (h : oxygenDisplayCompatibleAfterDehydration waters) : waters = 3 := by
  simp only [oxygenDisplayCompatibleAfterDehydration, dehydrationFormula] at h
  omega

theorem structure_g_from_problem (k waters : Nat)
    (hE : hydrogenDisplayCompatible k)
    (hBound : waters ≤ 3)
    (hG : oxygenDisplayCompatibleAfterDehydration waters) :
    waters = 3 ∧
      tripleAdjacentDehydration
        (oxidiseSixBenzylicGroups (symmetricPeralkylbenzene k)) = structureG := by
  refine ⟨oxygen_percentage_selects_three_waters waters hBound hG, ?_⟩
  rw [structure_f_from_problem k hE]
  rfl

/-! ## Structural and observational verification -/

def permutationImage (p : List Nat) (i : Nat) : Nat := p.getD i i

def identityPermutation (n : Nat) : List Nat := List.range n

def composePermutation (p q : List Nat) : List Nat :=
  (List.range p.length).map fun i => permutationImage p (permutationImage q i)

def permutationPower (p : List Nat) : Nat → List Nat
  | 0 => identityPermutation p.length
  | n + 1 => composePermutation p (permutationPower p n)

/-- Fully check that a vertex permutation preserves atoms and every explicit
bond, including order and stereochemical annotation.  `Nodup`, equal length,
and the range check make `p` a bijection; hence the injection of the finite
bond set into itself also reflects non-bonds. -/
def graphAutomorphism (m : Molecule) (p : List Nat) : Bool :=
  let n := m.atoms.length
  p.length == n && decide p.Nodup && p.all (fun i => i < n) &&
    (List.range n).all (fun i =>
      m.atoms[i]? == m.atoms[permutationImage p i]?) &&
    m.bonds.all (fun b =>
      bondOrderAt m (permutationImage p b.a) (permutationImage p b.b) ==
        some (b.order, b.stereo))

def hasRotationOfExactOrder (m : Molecule) (p : List Nat) (order : Nat) : Bool :=
  graphAutomorphism m p &&
    permutationPower p order == identityPermutation p.length &&
    ((List.range order).drop 1).all (fun exponent =>
      permutationPower p exponent != identityPermutation p.length)

def rotationE60 : List Nat :=
  [1, 2, 3, 4, 5, 0,
   7, 8, 9, 10, 11, 6,
   15, 16, 17, 18, 19, 20, 21, 22, 23,
   24, 25, 26, 27, 28, 29, 12, 13, 14]

def rotationF60 : List Nat :=
  [1, 2, 3, 4, 5, 0,
   7, 8, 9, 10, 11, 6,
   13, 14, 15, 16, 17, 12,
   19, 20, 21, 22, 23, 18,
   25, 26, 27, 28, 29, 24]

def rotationG120 : List Nat :=
  [2, 3, 4, 5, 0, 1,
   8, 9, 10, 11, 6, 7,
   14, 15, 16, 17, 12, 13,
   19, 20, 18]

/-- Every aromatic site of E bears one methyl carbon and that carbon bears
exactly the three explicit hydrogens assigned to the site. -/
def hasHexamethylbenzeneConnectivity (m : Molecule) : Bool :=
  (List.range 6).all fun site =>
    bondOrderAt m site (6 + site) == some (BondOrder.single, BondStereo.none) &&
      (List.range 3).all (fun q =>
        bondOrderAt m (6 + site) (12 + 3 * site + q) ==
          some (BondOrder.single, BondStereo.none))

/-- Six `ring-C(=O)-O-H` groups, including every bond order. -/
def hasMelliticAcidConnectivity (m : Molecule) : Bool :=
  (List.range 6).all fun site =>
    bondOrderAt m site (6 + site) == some (BondOrder.single, BondStereo.none) &&
    bondOrderAt m (6 + site) (12 + site) ==
      some (BondOrder.double, BondStereo.none) &&
    bondOrderAt m (6 + site) (18 + site) ==
      some (BondOrder.single, BondStereo.none) &&
    bondOrderAt m (18 + site) (24 + site) ==
      some (BondOrder.single, BondStereo.none)

/-- Six carbonyl substituents and the three cyclic-anhydride oxygen bridges
at neighbouring site pairs (0,1), (2,3), and (4,5). -/
def hasMelliticTrianhydrideConnectivity (m : Molecule) : Bool :=
  ((List.range 6).all fun site =>
    bondOrderAt m site (6 + site) == some (BondOrder.single, BondStereo.none) &&
    bondOrderAt m (6 + site) (12 + site) ==
      some (BondOrder.double, BondStereo.none)) &&
  ((List.range 3).all fun pair =>
    bondOrderAt m (6 + 2 * pair) (18 + pair) ==
      some (BondOrder.single, BondStereo.none) &&
    bondOrderAt m (7 + 2 * pair) (18 + pair) ==
      some (BondOrder.single, BondStereo.none))

theorem structure_e_formula :
    molecularFormula structureE = { carbon := 12, hydrogen := 18, oxygen := 0 } := by
  decide

theorem structure_f_formula :
    molecularFormula structureF = { carbon := 12, hydrogen := 6, oxygen := 12 } := by
  decide

theorem structure_g_formula :
    molecularFormula structureG = { carbon := 12, hydrogen := 0, oxygen := 9 } := by
  decide

theorem structure_e_matches_11_18_percent : hydrogenDisplayCompatible 1 := by
  norm_num [hydrogenDisplayCompatible, precursorCarbonCount,
    precursorHydrogenCount]

theorem structure_e_connectivity :
    hasHexamethylbenzeneConnectivity structureE = true := by
  decide

theorem structure_f_connectivity :
    hasMelliticAcidConnectivity structureF = true := by
  decide

theorem structure_g_connectivity :
    hasMelliticTrianhydrideConnectivity structureG = true := by
  decide

theorem structure_e_valid : validClosedShellMolecule structureE = true := by
  decide

theorem structure_f_valid : validClosedShellMolecule structureF = true := by
  decide

theorem structure_g_valid : validClosedShellMolecule structureG = true := by
  decide

theorem structure_e_has_sixfold_axis :
    hasRotationOfExactOrder structureE rotationE60 6 = true := by
  decide

theorem structure_f_has_sixfold_axis :
    hasRotationOfExactOrder structureF rotationF60 6 = true := by
  decide

theorem structure_g_has_threefold_axis :
    hasRotationOfExactOrder structureG rotationG120 3 = true := by
  decide

theorem structure_g_matches_49_98_percent_oxygen :
    oxygenDisplayCompatibleAfterDehydration 3 := by
  norm_num [oxygenDisplayCompatibleAfterDehydration, dehydrationFormula]

/-- Formula balance for `F → G + 3 H₂O`, proved from the explicit graphs. -/
theorem triple_dehydration_formula_balance :
    (molecularFormula structureF).carbon = (molecularFormula structureG).carbon ∧
    (molecularFormula structureF).hydrogen =
      (molecularFormula structureG).hydrogen + 2 * 3 ∧
    (molecularFormula structureF).oxygen =
      (molecularFormula structureG).oxygen + 3 := by
  decide

/-- The three requested outputs, derived in sequence from the unrounded mass
constraint and the two graph-level reaction transformations. -/
theorem identified_structures (k waters : Nat)
    (hE : hydrogenDisplayCompatible k)
    (hBound : waters ≤ 3)
    (hG : oxygenDisplayCompatibleAfterDehydration waters) :
    symmetricPeralkylbenzene k = structureE ∧
    oxidiseSixBenzylicGroups (symmetricPeralkylbenzene k) = structureF ∧
    waters = 3 ∧
    tripleAdjacentDehydration
      (oxidiseSixBenzylicGroups (symmetricPeralkylbenzene k)) = structureG := by
  have hg := structure_g_from_problem k waters hE hBound hG
  exact ⟨structure_e_from_problem k hE,
    structure_f_from_problem k hE, hg.1, hg.2⟩

#print axioms hydrogen_percentage_selects_methyl
#print axioms oxygen_percentage_selects_three_waters
#print axioms structure_e_from_problem
#print axioms structure_f_from_problem
#print axioms structure_g_from_problem
#print axioms structure_e_connectivity
#print axioms structure_f_connectivity
#print axioms structure_g_connectivity
#print axioms structure_e_has_sixfold_axis
#print axioms structure_f_has_sixfold_axis
#print axioms structure_g_has_threefold_axis
#print axioms structure_g_matches_49_98_percent_oxygen
#print axioms triple_dehydration_formula_balance
#print axioms identified_structures

end IChO2026Problems.T1A5
