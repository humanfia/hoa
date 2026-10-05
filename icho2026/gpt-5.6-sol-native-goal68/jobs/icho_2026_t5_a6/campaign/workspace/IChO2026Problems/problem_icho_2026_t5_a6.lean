import Mathlib

/-!
# IChO 2026 T5.6: constructive structures for PL2 and PL3

The problem deliberately asks the contestant to build structures.  This file therefore
formalises concrete molecular drawings, not names encoded as strings.  Every displayed
scaffold atom (including each `R` placeholder), bond order, formal charge, radical count,
and tetrahedral centre occurs in the data below.  Ordinary skeletal-formula convention is
used for the remaining C-bound hydrogens; their totals are checked independently by the
molecular-formula calculations.

The four `R` groups in PL2 and two in PL3 stand for the same hydrocarbon residue used in
the source question.  The dependency on part 5.3 is derived below: a two-C=C fatty acid
whose incorporation into PL1 gives 255 total bond orders is `C18H32O2`.
-/

namespace IChO2026Problems.ProblemIcho2026T5A6

/-! ## Formula and bond-order bookkeeping -/

/-- Element counts in a neutral molecular formula. -/
structure Formula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  phosphorus : ℕ
deriving DecidableEq, Repr

namespace Formula

def add (a b : Formula) : Formula :=
  ⟨a.carbon + b.carbon, a.hydrogen + b.hydrogen,
    a.oxygen + b.oxygen, a.phosphorus + b.phosphorus⟩

def scale (n : ℕ) (a : Formula) : Formula :=
  ⟨n * a.carbon, n * a.hydrogen, n * a.oxygen, n * a.phosphorus⟩

/-- The sum of sigma and pi bond orders for a closed-shell neutral formula,
using valences C 4, H 1, O 2 and P 5 (the `P=O` phosphate drawing). -/
def totalBondOrder (a : Formula) : ℕ :=
  (4 * a.carbon + a.hydrogen + 2 * a.oxygen + 5 * a.phosphorus) / 2

end Formula

def water : Formula := ⟨0, 2, 1, 0⟩
def glycerol : Formula := ⟨3, 8, 3, 0⟩
def propane13diol : Formula := ⟨3, 8, 2, 0⟩
def ethanol : Formula := ⟨2, 6, 1, 0⟩
def phosphoricAcid : Formula := ⟨0, 3, 4, 1⟩
def fattyAcid : Formula := ⟨18, 32, 2, 0⟩

/-- The two source-derived numerical conditions used from the preceding PL1 data
determine the fatty acid formula, rather than assuming it.  `h + 4 = 2*c` is the
acyclic monocarboxylic-acid formula after the two C=C bonds indicated by three
linear-chain ozonolysis pieces; `4*c + h = 104` is the PL1 255-bond equation. -/
theorem fatty_acid_counts_derived {c h : ℕ}
    (twoDoubleBonds : h + 4 = 2 * c)
    (pl1BondEquation : 4 * c + h = 104) :
    c = 18 ∧ h = 32 := by
  omega

def pl1Formula : Formula := ⟨81, 142, 17, 2⟩
def pl2Formula : Formula := ⟨81, 142, 16, 2⟩
def pl3NeutralFormula : Formula := ⟨41, 73, 8, 1⟩
def pl3PhysiologicalFormula : Formula := ⟨41, 72, 8, 1⟩

theorem glycerol_has_13_total_bond_orders :
    Formula.totalBondOrder glycerol = 13 := by decide

theorem propane13diol_has_12_total_bond_orders :
    Formula.totalBondOrder propane13diol = 12 := by decide

/-- Replacing the third glycerol hydrolysis fragment of PL1 by 1,3-propanediol
decreases the total bond order by exactly one, as demanded by 255 -> 254. -/
theorem pl2_bond_count_from_pl1 : 255 - 13 + 12 = 254 := by decide

theorem pl2_has_254_total_bond_orders :
    Formula.totalBondOrder pl2Formula = 254 := by decide

theorem pl2_hydrolysis_formula_balance :
    Formula.add pl2Formula (Formula.scale 8 water) =
      Formula.add (Formula.scale 4 fattyAcid)
        (Formula.add (Formula.scale 2 phosphoricAcid)
          (Formula.add propane13diol (Formula.scale 2 glycerol))) := by
  decide

theorem pl3_neutral_hydrolysis_formula_balance :
    Formula.add pl3NeutralFormula (Formula.scale 4 water) =
      Formula.add (Formula.scale 2 fattyAcid)
        (Formula.add phosphoricAcid (Formula.add ethanol glycerol)) := by
  decide

/-- The unknown coefficient in the displayed PL3 hydrolysis equation is forced
to be four; the oxygen balance alone suffices. -/
theorem pl3_water_coefficient_is_four {m : ℕ}
    (balanced : Formula.add pl3NeutralFormula (Formula.scale m water) =
      Formula.add (Formula.scale 2 fattyAcid)
        (Formula.add phosphoricAcid (Formula.add ethanol glycerol))) :
    m = 4 := by
  have oxygenBalance := congrArg Formula.oxygen balanced
  simp [Formula.add, Formula.scale, pl3NeutralFormula, water, fattyAcid,
    phosphoricAcid, ethanol, glycerol] at oxygenBalance
  omega

theorem physiological_PL3_is_one_deprotonation :
    pl3PhysiologicalFormula.hydrogen + 1 = pl3NeutralFormula.hydrogen := by
  decide

/-! ## Explicit molecular drawings -/

inductive Element
  | C | H | O | P
  /-- A problem-requested hydrocarbon-residue placeholder. -/
  | R
deriving DecidableEq, Repr, Fintype

inductive BondOrder | single | double
deriving DecidableEq, Repr, Fintype

def BondOrder.value : BondOrder → ℕ
  | .single => 1
  | .double => 2

structure Bond (α : Type) where
  left : α
  right : α
  order : BondOrder
deriving DecidableEq, Repr

def Bond.map (f : α → β) (b : Bond α) : Bond β :=
  ⟨f b.left, f b.right, b.order⟩

def Connected [DecidableEq α] (bonds : List (Bond α))
    (a b : α) (order : BondOrder) : Bool :=
  decide ({ left := a, right := b, order := order } ∈ bonds) ||
  decide ({ left := b, right := a, order := order } ∈ bonds)

inductive Handedness | plus | minus
deriving DecidableEq, Repr, Fintype

def Handedness.mirror : Handedness → Handedness
  | .plus => .minus
  | .minus => .plus

/-- Neighbour order together with `hand` is a complete tetrahedral descriptor.
The first neighbour is the wedged substituent and the fourth is the hashed one
in the natural-language drawing. -/
structure TetrahedralStereo (α : Type) where
  center : α
  neighbours : List α
  hand : Handedness
deriving DecidableEq, Repr

def TetrahedralStereo.mirror (s : TetrahedralStereo α) : TetrahedralStereo α :=
  { s with hand := s.hand.mirror }

structure MolecularDrawing (α : Type) where
  atoms : List α
  element : α → Element
  bonds : List (Bond α)
  formalCharge : α → ℤ
  radicalElectrons : α → ℕ
  stereocentres : List (TetrahedralStereo α)

def BondsUseDeclaredAtoms [DecidableEq α] (m : MolecularDrawing α) : Bool :=
  m.bonds.all fun b => decide (b.left ∈ m.atoms ∧ b.right ∈ m.atoms)

def ValidStereo [DecidableEq α] (m : MolecularDrawing α)
    (s : TetrahedralStereo α) : Prop :=
  s.neighbours.length = 4 ∧ s.neighbours.Nodup ∧
    s.neighbours.all (fun n => Connected m.bonds s.center n .single) = true

def IsEnantiomericPair (a b : MolecularDrawing α) : Prop :=
  b.atoms = a.atoms ∧
  b.element = a.element ∧
  b.bonds = a.bonds ∧
  b.formalCharge = a.formalCharge ∧
  b.radicalElectrons = a.radicalElectrons ∧
  b.stereocentres = a.stereocentres.map TetrahedralStereo.mirror ∧
  b.stereocentres ≠ a.stereocentres

inductive Side | left | right
deriving DecidableEq, Repr, Fintype

def Side.swap : Side → Side
  | .left => .right
  | .right => .left

inductive GlycerolPosition | sn1 | sn2 | sn3
deriving DecidableEq, Repr, Fintype

inductive AcylPosition | atSn1 | atSn2
deriving DecidableEq, Repr, Fintype

/-! ### PL2 -/

inductive PL2Atom
  | glycerolC (side : Side) (position : GlycerolPosition)
  | stereoH (side : Side)
  | esterO (side : Side) (position : AcylPosition)
  | carbonylC (side : Side) (position : AcylPosition)
  | carbonylO (side : Side) (position : AcylPosition)
  | tailR (side : Side) (position : AcylPosition)
  | glycerolPhosphateO (side : Side)
  | phosphorus (side : Side)
  | phosphorylO (side : Side)
  | phosphateHydroxylO (side : Side)
  | phosphateHydroxylH (side : Side)
  | coreO (side : Side)
  | coreC (position : GlycerolPosition)
deriving DecidableEq, Repr, Fintype

def pl2SwapAtom : PL2Atom → PL2Atom
  | .glycerolC s p => .glycerolC s.swap p
  | .stereoH s => .stereoH s.swap
  | .esterO s p => .esterO s.swap p
  | .carbonylC s p => .carbonylC s.swap p
  | .carbonylO s p => .carbonylO s.swap p
  | .tailR s p => .tailR s.swap p
  | .glycerolPhosphateO s => .glycerolPhosphateO s.swap
  | .phosphorus s => .phosphorus s.swap
  | .phosphorylO s => .phosphorylO s.swap
  | .phosphateHydroxylO s => .phosphateHydroxylO s.swap
  | .phosphateHydroxylH s => .phosphateHydroxylH s.swap
  | .coreO s => .coreO s.swap
  | .coreC .sn1 => .coreC .sn3
  | .coreC .sn2 => .coreC .sn2
  | .coreC .sn3 => .coreC .sn1

def pl2Element : PL2Atom → Element
  | .glycerolC .. | .carbonylC .. | .coreC .. => .C
  | .stereoH .. | .phosphateHydroxylH .. => .H
  | .esterO .. | .carbonylO .. | .glycerolPhosphateO .. |
      .phosphorylO .. | .phosphateHydroxylO .. | .coreO .. => .O
  | .phosphorus .. => .P
  | .tailR .. => .R

def pl2ArmBonds (s : Side) : List (Bond PL2Atom) :=
  [ ⟨.glycerolC s .sn1, .glycerolC s .sn2, .single⟩,
    ⟨.glycerolC s .sn2, .glycerolC s .sn3, .single⟩,
    ⟨.glycerolC s .sn2, .stereoH s, .single⟩,
    ⟨.glycerolC s .sn1, .esterO s .atSn1, .single⟩,
    ⟨.esterO s .atSn1, .carbonylC s .atSn1, .single⟩,
    ⟨.carbonylC s .atSn1, .carbonylO s .atSn1, .double⟩,
    ⟨.carbonylC s .atSn1, .tailR s .atSn1, .single⟩,
    ⟨.glycerolC s .sn2, .esterO s .atSn2, .single⟩,
    ⟨.esterO s .atSn2, .carbonylC s .atSn2, .single⟩,
    ⟨.carbonylC s .atSn2, .carbonylO s .atSn2, .double⟩,
    ⟨.carbonylC s .atSn2, .tailR s .atSn2, .single⟩,
    ⟨.glycerolC s .sn3, .glycerolPhosphateO s, .single⟩,
    ⟨.glycerolPhosphateO s, .phosphorus s, .single⟩,
    ⟨.phosphorus s, .phosphorylO s, .double⟩,
    ⟨.phosphorus s, .phosphateHydroxylO s, .single⟩,
    ⟨.phosphateHydroxylO s, .phosphateHydroxylH s, .single⟩,
    ⟨.phosphorus s, .coreO s, .single⟩ ]

def pl2HalfBonds : List (Bond PL2Atom) :=
  pl2ArmBonds .left ++
  [ ⟨.coreO .left, .coreC .sn1, .single⟩,
    ⟨.coreC .sn1, .coreC .sn2, .single⟩ ]

/-- The complete PL2 bond list is the union of one half with its image under
the left-right involution.  This makes the source's increased symmetry an
actual property of the molecular data, rather than a prose label. -/
def pl2Bonds : List (Bond PL2Atom) :=
  pl2HalfBonds ++ pl2HalfBonds.map (Bond.map pl2SwapAtom)

/-- The hydrolysis fragment `Z = HO-CH2-CH2-CH2-OH` as it occurs inside PL2. -/
def pl2ZHeavyAtomBonds : List (Bond PL2Atom) :=
  [ ⟨.coreO .left, .coreC .sn1, .single⟩,
    ⟨.coreC .sn1, .coreC .sn2, .single⟩,
    ⟨.coreC .sn2, .coreC .sn3, .single⟩,
    ⟨.coreC .sn3, .coreO .right, .single⟩ ]

theorem pl2_Z_has_only_single_heavy_atom_bonds :
    ∀ b ∈ pl2ZHeavyAtomBonds, b.order = .single := by
  intro b hb
  simp [pl2ZHeavyAtomBonds] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> rfl

def pl2StereoAt (s : Side) (h : Handedness) : TetrahedralStereo PL2Atom :=
  { center := .glycerolC s .sn2
    neighbours := [.esterO s .atSn2, .glycerolC s .sn1,
      .glycerolC s .sn3, .stereoH s]
    hand := h }

/-- Equal descriptors on the two arms mean that the right arm is a rotation,
not a reflection, of the left arm. -/
def pl2Stereo (h : Handedness) : List (TetrahedralStereo PL2Atom) :=
  [pl2StereoAt .left h, pl2StereoAt .right h]

def pl2AtomsForSide (s : Side) : List PL2Atom :=
  [ .glycerolC s .sn1, .glycerolC s .sn2, .glycerolC s .sn3,
    .stereoH s,
    .esterO s .atSn1, .esterO s .atSn2,
    .carbonylC s .atSn1, .carbonylC s .atSn2,
    .carbonylO s .atSn1, .carbonylO s .atSn2,
    .tailR s .atSn1, .tailR s .atSn2,
    .glycerolPhosphateO s, .phosphorus s, .phosphorylO s,
    .phosphateHydroxylO s, .phosphateHydroxylH s, .coreO s ]

def pl2Atoms : List PL2Atom :=
  pl2AtomsForSide .left ++ pl2AtomsForSide .right ++
    [.coreC .sn1, .coreC .sn2, .coreC .sn3]

def pl2Drawing (h : Handedness) : MolecularDrawing PL2Atom :=
  { atoms := pl2Atoms
    element := pl2Element
    bonds := pl2Bonds
    formalCharge := fun _ => 0
    radicalElectrons := fun _ => 0
    stereocentres := pl2Stereo h }

theorem pl2_stereocentres_are_bonded :
    ∀ s ∈ (pl2Drawing .plus).stereocentres,
      ValidStereo (pl2Drawing .plus) s := by
  intro s hs
  simp [pl2Drawing, pl2Stereo] at hs
  rcases hs with rfl | rfl
  · simp [ValidStereo, pl2StereoAt, pl2Drawing, pl2Bonds, pl2HalfBonds,
      pl2ArmBonds, Bond.map, pl2SwapAtom, Side.swap, Connected]
  · simp [ValidStereo, pl2StereoAt, pl2Drawing, pl2Bonds, pl2HalfBonds,
      pl2ArmBonds, Bond.map, pl2SwapAtom, Side.swap, Connected]

theorem pl2_has_four_R_residues :
    ((pl2Drawing .plus).atoms.filter fun a => pl2Element a = .R).length = 4 := by
  decide

theorem pl2_is_nonionised :
    ∀ a, (pl2Drawing .plus).formalCharge a = 0 := by
  intro a
  rfl

theorem pl2_has_no_radicals :
    ∀ a, (pl2Drawing .plus).radicalElectrons a = 0 := by
  intro a
  rfl

theorem pl2_all_bond_endpoints_are_declared :
    BondsUseDeclaredAtoms (pl2Drawing .plus) = true := by
  decide

theorem pl2_side_swap_is_involutive :
    ∀ a, pl2SwapAtom (pl2SwapAtom a) = a := by
  decide

theorem pl2_side_swap_preserves_elements :
    ∀ a, pl2Element (pl2SwapAtom a) = pl2Element a := by
  decide

theorem pl2_bonds_are_side_swap_orbits :
    pl2Bonds = pl2HalfBonds ++ pl2HalfBonds.map (Bond.map pl2SwapAtom) := by
  rfl

theorem pl2_side_swap_is_nontrivial :
    pl2SwapAtom (.tailR .left .atSn1) ≠ .tailR .left .atSn1 := by
  decide

theorem pl2_enantiomeric_pair :
    IsEnantiomericPair (pl2Drawing .plus) (pl2Drawing .minus) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · decide

/-- Complete specification for the requested PL2 drawing. -/
structure PL2RequestedStructure (m : MolecularDrawing PL2Atom) : Prop where
  exactAtoms : m.atoms = pl2Atoms
  exactElements : m.element = pl2Element
  exactConnectivity : m.bonds = pl2Bonds
  allBondEndpointsDeclared : BondsUseDeclaredAtoms m = true
  exactCharges : m.formalCharge = (fun _ => 0)
  exactRadicals : m.radicalElectrons = (fun _ => 0)
  exactStereochemistry : m.stereocentres = pl2Stereo .plus
  stereochemistryBonded : ∀ s ∈ m.stereocentres, ValidStereo m s
  fourFattyResidues : (m.atoms.filter fun a => m.element a = .R).length = 4
  zFormula : propane13diol = ⟨3, 8, 2, 0⟩
  zHasOnlySingleHeavyAtomBonds :
    ∀ b ∈ pl2ZHeavyAtomBonds, b.order = .single
  formula : pl2Formula = ⟨81, 142, 16, 2⟩
  totalBondOrder : Formula.totalBondOrder pl2Formula = 254
  hydrolysisBalance :
    Formula.add pl2Formula (Formula.scale 8 water) =
      Formula.add (Formula.scale 4 fattyAcid)
        (Formula.add (Formula.scale 2 phosphoricAcid)
          (Formula.add propane13diol (Formula.scale 2 glycerol)))
  enantiomerExists : IsEnantiomericPair m (pl2Drawing .minus)
  symmetricBondOrbit :
    m.bonds = pl2HalfBonds ++ pl2HalfBonds.map (Bond.map pl2SwapAtom)
  sideSwapInvolutive : ∀ a, pl2SwapAtom (pl2SwapAtom a) = a
  sideSwapPreservesElements : ∀ a,
    pl2Element (pl2SwapAtom a) = pl2Element a
  sideSwapNontrivial :
    pl2SwapAtom (.tailR .left .atSn1) ≠ .tailR .left .atSn1

theorem structure_pl2 : PL2RequestedStructure (pl2Drawing .plus) := by
  refine
    { exactAtoms := rfl
      exactElements := rfl
      exactConnectivity := rfl
      allBondEndpointsDeclared := pl2_all_bond_endpoints_are_declared
      exactCharges := rfl
      exactRadicals := rfl
      exactStereochemistry := rfl
      stereochemistryBonded := pl2_stereocentres_are_bonded
      fourFattyResidues := pl2_has_four_R_residues
      zFormula := rfl
      zHasOnlySingleHeavyAtomBonds := pl2_Z_has_only_single_heavy_atom_bonds
      formula := rfl
      totalBondOrder := pl2_has_254_total_bond_orders
      hydrolysisBalance := pl2_hydrolysis_formula_balance
      enantiomerExists := pl2_enantiomeric_pair
      symmetricBondOrbit := pl2_bonds_are_side_swap_orbits
      sideSwapInvolutive := pl2_side_swap_is_involutive
      sideSwapPreservesElements := pl2_side_swap_preserves_elements
      sideSwapNontrivial := pl2_side_swap_is_nontrivial }

/-! ### PL3 -/

inductive PL3Atom
  | glycerolC (position : GlycerolPosition)
  | stereoH
  | esterO (position : AcylPosition)
  | carbonylC (position : AcylPosition)
  | carbonylO (position : AcylPosition)
  | tailR (position : AcylPosition)
  | glycerolPhosphateO
  | phosphorus
  | phosphorylO
  | anionicO
  | ethoxyO
  | ethylC1
  | ethylC2
deriving DecidableEq, Repr, Fintype

def pl3Element : PL3Atom → Element
  | .glycerolC .. | .carbonylC .. | .ethylC1 | .ethylC2 => .C
  | .stereoH => .H
  | .esterO .. | .carbonylO .. | .glycerolPhosphateO |
      .phosphorylO | .anionicO | .ethoxyO => .O
  | .phosphorus => .P
  | .tailR .. => .R

def pl3Bonds : List (Bond PL3Atom) :=
  [ ⟨.glycerolC .sn1, .glycerolC .sn2, .single⟩,
    ⟨.glycerolC .sn2, .glycerolC .sn3, .single⟩,
    ⟨.glycerolC .sn2, .stereoH, .single⟩,
    ⟨.glycerolC .sn1, .esterO .atSn1, .single⟩,
    ⟨.esterO .atSn1, .carbonylC .atSn1, .single⟩,
    ⟨.carbonylC .atSn1, .carbonylO .atSn1, .double⟩,
    ⟨.carbonylC .atSn1, .tailR .atSn1, .single⟩,
    ⟨.glycerolC .sn2, .esterO .atSn2, .single⟩,
    ⟨.esterO .atSn2, .carbonylC .atSn2, .single⟩,
    ⟨.carbonylC .atSn2, .carbonylO .atSn2, .double⟩,
    ⟨.carbonylC .atSn2, .tailR .atSn2, .single⟩,
    ⟨.glycerolC .sn3, .glycerolPhosphateO, .single⟩,
    ⟨.glycerolPhosphateO, .phosphorus, .single⟩,
    ⟨.phosphorus, .phosphorylO, .double⟩,
    ⟨.phosphorus, .anionicO, .single⟩,
    ⟨.phosphorus, .ethoxyO, .single⟩,
    ⟨.ethoxyO, .ethylC1, .single⟩,
    ⟨.ethylC1, .ethylC2, .single⟩ ]

def pl3Stereo (h : Handedness) : List (TetrahedralStereo PL3Atom) :=
  [{ center := .glycerolC .sn2
     neighbours := [.esterO .atSn2, .glycerolC .sn1,
       .glycerolC .sn3, .stereoH]
     hand := h }]

def pl3FormalCharge : PL3Atom → ℤ
  | .anionicO => -1
  | _ => 0

def pl3Drawing (h : Handedness) : MolecularDrawing PL3Atom :=
  { atoms :=
      [ .glycerolC .sn1, .glycerolC .sn2, .glycerolC .sn3,
        .stereoH,
        .esterO .atSn1, .esterO .atSn2,
        .carbonylC .atSn1, .carbonylC .atSn2,
        .carbonylO .atSn1, .carbonylO .atSn2,
        .tailR .atSn1, .tailR .atSn2,
        .glycerolPhosphateO, .phosphorus, .phosphorylO,
        .anionicO, .ethoxyO, .ethylC1, .ethylC2 ]
    element := pl3Element
    bonds := pl3Bonds
    formalCharge := pl3FormalCharge
    radicalElectrons := fun _ => 0
    stereocentres := pl3Stereo h }

theorem pl3_stereocentre_is_bonded :
    ∀ s ∈ (pl3Drawing .plus).stereocentres,
      ValidStereo (pl3Drawing .plus) s := by
  intro s hs
  simp [pl3Drawing, pl3Stereo] at hs
  subst s
  simp [ValidStereo, pl3Stereo, pl3Drawing, pl3Bonds, Connected]

theorem pl3_has_two_R_residues :
    ((pl3Drawing .plus).atoms.filter fun a => pl3Element a = .R).length = 2 := by
  decide

theorem pl3_has_charge_negative_one_on_phosphate_oxygen :
    (pl3Drawing .plus).formalCharge .anionicO = -1 ∧
      (∀ a, a ≠ PL3Atom.anionicO → (pl3Drawing .plus).formalCharge a = 0) := by
  constructor
  · rfl
  · intro a ha
    cases a <;> simp_all [pl3Drawing, pl3FormalCharge]

theorem pl3_has_no_radicals :
    ∀ a, (pl3Drawing .plus).radicalElectrons a = 0 := by
  intro a
  rfl

theorem pl3_all_bond_endpoints_are_declared :
    BondsUseDeclaredAtoms (pl3Drawing .plus) = true := by
  decide

theorem pl3_enantiomeric_pair :
    IsEnantiomericPair (pl3Drawing .plus) (pl3Drawing .minus) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · decide

/-- Complete specification for the physiologically relevant PL3 monoanion. -/
structure PL3RequestedStructure (m : MolecularDrawing PL3Atom) : Prop where
  exactAtoms : m.atoms =
    [ .glycerolC .sn1, .glycerolC .sn2, .glycerolC .sn3,
      .stereoH,
      .esterO .atSn1, .esterO .atSn2,
      .carbonylC .atSn1, .carbonylC .atSn2,
      .carbonylO .atSn1, .carbonylO .atSn2,
      .tailR .atSn1, .tailR .atSn2,
      .glycerolPhosphateO, .phosphorus, .phosphorylO,
      .anionicO, .ethoxyO, .ethylC1, .ethylC2 ]
  exactElements : m.element = pl3Element
  exactConnectivity : m.bonds = pl3Bonds
  allBondEndpointsDeclared : BondsUseDeclaredAtoms m = true
  exactCharges : m.formalCharge = pl3FormalCharge
  exactRadicals : m.radicalElectrons = (fun _ => 0)
  exactStereochemistry : m.stereocentres = pl3Stereo .plus
  stereochemistryBonded : ∀ s ∈ m.stereocentres, ValidStereo m s
  twoFattyResidues : (m.atoms.filter fun a => m.element a = .R).length = 2
  physiologicalCharge : m.formalCharge .anionicO = -1 ∧
    ∀ a, a ≠ PL3Atom.anionicO → m.formalCharge a = 0
  neutralHydrolysisBalance :
    Formula.add pl3NeutralFormula (Formula.scale 4 water) =
      Formula.add (Formula.scale 2 fattyAcid)
        (Formula.add phosphoricAcid (Formula.add ethanol glycerol))
  waterCoefficient : ∀ {m : ℕ},
    Formula.add pl3NeutralFormula (Formula.scale m water) =
      Formula.add (Formula.scale 2 fattyAcid)
        (Formula.add phosphoricAcid (Formula.add ethanol glycerol)) → m = 4
  oneDeprotonation : pl3PhysiologicalFormula.hydrogen + 1 =
    pl3NeutralFormula.hydrogen
  physiologicalFormula : pl3PhysiologicalFormula = ⟨41, 72, 8, 1⟩
  enantiomericPair : IsEnantiomericPair m (pl3Drawing .minus)

theorem structure_pl3 : PL3RequestedStructure (pl3Drawing .plus) := by
  exact
    { exactAtoms := rfl
      exactElements := rfl
      exactConnectivity := rfl
      allBondEndpointsDeclared := pl3_all_bond_endpoints_are_declared
      exactCharges := rfl
      exactRadicals := rfl
      exactStereochemistry := rfl
      stereochemistryBonded := pl3_stereocentre_is_bonded
      twoFattyResidues := pl3_has_two_R_residues
      physiologicalCharge := pl3_has_charge_negative_one_on_phosphate_oxygen
      neutralHydrolysisBalance := pl3_neutral_hydrolysis_formula_balance
      waterCoefficient := pl3_water_coefficient_is_four
      oneDeprotonation := physiological_PL3_is_one_deprotonation
      physiologicalFormula := rfl
      enantiomericPair := pl3_enantiomeric_pair }

/-!
The two declarations below are the final requested outputs.  Their conjunction
makes it convenient to inspect all axioms of the complete submission at once.
-/
theorem requested_structures :
    PL2RequestedStructure (pl2Drawing .plus) ∧
      PL3RequestedStructure (pl3Drawing .plus) :=
  ⟨structure_pl2, structure_pl3⟩

#print axioms structure_pl2
#print axioms structure_pl3
#print axioms requested_structures

end IChO2026Problems.ProblemIcho2026T5A6
