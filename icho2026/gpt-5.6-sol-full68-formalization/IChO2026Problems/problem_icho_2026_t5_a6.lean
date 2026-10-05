import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T5, part A6

This file formalizes the two requested structural drawings without treating a
name or a displayed string as a molecular structure.  A molecular graph below
has typed sites, explicit bond orders, formal charges, radical counts, attached
hydrogen counts, and ordered tetrahedral ligands.  The problem-authorized `R`
abbreviation is represented by a typed residue site whose formula and internal
bond-order count are recorded separately.

The previous-part information used here is rederived inside this file.  In
particular, the bond-count and ozonolysis equations determine the formula of
`RCOOH`; no result from another generated problem file is imported.
-/

namespace IChO2026Problems.T5A6

open scoped BigOperators

/-! ## Formulae and source-stated hydrolysis reactions -/

/-- The four elements occurring in the source-bounded hydrolysis ledgers. -/
inductive Element where
  | C | H | O | P
  deriving DecidableEq, Fintype, Repr

/-- Molecular formula together with total formal charge. -/
@[ext]
structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  phosphorus : ℕ
  charge : ℤ
  deriving DecidableEq, Repr

def MolecularFormula.count (f : MolecularFormula) : Element → ℕ
  | .C => f.carbon
  | .H => f.hydrogen
  | .O => f.oxygen
  | .P => f.phosphorus

def waterFormula : MolecularFormula := ⟨0, 2, 1, 0, 0⟩
def phosphoricAcidFormula : MolecularFormula := ⟨0, 3, 4, 1, 0⟩
def glycerolFormula : MolecularFormula := ⟨3, 8, 3, 0, 0⟩
def ethanolFormula : MolecularFormula := ⟨2, 6, 1, 0, 0⟩

/-- The formula obtained below for the problem's fatty acid `RCOOH`. -/
def fattyAcidFormula : MolecularFormula := ⟨18, 32, 2, 0, 0⟩

/-- The saturated symmetric diol released from the central spacer of PL2. -/
def propane13DiolFormula : MolecularFormula := ⟨3, 8, 2, 0, 0⟩

def pl1Formula : MolecularFormula := ⟨81, 142, 17, 2, 0⟩
def pl2Formula : MolecularFormula := ⟨81, 142, 16, 2, 0⟩
def pl3NeutralFormula : MolecularFormula := ⟨41, 73, 8, 1, 0⟩
def pl3PhysiologicalFormula : MolecularFormula := ⟨41, 72, 8, 1, -1⟩

/-- This finite type is the complete species domain used in the three
hydrolysis ledgers.  There is deliberately no catch-all species. -/
inductive HydrolysisSpecies where
  | PL1
  | PL2
  | PL3Neutral
  | water
  | fattyAcid
  | phosphoricAcid
  | glycerol
  | propane13Diol
  | ethanol
  deriving DecidableEq, Fintype, Repr

def speciesFormula : HydrolysisSpecies → MolecularFormula
  | .PL1 => pl1Formula
  | .PL2 => pl2Formula
  | .PL3Neutral => pl3NeutralFormula
  | .water => waterFormula
  | .fattyAcid => fattyAcidFormula
  | .phosphoricAcid => phosphoricAcidFormula
  | .glycerol => glycerolFormula
  | .propane13Diol => propane13DiolFormula
  | .ethanol => ethanolFormula

/-- Total atoms of one element on one side of a CRNT stoichiometric complex. -/
def atomsOnSide {S : Type} [Fintype S] [DecidableEq S]
    (formula : S → MolecularFormula) (side : CRNT.Complex S)
    (element : Element) : ℕ :=
  ∑ species : S, side species * (formula species).count element

/-- Total formal charge on one side of a CRNT stoichiometric complex. -/
def chargeOnSide {S : Type} [Fintype S] [DecidableEq S]
    (formula : S → MolecularFormula) (side : CRNT.Complex S) : ℤ :=
  ∑ species : S, (side species : ℤ) * (formula species).charge

/-- The atom and charge ledgers actually used for a quantitative hydrolysis
stage. -/
def AtomChargeBalanced {S : Type} [Fintype S] [DecidableEq S]
    (formula : S → MolecularFormula) (reaction : CRNT.Reaction S) : Prop :=
  (∀ element : Element,
      atomsOnSide formula reaction.source element =
        atomsOnSide formula reaction.target element) ∧
    chargeOnSide formula reaction.source =
      chargeOnSide formula reaction.target

/-- `PL1 + 8 H₂O ⟶ 4 RCOOH + 2 H₃PO₄ + 3 glycerol`. -/
def pl1Hydrolysis : CRNT.Reaction HydrolysisSpecies where
  source
    | .PL1 => 1
    | .water => 8
    | _ => 0
  target
    | .fattyAcid => 4
    | .phosphoricAcid => 2
    | .glycerol => 3
    | _ => 0

/-- `PL2 + 8 H₂O ⟶ 4 RCOOH + 2 H₃PO₄ + Z + 2 glycerol`, with the
candidate `Z` kept as its independently checked 1,3-propanediol graph below. -/
def pl2Hydrolysis : CRNT.Reaction HydrolysisSpecies where
  source
    | .PL2 => 1
    | .water => 8
    | _ => 0
  target
    | .fattyAcid => 4
    | .phosphoricAcid => 2
    | .propane13Diol => 1
    | .glycerol => 2
    | _ => 0

/-- The source prints an unknown coefficient `m`; this is the corresponding
finite-species reaction family. -/
def pl3Hydrolysis (m : ℕ) : CRNT.Reaction HydrolysisSpecies where
  source
    | .PL3Neutral => 1
    | .water => m
    | _ => 0
  target
    | .fattyAcid => 2
    | .phosphoricAcid => 1
    | .ethanol => 1
    | .glycerol => 1
    | _ => 0

def pl1HydrolysisLedger : Prop := AtomChargeBalanced speciesFormula pl1Hydrolysis
def pl2HydrolysisLedger : Prop := AtomChargeBalanced speciesFormula pl2Hydrolysis
def pl3HydrolysisLedger (m : ℕ) : Prop :=
  AtomChargeBalanced speciesFormula (pl3Hydrolysis m)

/-! ## Previous part A3, derived from raw source equations -/

/-- Counts left unknown until the A3 equations are solved. -/
structure FattyAcidCounts where
  carbonAtoms : ℕ
  hydrogenAtoms : ℕ
  alkeneBonds : ℕ
  ozonolysisFragments : ℕ
  deriving DecidableEq, Repr

/-- Source and governing-law split for A3.

* `ozonolysisFragments = 3` is the printed observation;
* cleavage of an acyclic chain at every alkene gives one more fragment than
  alkene bonds;
* `H + 2d = 2C` is the valence relation for an acyclic monocarboxylic acid;
* `8C + 2H + 47 = 255` is the bond ledger obtained from four acid residues,
  three glycerols, two phosphates, and eight hydrolysis waters.
-/
def A3Constraints (x : FattyAcidCounts) : Prop :=
  x.ozonolysisFragments = 3 ∧
  x.ozonolysisFragments = x.alkeneBonds + 1 ∧
  x.hydrogenAtoms + 2 * x.alkeneBonds = 2 * x.carbonAtoms ∧
  8 * x.carbonAtoms + 2 * x.hydrogenAtoms + 47 = 255

def A3Conclusion (x : FattyAcidCounts) : Prop :=
  x.carbonAtoms = 18 ∧ x.hydrogenAtoms = 32 ∧ x.alkeneBonds = 2

theorem derivePreviousPartA3 (x : FattyAcidCounts) (h : A3Constraints x) :
    A3Conclusion x := by
  simp only [A3Constraints] at h
  simp only [A3Conclusion]
  omega

def fattyAcidCounts : FattyAcidCounts := ⟨18, 32, 2, 3⟩

theorem fattyAcidCounts_meet_A3_constraints : A3Constraints fattyAcidCounts := by
  norm_num [A3Constraints, fattyAcidCounts]

/-! ## An explicit molecular-graph language -/

/-- A residue site is the exact abbreviation authorized by the question. -/
inductive SiteKind where
  | atom (element : Element)
  | fattyResidueR
  deriving DecidableEq, Repr

/-- A heavy-atom or authorized residue site.  Hydrogens are explicit by count
at their attachment site; formal charge and unpaired electrons are never
implicit. -/
structure AtomSite where
  kind : SiteKind
  attachedHydrogens : ℕ
  formalCharge : ℤ
  radicalElectrons : ℕ
  deriving DecidableEq, Repr

inductive BondOrder where
  | single | double | triple
  deriving DecidableEq, Repr

def BondOrder.weight : BondOrder → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3

def BondOrder.piCount : BondOrder → ℕ
  | .single => 0
  | .double => 1
  | .triple => 2

structure Bond (Site : Type) where
  left : Site
  right : Site
  order : BondOrder
  deriving DecidableEq

inductive Handedness where
  | clockwise | counterclockwise
  deriving DecidableEq, Repr

def Handedness.mirror : Handedness → Handedness
  | .clockwise => .counterclockwise
  | .counterclockwise => .clockwise

inductive StereoLigand (Site : Type) where
  | site (site : Site)
  | attachedHydrogen
  deriving DecidableEq

/-- Tetrahedral parity is relative to the displayed ordered ligand list. -/
structure TetrahedralStereo (Site : Type) where
  center : Site
  orderedLigands : List (StereoLigand Site)
  handedness : Handedness
  deriving DecidableEq

structure MolecularGraph (Site : Type) where
  atom : Site → AtomSite
  bonds : List (Bond Site)
  stereocentres : List (TetrahedralStereo Site)

def carbonSite (hydrogens : ℕ) : AtomSite :=
  ⟨.atom .C, hydrogens, 0, 0⟩

def oxygenSite (hydrogens : ℕ) (charge : ℤ := 0) : AtomSite :=
  ⟨.atom .O, hydrogens, charge, 0⟩

def phosphorusSite : AtomSite := ⟨.atom .P, 0, 0, 0⟩
def residueRSite : AtomSite := ⟨.fattyResidueR, 0, 0, 0⟩

def singleBond {Site : Type} (a b : Site) : Bond Site := ⟨a, b, .single⟩
def doubleBond {Site : Type} (a b : Site) : Bond Site := ⟨a, b, .double⟩

/-- One `R` group is `C₁₇H₃₁` after the carboxyl carbon and hydroxyl are
removed from `C₁₈H₃₂O₂`. -/
def residueRFormula : MolecularFormula := ⟨17, 31, 0, 0, 0⟩

/-- Internal sigma-plus-pi bond order of the connected `R` substituent. -/
def residueRInternalBondOrder : ℕ := 49

/-- The two alkene pi bonds retained inside each displayed `R` residue. -/
def residueRInternalPiBonds : ℕ := 2

theorem residueR_internal_bond_ledger :
    2 * residueRInternalBondOrder + 1 =
      4 * residueRFormula.carbon + residueRFormula.hydrogen := by
  norm_num [residueRInternalBondOrder, residueRFormula]

def atomContribution (atom : AtomSite) : MolecularFormula :=
  match atom.kind with
  | .fattyResidueR => residueRFormula
  | .atom .C => ⟨1, atom.attachedHydrogens, 0, 0, atom.formalCharge⟩
  | .atom .H => ⟨0, 1 + atom.attachedHydrogens, 0, 0, atom.formalCharge⟩
  | .atom .O => ⟨0, atom.attachedHydrogens, 1, 0, atom.formalCharge⟩
  | .atom .P => ⟨0, atom.attachedHydrogens, 0, 1, atom.formalCharge⟩

def graphFormula {Site : Type} [Fintype Site] [DecidableEq Site]
    (graph : MolecularGraph Site) : MolecularFormula where
  carbon := ∑ site : Site, (atomContribution (graph.atom site)).carbon
  hydrogen := ∑ site : Site, (atomContribution (graph.atom site)).hydrogen
  oxygen := ∑ site : Site, (atomContribution (graph.atom site)).oxygen
  phosphorus := ∑ site : Site, (atomContribution (graph.atom site)).phosphorus
  charge := ∑ site : Site, (atomContribution (graph.atom site)).charge

def embeddedBondOrder (atom : AtomSite) : ℕ :=
  match atom.kind with
  | .fattyResidueR => residueRInternalBondOrder
  | _ => 0

def totalBondOrder {Site : Type} [Fintype Site] [DecidableEq Site]
    (graph : MolecularGraph Site) : ℕ :=
  (graph.bonds.map fun bond => bond.order.weight).sum +
  (∑ site : Site, (graph.atom site).attachedHydrogens) +
  (∑ site : Site, embeddedBondOrder (graph.atom site))

def embeddedPiBonds (atom : AtomSite) : ℕ :=
  match atom.kind with
  | .fattyResidueR => residueRInternalPiBonds
  | _ => 0

def totalPiBonds {Site : Type} [Fintype Site] [DecidableEq Site]
    (graph : MolecularGraph Site) : ℕ :=
  (graph.bonds.map fun bond => bond.order.piCount).sum +
    ∑ site : Site, embeddedPiBonds (graph.atom site)

def localBondOrder {Site : Type} [DecidableEq Site]
    (graph : MolecularGraph Site) (site : Site) : ℕ :=
  (graph.bonds.map fun bond =>
    if bond.left = site ∨ bond.right = site then bond.order.weight else 0).sum

def expectedExternalValence (atom : AtomSite) : ℕ :=
  match atom.kind with
  | .fattyResidueR => 1
  | .atom .H => 1
  | .atom .C => 4
  | .atom .P => 5
  | .atom .O => if atom.formalCharge = -1 then 1 else 2

def CovalentlyBonded {Site : Type} [DecidableEq Site]
    (graph : MolecularGraph Site) (left right : Site) : Prop :=
  ∃ bond ∈ graph.bonds,
    (bond.left = left ∧ bond.right = right) ∨
      (bond.left = right ∧ bond.right = left)

def MolecularGraph.Connected {Site : Type} [DecidableEq Site]
    (graph : MolecularGraph Site) : Prop :=
  ∀ left right : Site,
    Relation.ReflTransGen (CovalentlyBonded graph) left right

/-- For the explicit scaffold graphs here, connectedness together with one
fewer covalent edges than sites is the source-relevant acyclic certificate. -/
def MolecularGraph.TreeLike {Site : Type} [Fintype Site] [DecidableEq Site]
    (graph : MolecularGraph Site) : Prop :=
  graph.Connected ∧ graph.bonds.length + 1 = Fintype.card Site

def isOxygenSite (atom : AtomSite) : Prop := atom.kind = .atom .O

def HasPeroxideBond {Site : Type} (graph : MolecularGraph Site) : Prop :=
  ∃ bond ∈ graph.bonds,
    bond.order = .single ∧
      isOxygenSite (graph.atom bond.left) ∧
      isOxygenSite (graph.atom bond.right)

def stereoLigandAttached {Site : Type} [DecidableEq Site]
    (graph : MolecularGraph Site) (center : Site) : StereoLigand Site → Prop
  | .site site => CovalentlyBonded graph center site
  | .attachedHydrogen => 0 < (graph.atom center).attachedHydrogens

def stereoWellFormed {Site : Type} [DecidableEq Site]
    (graph : MolecularGraph Site) (stereo : TetrahedralStereo Site) : Prop :=
  (graph.atom stereo.center).kind = .atom .C ∧
  stereo.orderedLigands.length = 4 ∧
  stereo.orderedLigands.Nodup ∧
  ∀ ligand ∈ stereo.orderedLigands,
    stereoLigandAttached graph stereo.center ligand

def MolecularGraph.WellFormed {Site : Type} [Fintype Site] [DecidableEq Site]
    (graph : MolecularGraph Site) : Prop :=
  graph.bonds.Nodup ∧
  (∀ bond ∈ graph.bonds, bond.left ≠ bond.right) ∧
  (∀ site : Site,
    localBondOrder graph site + (graph.atom site).attachedHydrogens =
      expectedExternalValence (graph.atom site)) ∧
  (∀ site : Site, (graph.atom site).radicalElectrons = 0) ∧
  (∀ stereo ∈ graph.stereocentres, stereoWellFormed graph stereo)

def mirrorStereo {Site : Type} (stereo : TetrahedralStereo Site) :
    TetrahedralStereo Site :=
  { stereo with handedness := stereo.handedness.mirror }

def mirrorGraph {Site : Type} (graph : MolecularGraph Site) : MolecularGraph Site :=
  { graph with stereocentres := graph.stereocentres.map mirrorStereo }

def EnantiomericPair {Site : Type} [DecidableEq Site]
    (left right : MolecularGraph Site) : Prop :=
  left.stereocentres ≠ [] ∧ right = mirrorGraph left

/-! The following elementary graph lemmas let the concrete molecular
scaffolds certify connectedness by their displayed bond lists. -/

theorem covalentlyBonded_symm {Site : Type} [DecidableEq Site]
    {graph : MolecularGraph Site} {left right : Site}
    (h : CovalentlyBonded graph left right) :
    CovalentlyBonded graph right left := by
  rcases h with ⟨bond, hbond, hends | hends⟩
  · exact ⟨bond, hbond, Or.inr hends⟩
  · exact ⟨bond, hbond, Or.inl hends⟩

theorem reflTransGen_symm_of_symm {α : Type} {relation : α → α → Prop}
    (hsymm : ∀ {left right}, relation left right → relation right left)
    {left right : α} (h : Relation.ReflTransGen relation left right) :
    Relation.ReflTransGen relation right left := by
  induction h with
  | refl => exact .refl
  | tail hpath hedge ih =>
      exact Relation.ReflTransGen.head (hsymm hedge) ih

theorem listedBond_rtc {Site : Type} [DecidableEq Site]
    (graph : MolecularGraph Site) (bond : Bond Site)
    (hbond : bond ∈ graph.bonds) :
    Relation.ReflTransGen (CovalentlyBonded graph) bond.left bond.right := by
  exact Relation.ReflTransGen.single
    ⟨bond, hbond, Or.inl ⟨rfl, rfl⟩⟩

theorem listedBond_covalentlyBonded {Site : Type} [DecidableEq Site]
    (graph : MolecularGraph Site) (bond : Bond Site)
    (hbond : bond ∈ graph.bonds) :
    CovalentlyBonded graph bond.left bond.right :=
  ⟨bond, hbond, Or.inl ⟨rfl, rfl⟩⟩

theorem listedBond_covalentlyBonded_rev {Site : Type} [DecidableEq Site]
    (graph : MolecularGraph Site) (bond : Bond Site)
    (hbond : bond ∈ graph.bonds) :
    CovalentlyBonded graph bond.right bond.left :=
  covalentlyBonded_symm (listedBond_covalentlyBonded graph bond hbond)

theorem listedBond_rtc_rev {Site : Type} [DecidableEq Site]
    (graph : MolecularGraph Site) (bond : Bond Site)
    (hbond : bond ∈ graph.bonds) :
    Relation.ReflTransGen (CovalentlyBonded graph) bond.right bond.left := by
  exact reflTransGen_symm_of_symm covalentlyBonded_symm
    (listedBond_rtc graph bond hbond)

theorem connected_of_root {Site : Type} [DecidableEq Site]
    (graph : MolecularGraph Site) (root : Site)
    (hreaches : ∀ site, Relation.ReflTransGen (CovalentlyBonded graph) root site) :
    graph.Connected := by
  intro left right
  exact (reflTransGen_symm_of_symm covalentlyBonded_symm (hreaches left)).trans
    (hreaches right)

/-! ## Previous part A2: PL1 and its stabilized monoanion -/

inductive PL1Site where
  | residue (arm acyl : Bool)
  | carbonylCarbon (arm acyl : Bool)
  | carbonylOxygen (arm acyl : Bool)
  | esterOxygen (arm acyl : Bool)
  | glycerolCarbon (arm : Bool) (position : Fin 3)
  | glycerolPhosphateOxygen (arm : Bool)
  | phosphorus (arm : Bool)
  | phosphorylOxygen (arm : Bool)
  | acidicOxygen (arm : Bool)
  | linkerPhosphateOxygen (arm : Bool)
  | linkerCarbon (position : Fin 3)
  | centralHydroxylOxygen
  deriving DecidableEq, Fintype

def acylPosition (acyl : Bool) : Fin 3 := if acyl then 1 else 0
def linkerEnd (arm : Bool) : Fin 3 := if arm then 2 else 0

def pl1Atom : PL1Site → AtomSite
  | .residue _ _ => residueRSite
  | .carbonylCarbon _ _ => carbonSite 0
  | .carbonylOxygen _ _ => oxygenSite 0
  | .esterOxygen _ _ => oxygenSite 0
  | .glycerolCarbon _ position => carbonSite (if position = 1 then 1 else 2)
  | .glycerolPhosphateOxygen _ => oxygenSite 0
  | .phosphorus _ => phosphorusSite
  | .phosphorylOxygen _ => oxygenSite 0
  | .acidicOxygen _ => oxygenSite 1
  | .linkerPhosphateOxygen _ => oxygenSite 0
  | .linkerCarbon position => carbonSite (if position = 1 then 1 else 2)
  | .centralHydroxylOxygen => oxygenSite 1

def pl1AcylBonds (arm acyl : Bool) : List (Bond PL1Site) :=
  [singleBond (.residue arm acyl) (.carbonylCarbon arm acyl),
   doubleBond (.carbonylCarbon arm acyl) (.carbonylOxygen arm acyl),
   singleBond (.carbonylCarbon arm acyl) (.esterOxygen arm acyl),
   singleBond (.esterOxygen arm acyl) (.glycerolCarbon arm (acylPosition acyl))]

def pl1ArmBonds (arm : Bool) : List (Bond PL1Site) :=
  ([false, true].flatMap fun acyl => pl1AcylBonds arm acyl) ++
  [singleBond (.glycerolCarbon arm 0) (.glycerolCarbon arm 1),
   singleBond (.glycerolCarbon arm 1) (.glycerolCarbon arm 2),
   singleBond (.glycerolCarbon arm 2) (.glycerolPhosphateOxygen arm),
   singleBond (.glycerolPhosphateOxygen arm) (.phosphorus arm),
   doubleBond (.phosphorus arm) (.phosphorylOxygen arm),
   singleBond (.phosphorus arm) (.acidicOxygen arm),
   singleBond (.phosphorus arm) (.linkerPhosphateOxygen arm),
   singleBond (.linkerPhosphateOxygen arm) (.linkerCarbon (linkerEnd arm))]

def pl1Bonds : List (Bond PL1Site) :=
  ([false, true].flatMap pl1ArmBonds) ++
  [singleBond (.linkerCarbon 0) (.linkerCarbon 1),
   singleBond (.linkerCarbon 1) (.linkerCarbon 2),
   singleBond (.linkerCarbon 1) .centralHydroxylOxygen]

def outerGlycerolStereoPL1 (arm : Bool) (handedness : Handedness) :
    TetrahedralStereo PL1Site where
  center := .glycerolCarbon arm 1
  orderedLigands :=
    [.site (.esterOxygen arm true),
     .site (.glycerolCarbon arm 0),
     .site (.glycerolCarbon arm 2),
     .attachedHydrogen]
  handedness := handedness

def pl1Graph (handedness : Handedness) : MolecularGraph PL1Site where
  atom := pl1Atom
  bonds := pl1Bonds
  stereocentres := [outerGlycerolStereoPL1 false handedness,
    outerGlycerolStereoPL1 true handedness]

theorem pl1ArmBond_mem (handedness : Handedness) (arm : Bool)
    {bond : Bond PL1Site} (hbond : bond ∈ pl1ArmBonds arm) :
    bond ∈ (pl1Graph handedness).bonds := by
  change bond ∈ ([false, true].flatMap pl1ArmBonds) ++ _
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨arm, by cases arm <;> simp, hbond⟩

theorem pl1AcylBond_mem (handedness : Handedness) (arm acyl : Bool)
    {bond : Bond PL1Site} (hbond : bond ∈ pl1AcylBonds arm acyl) :
    bond ∈ (pl1Graph handedness).bonds := by
  apply pl1ArmBond_mem handedness arm
  change bond ∈ ([false, true].flatMap fun acyl => pl1AcylBonds arm acyl) ++ _
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨acyl, by cases acyl <;> simp, hbond⟩

theorem pl1Graph_connected (handedness : Handedness) :
    (pl1Graph handedness).Connected := by
  apply connected_of_root (pl1Graph handedness) (.linkerCarbon 1)
  have hLinker (position : Fin 3) :
      Relation.ReflTransGen (CovalentlyBonded (pl1Graph handedness))
        (.linkerCarbon 1) (.linkerCarbon position) := by
    fin_cases position
    · exact listedBond_rtc_rev (pl1Graph handedness)
        (singleBond (.linkerCarbon 0) (.linkerCarbon 1)) (by
          simp [pl1Graph, pl1Bonds])
    · exact .refl
    · exact listedBond_rtc (pl1Graph handedness)
        (singleBond (.linkerCarbon 1) (.linkerCarbon 2)) (by
          simp [pl1Graph, pl1Bonds])
  have hLinkerPhosphate (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl1Graph handedness))
        (.linkerCarbon 1) (.linkerPhosphateOxygen arm) :=
    (hLinker (linkerEnd arm)).trans
      (listedBond_rtc_rev (pl1Graph handedness)
        (singleBond (.linkerPhosphateOxygen arm) (.linkerCarbon (linkerEnd arm)))
        (pl1ArmBond_mem handedness arm (by simp [pl1ArmBonds])))
  have hPhosphorus (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl1Graph handedness))
        (.linkerCarbon 1) (.phosphorus arm) :=
    (hLinkerPhosphate arm).trans
      (listedBond_rtc_rev (pl1Graph handedness)
        (singleBond (.phosphorus arm) (.linkerPhosphateOxygen arm))
        (pl1ArmBond_mem handedness arm (by simp [pl1ArmBonds])))
  have hGlycerolPhosphate (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl1Graph handedness))
        (.linkerCarbon 1) (.glycerolPhosphateOxygen arm) :=
    (hPhosphorus arm).trans
      (listedBond_rtc_rev (pl1Graph handedness)
        (singleBond (.glycerolPhosphateOxygen arm) (.phosphorus arm))
        (pl1ArmBond_mem handedness arm (by simp [pl1ArmBonds])))
  have hGlycerolTwo (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl1Graph handedness))
        (.linkerCarbon 1) (.glycerolCarbon arm 2) :=
    (hGlycerolPhosphate arm).trans
      (listedBond_rtc_rev (pl1Graph handedness)
        (singleBond (.glycerolCarbon arm 2) (.glycerolPhosphateOxygen arm))
        (pl1ArmBond_mem handedness arm (by simp [pl1ArmBonds])))
  have hGlycerolOne (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl1Graph handedness))
        (.linkerCarbon 1) (.glycerolCarbon arm 1) :=
    (hGlycerolTwo arm).trans
      (listedBond_rtc_rev (pl1Graph handedness)
        (singleBond (.glycerolCarbon arm 1) (.glycerolCarbon arm 2))
        (pl1ArmBond_mem handedness arm (by simp [pl1ArmBonds])))
  have hGlycerolZero (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl1Graph handedness))
        (.linkerCarbon 1) (.glycerolCarbon arm 0) :=
    (hGlycerolOne arm).trans
      (listedBond_rtc_rev (pl1Graph handedness)
        (singleBond (.glycerolCarbon arm 0) (.glycerolCarbon arm 1))
        (pl1ArmBond_mem handedness arm (by simp [pl1ArmBonds])))
  have hGlycerol (arm : Bool) (position : Fin 3) :
      Relation.ReflTransGen (CovalentlyBonded (pl1Graph handedness))
        (.linkerCarbon 1) (.glycerolCarbon arm position) := by
    fin_cases position
    · exact hGlycerolZero arm
    · exact hGlycerolOne arm
    · exact hGlycerolTwo arm
  have hEster (arm acyl : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl1Graph handedness))
        (.linkerCarbon 1) (.esterOxygen arm acyl) :=
    (hGlycerol arm (acylPosition acyl)).trans
      (listedBond_rtc_rev (pl1Graph handedness)
        (singleBond (.esterOxygen arm acyl)
          (.glycerolCarbon arm (acylPosition acyl)))
        (pl1AcylBond_mem handedness arm acyl (by simp [pl1AcylBonds])))
  have hCarbonyl (arm acyl : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl1Graph handedness))
        (.linkerCarbon 1) (.carbonylCarbon arm acyl) :=
    (hEster arm acyl).trans
      (listedBond_rtc_rev (pl1Graph handedness)
        (singleBond (.carbonylCarbon arm acyl) (.esterOxygen arm acyl))
        (pl1AcylBond_mem handedness arm acyl (by simp [pl1AcylBonds])))
  intro site
  cases site with
  | residue arm acyl =>
      exact (hCarbonyl arm acyl).trans
        (listedBond_rtc_rev (pl1Graph handedness)
          (singleBond (.residue arm acyl) (.carbonylCarbon arm acyl))
          (pl1AcylBond_mem handedness arm acyl (by simp [pl1AcylBonds])))
  | carbonylCarbon arm acyl => exact hCarbonyl arm acyl
  | carbonylOxygen arm acyl =>
      exact (hCarbonyl arm acyl).trans
        (listedBond_rtc (pl1Graph handedness)
          (doubleBond (.carbonylCarbon arm acyl) (.carbonylOxygen arm acyl))
          (pl1AcylBond_mem handedness arm acyl (by simp [pl1AcylBonds])))
  | esterOxygen arm acyl => exact hEster arm acyl
  | glycerolCarbon arm position => exact hGlycerol arm position
  | glycerolPhosphateOxygen arm => exact hGlycerolPhosphate arm
  | phosphorus arm => exact hPhosphorus arm
  | phosphorylOxygen arm =>
      exact (hPhosphorus arm).trans
        (listedBond_rtc (pl1Graph handedness)
          (doubleBond (.phosphorus arm) (.phosphorylOxygen arm))
          (pl1ArmBond_mem handedness arm (by simp [pl1ArmBonds])))
  | acidicOxygen arm =>
      exact (hPhosphorus arm).trans
        (listedBond_rtc (pl1Graph handedness)
          (singleBond (.phosphorus arm) (.acidicOxygen arm))
          (pl1ArmBond_mem handedness arm (by simp [pl1ArmBonds])))
  | linkerPhosphateOxygen arm => exact hLinkerPhosphate arm
  | linkerCarbon position => exact hLinker position
  | centralHydroxylOxygen =>
      exact listedBond_rtc (pl1Graph handedness)
        (singleBond (.linkerCarbon 1) .centralHydroxylOxygen) (by
          simp [pl1Graph, pl1Bonds])

theorem outerGlycerolStereoPL1_wellFormed (arm : Bool)
    (handedness : Handedness) :
    stereoWellFormed (pl1Graph handedness)
      (outerGlycerolStereoPL1 arm handedness) := by
  refine ⟨rfl, rfl, by simp [outerGlycerolStereoPL1], ?_⟩
  intro ligand hligand
  simp [outerGlycerolStereoPL1] at hligand
  rcases hligand with rfl | rfl | rfl | rfl
  · exact listedBond_covalentlyBonded_rev (pl1Graph handedness)
      (singleBond (.esterOxygen arm true)
        (.glycerolCarbon arm (acylPosition true)))
      (pl1AcylBond_mem handedness arm true (by simp [pl1AcylBonds]))
  · exact listedBond_covalentlyBonded_rev (pl1Graph handedness)
      (singleBond (.glycerolCarbon arm 0) (.glycerolCarbon arm 1))
      (pl1ArmBond_mem handedness arm (by simp [pl1ArmBonds]))
  · exact listedBond_covalentlyBonded (pl1Graph handedness)
      (singleBond (.glycerolCarbon arm 1) (.glycerolCarbon arm 2))
      (pl1ArmBond_mem handedness arm (by simp [pl1ArmBonds]))
  · simp [stereoLigandAttached, outerGlycerolStereoPL1, pl1Graph, pl1Atom,
      carbonSite]

theorem pl1Graph_wellFormed (handedness : Handedness) :
    (pl1Graph handedness).WellFormed := by
  unfold MolecularGraph.WellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change pl1Bonds.Nodup
    native_decide
  · intro bond hbond
    simp [pl1Graph, pl1Bonds, pl1ArmBonds, pl1AcylBonds] at hbond
    rcases hbond with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [singleBond, doubleBond, acylPosition, linkerEnd]
  · cases handedness <;> native_decide
  · cases handedness <;> native_decide
  · intro stereo hstereo
    simp [pl1Graph] at hstereo
    rcases hstereo with rfl | rfl
    · exact outerGlycerolStereoPL1_wellFormed false handedness
    · exact outerGlycerolStereoPL1_wellFormed true handedness

def yAtom (deprotonatedArm : Bool) : PL1Site → AtomSite
  | .acidicOxygen arm =>
      if arm = deprotonatedArm then oxygenSite 0 (-1) else oxygenSite 1
  | site => pl1Atom site

def yGraph (deprotonatedArm : Bool) (handedness : Handedness) :
    MolecularGraph PL1Site where
  atom := yAtom deprotonatedArm
  bonds := pl1Bonds
  stereocentres := [outerGlycerolStereoPL1 false handedness,
    outerGlycerolStereoPL1 true handedness]

theorem outerGlycerolStereoY_wellFormed (deprotonatedArm arm : Bool) :
    stereoWellFormed (yGraph deprotonatedArm .clockwise)
      (outerGlycerolStereoPL1 arm .clockwise) := by
  refine ⟨rfl, rfl, by simp [outerGlycerolStereoPL1], ?_⟩
  intro ligand hligand
  simp [outerGlycerolStereoPL1] at hligand
  rcases hligand with rfl | rfl | rfl | rfl
  · exact listedBond_covalentlyBonded_rev (yGraph deprotonatedArm .clockwise)
      (singleBond (.esterOxygen arm true)
        (.glycerolCarbon arm (acylPosition true)))
      (by simpa [yGraph, pl1Graph] using
        pl1AcylBond_mem .clockwise arm true (by simp [pl1AcylBonds]))
  · exact listedBond_covalentlyBonded_rev (yGraph deprotonatedArm .clockwise)
      (singleBond (.glycerolCarbon arm 0) (.glycerolCarbon arm 1))
      (by simpa [yGraph, pl1Graph] using
        pl1ArmBond_mem .clockwise arm (by simp [pl1ArmBonds]))
  · exact listedBond_covalentlyBonded (yGraph deprotonatedArm .clockwise)
      (singleBond (.glycerolCarbon arm 1) (.glycerolCarbon arm 2))
      (by simpa [yGraph, pl1Graph] using
        pl1ArmBond_mem .clockwise arm (by simp [pl1ArmBonds]))
  · simp [stereoLigandAttached, outerGlycerolStereoPL1, yGraph, yAtom,
      pl1Atom, carbonSite]

theorem yGraph_wellFormed (deprotonatedArm : Bool) :
    (yGraph deprotonatedArm .clockwise).WellFormed := by
  unfold MolecularGraph.WellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [yGraph, pl1Graph] using
      (pl1Graph_wellFormed .clockwise).1
  · simpa [yGraph, pl1Graph] using
      (pl1Graph_wellFormed .clockwise).2.1
  · cases deprotonatedArm <;> native_decide
  · cases deprotonatedArm <;> native_decide
  · intro stereo hstereo
    simp [yGraph] at hstereo
    rcases hstereo with rfl | rfl
    · exact outerGlycerolStereoY_wellFormed deprotonatedArm false
    · exact outerGlycerolStereoY_wellFormed deprotonatedArm true

structure HydrogenBond (Site : Type) where
  donorOxygen : Site
  acceptorOxygen : Site
  deriving DecidableEq

/-- The two hydrogen bonds close the two source-relevant headgroup rings. -/
def yHydrogenBonds (deprotonatedArm : Bool) : List (HydrogenBond PL1Site) :=
  [⟨.centralHydroxylOxygen, .acidicOxygen deprotonatedArm⟩,
   ⟨.acidicOxygen (!deprotonatedArm), .centralHydroxylOxygen⟩]

/-- Nontrivial carrier for the monoanion stabilization requested in A2: the
two proton-location contributors share the covalent skeleton and are exchanged
together with the two-ring hydrogen-bond network. -/
def MonoanionYSpec : Prop :=
  (yGraph false .clockwise).WellFormed ∧
  (yGraph true .clockwise).WellFormed ∧
  graphFormula (yGraph false .clockwise) = ⟨81, 141, 17, 2, -1⟩ ∧
  graphFormula (yGraph true .clockwise) = ⟨81, 141, 17, 2, -1⟩ ∧
  (yGraph false .clockwise).bonds = (yGraph true .clockwise).bonds ∧
  yHydrogenBonds false ≠ [] ∧ yHydrogenBonds true ≠ []

def PreviousPartA2Spec : Prop :=
  (pl1Graph .clockwise).WellFormed ∧
  (pl1Graph .clockwise).TreeLike ∧
  ¬ HasPeroxideBond (pl1Graph .clockwise) ∧
  graphFormula (pl1Graph .clockwise) = pl1Formula ∧
  totalBondOrder (pl1Graph .clockwise) = 255 ∧
  EnantiomericPair (pl1Graph .clockwise) (pl1Graph .counterclockwise) ∧
  MonoanionYSpec

theorem derivePreviousPartA2 : PreviousPartA2Spec := by
  unfold PreviousPartA2Spec
  refine ⟨pl1Graph_wellFormed .clockwise, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨pl1Graph_connected .clockwise, by native_decide⟩
  · rintro ⟨bond, hbond, horder, hleft, hright⟩
    simp [pl1Graph, pl1Bonds, pl1ArmBonds, pl1AcylBonds] at hbond
    rcases hbond with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [singleBond, doubleBond, isOxygenSite, pl1Graph, pl1Atom, carbonSite,
        oxygenSite, phosphorusSite, residueRSite, acylPosition, linkerEnd] at *
  · native_decide
  · native_decide
  · constructor
    · simp [pl1Graph]
    · rfl
  · unfold MonoanionYSpec
    refine ⟨yGraph_wellFormed false, yGraph_wellFormed true, ?_, ?_, rfl, ?_, ?_⟩
    · native_decide
    · native_decide
    · simp [yHydrogenBonds]
    · simp [yHydrogenBonds]

/-! ## The symmetric saturated diol `Z` -/

inductive ZSite where
  | terminalOxygen (endIndex : Bool)
  | carbon (position : Fin 3)
  deriving DecidableEq, Fintype

def zAtom : ZSite → AtomSite
  | .terminalOxygen _ => oxygenSite 1
  | .carbon _ => carbonSite 2

def zBonds : List (Bond ZSite) :=
  [singleBond (.terminalOxygen false) (.carbon 0),
   singleBond (.carbon 0) (.carbon 1),
   singleBond (.carbon 1) (.carbon 2),
   singleBond (.carbon 2) (.terminalOxygen true)]

def zGraph : MolecularGraph ZSite where
  atom := zAtom
  bonds := zBonds
  stereocentres := []

theorem zGraph_wellFormed : zGraph.WellFormed := by
  unfold MolecularGraph.WellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change zBonds.Nodup
    native_decide
  · intro bond hbond
    simp [zGraph, zBonds] at hbond
    rcases hbond with rfl | rfl | rfl | rfl <;> simp [singleBond]
  · native_decide
  · native_decide
  · simp [zGraph]

def ZSpec : Prop :=
  zGraph.WellFormed ∧
  graphFormula zGraph = propane13DiolFormula ∧
  totalBondOrder zGraph = 12 ∧
  totalPiBonds zGraph = 0 ∧
  zAtom (.carbon 1) = carbonSite 2

/-! ## Requested output 1: PL2 -/

inductive PL2Site where
  | residue (arm acyl : Bool)
  | carbonylCarbon (arm acyl : Bool)
  | carbonylOxygen (arm acyl : Bool)
  | esterOxygen (arm acyl : Bool)
  | glycerolCarbon (arm : Bool) (position : Fin 3)
  | glycerolPhosphateOxygen (arm : Bool)
  | phosphorus (arm : Bool)
  | phosphorylOxygen (arm : Bool)
  | acidicOxygen (arm : Bool)
  | linkerPhosphateOxygen (arm : Bool)
  | linkerCarbon (position : Fin 3)
  deriving DecidableEq, Fintype

def pl2Atom : PL2Site → AtomSite
  | .residue _ _ => residueRSite
  | .carbonylCarbon _ _ => carbonSite 0
  | .carbonylOxygen _ _ => oxygenSite 0
  | .esterOxygen _ _ => oxygenSite 0
  | .glycerolCarbon _ position => carbonSite (if position = 1 then 1 else 2)
  | .glycerolPhosphateOxygen _ => oxygenSite 0
  | .phosphorus _ => phosphorusSite
  | .phosphorylOxygen _ => oxygenSite 0
  | .acidicOxygen _ => oxygenSite 1
  | .linkerPhosphateOxygen _ => oxygenSite 0
  | .linkerCarbon _ => carbonSite 2

def pl2AcylBonds (arm acyl : Bool) : List (Bond PL2Site) :=
  [singleBond (.residue arm acyl) (.carbonylCarbon arm acyl),
   doubleBond (.carbonylCarbon arm acyl) (.carbonylOxygen arm acyl),
   singleBond (.carbonylCarbon arm acyl) (.esterOxygen arm acyl),
   singleBond (.esterOxygen arm acyl) (.glycerolCarbon arm (acylPosition acyl))]

def pl2ArmBonds (arm : Bool) : List (Bond PL2Site) :=
  ([false, true].flatMap fun acyl => pl2AcylBonds arm acyl) ++
  [singleBond (.glycerolCarbon arm 0) (.glycerolCarbon arm 1),
   singleBond (.glycerolCarbon arm 1) (.glycerolCarbon arm 2),
   singleBond (.glycerolCarbon arm 2) (.glycerolPhosphateOxygen arm),
   singleBond (.glycerolPhosphateOxygen arm) (.phosphorus arm),
   doubleBond (.phosphorus arm) (.phosphorylOxygen arm),
   singleBond (.phosphorus arm) (.acidicOxygen arm),
   singleBond (.phosphorus arm) (.linkerPhosphateOxygen arm),
   singleBond (.linkerPhosphateOxygen arm) (.linkerCarbon (linkerEnd arm))]

def pl2Bonds : List (Bond PL2Site) :=
  ([false, true].flatMap pl2ArmBonds) ++
  [singleBond (.linkerCarbon 0) (.linkerCarbon 1),
   singleBond (.linkerCarbon 1) (.linkerCarbon 2)]

def outerGlycerolStereoPL2 (arm : Bool) (handedness : Handedness) :
    TetrahedralStereo PL2Site where
  center := .glycerolCarbon arm 1
  orderedLigands :=
    [.site (.esterOxygen arm true),
     .site (.glycerolCarbon arm 0),
     .site (.glycerolCarbon arm 2),
     .attachedHydrogen]
  handedness := handedness

/-- One PL2 enantiomer has equal tetrahedral parity at its two outer glycerol
centres; simultaneous inversion gives the other enantiomer. -/
def pl2Graph (handedness : Handedness) : MolecularGraph PL2Site where
  atom := pl2Atom
  bonds := pl2Bonds
  stereocentres := [outerGlycerolStereoPL2 false handedness,
    outerGlycerolStereoPL2 true handedness]

theorem pl2ArmBond_mem (handedness : Handedness) (arm : Bool)
    {bond : Bond PL2Site} (hbond : bond ∈ pl2ArmBonds arm) :
    bond ∈ (pl2Graph handedness).bonds := by
  change bond ∈ ([false, true].flatMap pl2ArmBonds) ++ _
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨arm, by cases arm <;> simp, hbond⟩

theorem pl2AcylBond_mem (handedness : Handedness) (arm acyl : Bool)
    {bond : Bond PL2Site} (hbond : bond ∈ pl2AcylBonds arm acyl) :
    bond ∈ (pl2Graph handedness).bonds := by
  apply pl2ArmBond_mem handedness arm
  change bond ∈ ([false, true].flatMap fun acyl => pl2AcylBonds arm acyl) ++ _
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨acyl, by cases acyl <;> simp, hbond⟩

theorem pl2Graph_connected (handedness : Handedness) :
    (pl2Graph handedness).Connected := by
  apply connected_of_root (pl2Graph handedness) (.linkerCarbon 1)
  have hLinker (position : Fin 3) :
      Relation.ReflTransGen (CovalentlyBonded (pl2Graph handedness))
        (.linkerCarbon 1) (.linkerCarbon position) := by
    fin_cases position
    · exact listedBond_rtc_rev (pl2Graph handedness)
        (singleBond (.linkerCarbon 0) (.linkerCarbon 1)) (by
          simp [pl2Graph, pl2Bonds])
    · exact .refl
    · exact listedBond_rtc (pl2Graph handedness)
        (singleBond (.linkerCarbon 1) (.linkerCarbon 2)) (by
          simp [pl2Graph, pl2Bonds])
  have hLinkerPhosphate (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl2Graph handedness))
        (.linkerCarbon 1) (.linkerPhosphateOxygen arm) :=
    (hLinker (linkerEnd arm)).trans
      (listedBond_rtc_rev (pl2Graph handedness)
        (singleBond (.linkerPhosphateOxygen arm) (.linkerCarbon (linkerEnd arm)))
        (pl2ArmBond_mem handedness arm (by simp [pl2ArmBonds])))
  have hPhosphorus (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl2Graph handedness))
        (.linkerCarbon 1) (.phosphorus arm) :=
    (hLinkerPhosphate arm).trans
      (listedBond_rtc_rev (pl2Graph handedness)
        (singleBond (.phosphorus arm) (.linkerPhosphateOxygen arm))
        (pl2ArmBond_mem handedness arm (by simp [pl2ArmBonds])))
  have hGlycerolPhosphate (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl2Graph handedness))
        (.linkerCarbon 1) (.glycerolPhosphateOxygen arm) :=
    (hPhosphorus arm).trans
      (listedBond_rtc_rev (pl2Graph handedness)
        (singleBond (.glycerolPhosphateOxygen arm) (.phosphorus arm))
        (pl2ArmBond_mem handedness arm (by simp [pl2ArmBonds])))
  have hGlycerolTwo (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl2Graph handedness))
        (.linkerCarbon 1) (.glycerolCarbon arm 2) :=
    (hGlycerolPhosphate arm).trans
      (listedBond_rtc_rev (pl2Graph handedness)
        (singleBond (.glycerolCarbon arm 2) (.glycerolPhosphateOxygen arm))
        (pl2ArmBond_mem handedness arm (by simp [pl2ArmBonds])))
  have hGlycerolOne (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl2Graph handedness))
        (.linkerCarbon 1) (.glycerolCarbon arm 1) :=
    (hGlycerolTwo arm).trans
      (listedBond_rtc_rev (pl2Graph handedness)
        (singleBond (.glycerolCarbon arm 1) (.glycerolCarbon arm 2))
        (pl2ArmBond_mem handedness arm (by simp [pl2ArmBonds])))
  have hGlycerolZero (arm : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl2Graph handedness))
        (.linkerCarbon 1) (.glycerolCarbon arm 0) :=
    (hGlycerolOne arm).trans
      (listedBond_rtc_rev (pl2Graph handedness)
        (singleBond (.glycerolCarbon arm 0) (.glycerolCarbon arm 1))
        (pl2ArmBond_mem handedness arm (by simp [pl2ArmBonds])))
  have hGlycerol (arm : Bool) (position : Fin 3) :
      Relation.ReflTransGen (CovalentlyBonded (pl2Graph handedness))
        (.linkerCarbon 1) (.glycerolCarbon arm position) := by
    fin_cases position
    · exact hGlycerolZero arm
    · exact hGlycerolOne arm
    · exact hGlycerolTwo arm
  have hEster (arm acyl : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl2Graph handedness))
        (.linkerCarbon 1) (.esterOxygen arm acyl) :=
    (hGlycerol arm (acylPosition acyl)).trans
      (listedBond_rtc_rev (pl2Graph handedness)
        (singleBond (.esterOxygen arm acyl)
          (.glycerolCarbon arm (acylPosition acyl)))
        (pl2AcylBond_mem handedness arm acyl (by simp [pl2AcylBonds])))
  have hCarbonyl (arm acyl : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl2Graph handedness))
        (.linkerCarbon 1) (.carbonylCarbon arm acyl) :=
    (hEster arm acyl).trans
      (listedBond_rtc_rev (pl2Graph handedness)
        (singleBond (.carbonylCarbon arm acyl) (.esterOxygen arm acyl))
        (pl2AcylBond_mem handedness arm acyl (by simp [pl2AcylBonds])))
  intro site
  cases site with
  | residue arm acyl =>
      exact (hCarbonyl arm acyl).trans
        (listedBond_rtc_rev (pl2Graph handedness)
          (singleBond (.residue arm acyl) (.carbonylCarbon arm acyl))
          (pl2AcylBond_mem handedness arm acyl (by simp [pl2AcylBonds])))
  | carbonylCarbon arm acyl => exact hCarbonyl arm acyl
  | carbonylOxygen arm acyl =>
      exact (hCarbonyl arm acyl).trans
        (listedBond_rtc (pl2Graph handedness)
          (doubleBond (.carbonylCarbon arm acyl) (.carbonylOxygen arm acyl))
          (pl2AcylBond_mem handedness arm acyl (by simp [pl2AcylBonds])))
  | esterOxygen arm acyl => exact hEster arm acyl
  | glycerolCarbon arm position => exact hGlycerol arm position
  | glycerolPhosphateOxygen arm => exact hGlycerolPhosphate arm
  | phosphorus arm => exact hPhosphorus arm
  | phosphorylOxygen arm =>
      exact (hPhosphorus arm).trans
        (listedBond_rtc (pl2Graph handedness)
          (doubleBond (.phosphorus arm) (.phosphorylOxygen arm))
          (pl2ArmBond_mem handedness arm (by simp [pl2ArmBonds])))
  | acidicOxygen arm =>
      exact (hPhosphorus arm).trans
        (listedBond_rtc (pl2Graph handedness)
          (singleBond (.phosphorus arm) (.acidicOxygen arm))
          (pl2ArmBond_mem handedness arm (by simp [pl2ArmBonds])))
  | linkerPhosphateOxygen arm => exact hLinkerPhosphate arm
  | linkerCarbon position => exact hLinker position

theorem outerGlycerolStereoPL2_wellFormed (arm : Bool)
    (handedness : Handedness) :
    stereoWellFormed (pl2Graph handedness)
      (outerGlycerolStereoPL2 arm handedness) := by
  refine ⟨rfl, rfl, by simp [outerGlycerolStereoPL2], ?_⟩
  intro ligand hligand
  simp [outerGlycerolStereoPL2] at hligand
  rcases hligand with rfl | rfl | rfl | rfl
  · exact listedBond_covalentlyBonded_rev (pl2Graph handedness)
      (singleBond (.esterOxygen arm true)
        (.glycerolCarbon arm (acylPosition true)))
      (pl2AcylBond_mem handedness arm true (by simp [pl2AcylBonds]))
  · exact listedBond_covalentlyBonded_rev (pl2Graph handedness)
      (singleBond (.glycerolCarbon arm 0) (.glycerolCarbon arm 1))
      (pl2ArmBond_mem handedness arm (by simp [pl2ArmBonds]))
  · exact listedBond_covalentlyBonded (pl2Graph handedness)
      (singleBond (.glycerolCarbon arm 1) (.glycerolCarbon arm 2))
      (pl2ArmBond_mem handedness arm (by simp [pl2ArmBonds]))
  · simp [stereoLigandAttached, outerGlycerolStereoPL2, pl2Graph, pl2Atom,
      carbonSite]

theorem pl2Graph_wellFormed (handedness : Handedness) :
    (pl2Graph handedness).WellFormed := by
  unfold MolecularGraph.WellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change pl2Bonds.Nodup
    native_decide
  · intro bond hbond
    simp [pl2Graph, pl2Bonds, pl2ArmBonds, pl2AcylBonds] at hbond
    rcases hbond with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [singleBond, doubleBond, acylPosition, linkerEnd]
  · cases handedness <;> native_decide
  · cases handedness <;> native_decide
  · intro stereo hstereo
    simp [pl2Graph] at hstereo
    rcases hstereo with rfl | rfl
    · exact outerGlycerolStereoPL2_wellFormed false handedness
    · exact outerGlycerolStereoPL2_wellFormed true handedness

/-- The extra local exchange symmetry absent from PL1 is witnessed at the
central spacer: PL2 has a methylene with two H ligands, whereas PL1 has one H
and one hydroxyl substituent. -/
def localHydrogenPermutationMultiplicity (atom : AtomSite) : ℕ :=
  Nat.factorial atom.attachedHydrogens

def PL2MoreSymmetricThanPL1 : Prop :=
  pl2Atom (.linkerCarbon 1) = carbonSite 2 ∧
  pl1Atom (.linkerCarbon 1) = carbonSite 1 ∧
  localHydrogenPermutationMultiplicity (pl1Atom (.linkerCarbon 1)) <
    localHydrogenPermutationMultiplicity (pl2Atom (.linkerCarbon 1)) ∧
  (singleBond (.linkerCarbon 1) (.linkerCarbon 2) : Bond PL2Site) ∈ pl2Bonds ∧
  (singleBond (.linkerCarbon 1) (.linkerCarbon 2) : Bond PL1Site) ∈ pl1Bonds ∧
  (singleBond (.linkerCarbon 1) .centralHydroxylOxygen : Bond PL1Site) ∈ pl1Bonds

def PL2OutputSpec : Prop :=
  (pl2Graph .clockwise).WellFormed ∧
  (pl2Graph .counterclockwise).WellFormed ∧
  (pl2Graph .clockwise).TreeLike ∧
  graphFormula (pl2Graph .clockwise) = pl2Formula ∧
  totalBondOrder (pl2Graph .clockwise) = 254 ∧
  pl2HydrolysisLedger ∧
  ZSpec ∧
  PL2MoreSymmetricThanPL1 ∧
  EnantiomericPair (pl2Graph .clockwise) (pl2Graph .counterclockwise)

theorem deriveStructurePL2 : PL2OutputSpec := by
  unfold PL2OutputSpec
  refine ⟨pl2Graph_wellFormed .clockwise,
    pl2Graph_wellFormed .counterclockwise, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨pl2Graph_connected .clockwise, by native_decide⟩
  · native_decide
  · native_decide
  · unfold pl2HydrolysisLedger AtomChargeBalanced
    constructor
    · intro element
      fin_cases element <;> native_decide
    · native_decide
  · unfold ZSpec
    exact ⟨zGraph_wellFormed, by native_decide, by native_decide,
      by native_decide, by native_decide⟩
  · unfold PL2MoreSymmetricThanPL1
    native_decide
  · constructor
    · simp [pl2Graph]
    · rfl

/-! ## Requested output 2: PL3 -/

inductive PL3Site where
  | residue (acyl : Bool)
  | carbonylCarbon (acyl : Bool)
  | carbonylOxygen (acyl : Bool)
  | esterOxygen (acyl : Bool)
  | glycerolCarbon (position : Fin 3)
  | glycerolPhosphateOxygen
  | phosphorus
  | phosphorylOxygen
  | acidicOxygen
  | ethanolOxygen
  | ethanolCarbon (position : Fin 2)
  deriving DecidableEq, Fintype

def pl3Atom (physiological : Bool) : PL3Site → AtomSite
  | .residue _ => residueRSite
  | .carbonylCarbon _ => carbonSite 0
  | .carbonylOxygen _ => oxygenSite 0
  | .esterOxygen _ => oxygenSite 0
  | .glycerolCarbon position => carbonSite (if position = 1 then 1 else 2)
  | .glycerolPhosphateOxygen => oxygenSite 0
  | .phosphorus => phosphorusSite
  | .phosphorylOxygen => oxygenSite 0
  | .acidicOxygen => if physiological then oxygenSite 0 (-1) else oxygenSite 1
  | .ethanolOxygen => oxygenSite 0
  | .ethanolCarbon position => carbonSite (if position = 0 then 2 else 3)

def pl3AcylBonds (acyl : Bool) : List (Bond PL3Site) :=
  [singleBond (.residue acyl) (.carbonylCarbon acyl),
   doubleBond (.carbonylCarbon acyl) (.carbonylOxygen acyl),
   singleBond (.carbonylCarbon acyl) (.esterOxygen acyl),
   singleBond (.esterOxygen acyl) (.glycerolCarbon (acylPosition acyl))]

def pl3Bonds : List (Bond PL3Site) :=
  ([false, true].flatMap pl3AcylBonds) ++
  [singleBond (.glycerolCarbon 0) (.glycerolCarbon 1),
   singleBond (.glycerolCarbon 1) (.glycerolCarbon 2),
   singleBond (.glycerolCarbon 2) .glycerolPhosphateOxygen,
   singleBond .glycerolPhosphateOxygen .phosphorus,
   doubleBond .phosphorus .phosphorylOxygen,
   singleBond .phosphorus .acidicOxygen,
   singleBond .phosphorus .ethanolOxygen,
   singleBond .ethanolOxygen (.ethanolCarbon 0),
   singleBond (.ethanolCarbon 0) (.ethanolCarbon 1)]

def glycerolStereoPL3 (handedness : Handedness) : TetrahedralStereo PL3Site where
  center := .glycerolCarbon 1
  orderedLigands :=
    [.site (.esterOxygen true),
     .site (.glycerolCarbon 0),
     .site (.glycerolCarbon 2),
     .attachedHydrogen]
  handedness := handedness

def pl3Graph (physiological : Bool) (handedness : Handedness) :
    MolecularGraph PL3Site where
  atom := pl3Atom physiological
  bonds := pl3Bonds
  stereocentres := [glycerolStereoPL3 handedness]

theorem pl3AcylBond_mem (physiological : Bool) (handedness : Handedness)
    (acyl : Bool) {bond : Bond PL3Site} (hbond : bond ∈ pl3AcylBonds acyl) :
    bond ∈ (pl3Graph physiological handedness).bonds := by
  change bond ∈ ([false, true].flatMap pl3AcylBonds) ++ _
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨acyl, by cases acyl <;> simp, hbond⟩

theorem pl3Graph_connected (physiological : Bool) (handedness : Handedness) :
    (pl3Graph physiological handedness).Connected := by
  apply connected_of_root (pl3Graph physiological handedness) (.glycerolCarbon 1)
  have hGlycerol (position : Fin 3) :
      Relation.ReflTransGen (CovalentlyBonded (pl3Graph physiological handedness))
        (.glycerolCarbon 1) (.glycerolCarbon position) := by
    fin_cases position
    · exact listedBond_rtc_rev (pl3Graph physiological handedness)
        (singleBond (.glycerolCarbon 0) (.glycerolCarbon 1)) (by
          simp [pl3Graph, pl3Bonds])
    · exact .refl
    · exact listedBond_rtc (pl3Graph physiological handedness)
        (singleBond (.glycerolCarbon 1) (.glycerolCarbon 2)) (by
          simp [pl3Graph, pl3Bonds])
  have hGlycerolPhosphate :
      Relation.ReflTransGen (CovalentlyBonded (pl3Graph physiological handedness))
        (.glycerolCarbon 1) .glycerolPhosphateOxygen :=
    (hGlycerol 2).trans
      (listedBond_rtc (pl3Graph physiological handedness)
        (singleBond (.glycerolCarbon 2) .glycerolPhosphateOxygen) (by
          simp [pl3Graph, pl3Bonds]))
  have hPhosphorus :
      Relation.ReflTransGen (CovalentlyBonded (pl3Graph physiological handedness))
        (.glycerolCarbon 1) .phosphorus :=
    hGlycerolPhosphate.trans
      (listedBond_rtc (pl3Graph physiological handedness)
        (singleBond .glycerolPhosphateOxygen .phosphorus) (by
          simp [pl3Graph, pl3Bonds]))
  have hEthanolOxygen :
      Relation.ReflTransGen (CovalentlyBonded (pl3Graph physiological handedness))
        (.glycerolCarbon 1) .ethanolOxygen :=
    hPhosphorus.trans
      (listedBond_rtc (pl3Graph physiological handedness)
        (singleBond .phosphorus .ethanolOxygen) (by
          simp [pl3Graph, pl3Bonds]))
  have hEthanolZero :
      Relation.ReflTransGen (CovalentlyBonded (pl3Graph physiological handedness))
        (.glycerolCarbon 1) (.ethanolCarbon 0) :=
    hEthanolOxygen.trans
      (listedBond_rtc (pl3Graph physiological handedness)
        (singleBond .ethanolOxygen (.ethanolCarbon 0)) (by
          simp [pl3Graph, pl3Bonds]))
  have hEthanolOne :
      Relation.ReflTransGen (CovalentlyBonded (pl3Graph physiological handedness))
        (.glycerolCarbon 1) (.ethanolCarbon 1) :=
    hEthanolZero.trans
      (listedBond_rtc (pl3Graph physiological handedness)
        (singleBond (.ethanolCarbon 0) (.ethanolCarbon 1)) (by
          simp [pl3Graph, pl3Bonds]))
  have hEster (acyl : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl3Graph physiological handedness))
        (.glycerolCarbon 1) (.esterOxygen acyl) :=
    (hGlycerol (acylPosition acyl)).trans
      (listedBond_rtc_rev (pl3Graph physiological handedness)
        (singleBond (.esterOxygen acyl) (.glycerolCarbon (acylPosition acyl)))
        (pl3AcylBond_mem physiological handedness acyl (by
          simp [pl3AcylBonds])))
  have hCarbonyl (acyl : Bool) :
      Relation.ReflTransGen (CovalentlyBonded (pl3Graph physiological handedness))
        (.glycerolCarbon 1) (.carbonylCarbon acyl) :=
    (hEster acyl).trans
      (listedBond_rtc_rev (pl3Graph physiological handedness)
        (singleBond (.carbonylCarbon acyl) (.esterOxygen acyl))
        (pl3AcylBond_mem physiological handedness acyl (by
          simp [pl3AcylBonds])))
  intro site
  cases site with
  | residue acyl =>
      exact (hCarbonyl acyl).trans
        (listedBond_rtc_rev (pl3Graph physiological handedness)
          (singleBond (.residue acyl) (.carbonylCarbon acyl))
          (pl3AcylBond_mem physiological handedness acyl (by
            simp [pl3AcylBonds])))
  | carbonylCarbon acyl => exact hCarbonyl acyl
  | carbonylOxygen acyl =>
      exact (hCarbonyl acyl).trans
        (listedBond_rtc (pl3Graph physiological handedness)
          (doubleBond (.carbonylCarbon acyl) (.carbonylOxygen acyl))
          (pl3AcylBond_mem physiological handedness acyl (by
            simp [pl3AcylBonds])))
  | esterOxygen acyl => exact hEster acyl
  | glycerolCarbon position => exact hGlycerol position
  | glycerolPhosphateOxygen => exact hGlycerolPhosphate
  | phosphorus => exact hPhosphorus
  | phosphorylOxygen =>
      exact hPhosphorus.trans
        (listedBond_rtc (pl3Graph physiological handedness)
          (doubleBond .phosphorus .phosphorylOxygen) (by
            simp [pl3Graph, pl3Bonds]))
  | acidicOxygen =>
      exact hPhosphorus.trans
        (listedBond_rtc (pl3Graph physiological handedness)
          (singleBond .phosphorus .acidicOxygen) (by
            simp [pl3Graph, pl3Bonds]))
  | ethanolOxygen => exact hEthanolOxygen
  | ethanolCarbon position =>
      fin_cases position
      · exact hEthanolZero
      · exact hEthanolOne

theorem glycerolStereoPL3_wellFormed (physiological : Bool)
    (handedness : Handedness) :
    stereoWellFormed (pl3Graph physiological handedness)
      (glycerolStereoPL3 handedness) := by
  refine ⟨rfl, rfl, by simp [glycerolStereoPL3], ?_⟩
  intro ligand hligand
  simp [glycerolStereoPL3] at hligand
  rcases hligand with rfl | rfl | rfl | rfl
  · exact listedBond_covalentlyBonded_rev (pl3Graph physiological handedness)
      (singleBond (.esterOxygen true) (.glycerolCarbon (acylPosition true)))
      (pl3AcylBond_mem physiological handedness true (by simp [pl3AcylBonds]))
  · exact listedBond_covalentlyBonded_rev (pl3Graph physiological handedness)
      (singleBond (.glycerolCarbon 0) (.glycerolCarbon 1)) (by
        simp [pl3Graph, pl3Bonds])
  · exact listedBond_covalentlyBonded (pl3Graph physiological handedness)
      (singleBond (.glycerolCarbon 1) (.glycerolCarbon 2)) (by
        simp [pl3Graph, pl3Bonds])
  · simp [stereoLigandAttached, glycerolStereoPL3, pl3Graph, pl3Atom,
      carbonSite]

theorem pl3Graph_wellFormed (physiological : Bool) (handedness : Handedness) :
    (pl3Graph physiological handedness).WellFormed := by
  unfold MolecularGraph.WellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change pl3Bonds.Nodup
    native_decide
  · intro bond hbond
    simp [pl3Graph, pl3Bonds, pl3AcylBonds] at hbond
    rcases hbond with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [singleBond, doubleBond, acylPosition]
  · cases physiological <;> cases handedness <;> native_decide
  · cases physiological <;> cases handedness <;> native_decide
  · intro stereo hstereo
    simp [pl3Graph] at hstereo
    subst stereo
    exact glycerolStereoPL3_wellFormed physiological handedness

/-- Deprotonation at physiological pH changes only the acidic O-H site and the
net charge; it does not change connectivity or tetrahedral parity. -/
def PL3PhysiologicalIonizationSpec : Prop :=
  (pl3Graph false .clockwise).bonds = (pl3Graph true .clockwise).bonds ∧
  (pl3Graph false .clockwise).stereocentres =
    (pl3Graph true .clockwise).stereocentres ∧
  graphFormula (pl3Graph false .clockwise) = pl3NeutralFormula ∧
  graphFormula (pl3Graph true .clockwise) = pl3PhysiologicalFormula

def PL3OutputSpec : Prop :=
  (pl3Graph true .clockwise).WellFormed ∧
  (pl3Graph true .counterclockwise).WellFormed ∧
  (pl3Graph true .clockwise).TreeLike ∧
  PL3PhysiologicalIonizationSpec ∧
  graphFormula (pl3Graph true .clockwise) = pl3PhysiologicalFormula ∧
  (graphFormula (pl3Graph true .clockwise)).charge = -1 ∧
  EnantiomericPair (pl3Graph true .clockwise) (pl3Graph true .counterclockwise) ∧
  pl3HydrolysisLedger 4

theorem pl3BalancedHydrolysisDeterminesWaterCoefficient (m : ℕ)
    (h : pl3HydrolysisLedger m) : m = 4 := by
  simp only [pl3HydrolysisLedger, AtomChargeBalanced] at h
  have hH := h.1 Element.H
  have hspecies : (Finset.univ : Finset HydrolysisSpecies) =
      {.PL1, .PL2, .PL3Neutral, .water, .fattyAcid, .phosphoricAcid,
        .glycerol, .propane13Diol, .ethanol} := by
    native_decide
  simp only [atomsOnSide, hspecies] at hH
  simp [speciesFormula, pl3Hydrolysis,
    MolecularFormula.count, pl3NeutralFormula, waterFormula,
    fattyAcidFormula, phosphoricAcidFormula, ethanolFormula,
    glycerolFormula] at hH
  omega

theorem deriveStructurePL3 : PL3OutputSpec := by
  unfold PL3OutputSpec
  refine ⟨pl3Graph_wellFormed true .clockwise,
    pl3Graph_wellFormed true .counterclockwise, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨pl3Graph_connected true .clockwise, by native_decide⟩
  · unfold PL3PhysiologicalIonizationSpec
    exact ⟨rfl, rfl, by native_decide, by native_decide⟩
  · native_decide
  · native_decide
  · constructor
    · simp [pl3Graph]
    · rfl
  · unfold pl3HydrolysisLedger AtomChargeBalanced
    constructor
    · intro element
      fin_cases element <;> native_decide
    · native_decide

/-! ## Answer-blind semantic and machine-readable result carriers -/

/-- Raw derivation carrier: previous-part derivations and both source-checked
structural outputs are kept together because the current question has two
requested outputs. -/
def RawResult : Prop :=
  PreviousPartA2Spec ∧
  A3Constraints fattyAcidCounts ∧ A3Conclusion fattyAcidCounts ∧
  PL2OutputSpec ∧ PL3OutputSpec

/-- Exact-symbolic reported carrier, in the source-requested PL2 then PL3 order. -/
def ReportedResult : Prop := PL2OutputSpec ∧ PL3OutputSpec

theorem rawResult : RawResult := by
  exact ⟨derivePreviousPartA2, fattyAcidCounts_meet_A3_constraints,
    derivePreviousPartA3 fattyAcidCounts fattyAcidCounts_meet_A3_constraints,
    deriveStructurePL2, deriveStructurePL3⟩

theorem reportedResult : ReportedResult := by
  exact ⟨deriveStructurePL2, deriveStructurePL3⟩

/-- Hash-bound raw symbolic result contract for the answer-blind verifier. -/
theorem rawResultContract :
    ("3fe3584e4b532571525cd79b559f414a40cd6310d0bb68eb7314fc5c0a2c78b9" : String) =
        "3fe3584e4b532571525cd79b559f414a40cd6310d0bb68eb7314fc5c0a2c78b9" ∧
      IChO2026Problems.T5A6.RawResult := by
  exact ⟨rfl, rawResult⟩

/-- Hash-bound reported symbolic result contract for the answer-blind verifier. -/
theorem reportedResultContract :
    ("f9f4fae2b03574f555c26199208c2318a502a029033f45519640f2853fab37b4" : String) =
        "f9f4fae2b03574f555c26199208c2318a502a029033f45519640f2853fab37b4" ∧
      IChO2026Problems.T5A6.ReportedResult := by
  exact ⟨rfl, reportedResult⟩

end IChO2026Problems.T5A6
