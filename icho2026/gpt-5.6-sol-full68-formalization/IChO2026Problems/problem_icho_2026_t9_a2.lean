import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T9 A2: per-3,6-anhydro-beta-cyclodextrin

The two problem images show beta-cyclodextrin as a closed ring of seven
alpha-D-glucopyranoside residues.  Each displayed residue has hydroxyl groups
at C2, C3, and C6.  The source arrow uses seven equivalents of tosyl chloride
in pyridine, followed by sodium hydroxide in water at 60 degrees Celsius, and
states that the labelled product `K` has one free hydroxyl per residue.

The source arrow is used only as a qualitative named transformation: no yield,
completion, sole-product, phase-balance, or omitted-stream claim is made here.
The chemistry bridge is independently scoped by the abstract of H. Yamamura
and K. Fujita, "Preparation of Heptakis(6-O-(p-tosyl))-beta-cyclodextrin ...
and Their Conversion to Heptakis(3,6-anhydro)-beta-cyclodextrin", Chemical and
Pharmaceutical Bulletin 39 (1991), 2505--2508,
DOI `10.1248/cpb.39.2505`, at
`https://www.jstage.jst.go.jp/article/cpb1958/39/10/39_10_2505/_article`.
The abstract identifies the conversion to heptakis(3,6-anhydro)-beta-CD and
states that its glucose units adopt the inverted 1C4 chair.  The graph edit
below expresses exactly that scoped claim; it is not an open-world reaction
classification.
-/

namespace IChO2026Problems.T9A2

noncomputable section

/-! ## Source reaction and its deliberately qualitative use -/

/-- Chemical entities explicitly named or depicted in the source arrow. -/
inductive ChemicalSpecies where
  | betaCyclodextrin
  | tosylChloride
  | pyridine
  | sodiumHydroxide
  | water
  | compoundK
  deriving DecidableEq, Fintype, Repr

/-- Roles attached to materials on an arrow; an absent amount remains absent. -/
inductive MaterialRole where
  | substrate
  | reagent
  | solvent
  | labelledProduct
  deriving DecidableEq, Fintype, Repr

/-- Phases are retained only where the problem itself supplies them. -/
inductive SourcePhase where
  | unspecified
  | aqueous
  deriving DecidableEq, Fintype, Repr

/-- A source-labelled material portion.  `equivalents = none` means that the
problem gives no numerical amount, not that the amount is zero. -/
structure MaterialPortion where
  species : ChemicalSpecies
  role : MaterialRole
  phase : SourcePhase
  equivalents : Option ℚ
  deriving DecidableEq, Repr

/-- One directed reaction stage, preserving an omitted temperature as `none`. -/
structure ReactionStage where
  materials : List MaterialPortion
  temperatureCelsius : Option ℚ
  deriving DecidableEq, Repr

/-- The complete two-step source arrow, including its named endpoints. -/
structure ReactionScheme where
  substrate : ChemicalSpecies
  productLabel : ChemicalSpecies
  stages : List ReactionStage
  deriving DecidableEq, Repr

/-- The seven equivalents of tosyl chloride printed over the first arrow. -/
def tosylChloridePortion : MaterialPortion :=
  { species := .tosylChloride
    role := .reagent
    phase := .unspecified
    equivalents := some 7 }

/-- Pyridine (`Py`) is printed as the first-stage medium. -/
def pyridinePortion : MaterialPortion :=
  { species := .pyridine
    role := .solvent
    phase := .unspecified
    equivalents := none }

/-- Sodium hydroxide is printed without a numerical equivalent count. -/
def sodiumHydroxidePortion : MaterialPortion :=
  { species := .sodiumHydroxide
    role := .reagent
    phase := .aqueous
    equivalents := none }

/-- Water is the explicitly printed second-stage medium. -/
def waterPortion : MaterialPortion :=
  { species := .water
    role := .solvent
    phase := .aqueous
    equivalents := none }

/-- First source stage; its temperature is not supplied. -/
def tosylationStage : ReactionStage :=
  { materials := [tosylChloridePortion, pyridinePortion]
    temperatureCelsius := none }

/-- Second source stage at exactly 60 degrees Celsius as printed. -/
def aqueousBaseStage : ReactionStage :=
  { materials := [sodiumHydroxidePortion, waterPortion]
    temperatureCelsius := some 60 }

/-- The two stages transcribed from page 2. -/
def sourceReaction : ReactionScheme :=
  { substrate := .betaCyclodextrin
    productLabel := .compoundK
    stages := [tosylationStage, aqueousBaseStage] }

/-- A fieldwise, non-opaque check of every condition printed over the arrow. -/
def SourceReactionSpec (scheme : ReactionScheme) : Prop :=
  scheme.substrate = .betaCyclodextrin ∧
  scheme.productLabel = .compoundK ∧
  scheme.stages = [tosylationStage, aqueousBaseStage] ∧
  tosylChloridePortion.species = .tosylChloride ∧
  tosylChloridePortion.equivalents = some 7 ∧
  pyridinePortion.species = .pyridine ∧
  pyridinePortion.role = .solvent ∧
  sodiumHydroxidePortion.species = .sodiumHydroxide ∧
  sodiumHydroxidePortion.phase = .aqueous ∧
  waterPortion.species = .water ∧
  waterPortion.role = .solvent ∧
  aqueousBaseStage.temperatureCelsius = some 60

theorem sourceReaction_spec : SourceReactionSpec sourceReaction := by
  simp [SourceReactionSpec, sourceReaction, tosylationStage,
    aqueousBaseStage, tosylChloridePortion, pyridinePortion,
    sodiumHydroxidePortion, waterPortion]

/-- Required staged-transformation classification. -/
inductive StagedTransformationUse where
  | quantitativeMaterialStage
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Fintype, Repr

/-- The drawing question uses the arrow as a compatibility constraint only. -/
def sourceArrowUse : StagedTransformationUse :=
  .qualitativeNamedTransformOnly

theorem sourceArrow_is_qualitative :
    sourceArrowUse = .qualitativeNamedTransformOnly := by
  rfl

/-! ## Atom-complete source template -/

/-- The seven source-labelled glucopyranoside positions in beta-CD. -/
abbrev BetaUnit := Fin 7

/-- Successor around the closed seven-membered glycosidic macrocycle. -/
def nextUnit (i : BetaUnit) : BetaUnit := i + 1

/-- Predecessor around the same macrocycle. -/
def previousUnit (i : BetaUnit) : BetaUnit := i - 1

/-- Every atom slot in one displayed beta-CD repeat, including all hydrogens.
The glycosidic oxygen belongs to the C1 side of its alpha-1,4 link. -/
inductive GlucoseAtomSite where
  | c1 | c2 | c3 | c4 | c5 | c6
  | ringO5
  | hydroxyO2 | hydroxyO3 | hydroxyO6
  | glycosidicO
  | h1 | h2 | h3 | h4 | h5 | h6a | h6b
  | hydroxyH2 | hydroxyH3 | hydroxyH6
  deriving DecidableEq, Fintype, Repr

/-- An atom is located by a macrocycle unit and an atom slot in that unit. -/
abbrev BetaAtom := BetaUnit × GlucoseAtomSite

/-- Elements occurring in the substrate and product molecular graphs. -/
inductive Element where
  | hydrogen | carbon | oxygen
  deriving DecidableEq, Fintype, Repr

/-- Atom metadata makes charge, radical state, and isotope choice explicit. -/
structure AtomDescriptor where
  element : Element
  isotopeMassNumber : Option ℕ
  formalCharge : ℤ
  radicalElectrons : ℕ
  deriving DecidableEq, Repr

/-- Element at each atom slot of a beta-CD repeat. -/
def siteElement : GlucoseAtomSite → Element
  | .c1 | .c2 | .c3 | .c4 | .c5 | .c6 => .carbon
  | .ringO5 | .hydroxyO2 | .hydroxyO3 | .hydroxyO6 | .glycosidicO => .oxygen
  | .h1 | .h2 | .h3 | .h4 | .h5 | .h6a | .h6b
  | .hydroxyH2 | .hydroxyH3 | .hydroxyH6 => .hydrogen

/-- Every depicted atom is neutral, closed-shell, and of natural isotopic
composition; no isotope is singled out by the source. -/
def sourceAtomDescriptor (a : BetaAtom) : AtomDescriptor :=
  { element := siteElement a.2
    isotopeMassNumber := none
    formalCharge := 0
    radicalElectrons := 0 }

/-- Bond orders supported by the explicit molecular graph. -/
inductive BondOrder where
  | absent | single | double | triple
  deriving DecidableEq, Fintype, Repr

/-- The 21 covalent bonds internal to one alpha-D-glucopyranoside residue in
the source template.  Cross-residue alpha-1,4 bonds are listed separately. -/
def sourceLocalBondPairs : Finset (GlucoseAtomSite × GlucoseAtomSite) :=
  { (.c1, .c2), (.c2, .c3), (.c3, .c4), (.c4, .c5),
    (.c5, .ringO5), (.ringO5, .c1), (.c5, .c6),
    (.c2, .hydroxyO2), (.hydroxyO2, .hydroxyH2),
    (.c3, .hydroxyO3), (.hydroxyO3, .hydroxyH3),
    (.c6, .hydroxyO6), (.hydroxyO6, .hydroxyH6),
    (.c1, .glycosidicO),
    (.c1, .h1), (.c2, .h2), (.c3, .h3), (.c4, .h4),
    (.c5, .h5), (.c6, .h6a), (.c6, .h6b) }

/-- Undirected incidence in the atom-complete repeat graph. -/
def IsSourceLocalBond (a b : GlucoseAtomSite) : Prop :=
  (a, b) ∈ sourceLocalBondPairs ∨ (b, a) ∈ sourceLocalBondPairs

/-- The explicit local bond ledger is computationally decidable. -/
instance instDecidableIsSourceLocalBond (a b : GlucoseAtomSite) :
    Decidable (IsSourceLocalBond a b) := by
  unfold IsSourceLocalBond
  infer_instance

/-- The cross-boundary bond `C1(i)-O(i)-C4(i+1)` closes the alpha-1,4 ring. -/
def IsSourceCrossBoundaryBond (a b : BetaAtom) : Prop :=
  (a.2 = .glycosidicO ∧ b.2 = .c4 ∧ b.1 = nextUnit a.1) ∨
  (b.2 = .glycosidicO ∧ a.2 = .c4 ∧ a.1 = nextUnit b.1)

/-- Cross-boundary incidence is decidable from the finite atom labels. -/
instance instDecidableIsSourceCrossBoundaryBond (a b : BetaAtom) :
    Decidable (IsSourceCrossBoundaryBond a b) := by
  unfold IsSourceCrossBoundaryBond
  infer_instance

/-- Exact single-bond graph of the beta-CD template before reaction. -/
def sourceBondOrder (a b : BetaAtom) : BondOrder := by
  exact
    if (a.1 = b.1 ∧ IsSourceLocalBond a.2 b.2) ∨
        IsSourceCrossBoundaryBond a b then
      .single
    else
      .absent

/-! ## Explicit relative stereochemistry -/

/-- The five tetrahedral carbon positions in every alpha-D-glucopyranoside. -/
inductive StereoPosition where
  | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq, Fintype, Repr

/-- Faces are viewed relative to the conventional Haworth mean-ring plane. -/
inductive RingFace where
  | top | bottom
  deriving DecidableEq, Fintype, Repr

/-- A ligand may belong to the same residue or be the glycosidic oxygen from
the preceding residue. -/
inductive RelativeResidue where
  | same | previous
  deriving DecidableEq, Fintype, Repr

/-- A graph-resolvable ligand reference for a stereogenic carbon. -/
structure AtomReference where
  residue : RelativeResidue
  site : GlucoseAtomSite
  deriving DecidableEq, Repr

/-- An explicit tetrahedral annotation: named centre, named ligand, and face. -/
structure StereoAnnotation where
  center : GlucoseAtomSite
  ligand : AtomReference
  ligandFace : RingFace
  deriving DecidableEq, Repr

/-- The alpha-D-gluco relative configuration read from the source template:
C1-O(glycosidic), C2-O, C3-O, and C4-O are down, down, up, and down,
while the C5-C6 bond is up.  This face table is unchanged by chair inversion. -/
def alphaDGlucoStereo : StereoPosition → StereoAnnotation
  | .c1 =>
      { center := .c1
        ligand := { residue := .same, site := .glycosidicO }
        ligandFace := .bottom }
  | .c2 =>
      { center := .c2
        ligand := { residue := .same, site := .hydroxyO2 }
        ligandFace := .bottom }
  | .c3 =>
      { center := .c3
        ligand := { residue := .same, site := .hydroxyO3 }
        ligandFace := .top }
  | .c4 =>
      { center := .c4
        ligand := { residue := .previous, site := .glycosidicO }
        ligandFace := .bottom }
  | .c5 =>
      { center := .c5
        ligand := { residue := .same, site := .c6 }
        ligandFace := .top }

/-- Resolve a stereochemical atom reference into the seven-unit graph. -/
def resolveReference (i : BetaUnit) (r : AtomReference) : BetaAtom :=
  (match r.residue with
    | .same => i
    | .previous => previousUnit i,
   r.site)

/-- A molecule over the fixed, source-derived atom-slot universe.  `present`
separates actual product atoms from atom slots removed by the transformation. -/
structure MolecularStructure where
  present : BetaAtom → Bool
  atom : BetaAtom → AtomDescriptor
  bondOrder : BetaAtom → BetaAtom → BondOrder
  stereo : BetaUnit → StereoPosition → StereoAnnotation

/-- Atom-complete beta-CD substrate read directly from the two figures. -/
def betaCDStructure : MolecularStructure :=
  { present := fun _ => true
    atom := sourceAtomDescriptor
    bondOrder := sourceBondOrder
    stereo := fun _ => alphaDGlucoStereo }

/-! ## The source-scoped 3,6-anhydro graph edit -/

/-- Exactly the three atom slots lost per residue on replacing C3-OH and C6-OH
by the C3-O-C6 intramolecular ether: O6, H(O3), and H(O6). -/
def removedBy36Cyclization : GlucoseAtomSite → Bool
  | .hydroxyO6 | .hydroxyH3 | .hydroxyH6 => true
  | _ => false

/-- Presence predicate generated from the source graph, uniformly for all
seven residues. -/
def retainedIn36Product (a : BetaAtom) : Bool :=
  !(removedBy36Cyclization a.2)

/-- The one new heavy-atom bond in each residue is O3-C6. -/
def IsNew36Bridge (a b : BetaAtom) : Prop :=
  a.1 = b.1 ∧
    ((a.2 = .hydroxyO3 ∧ b.2 = .c6) ∨
     (b.2 = .hydroxyO3 ∧ a.2 = .c6))

/-- The proposed intramolecular bridge is decidable from atom labels. -/
instance instDecidableIsNew36Bridge (a b : BetaAtom) :
    Decidable (IsNew36Bridge a b) := by
  unfold IsNew36Bridge
  infer_instance

/-- Bond edit for intramolecular 3,6-anhydro formation.  All orders between
retained atoms are preserved, and only the O3-C6 single bond is added. -/
def cyclized36BondOrder (m : MolecularStructure) (a b : BetaAtom) : BondOrder := by
  exact
    if retainedIn36Product a = true ∧ retainedIn36Product b = true then
      if IsNew36Bridge a b then .single else m.bondOrder a b
    else
      .absent

/-- Constructive candidate generation from the source molecule, rather than a
candidate-named singleton or an assumed target equality. -/
def intramolecular36Cyclization (m : MolecularStructure) : MolecularStructure :=
  { present := retainedIn36Product
    atom := m.atom
    bondOrder := cyclized36BondOrder m
    stereo := m.stereo }

/-- Concrete structure candidate for the named product `K`. -/
def kStructure : MolecularStructure :=
  intramolecular36Cyclization betaCDStructure

/-- Transparent specification of the 3,6-anhydro edit. -/
def IsPer36AnhydroEdit
    (substrate product : MolecularStructure) : Prop :=
  (∀ a, product.present a = retainedIn36Product a) ∧
  product.atom = substrate.atom ∧
  (∀ a b, product.bondOrder a b = cyclized36BondOrder substrate a b) ∧
  product.stereo = substrate.stereo

/-- Source-to-Lean chemistry bridge, scoped to the displayed beta-CD arrow and
the cited 1991 beta-CD conversion.  It asserts compatibility only, not a yield
or an exhaustive product classification. -/
def SourceArrowPer36AnhydroCompatibility
    (product : MolecularStructure) : Prop :=
  SourceReactionSpec sourceReaction ∧
  sourceArrowUse = .qualitativeNamedTransformOnly ∧
  IsPer36AnhydroEdit betaCDStructure product

theorem sourceArrow_constructs_k :
    SourceArrowPer36AnhydroCompatibility kStructure := by
  refine ⟨sourceReaction_spec, sourceArrow_is_qualitative, ?_⟩
  exact ⟨fun _ => rfl, rfl, fun _ _ => rfl, rfl⟩

/-! ## Independent structural checks on the constructed candidate -/

/-- A chemically well-formed finite graph has symmetric, loop-free bonds and
no bond incident to a non-present atom. -/
def MolecularGraphWellFormed (m : MolecularStructure) : Prop :=
  (∀ a, m.bondOrder a a = .absent) ∧
  (∀ a b, m.bondOrder a b = m.bondOrder b a) ∧
  (∀ a b, m.present a = false → m.bondOrder a b = .absent) ∧
  (∀ a b, m.present b = false → m.bondOrder a b = .absent)

/-- Integer valence contribution of a bond order. -/
def BondOrder.valence : BondOrder → ℕ
  | .absent => 0
  | .single => 1
  | .double => 2
  | .triple => 3

/-- Bond-order valence at one atom slot. -/
def valenceAt (m : MolecularStructure) (a : BetaAtom) : ℕ :=
  ∑ b : BetaAtom, (m.bondOrder a b).valence

/-- Every present atom has its ordinary closed-shell valence. -/
def OrdinaryValenceSpec (m : MolecularStructure) : Prop :=
  ∀ a, m.present a = true →
    match (m.atom a).element with
    | .hydrogen => valenceAt m a = 1
    | .carbon => valenceAt m a = 4
    | .oxygen => valenceAt m a = 2

/-- Number of present atoms of a specified element. -/
def elementCount (m : MolecularStructure) (e : Element) : ℕ :=
  ((Finset.univ : Finset BetaAtom).filter fun a =>
    m.present a = true ∧ (m.atom a).element = e).card

/-- C/H/O molecular formula recombined from the complete atom ledger. -/
structure CHOFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

/-- Formula obtained by recounting all present atom vertices. -/
def molecularFormula (m : MolecularStructure) : CHOFormula :=
  { carbon := elementCount m .carbon
    hydrogen := elementCount m .hydrogen
    oxygen := elementCount m .oxygen }

/-- Candidate-local primitive formula check: seven waters separate the source
graph formula from the 3,6-anhydro graph formula.  This is not a stage-yield or
whole-process material-balance assertion. -/
def SevenWaterFormulaDifference
    (before after : CHOFormula) : Prop :=
  before.carbon = after.carbon ∧
  before.hydrogen = after.hydrogen + 7 * 2 ∧
  before.oxygen = after.oxygen + 7

theorem source_formula_from_atom_recount :
    molecularFormula betaCDStructure =
      { carbon := 42, hydrogen := 70, oxygen := 35 } := by
  native_decide

theorem k_formula_from_atom_recount :
    molecularFormula kStructure =
      { carbon := 42, hydrogen := 56, oxygen := 28 } := by
  native_decide

theorem k_formula_has_seven_water_difference :
    SevenWaterFormulaDifference
      (molecularFormula betaCDStructure) (molecularFormula kStructure) := by
  rw [source_formula_from_atom_recount, k_formula_from_atom_recount]
  norm_num [SevenWaterFormulaDifference]

/-- Potential hydroxyl positions in the source glucose unit. -/
inductive HydroxylPosition where
  | c2 | c3 | c6
  deriving DecidableEq, Fintype, Repr

/-- Oxygen slot belonging to a source hydroxyl position. -/
def hydroxylOxygenSite : HydroxylPosition → GlucoseAtomSite
  | .c2 => .hydroxyO2
  | .c3 => .hydroxyO3
  | .c6 => .hydroxyO6

/-- Hydrogen slot belonging to a source hydroxyl position. -/
def hydroxylHydrogenSite : HydroxylPosition → GlucoseAtomSite
  | .c2 => .hydroxyH2
  | .c3 => .hydroxyH3
  | .c6 => .hydroxyH6

/-- A free OH requires both atoms and their O-H bond to remain present. -/
def IsFreeHydroxyl
    (m : MolecularStructure) (i : BetaUnit) (p : HydroxylPosition) : Prop :=
  m.present (i, hydroxylOxygenSite p) = true ∧
  m.present (i, hydroxylHydrogenSite p) = true ∧
  m.bondOrder (i, hydroxylOxygenSite p) (i, hydroxylHydrogenSite p) = .single

/-- Free-hydroxyl status is decidable for an explicit molecular structure. -/
instance instDecidableIsFreeHydroxyl
    (m : MolecularStructure) (i : BetaUnit) (p : HydroxylPosition) :
    Decidable (IsFreeHydroxyl m i p) := by
  unfold IsFreeHydroxyl
  infer_instance

/-- Number of free hydroxyls on a specified glucopyranoside unit. -/
def freeHydroxylCount (m : MolecularStructure) (i : BetaUnit) : ℕ := by
  exact ((Finset.univ : Finset HydroxylPosition).filter fun p =>
    IsFreeHydroxyl m i p).card

/-- The problem's "only one OH" check, including its identity at C2. -/
def OneC2HydroxylPerUnit (m : MolecularStructure) : Prop :=
  ∀ i : BetaUnit,
    freeHydroxylCount m i = 1 ∧
    IsFreeHydroxyl m i .c2 ∧
    ¬ IsFreeHydroxyl m i .c3 ∧
    ¬ IsFreeHydroxyl m i .c6

theorem k_has_exactly_one_c2_hydroxyl_per_unit :
    OneC2HydroxylPerUnit kStructure := by
  unfold OneC2HydroxylPerUnit
  native_decide

/-- One alpha-1,4 glycosidic link in the retained macrocycle. -/
def HasAlpha14Link
    (m : MolecularStructure) (i : BetaUnit) : Prop :=
  m.bondOrder (i, .c1) (i, .glycosidicO) = .single ∧
  m.bondOrder (i, .glycosidicO) (nextUnit i, .c4) = .single

/-- Each explicitly addressed glycosidic link is decidable. -/
instance instDecidableHasAlpha14Link
    (m : MolecularStructure) (i : BetaUnit) :
    Decidable (HasAlpha14Link m i) := by
  unfold HasAlpha14Link
  infer_instance

/-- The seven cross-boundary links remain a closed alpha-1,4 macrocycle. -/
def RetainsSevenAlpha14Links (m : MolecularStructure) : Prop := by
  exact
    (∀ i : BetaUnit, HasAlpha14Link m i) ∧
    ((Finset.univ : Finset BetaUnit).filter fun i => HasAlpha14Link m i).card = 7

theorem k_retains_seven_alpha14_links :
    RetainsSevenAlpha14Links kStructure := by
  unfold RetainsSevenAlpha14Links
  native_decide

/-- Resolve the ligand named in a stereochemical annotation. -/
def stereoLigandAtom (i : BetaUnit) (p : StereoPosition) : BetaAtom :=
  resolveReference i (alphaDGlucoStereo p).ligand

/-- Resolve its stereogenic carbon. -/
def stereoCenterAtom (i : BetaUnit) (p : StereoPosition) : BetaAtom :=
  (i, (alphaDGlucoStereo p).center)

/-- Every one of the 35 annotations names present, singly bonded graph atoms
and reproduces the alpha-D-gluco face table. -/
def ExplicitStereoSpec (m : MolecularStructure) : Prop :=
  (∀ i p, m.stereo i p = alphaDGlucoStereo p) ∧
  (∀ i p, m.present (stereoCenterAtom i p) = true) ∧
  (∀ i p, m.present (stereoLigandAtom i p) = true) ∧
  (∀ i p,
    m.bondOrder (stereoCenterAtom i p) (stereoLigandAtom i p) = .single)

/-- The number of explicitly annotated tetrahedral stereocentres. -/
def annotatedStereocenterCount : ℕ :=
  Fintype.card BetaUnit * Fintype.card StereoPosition

theorem k_has_explicit_alpha_d_stereochemistry :
    ExplicitStereoSpec kStructure ∧ annotatedStereocenterCount = 35 := by
  constructor
  · refine ⟨fun _ _ => rfl, fun i p => ?_, fun i p => ?_, fun i p => ?_⟩
    · cases p <;> rfl
    · cases p <;>
        simp [stereoLigandAtom, resolveReference, alphaDGlucoStereo,
          kStructure, intramolecular36Cyclization, retainedIn36Product,
          removedBy36Cyclization]
    · cases p <;>
        simp [stereoCenterAtom, stereoLigandAtom, resolveReference,
          alphaDGlucoStereo, kStructure, intramolecular36Cyclization,
          retainedIn36Product, removedBy36Cyclization, cyclized36BondOrder,
          IsNew36Bridge, betaCDStructure, sourceBondOrder,
          IsSourceLocalBond, sourceLocalBondPairs,
          IsSourceCrossBoundaryBond, previousUnit, nextUnit]
  · native_decide

/-- Total formal charge on all present atoms. -/
def totalFormalCharge (m : MolecularStructure) : ℤ :=
  ∑ a : BetaAtom, if m.present a = true then (m.atom a).formalCharge else 0

/-- Total unpaired-electron count on all present atoms. -/
def totalRadicalElectrons (m : MolecularStructure) : ℕ :=
  ∑ a : BetaAtom, if m.present a = true then (m.atom a).radicalElectrons else 0

theorem k_is_neutral_closed_shell :
    totalFormalCharge kStructure = 0 ∧
    totalRadicalElectrons kStructure = 0 := by
  simp [totalFormalCharge, totalRadicalElectrons, kStructure,
    intramolecular36Cyclization, betaCDStructure, sourceAtomDescriptor]

theorem k_graph_is_well_formed_and_valent :
    MolecularGraphWellFormed kStructure ∧ OrdinaryValenceSpec kStructure := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · native_decide
    · native_decide
    · native_decide
    · native_decide
  · unfold OrdinaryValenceSpec
    rintro ⟨i, site⟩ hpresent
    change
      match siteElement site with
      | .hydrogen => valenceAt kStructure (i, site) = 1
      | .carbon => valenceAt kStructure (i, site) = 4
      | .oxygen => valenceAt kStructure (i, site) = 2
    fin_cases i <;> cases site <;>
      simp [kStructure, intramolecular36Cyclization, retainedIn36Product,
        removedBy36Cyclization] at hpresent <;>
      simp only [siteElement] <;> native_decide

/-! ## Chair candidate domain and favourable conformation -/

/-- The two ring-flip chair alternatives; this finite domain comes from the
ordinary chair pair, not from a candidate-named singleton. -/
inductive ChairConformation where
  | fourCOne
  | oneCFour
  deriving DecidableEq, Fintype, Repr

/-- Whether the named stereodirecting substituent is axial or equatorial. -/
inductive ChairDisposition where
  | axial
  | equatorial
  deriving DecidableEq, Fintype, Repr

/-- Axial face at each stereogenic carbon in the two ring-flip chairs. -/
def axialFace : ChairConformation → StereoPosition → RingFace
  | .fourCOne, .c1 => .bottom
  | .fourCOne, .c2 => .top
  | .fourCOne, .c3 => .bottom
  | .fourCOne, .c4 => .top
  | .fourCOne, .c5 => .bottom
  | .oneCFour, .c1 => .top
  | .oneCFour, .c2 => .bottom
  | .oneCFour, .c3 => .top
  | .oneCFour, .c4 => .bottom
  | .oneCFour, .c5 => .top

/-- Disposition computed from the retained face configuration and a chair. -/
def substituentDisposition
    (chair : ChairConformation) (p : StereoPosition) : ChairDisposition :=
  if (alphaDGlucoStereo p).ligandFace = axialFace chair p then
    .axial
  else
    .equatorial

/-- Transparent bridge-geometry score: the 3,6 ring asks the C3-O and C5-C6
attachments to occupy their inward axial dispositions.  Each mismatch counts
once; this is a structural comparison, not a claimed energy in physical units. -/
def bridgeMismatchCount (chair : ChairConformation) : ℕ :=
  (if substituentDisposition chair .c3 = .axial then 0 else 1) +
  (if substituentDisposition chair .c5 = .axial then 0 else 1)

/-- A favourable chair is the unique strict minimizer of the transparent
bridge-mismatch score over both ordinary chair alternatives. -/
def IsFavorableChair (chair : ChairConformation) : Prop :=
  ∀ other : ChairConformation,
    other ≠ chair → bridgeMismatchCount chair < bridgeMismatchCount other

theorem oneCFour_is_favorable_for_per36_anhydro :
    IsFavorableChair .oneCFour := by
  intro other hne
  cases other
  · native_decide
  · exact (hne rfl).elim

/-- A completed source drawing consists of its atom-complete molecular graph
and one chair label for every one of the seven identical residues. -/
structure CompletedKDrawing where
  molecule : MolecularStructure
  chair : BetaUnit → ChairConformation

/-- The derived drawing candidate. -/
def kDrawing : CompletedKDrawing :=
  { molecule := kStructure
    chair := fun _ => .oneCFour }

/-! ## Requested-output contracts -/

/-- Raw symbolic proposition for the first requested output. -/
def ChairConformationRawResult : Prop :=
  IsFavorableChair .oneCFour ∧
  ∀ i : BetaUnit, kDrawing.chair i = .oneCFour

/-- Exact-symbolic reporting does not round or weaken the raw chair result. -/
def ChairConformationReportedResult : Prop :=
  ChairConformationRawResult

theorem chair_conformation_raw_result : ChairConformationRawResult := by
  exact ⟨oneCFour_is_favorable_for_per36_anhydro, fun _ => rfl⟩

theorem chair_conformation_reported_result :
    ChairConformationReportedResult := by
  exact chair_conformation_raw_result

/-- Full, independently checkable specification of the second requested
output.  It covers the source arrow, every atom and bond order, all five
stereocentres per residue, charge/radical state, formula, free OH identity,
and all seven cross-boundary glycosidic links. -/
def KStructureSpec (m : MolecularStructure) : Prop :=
  SourceArrowPer36AnhydroCompatibility m ∧
  MolecularGraphWellFormed m ∧
  OrdinaryValenceSpec m ∧
  molecularFormula m = { carbon := 42, hydrogen := 56, oxygen := 28 } ∧
  SevenWaterFormulaDifference (molecularFormula betaCDStructure)
    (molecularFormula m) ∧
  OneC2HydroxylPerUnit m ∧
  RetainsSevenAlpha14Links m ∧
  ExplicitStereoSpec m ∧
  annotatedStereocenterCount = 35 ∧
  totalFormalCharge m = 0 ∧
  totalRadicalElectrons m = 0

/-- Raw symbolic proposition for the complete structure of `K`. -/
def StructureKRawResult : Prop :=
  KStructureSpec kDrawing.molecule

/-- Exact-symbolic reporting preserves the complete graph-and-stereo result. -/
def StructureKReportedResult : Prop :=
  StructureKRawResult

theorem structure_k_raw_result : StructureKRawResult := by
  refine ⟨sourceArrow_constructs_k, k_graph_is_well_formed_and_valent.1,
    k_graph_is_well_formed_and_valent.2, k_formula_from_atom_recount,
    k_formula_has_seven_water_difference,
    k_has_exactly_one_c2_hydroxyl_per_unit, k_retains_seven_alpha14_links,
    k_has_explicit_alpha_d_stereochemistry.1,
    k_has_explicit_alpha_d_stereochemistry.2,
    k_is_neutral_closed_shell.1, k_is_neutral_closed_shell.2⟩

theorem structure_k_reported_result : StructureKReportedResult := by
  exact structure_k_raw_result

/-- Combined carrier covering both requested outputs in source order. -/
theorem problem_icho_2026_t9_a2 :
    ChairConformationReportedResult ∧ StructureKReportedResult := by
  exact ⟨chair_conformation_reported_result, structure_k_reported_result⟩

end

end IChO2026Problems.T9A2
