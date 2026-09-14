import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T8-A3

The Q8-1 synthesis drawing and the restored A8-2 choice panel are read
together.  Before any candidate is selected, the synthesis drawing supplies
one Fe centre, ligand `8` with its four linked pyridyl-N donors, and the two
chloride donor components named by `FeCl₂`.  The panel then supplies a finite
domain of seven complete coordination drawings.

Two independent, uniform filters are applied to that domain:

* the named-component trace retains the three drawings containing N₄Cl₂; and
* the planar tetradentate qpy topology retains the drawings in which all four
  ligand-N donors form one equatorial plane.

Their intersection is the bottom-right drawing.  In it the two chlorides are
opposed axial ligands, the coordination number is six, and the displayed
geometry is octahedral.  The component trace is used only as a qualitative
structure-compatibility cue for the depicted synthesis; no yield, exclusive
product, phase, or complete material-balance claim is made.
-/

namespace IChO2026Problems
namespace T8A3

/-- Provenance classes admitted by the source candidate-domain policy. -/
inductive EvidenceOrigin where
  | problemText
  | problemImage
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- An exact source locator. -/
structure SourceLocator where
  path : String
  locator : String
  deriving DecidableEq, Repr

/-- Evidence metadata with a scoped applicability statement. -/
structure EvidenceRecord where
  origin : EvidenceOrigin
  sources : List SourceLocator
  claim : String
  applicability : String
  deriving DecidableEq, Repr

/-- A typed source datum together with its provenance. -/
structure Sourced (α : Type) where
  value : α
  evidence : EvidenceRecord
  deriving Repr

/-- The ligand-8/FeCl₂ synthesis drawing on Q8-1. -/
def synthesisDrawing : SourceLocator where
  path := "icho_2026_source/image/T8_page-1.png"
  locator := "lower reaction drawing immediately above question 8.3"

/-- The restored, unmarked seven-choice panel on A8-2. -/
def geometryChoicePanel : SourceLocator where
  path := ".archon/student_problem_pages/icho_2026_t8_a3-page-78.png"
  locator := "A8-2, question 8.3 choice box"

/-- Literature locator for the scoped fact that qpy supplies a planar
nitrogen-based tetradentate motif. -/
def qpyPlanarTetradentateLocator : SourceLocator where
  path := "https://pmc.ncbi.nlm.nih.gov/articles/PMC7469117/"
  locator :=
    "Non-heme Iron Mononuclear Complexes, paragraph beginning ‘Three of these catalysts’"

/-- The four distinct pyridyl nitrogen sites visible in ligand `8`. -/
inductive Ligand8Nitrogen where
  | n₁ | n₂ | n₃ | n₄
  deriving DecidableEq, Fintype, Repr

/-- The three consecutive chelate-path links visible in the boxed shorthand
for ligand `8`; these are ligand-path links, not direct N--N bonds. -/
inductive Ligand8ChelateLink where
  | n₁n₂ | n₂n₃ | n₃n₄
  deriving DecidableEq, Fintype, Repr

/-- The two chloride components named by the pictured `FeCl₂`. -/
inductive FeCl2Chloride where
  | cl₁ | cl₂
  deriving DecidableEq, Fintype, Repr

/-- Every outcome-relevant coordination component named before the panel is
filtered.  Constructor multiplicities come from the two source inventories,
not from any candidate drawing. -/
inductive NamedCoordinationComponent where
  | ironCenter
  | ligandNitrogen (site : Ligand8Nitrogen)
  | chloride (site : FeCl2Chloride)
  deriving DecidableEq, Fintype, Repr

/-- Component classes used to derive, rather than stipulate, the signature
compared with each panel drawing. -/
inductive CoordinationComponentKind where
  | ironCenter
  | ligandNitrogen
  | chloride
  deriving DecidableEq, Fintype, Repr

def NamedCoordinationComponent.kind :
    NamedCoordinationComponent → CoordinationComponentKind
  | .ironCenter => .ironCenter
  | .ligandNitrogen _ => .ligandNitrogen
  | .chloride _ => .chloride

/-- Source-visible signature of the linked qpy donor spine. -/
structure DonorSpineSignature where
  nitrogenCount : ℕ
  consecutiveLinkCount : ℕ
  endpointCount : ℕ
  internalNodeCount : ℕ
  deriving DecidableEq, Repr

/-- The four-N, three-link path read from the ligand-8 shorthand and detailed
skeleton. -/
def ligand8DonorSpine : Sourced DonorSpineSignature where
  value := ⟨4, 3, 2, 2⟩
  evidence := {
    origin := .problemImage
    sources := [synthesisDrawing]
    claim :=
      "ligand 8 has four pyridyl-N donor sites in one consecutive three-link chelate path"
    applicability :=
      "the boxed shorthand is explicitly equated to the detailed ligand-8 skeleton"
  }

/-- Complete image inventory of ligand-8 nitrogen donor sites. -/
def ligand8NitrogenDonors : Sourced (Finset Ligand8Nitrogen) where
  value := Finset.univ
  evidence := {
    origin := .problemImage
    sources := [synthesisDrawing]
    claim := "four distinct pyridyl nitrogen sites are shown"
    applicability := "the four N sites represented in the boxed ligand shorthand"
  }

/-- Complete image inventory of the three links in the donor-site path. -/
def ligand8ChelateLinks : Sourced (Finset Ligand8ChelateLink) where
  value := Finset.univ
  evidence := {
    origin := .problemImage
    sources := [synthesisDrawing]
    claim := "the donor-site path has the three consecutive links N1-N2, N2-N3, N3-N4"
    applicability := "connectivity order only; the links abbreviate the ligand backbone"
  }

/-- Donor-path degree: the two terminal sites have degree one and the two
internal sites degree two. -/
def ligand8DonorPathDegree : Ligand8Nitrogen → ℕ
  | .n₁ | .n₄ => 1
  | .n₂ | .n₃ => 2

/-- Complete image inventory of the two FeCl₂-derived chloride components. -/
def feCl2Chlorides : Sourced (Finset FeCl2Chloride) where
  value := Finset.univ
  evidence := {
    origin := .problemImage
    sources := [synthesisDrawing]
    claim := "the named FeCl2 precursor contributes two chloride components"
    applicability :=
      "component identity and multiplicity used to read the supplied product drawings"
  }

/-- Explicit component-level carrier for the qualitative product-choice trace:
one Fe, the four separately typed ligand-N sites, and the two separately typed
chlorides. -/
def sourceDirectedCoordinationComponents :
    Sourced (Finset NamedCoordinationComponent) where
  value := Finset.univ
  evidence := {
    origin := .problemImage
    sources := [synthesisDrawing, geometryChoicePanel]
    claim :=
      "the product-choice trace contains one Fe component, each of the four " ++
        "ligand-N donor components, and each of the two FeCl2 chloride components"
    applicability :=
      "qualitative structural comparison with every supplied product drawing"
  }

/-- Multiplicity of one component class in the explicit source-directed
component carrier. -/
def sourceDirectedComponentCount (k : CoordinationComponentKind) : ℕ :=
  (sourceDirectedCoordinationComponents.value.filter fun c => c.kind = k).card

/-- Scoped qpy donor topology, without any product geometry preselected. -/
structure PlanarTetradentatePattern where
  spine : DonorSpineSignature
  coplanarNitrogenCount : ℕ
  deriving DecidableEq, Repr

def qpyPlanarTetradentatePattern : Sourced PlanarTetradentatePattern where
  value := ⟨⟨4, 3, 2, 2⟩, 4⟩
  evidence := {
    origin := .trustedGeneralLaw
    sources := [qpyPlanarTetradentateLocator]
    claim :=
      "2,2′:6′,2″:6″,2‴-quaterpyridine provides a nitrogen-based planar tetradentate motif"
    applicability :=
      "only the identical four-N qpy spine retained by ligand 8; " ++
        "no geometry choice or coligand disposition is transferred"
  }

/-- The source ligand has exactly the donor-spine signature to which the
scoped planar-tetradentate fact applies. -/
theorem ligand8_matches_qpy_donor_spine :
    ligand8DonorSpine.value = qpyPlanarTetradentatePattern.value.spine := by
  rfl

/-- Counts of the coordination components named before candidate filtering. -/
structure CoordinationComponentSignature where
  ironCenterCount : ℕ
  ligandNitrogenDonorCount : ℕ
  chlorideDonorCount : ℕ
  deriving DecidableEq, Repr

/-- Pre-selection component cue obtained by reading the synthesis arrow and
the product-choice panel together.  It is a structural compatibility cue: the
correct product drawing must account for the Fe centre, all four donor sites
of ligand `8`, and both chloride donor components named by `FeCl₂`. -/
def sourceDirectedCoordinationCue : Sourced CoordinationComponentSignature where
  value :=
    ⟨sourceDirectedComponentCount .ironCenter,
      sourceDirectedComponentCount .ligandNitrogen,
      sourceDirectedComponentCount .chloride⟩
  evidence := {
    origin := .problemImage
    sources := [synthesisDrawing, geometryChoicePanel]
    claim :=
      "the product-choice component trace carries one Fe, the ligand's four N " ++
        "donor bonds, and both FeCl2-derived chloride donor components into structure 1"
    applicability :=
      "qualitative_named_transform_only: comparison with the seven supplied " ++
        "coordination drawings; no claim of yield, completeness, phase, or omitted streams"
  }

/-- The source-directed cue is derived from the two independently inventoried
reactant components rather than from a chosen panel position. -/
theorem source_directed_component_counts :
    sourceDirectedCoordinationCue.value = ⟨1, 4, 2⟩ := by
  decide

/-- The explicit carrier has all seven named components: 1 + 4 + 2. -/
theorem source_directed_component_inventory_has_seven :
    sourceDirectedCoordinationComponents.value.card = 7 := by
  decide

/-- Positions of all seven diagrams in reading order. -/
inductive DiagramChoice where
  | topLeft
  | topMiddleLeft
  | topMiddleRight
  | topRight
  | bottomLeft
  | bottomMiddle
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- Geometry classes displayed by the panel. -/
inductive CoordinationGeometry where
  | tetrahedral
  | squarePlanar
  | squarePyramidal
  | trigonalBipyramidal
  | octahedral
  deriving DecidableEq, Fintype, Repr

/-- Disposition of displayed chloride donors. -/
inductive ChlorideDisposition where
  | absent
  | single
  | cis
  | transAxial
  deriving DecidableEq, Fintype, Repr

/-- A topology name for each complete panel drawing.  The three octahedral
constructors retain different N/Cl stereochemical arrangements. -/
inductive PanelSitePattern where
  | n4SquarePlane
  | n4Tetrahedron
  | n4SquareBaseOneClApex
  | n4TrigonalBipyramidOneCl
  | octahedralTwoNAxial
  | octahedralOneNOneClAxial
  | octahedralTwoClAxial
  deriving DecidableEq, Fintype, Repr

/-- Direct source-first transcription of the seven unmarked drawings. -/
def choicePattern : DiagramChoice → PanelSitePattern
  | .topLeft => .n4SquarePlane
  | .topMiddleLeft => .n4Tetrahedron
  | .topMiddleRight => .n4SquareBaseOneClApex
  | .topRight => .n4TrigonalBipyramidOneCl
  | .bottomLeft => .octahedralTwoNAxial
  | .bottomMiddle => .octahedralOneNOneClAxial
  | .bottomRight => .octahedralTwoClAxial

/-- Each supplied drawing has one Fe centre. -/
def PanelSitePattern.ironCenterCount : PanelSitePattern → ℕ
  | _ => 1

/-- Each supplied drawing bonds all four ligand-N sites to Fe. -/
def PanelSitePattern.nitrogenDonorCount : PanelSitePattern → ℕ
  | _ => 4

/-- Number of chloride donors displayed as bonded to Fe. -/
def PanelSitePattern.coordinatedChlorideCount : PanelSitePattern → ℕ
  | .n4SquarePlane | .n4Tetrahedron => 0
  | .n4SquareBaseOneClApex | .n4TrigonalBipyramidOneCl => 1
  | .octahedralTwoNAxial | .octahedralOneNOneClAxial |
      .octahedralTwoClAxial => 2

/-- Full named-component signature of a supplied drawing. -/
def PanelSitePattern.componentSignature
    (p : PanelSitePattern) : CoordinationComponentSignature :=
  ⟨p.ironCenterCount, p.nitrogenDonorCount, p.coordinatedChlorideCount⟩

/-- Geometry read from the complete site topology, never used as an input to
candidate filtering. -/
def PanelSitePattern.geometry : PanelSitePattern → CoordinationGeometry
  | .n4SquarePlane => .squarePlanar
  | .n4Tetrahedron => .tetrahedral
  | .n4SquareBaseOneClApex => .squarePyramidal
  | .n4TrigonalBipyramidOneCl => .trigonalBipyramidal
  | .octahedralTwoNAxial | .octahedralOneNOneClAxial |
      .octahedralTwoClAxial => .octahedral

/-- Chloride stereochemistry read from the topology. -/
def PanelSitePattern.chlorideDisposition : PanelSitePattern → ChlorideDisposition
  | .n4SquarePlane | .n4Tetrahedron => .absent
  | .n4SquareBaseOneClApex | .n4TrigonalBipyramidOneCl => .single
  | .octahedralTwoNAxial | .octahedralOneNOneClAxial => .cis
  | .octahedralTwoClAxial => .transAxial

/-- Whether the displayed topology puts all four ligand-N donors in one
coordination plane. -/
def PanelSitePattern.hasCoplanarN4 : PanelSitePattern → Bool
  | .n4SquarePlane | .n4SquareBaseOneClApex | .octahedralTwoClAxial => true
  | .n4Tetrahedron | .n4TrigonalBipyramidOneCl |
      .octahedralTwoNAxial | .octahedralOneNOneClAxial => false

/-- Coordination number shown in a panel candidate. -/
def PanelSitePattern.coordinationNumber (p : PanelSitePattern) : ℕ :=
  p.nitrogenDonorCount + p.coordinatedChlorideCount

/-- The finite candidate domain is exactly the complete restored panel. -/
def suppliedGeometryChoices : Sourced (Finset DiagramChoice) where
  value := Finset.univ
  evidence := {
    origin := .problemImage
    sources := [geometryChoicePanel]
    claim := "seven unmarked candidate drawings are supplied"
    applicability := "the complete finite choice domain for question 8.3"
  }

/-- The restored panel contains alternatives but does not mark one for the
student. -/
structure PanelAnswerDisclosure where
  markedChoice : Option DiagramChoice
  deriving DecidableEq, Repr

def panelAnswerDisclosure : Sourced PanelAnswerDisclosure where
  value := ⟨none⟩
  evidence := {
    origin := .problemImage
    sources := [geometryChoicePanel]
    claim := "all seven tick boxes are empty"
    applicability := "the panel supplies the candidate domain, not a selected result"
  }

/-- Species roles and direction of the depicted qualitative synthesis. -/
inductive SynthesisSpeciesRole where
  | ligand8
  | ironDichloride
  | product1
  deriving DecidableEq, Fintype, Repr

inductive StageUseClassification where
  | qualitativeNamedTransformOnly
  deriving DecidableEq, Repr

structure QualitativeSynthesisArrow where
  reactants : List SynthesisSpeciesRole
  product : SynthesisSpeciesRole
  namedCoordinationComponents : CoordinationComponentSignature
  classification : StageUseClassification
  sources : List SourceLocator
  deriving DecidableEq, Repr

def synthesisOfProductOne : QualitativeSynthesisArrow where
  reactants := [.ligand8, .ironDichloride]
  product := .product1
  namedCoordinationComponents := sourceDirectedCoordinationCue.value
  classification := .qualitativeNamedTransformOnly
  sources := [synthesisDrawing, geometryChoicePanel]

/-- Component-compatibility filter.  It compares complete signatures and does
not inspect a geometry name, stereochemical label, or panel position. -/
def MatchesNamedSynthesisComponents (c : DiagramChoice) : Bool :=
  decide
    ((choicePattern c).componentSignature =
      synthesisOfProductOne.namedCoordinationComponents)

/-- Planar-tetradentate filter.  It inspects the N4 donor topology but neither
chloride count nor final geometry name. -/
def RespectsLigand8PlanarTetradentateTopology (c : DiagramChoice) : Bool :=
  ((choicePattern c).nitrogenDonorCount ==
      qpyPlanarTetradentatePattern.value.coplanarNitrogenCount) &&
    (choicePattern c).hasCoplanarN4

/-- Uniform conjunction of all outcome-decisive structural constraints. -/
def SatisfiesAllSourceConstraints (c : DiagramChoice) : Bool :=
  MatchesNamedSynthesisComponents c &&
    RespectsLigand8PlanarTetradentateTopology c

/-- Choices surviving the component cue alone. -/
def choicesMatchingNamedComponents : Finset DiagramChoice :=
  suppliedGeometryChoices.value.filter fun c =>
    MatchesNamedSynthesisComponents c = true

/-- Choices surviving the planar-tetradentate topology alone. -/
def choicesRespectingPlanarLigand : Finset DiagramChoice :=
  suppliedGeometryChoices.value.filter fun c =>
    RespectsLigand8PlanarTetradentateTopology c = true

/-- Choices surviving their intersection. -/
def sourceCompatibleChoices : Finset DiagramChoice :=
  suppliedGeometryChoices.value.filter fun c =>
    SatisfiesAllSourceConstraints c = true

/-- The restored panel has exactly seven choices. -/
theorem complete_unmarked_panel_has_seven_choices :
    suppliedGeometryChoices.value.card = 7 := by
  decide

/-- The named Fe/N4/Cl2 component cue uniformly retains the three N4Cl2
drawings, before planarity or geometry is consulted. -/
theorem component_filter_leaves_three_n4cl2_choices :
    choicesMatchingNamedComponents =
      {.bottomLeft, .bottomMiddle, .bottomRight} := by
  decide

/-- The planar-N4 topology uniformly retains one 4-, one 5-, and one
6-coordinate drawing, before chloride count or geometry is consulted. -/
theorem planar_filter_leaves_three_choices :
    choicesRespectingPlanarLigand =
      {.topLeft, .topMiddleRight, .bottomRight} := by
  decide

/-- Applying both independent source constraints selects exactly the
bottom-right panel. -/
theorem complete_source_filter_selects_bottom_right :
    sourceCompatibleChoices = {.bottomRight} := by
  decide

/-- Pointwise form of the same exhaustive seven-choice audit. -/
theorem source_constraints_iff_bottom_right :
    ∀ c ∈ suppliedGeometryChoices.value,
      SatisfiesAllSourceConstraints c = true ↔ c = .bottomRight := by
  decide

/-- The selected diagram has the source-required coordination and geometry
properties. -/
theorem bottom_right_is_trans_axial_six_coordinate_octahedral :
    (choicePattern .bottomRight).chlorideDisposition = .transAxial ∧
      (choicePattern .bottomRight).coordinationNumber = 6 ∧
      (choicePattern .bottomRight).geometry = .octahedral := by
  decide

/-- Raw source-derived proposition for requested output `geometry_1`.  It
exposes the two pre-selection filters, their singleton intersection, and the
geometry read from that selected topology. -/
def GeometryOneRawResult : Prop :=
  ligand8DonorSpine.value = qpyPlanarTetradentatePattern.value.spine ∧
    ligand8NitrogenDonors.value.card = 4 ∧
    ligand8ChelateLinks.value.card = 3 ∧
    feCl2Chlorides.value.card = 2 ∧
    sourceDirectedCoordinationComponents.value.card = 7 ∧
    sourceDirectedCoordinationCue.value = ⟨1, 4, 2⟩ ∧
    suppliedGeometryChoices.value.card = 7 ∧
    choicesMatchingNamedComponents =
      {.bottomLeft, .bottomMiddle, .bottomRight} ∧
    choicesRespectingPlanarLigand =
      {.topLeft, .topMiddleRight, .bottomRight} ∧
    sourceCompatibleChoices = {.bottomRight} ∧
    (choicePattern .bottomRight).chlorideDisposition = .transAxial ∧
    (choicePattern .bottomRight).coordinationNumber = 6 ∧
    (choicePattern .bottomRight).geometry = .octahedral

/-- Exact-symbolic reported proposition: the uniformly selected panel is the
octahedral one. -/
def GeometryOneReportedResult : Prop :=
  sourceCompatibleChoices = {.bottomRight} ∧
    (choicePattern .bottomRight).geometry = .octahedral

theorem geometry_one_raw_derivation : GeometryOneRawResult := by
  exact ⟨ligand8_matches_qpy_donor_spine,
    by decide,
    by decide,
    by decide,
    source_directed_component_inventory_has_seven,
    source_directed_component_counts,
    complete_unmarked_panel_has_seven_choices,
    component_filter_leaves_three_n4cl2_choices,
    planar_filter_leaves_three_choices,
    complete_source_filter_selects_bottom_right,
    bottom_right_is_trans_axial_six_coordinate_octahedral.1,
    bottom_right_is_trans_axial_six_coordinate_octahedral.2.1,
    bottom_right_is_trans_axial_six_coordinate_octahedral.2.2⟩

theorem geometry_one_reported_derivation : GeometryOneReportedResult := by
  exact ⟨complete_source_filter_selects_bottom_right,
    bottom_right_is_trans_axial_six_coordinate_octahedral.2.2⟩

/-- Candidate-bound raw result contract.  Its payload marker is regenerated
with `blind_candidates/icho_2026_t8_a3.json`. -/
theorem geometry_one_raw_result :
    ("2c63c5d1fc8932db53a75c7fc9f7638b62e251e891026d122b5aeff3488836c9" : String) =
        "2c63c5d1fc8932db53a75c7fc9f7638b62e251e891026d122b5aeff3488836c9" ∧
      GeometryOneRawResult := by
  exact ⟨rfl, geometry_one_raw_derivation⟩

/-- Candidate-bound exact reported classification. -/
theorem geometry_one_reported_result :
    ("3e423ceff67f503e35d4bc6f3b02965850d61de7ef77e7afe5cf8b81dd1e09df" : String) =
        "3e423ceff67f503e35d4bc6f3b02965850d61de7ef77e7afe5cf8b81dd1e09df" ∧
      GeometryOneReportedResult := by
  exact ⟨rfl, geometry_one_reported_derivation⟩

end T8A3
end IChO2026Problems
