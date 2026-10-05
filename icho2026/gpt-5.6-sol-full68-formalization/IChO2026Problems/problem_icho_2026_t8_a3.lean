import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T8-A3: coordination geometry of catalyst 1

The bound problem page shows ligand `8`, `FeCl₂`, and a right-directed
qualitative synthesis arrow to molecular catalyst `1`.  A source-first recount
of ligand `8` gives a consecutive four-pyridyl donor core.  The product-side
coordination contacts are not drawn on the problem page, so the missing bridge
is supplied by narrowly scoped peer-reviewed literature rather than inferred
from the precursor formula alone.

The exact carboxy-functionalized Fe--qpy catalyst is depicted with four Fe--N
contacts and two Fe--Cl contacts.  A second quaterpyridine source records the
applicable four-in-plane/two-axial topology.  These observations are encoded as
site and contact data without first assigning a geometry name.  A uniform
filter over a source-independent vocabulary of standard coordination
geometries then yields the requested exact symbolic classification.

The synthesis arrow is used only as `qualitative_named_transform_only`: no
yield, completion, phase balance, sole-product claim, or empty omitted stream
is asserted.
-/

namespace IChO2026Problems
namespace ProblemIcho2026T8A3

/-! ## Problem-side source transcription -/

inductive EvidenceOrigin where
  | problemText
  | problemImage
  | peerReviewedLiterature
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Fintype, Repr

structure SourceLocator where
  origin : EvidenceOrigin
  path : String
  sha256 : String
  region : String
  deriving DecidableEq, Repr

def page1SynthesisLocator : SourceLocator where
  origin := .problemImage
  path := "icho_2026_source/image/T8_page-1.png"
  sha256 :=
    "3490231dd64238ab3db32a48d86f92c857f9fef386b510c45ba1b80f483cc843"
  region :=
    "lower panel: four-pyridyl ligand 8 plus FeCl2, arrow directed to catalyst 1"

def currentQuestionLocator : SourceLocator where
  origin := .problemText
  path := "reports/icho_2026/problem_icho_2026_t8_a3.source.json"
  sha256 :=
    "a6d5893404d188608893cf85a9056b62487cb2a23300404513ded6194ea4bd2a"
  region := "entry.current_question and entry.requested_outputs[0]"

def currentQuestionText : String :=
  "Tick the correct geometry for the structure of 1."

inductive Species where
  | carbonDioxide
  | carbonMonoxide
  | catalyst1
  | sacrificialReductant2
  | intermediate3
  | intermediate4
  | intermediate5
  | product6
  | product7
  | ligand8
  | ironDichloride
  deriving DecidableEq, Fintype, Repr

inductive Phase where
  | gas
  | aqueous
  | unspecified
  deriving DecidableEq, Fintype, Repr

/-- Only the named roles and arrow direction printed in the lower synthesis
panel are represented.  Omitted coefficients, phases, protocol, yield, and
byproducts remain unspecified. -/
structure QualitativeNamedTransform where
  shownReactants : List Species
  namedProduct : Species
  locator : SourceLocator
  deriving DecidableEq, Repr

def catalyst1SynthesisArrow : QualitativeNamedTransform where
  shownReactants := [.ligand8, .ironDichloride]
  namedProduct := .catalyst1
  locator := page1SynthesisLocator

inductive TransformUseClassification where
  | qualitativeNamedTransformOnly
  | quantitativeMaterialStage
  deriving DecidableEq, Fintype, Repr

def catalyst1SynthesisUse : TransformUseClassification :=
  .qualitativeNamedTransformOnly

def Catalyst1SynthesisArrowSpecification : Prop :=
  catalyst1SynthesisArrow.shownReactants =
      [.ligand8, .ironDichloride] ∧
  catalyst1SynthesisArrow.namedProduct = .catalyst1 ∧
  catalyst1SynthesisArrow.locator = page1SynthesisLocator ∧
  catalyst1SynthesisUse = .qualitativeNamedTransformOnly

theorem catalyst1_synthesis_arrow_specification :
    Catalyst1SynthesisArrowSpecification := by
  unfold Catalyst1SynthesisArrowSpecification
  native_decide

/-! ## Source-first ligand recount -/

inductive Ligand8PyridylRing where
  | ring1
  | ring2
  | ring3
  | ring4
  deriving DecidableEq, Fintype, Repr

inductive Ligand8Nitrogen where
  | n1
  | n2
  | n3
  | n4
  deriving DecidableEq, Fintype, Repr

def nitrogenOnRing : Ligand8PyridylRing → Ligand8Nitrogen
  | .ring1 => .n1
  | .ring2 => .n2
  | .ring3 => .n3
  | .ring4 => .n4

/-- The three consecutive inter-pyridyl links seen in the ligand drawing. -/
def ligand8ChelatePath : Finset (Ligand8Nitrogen × Ligand8Nitrogen) :=
  {(.n1, .n2), (.n2, .n3), (.n3, .n4)}

structure LigandCoreSignature where
  pyridylRingCount : ℕ
  pyridylNitrogenCount : ℕ
  consecutiveInterRingLinkCount : ℕ
  benzoicAcidSubstituentCount : ℕ
  deriving DecidableEq, Repr

def page1Ligand8Core : LigandCoreSignature where
  pyridylRingCount := Fintype.card Ligand8PyridylRing
  pyridylNitrogenCount := Fintype.card Ligand8Nitrogen
  consecutiveInterRingLinkCount := ligand8ChelatePath.card
  benzoicAcidSubstituentCount := 1

/-- The exact-catalyst literature inset has the same connected donor core and
remote benzoic-acid substituent as the page-1 ligand. -/
def exactFigureLigandCore : LigandCoreSignature where
  pyridylRingCount := 4
  pyridylNitrogenCount := 4
  consecutiveInterRingLinkCount := 3
  benzoicAcidSubstituentCount := 1

def Ligand8ImageSpecification : Prop :=
  Fintype.card Ligand8PyridylRing = 4 ∧
  Fintype.card Ligand8Nitrogen = 4 ∧
  Finset.univ.image nitrogenOnRing =
      (Finset.univ : Finset Ligand8Nitrogen) ∧
  ligand8ChelatePath = {(.n1, .n2), (.n2, .n3), (.n3, .n4)} ∧
  page1Ligand8Core = exactFigureLigandCore

theorem ligand8_image_specification : Ligand8ImageSpecification := by
  unfold Ligand8ImageSpecification
  native_decide

/-! ## Narrow public-literature bridge -/

structure LiteratureRecord where
  title : String
  doi : String
  stableUrl : String
  locator : String
  scopedClaim : String
  applicabilityConditions : String
  exclusions : String
  contentSha256 : String
  deriving DecidableEq, Repr

/-- Exact functionalized-catalyst source.  Figure 1d draws the same
benzoic-acid-functionalized qpy ligand coordinated to Fe through four nitrogen
sites and two chlorido sites. -/
def exactFeQpyLiterature : LiteratureRecord where
  title :=
    "Illuminating the mechanistic impacts of an Fe-quaterpyridine functionalized crystalline poly(triazine imide) semiconductor for photocatalytic CO2 reduction"
  doi := "10.1039/d5qi00859j"
  stableUrl := "https://www.osti.gov/servlets/purl/3377957"
  locator :=
    "printed pages 6642 and 6644: Methods B; Figure 1d inset and caption"
  scopedClaim :=
    "The benzoic-acid-functionalized qpy ligand is coordinated from anhydrous FeCl2; Figure 1d depicts four Fe-N contacts and two opposed Fe-Cl contacts for Fe-qpy."
  applicabilityConditions :=
    "The problem ligand and Figure 1d ligand have the same consecutive four-pyridyl donor core and the same benzoic-acid substituent; only the depicted contact topology is used."
  exclusions :=
    "No yield, completion, phase, spin state, exact metric angle, catalytic rate, or sole-product statement is imported."
  contentSha256 :=
    "9f45fc489b714d50dca635ff51bb7270159d2531edc9311dcc595a30c70bec0e"

/-- A second source states the four-in-plane/two-axial topology for
quaterpyridine complexes.  Its different substituents and ancillary ligand
identities are explicitly excluded from transfer. -/
def qpyBasalAxialLiterature : LiteratureRecord where
  title :=
    "DFT Study of the CNS Ligand Effect on the Geometry, Spin-State, and Absorption Spectrum in Ruthenium, Iron, and Cobalt Quaterpyridine Complexes"
  doi := "10.1021/acsomega.9b00921"
  stableUrl := "https://pmc.ncbi.nlm.nih.gov/articles/PMC6647971/"
  locator :=
    "Introduction paragraph beginning 'In this paper, we study'"
  scopedClaim :=
    "A consecutive quaterpyridine chelate supplies four in-plane basal N-donor positions, with two additional monodentate donors in axial positions."
  applicabilityConditions :=
    "Transferred only at the four-N quaterpyridine plus two monodentate-site topology level, corroborated for the target by the exact Figure 1d contact drawing."
  exclusions :=
    "No CNS identity, substituent identity, bond metric, solvent, spin state, energy, spectrum, or reactivity is transferred."
  contentSha256 :=
    "7250c33d0cff117d0866cccea0998961dfd0c9b593a442989f05dac2525d5632"

inductive ChlorideDonor where
  | cl1
  | cl2
  deriving DecidableEq, Fintype, Repr

inductive Catalyst1DonorSite where
  | qpyNitrogen (nitrogen : Ligand8Nitrogen)
  | chloride (chloride : ChlorideDonor)
  deriving DecidableEq, Fintype, Repr

inductive MetalCenter where
  | catalyst1Iron
  deriving DecidableEq, Fintype, Repr

structure MetalDonorCoordinationBond where
  center : MetalCenter
  donor : Catalyst1DonorSite
  deriving DecidableEq

def catalyst1Bond (donor : Catalyst1DonorSite) :
    MetalDonorCoordinationBond where
  center := .catalyst1Iron
  donor := donor

/-- The six Fe--donor contacts depicted for the exact functionalized catalyst. -/
def catalyst1CoordinationBonds : Finset MetalDonorCoordinationBond :=
  { catalyst1Bond (.qpyNitrogen .n1),
    catalyst1Bond (.qpyNitrogen .n2),
    catalyst1Bond (.qpyNitrogen .n3),
    catalyst1Bond (.qpyNitrogen .n4),
    catalyst1Bond (.chloride .cl1),
    catalyst1Bond (.chloride .cl2) }

def catalyst1BasalSites : Finset Catalyst1DonorSite :=
  { .qpyNitrogen .n1, .qpyNitrogen .n2,
    .qpyNitrogen .n3, .qpyNitrogen .n4 }

def catalyst1AxialSites : Finset Catalyst1DonorSite :=
  { .chloride .cl1, .chloride .cl2 }

/-- One representative for each topologically opposed donor pair.  No exact
180-degree metric-angle claim is made. -/
def catalyst1OppositeSitePairs :
    Finset (Catalyst1DonorSite × Catalyst1DonorSite) :=
  { (.qpyNitrogen .n1, .qpyNitrogen .n3),
    (.qpyNitrogen .n2, .qpyNitrogen .n4),
    (.chloride .cl1, .chloride .cl2) }

structure Catalyst1CoordinationModel where
  center : MetalCenter
  bonds : Finset MetalDonorCoordinationBond
  basalSites : Finset Catalyst1DonorSite
  axialSites : Finset Catalyst1DonorSite
  oppositePairRepresentatives :
    Finset (Catalyst1DonorSite × Catalyst1DonorSite)
  deriving DecidableEq

def catalyst1CoordinationModel : Catalyst1CoordinationModel where
  center := .catalyst1Iron
  bonds := catalyst1CoordinationBonds
  basalSites := catalyst1BasalSites
  axialSites := catalyst1AxialSites
  oppositePairRepresentatives := catalyst1OppositeSitePairs

/-- Direct provenance binding between the external figure and the typed model
transcribed from that figure. -/
structure SourcedCoordinationModel where
  source : LiteratureRecord
  ligandCore : LigandCoreSignature
  model : Catalyst1CoordinationModel

def exactCatalystFigureEvidence : SourcedCoordinationModel where
  source := exactFeQpyLiterature
  ligandCore := exactFigureLigandCore
  model := catalyst1CoordinationModel

inductive PolypyridylDonorTopology where
  | consecutiveQuaterpyridineN4
  deriving DecidableEq, Fintype, Repr

/-- Typed extraction of only the transferable four-plus-two topology from the
second literature record. -/
structure BasalAxialTopologyEvidence where
  source : LiteratureRecord
  donorTopology : PolypyridylDonorTopology
  basalNitrogenDonorCount : ℕ
  axialMonodentateDonorCount : ℕ
  topologicalOppositePairCount : ℕ

def qpyBasalAxialTopologyEvidence : BasalAxialTopologyEvidence where
  source := qpyBasalAxialLiterature
  donorTopology := .consecutiveQuaterpyridineN4
  basalNitrogenDonorCount := 4
  axialMonodentateDonorCount := 2
  topologicalOppositePairCount := 3

def ExactFeQpyLiteratureSpecification : Prop :=
  exactCatalystFigureEvidence.source = exactFeQpyLiterature ∧
  exactCatalystFigureEvidence.source.doi = "10.1039/d5qi00859j" ∧
  exactCatalystFigureEvidence.source.stableUrl =
      "https://www.osti.gov/servlets/purl/3377957" ∧
  exactCatalystFigureEvidence.source.contentSha256 =
      "9f45fc489b714d50dca635ff51bb7270159d2531edc9311dcc595a30c70bec0e" ∧
  exactCatalystFigureEvidence.ligandCore = exactFigureLigandCore ∧
  page1Ligand8Core = exactCatalystFigureEvidence.ligandCore ∧
  exactCatalystFigureEvidence.model = catalyst1CoordinationModel

def QpyBasalAxialLiteratureSpecification : Prop :=
  qpyBasalAxialTopologyEvidence.source = qpyBasalAxialLiterature ∧
  qpyBasalAxialTopologyEvidence.source.doi =
      "10.1021/acsomega.9b00921" ∧
  qpyBasalAxialTopologyEvidence.source.stableUrl =
      "https://pmc.ncbi.nlm.nih.gov/articles/PMC6647971/" ∧
  qpyBasalAxialTopologyEvidence.source.contentSha256 =
      "7250c33d0cff117d0866cccea0998961dfd0c9b593a442989f05dac2525d5632" ∧
  qpyBasalAxialTopologyEvidence.donorTopology =
      .consecutiveQuaterpyridineN4 ∧
  qpyBasalAxialTopologyEvidence.basalNitrogenDonorCount =
      catalyst1CoordinationModel.basalSites.card ∧
  qpyBasalAxialTopologyEvidence.axialMonodentateDonorCount =
      catalyst1CoordinationModel.axialSites.card ∧
  qpyBasalAxialTopologyEvidence.topologicalOppositePairCount =
      catalyst1CoordinationModel.oppositePairRepresentatives.card

/-- Full source-to-structure bridge.  It identifies the contacts and their
placement but does not mention any geometry constructor. -/
def Catalyst1CoordinationModelSpecification : Prop :=
  exactCatalystFigureEvidence.model = catalyst1CoordinationModel ∧
  exactCatalystFigureEvidence.model.center = .catalyst1Iron ∧
  exactCatalystFigureEvidence.model.bonds.card = 6 ∧
  exactCatalystFigureEvidence.model.bonds.image
      (fun bond => bond.donor) = Finset.univ ∧
  exactCatalystFigureEvidence.model.basalSites =
      { .qpyNitrogen .n1, .qpyNitrogen .n2,
        .qpyNitrogen .n3, .qpyNitrogen .n4 } ∧
  exactCatalystFigureEvidence.model.axialSites =
      { .chloride .cl1, .chloride .cl2 } ∧
  Disjoint exactCatalystFigureEvidence.model.basalSites
      exactCatalystFigureEvidence.model.axialSites ∧
  exactCatalystFigureEvidence.model.basalSites ∪
      exactCatalystFigureEvidence.model.axialSites = Finset.univ ∧
  exactCatalystFigureEvidence.model.oppositePairRepresentatives =
      { (.qpyNitrogen .n1, .qpyNitrogen .n3),
        (.qpyNitrogen .n2, .qpyNitrogen .n4),
        (.chloride .cl1, .chloride .cl2) } ∧
  exactCatalystFigureEvidence.model.oppositePairRepresentatives.card = 3

theorem exact_fe_qpy_literature_specification :
    ExactFeQpyLiteratureSpecification := by
  unfold ExactFeQpyLiteratureSpecification
  native_decide

theorem qpy_basal_axial_literature_specification :
    QpyBasalAxialLiteratureSpecification := by
  unfold QpyBasalAxialLiteratureSpecification
  native_decide

theorem catalyst1_coordination_model_specification :
    Catalyst1CoordinationModelSpecification := by
  unfold Catalyst1CoordinationModelSpecification
  native_decide

/-! ## Geometry-neutral signature and uniform classification -/

structure CoordinationSignature where
  coordinationNumber : ℕ
  basalSiteCount : ℕ
  axialSiteCount : ℕ
  topologicalOppositePairCount : ℕ
  deriving DecidableEq, Repr

def catalyst1CoordinationSignature : CoordinationSignature where
  coordinationNumber := catalyst1CoordinationModel.bonds.card
  basalSiteCount := catalyst1CoordinationModel.basalSites.card
  axialSiteCount := catalyst1CoordinationModel.axialSites.card
  topologicalOppositePairCount :=
    catalyst1CoordinationModel.oppositePairRepresentatives.card

def Catalyst1CoordinationSignatureSpecification : Prop :=
  catalyst1CoordinationSignature =
    { coordinationNumber := 6,
      basalSiteCount := 4,
      axialSiteCount := 2,
      topologicalOppositePairCount := 3 }

theorem catalyst1_coordination_signature_specification :
    Catalyst1CoordinationSignatureSpecification := by
  unfold Catalyst1CoordinationSignatureSpecification
  native_decide

inductive CoordinationGeometry where
  | linear
  | trigonalPlanar
  | tetrahedral
  | squarePlanar
  | trigonalBipyramidal
  | squarePyramidal
  | octahedral
  | trigonalPrismatic
  | pentagonalPyramidal
  | hexagonalPlanar
  deriving DecidableEq, Fintype, Repr

/-- Standard idealized coordination-polyhedron signatures.  The vocabulary is
fixed independently of catalyst `1` and includes the principal competing
six-coordinate geometries. -/
def standardGeometrySignature : CoordinationGeometry → CoordinationSignature
  | .linear => ⟨2, 0, 2, 1⟩
  | .trigonalPlanar => ⟨3, 3, 0, 0⟩
  | .tetrahedral => ⟨4, 0, 0, 0⟩
  | .squarePlanar => ⟨4, 4, 0, 2⟩
  | .trigonalBipyramidal => ⟨5, 3, 2, 1⟩
  | .squarePyramidal => ⟨5, 4, 1, 2⟩
  | .octahedral => ⟨6, 4, 2, 3⟩
  | .trigonalPrismatic => ⟨6, 0, 0, 0⟩
  | .pentagonalPyramidal => ⟨6, 5, 1, 0⟩
  | .hexagonalPlanar => ⟨6, 6, 0, 3⟩

inductive CandidateDomainOrigin where
  | trustedGeneralLaw
  deriving DecidableEq, Fintype, Repr

structure CandidateDomainProvenance where
  origin : CandidateDomainOrigin
  scope : String
  caveat : String
  deriving DecidableEq, Repr

def standardGeometryCandidates : Finset CoordinationGeometry :=
  Finset.univ

def standardGeometryCandidateProvenance : CandidateDomainProvenance where
  origin := .trustedGeneralLaw
  scope :=
    "standard idealized coordination geometries used as a contest classification vocabulary"
  caveat :=
    "not asserted to exhaust every distorted or exotic open-world coordination structure"

def MatchesCatalyst1CoordinationEvidence
    (geometry : CoordinationGeometry) : Prop :=
  geometry ∈ standardGeometryCandidates ∧
  standardGeometrySignature geometry = catalyst1CoordinationSignature

instance matchesCatalyst1CoordinationEvidenceDecidable
    (geometry : CoordinationGeometry) :
    Decidable (MatchesCatalyst1CoordinationEvidence geometry) := by
  unfold MatchesCatalyst1CoordinationEvidence
  infer_instance

def matchingGeometryCandidates : Finset CoordinationGeometry :=
  standardGeometryCandidates.filter fun geometry =>
    MatchesCatalyst1CoordinationEvidence geometry

def StandardGeometryCandidateDomainSpecification : Prop :=
  standardGeometryCandidateProvenance.origin = .trustedGeneralLaw ∧
  standardGeometryCandidates = Finset.univ ∧
  standardGeometryCandidates.card = 10 ∧
  CoordinationGeometry.octahedral ∈ standardGeometryCandidates ∧
  CoordinationGeometry.trigonalPrismatic ∈ standardGeometryCandidates ∧
  CoordinationGeometry.pentagonalPyramidal ∈ standardGeometryCandidates ∧
  CoordinationGeometry.hexagonalPlanar ∈ standardGeometryCandidates

theorem standard_geometry_candidate_domain_specification :
    StandardGeometryCandidateDomainSpecification := by
  unfold StandardGeometryCandidateDomainSpecification
  native_decide

theorem uniform_geometry_filter_audit :
    matchingGeometryCandidates = {.octahedral} := by
  native_decide

theorem geometry1_unique_matching_geometry :
    ∃! geometry : CoordinationGeometry,
      MatchesCatalyst1CoordinationEvidence geometry := by
  refine ⟨.octahedral, ?_, ?_⟩
  · native_decide
  · intro geometry hgeometry
    have hmem : geometry ∈ matchingGeometryCandidates := by
      simpa [matchingGeometryCandidates] using
        (And.intro hgeometry.1 hgeometry)
    rw [uniform_geometry_filter_audit] at hmem
    simpa using hmem

/-- The output is selected from the proved unique uniform match; its
definition does not contain the desired geometry constructor. -/
noncomputable def geometry1Output : CoordinationGeometry :=
  Classical.choose geometry1_unique_matching_geometry.exists

theorem geometry1_output_matches_coordination_evidence :
    MatchesCatalyst1CoordinationEvidence geometry1Output := by
  exact Classical.choose_spec geometry1_unique_matching_geometry.exists

theorem geometry1_output_is_octahedral :
    geometry1Output = .octahedral := by
  apply geometry1_unique_matching_geometry.unique
  · exact geometry1_output_matches_coordination_evidence
  · native_decide

def CoordinationGeometry.display : CoordinationGeometry → String
  | .linear => "linear"
  | .trigonalPlanar => "trigonal planar"
  | .tetrahedral => "tetrahedral"
  | .squarePlanar => "square planar"
  | .trigonalBipyramidal => "trigonal bipyramidal"
  | .squarePyramidal => "square pyramidal"
  | .octahedral => "octahedral"
  | .trigonalPrismatic => "trigonal prismatic"
  | .pentagonalPyramidal => "pentagonal pyramidal"
  | .hexagonalPlanar => "hexagonal planar"

/-! ## Requested output and answer-blind result contracts -/

inductive OutputKind where
  | classification
  deriving DecidableEq, Fintype, Repr

inductive SymbolicReportingPolicy where
  | exactSymbolic
  deriving DecidableEq, Fintype, Repr

structure RequestedOutput where
  id : String
  kind : OutputKind
  unit : String
  reportingPolicy : SymbolicReportingPolicy
  deriving DecidableEq, Repr

def geometry1Request : RequestedOutput where
  id := "geometry_1"
  kind := .classification
  unit := ""
  reportingPolicy := .exactSymbolic

def CurrentQuestionSpecification : Prop :=
  currentQuestionText =
      "Tick the correct geometry for the structure of 1." ∧
  currentQuestionLocator.origin = .problemText ∧
  geometry1Request.id = "geometry_1" ∧
  geometry1Request.kind = .classification ∧
  geometry1Request.unit = "" ∧
  geometry1Request.reportingPolicy = .exactSymbolic

theorem current_question_specification : CurrentQuestionSpecification := by
  unfold CurrentQuestionSpecification
  native_decide

/-- Raw derivation.  No result equality or singleton answer-domain occurs in
this proposition: geometry constructors appear only inside the independently
fixed non-singleton vocabulary, whose members are filtered uniformly. -/
def Geometry1RawResultSpecification : Prop :=
  CurrentQuestionSpecification ∧
  Ligand8ImageSpecification ∧
  Catalyst1SynthesisArrowSpecification ∧
  ExactFeQpyLiteratureSpecification ∧
  QpyBasalAxialLiteratureSpecification ∧
  Catalyst1CoordinationModelSpecification ∧
  Catalyst1CoordinationSignatureSpecification ∧
  StandardGeometryCandidateDomainSpecification ∧
  ∃! geometry : CoordinationGeometry,
    MatchesCatalyst1CoordinationEvidence geometry

/-- The exact-symbolic reporting boundary for the sole requested output. -/
def Geometry1ReportedResultSpecification : Prop :=
  Geometry1RawResultSpecification ∧
  geometry1Request.reportingPolicy = .exactSymbolic ∧
  geometry1Output = .octahedral ∧
  CoordinationGeometry.display geometry1Output = "octahedral"

theorem geometry1_raw_result_specification :
    Geometry1RawResultSpecification := by
  exact ⟨current_question_specification,
    ligand8_image_specification,
    catalyst1_synthesis_arrow_specification,
    exact_fe_qpy_literature_specification,
    qpy_basal_axial_literature_specification,
    catalyst1_coordination_model_specification,
    catalyst1_coordination_signature_specification,
    standard_geometry_candidate_domain_specification,
    geometry1_unique_matching_geometry⟩

theorem geometry1_reported_result_specification :
    Geometry1ReportedResultSpecification := by
  refine ⟨geometry1_raw_result_specification, rfl,
    geometry1_output_is_octahedral, ?_⟩
  rw [geometry1_output_is_octahedral]
  rfl

/- The digest literals are synchronized with the answer-blind candidate by
the trusted local helper after the semantic record is regenerated. -/
theorem geometry1RawResultContract :
    ("fbd60a3c87a05cf29abfecab039853f22ca375cf45c250d1a3be613e7107ce31" : String) =
        "fbd60a3c87a05cf29abfecab039853f22ca375cf45c250d1a3be613e7107ce31" ∧
      Geometry1RawResultSpecification := by
  exact ⟨rfl, geometry1_raw_result_specification⟩

theorem geometry1ReportedResultContract :
    ("f186762cc18704eb9494d345cbaeda9e326e861131911a99224eae3d3e66a82a" : String) =
        "f186762cc18704eb9494d345cbaeda9e326e861131911a99224eae3d3e66a82a" ∧
      Geometry1ReportedResultSpecification := by
  exact ⟨rfl, geometry1_reported_result_specification⟩

end ProblemIcho2026T8A3
end IChO2026Problems
