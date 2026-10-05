import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026, problem T3, part A3

This file formalizes the table-completion problem from the two bound problem
images.  It deliberately separates three layers of information:

* the functional group, connector count, and geometry read from each depicted
  monomer;
* the connector profiles read from the seven topology cartoons; and
* a proposed filling of the fourteen white cells in the table.

In particular, `XXX` is not an unconstrained flag.  A cell containing `XXX` is
valid only when every source-listed monomer pair that can undergo one of the
three permitted condensations and fits that topology is already represented by
a supplied or newly filled example.
-/

namespace IChO2026Problems.IChO2026T3A3

/-- The five reactive functional-group classes distinguished in the monomer
panel on problem page T3-3. -/
inductive FunctionalGroupClass where
  | boronicAcid
  | vicinalDiol
  | primaryAmine
  | aldehyde
  | activatedMethyleneNitrile
  deriving DecidableEq, Repr, Fintype

/-- Geometric connector profiles obtained by tracing all functionalized arms
of each molecular drawing on problem page T3-3.  The two planar four-connected
profiles are kept distinct because the source supplies distinct tetragonal and
kagome topology cartoons. -/
inductive ConnectorGeometry where
  | linear
  | trigonalPlanar
  | tetragonalPlanar
  | kagomePlanar
  | hexagonalPlanar
  | tetrahedral3D
  deriving DecidableEq, Repr, Fintype

/-- The number of outgoing condensation sites carried by a connector geometry. -/
def ConnectorGeometry.degree : ConnectorGeometry → ℕ
  | .linear => 2
  | .trigonalPlanar => 3
  | .tetragonalPlanar => 4
  | .kagomePlanar => 4
  | .hexagonalPlanar => 6
  | .tetrahedral3D => 4

/-- Exactly the fifteen labeled monomers visible in the bound source image. -/
inductive Monomer where
  | a1 | a2 | a3 | a4
  | b1 | b2 | b3
  | c1 | c2 | c3
  | d1 | d2 | d3 | d4
  | e1
  deriving DecidableEq, Repr, Fintype

/-- Source-image data for one monomer: reactive class, visually counted sites,
and the geometry of those sites. -/
structure MonomerDatum where
  functionalGroup : FunctionalGroupClass
  connectorCount : ℕ
  geometry : ConnectorGeometry
  deriving DecidableEq, Repr

/-- Transcription of the complete monomer panel on T3-3.  Adjacent OH groups
forming one catechol/boronate connection count as one connector, as do each
depicted `B(OH)₂`, `NH₂`, `CHO`, or activated `CH₂CN` terminus. -/
def monomerDatum : Monomer → MonomerDatum
  | .a1 => ⟨.boronicAcid, 3, .trigonalPlanar⟩
  | .a2 => ⟨.boronicAcid, 2, .linear⟩
  | .a3 => ⟨.boronicAcid, 4, .tetragonalPlanar⟩
  | .a4 => ⟨.boronicAcid, 4, .tetrahedral3D⟩
  | .b1 => ⟨.vicinalDiol, 4, .tetragonalPlanar⟩
  | .b2 => ⟨.vicinalDiol, 2, .linear⟩
  | .b3 => ⟨.vicinalDiol, 3, .trigonalPlanar⟩
  | .c1 => ⟨.primaryAmine, 2, .linear⟩
  | .c2 => ⟨.primaryAmine, 4, .kagomePlanar⟩
  | .c3 => ⟨.primaryAmine, 4, .tetragonalPlanar⟩
  | .d1 => ⟨.aldehyde, 6, .hexagonalPlanar⟩
  | .d2 => ⟨.aldehyde, 3, .trigonalPlanar⟩
  | .d3 => ⟨.aldehyde, 4, .tetrahedral3D⟩
  | .d4 => ⟨.aldehyde, 2, .linear⟩
  | .e1 => ⟨.activatedMethyleneNitrile, 3, .trigonalPlanar⟩

/-- A nontrivial consistency check on the visual component ledger: every
explicitly counted terminus agrees with the degree of its assigned geometry. -/
def MonomerLedgerConsistent : Prop :=
  ∀ m : Monomer,
    (monomerDatum m).connectorCount = (monomerDatum m).geometry.degree

/-- Source-permitted covalent linkages in this subquestion. -/
inductive LinkageKind where
  | boronateEster
  | imine
  | carbonCarbon
  deriving DecidableEq, Repr, Fintype

/-- A monomer combination in the role order used by the source table: A with
B, C with D, or E with D.  All pairs of depicted monomers remain in the ambient
type; chemical compatibility is imposed separately. -/
structure MonomerCombination where
  first : Monomer
  second : Monomer
  deriving DecidableEq, Repr, Fintype

/-- Short constructor used only to display combinations. -/
def combination (first second : Monomer) : MonomerCombination :=
  ⟨first, second⟩

/-- The three functional-group matchings explicitly allowed by the question.
`none` retains every other pair as an auditable rejected candidate. -/
def canonicalCondensationLinkage
    (first second : Monomer) : Option LinkageKind :=
  match (monomerDatum first).functionalGroup,
      (monomerDatum second).functionalGroup with
  | .boronicAcid, .vicinalDiol => some .boronateEster
  | .primaryAmine, .aldehyde => some .imine
  | .activatedMethyleneNitrile, .aldehyde => some .carbonCarbon
  | _, _ => none

/-- A pair is chemically compatible precisely when its two source-depicted
functional-group classes give one of the three permitted condensations. -/
def CondensationCompatible (p : MonomerCombination) : Prop :=
  ∃ linkage : LinkageKind,
    canonicalCondensationLinkage p.first p.second = some linkage

/-- The seven named topology columns, including both distinct tetragonal and
both distinct hexagonal connector patterns. -/
inductive Topology where
  | tetragonal1
  | tetragonal2
  | hexagonal1
  | hexagonal2
  | trigonal
  | kagome
  | tetrahedral
  deriving DecidableEq, Repr, Fintype

/-- One colored building-block role in a topology cartoon. -/
structure BuildingBlockProfile where
  geometry : ConnectorGeometry
  degree : ℕ
  deriving DecidableEq, Repr

/-- The two differently colored building-block roles traced in a topology
cartoon.  `spatialDimension = 3` is used only for the tetrahedral net. -/
structure TopologyConstraint where
  black : BuildingBlockProfile
  red : BuildingBlockProfile
  spatialDimension : ℕ
  deriving DecidableEq, Repr

/-- Connector-degree ledger read panel-by-panel from the topology cartoons on
T3-3.  Ordering of black and red is visual only; matching below is symmetric. -/
def topologyConstraint : Topology → TopologyConstraint
  | .tetragonal1 => ⟨⟨.tetragonalPlanar, 4⟩, ⟨.linear, 2⟩, 2⟩
  | .tetragonal2 => ⟨⟨.tetragonalPlanar, 4⟩, ⟨.tetragonalPlanar, 4⟩, 2⟩
  | .hexagonal1 => ⟨⟨.trigonalPlanar, 3⟩, ⟨.linear, 2⟩, 2⟩
  | .hexagonal2 => ⟨⟨.trigonalPlanar, 3⟩, ⟨.trigonalPlanar, 3⟩, 2⟩
  | .trigonal => ⟨⟨.hexagonalPlanar, 6⟩, ⟨.linear, 2⟩, 2⟩
  | .kagome => ⟨⟨.kagomePlanar, 4⟩, ⟨.linear, 2⟩, 2⟩
  | .tetrahedral => ⟨⟨.tetrahedral3D, 4⟩, ⟨.linear, 2⟩, 3⟩

/-- A monomer realizes one colored building-block role only when both its
geometry and its independently counted number of connectors agree. -/
def RealizesProfile (m : Monomer) (profile : BuildingBlockProfile) : Prop :=
  (monomerDatum m).geometry = profile.geometry ∧
    (monomerDatum m).connectorCount = profile.degree

/-- The colors in the source cartoons merely distinguish building blocks, so
the two monomers may realize the black/red profiles in either order. -/
def FitsTopology (p : MonomerCombination) (t : Topology) : Prop :=
  let constraint := topologyConstraint t
  (RealizesProfile p.first constraint.black ∧
      RealizesProfile p.second constraint.red) ∨
    (RealizesProfile p.first constraint.red ∧
      RealizesProfile p.second constraint.black)

/-- The source-derived admissibility test, independent of any proposed table
answer. -/
def AdmissibleFor (p : MonomerCombination) (t : Topology) : Prop :=
  CondensationCompatible p ∧ FitsTopology p t

/-- First-row cells printed by the question itself. -/
inductive PrintedFirstRowCell where
  | black
  | supplied (pair : MonomerCombination)
  deriving DecidableEq, Repr

/-- Exact transcription of the shaded/supplied first row on problem page T3-4. -/
def printedFirstRow : Topology → PrintedFirstRowCell
  | .tetragonal1 => .black
  | .tetragonal2 => .black
  | .hexagonal1 => .supplied (combination .a2 .b3)
  | .hexagonal2 => .supplied (combination .e1 .d2)
  | .trigonal => .black
  | .kagome => .supplied (combination .c2 .d4)
  | .tetrahedral => .black

/-- A writable cell has no blank constructor: it must contain a new example or
the literal classification `XXX`. -/
inductive FilledCell where
  | example (pair : MonomerCombination)
  | xxx
  deriving DecidableEq, Repr

/-- There are two writable rows and seven columns, hence exactly fourteen
total writable cells. -/
structure TopologyTableCompletion where
  upper : Topology → FilledCell
  lower : Topology → FilledCell

/-- The source-provided example, when the first row of a column contains one. -/
def suppliedPair? (t : Topology) : Option MonomerCombination :=
  match printedFirstRow t with
  | .black => none
  | .supplied p => some p

/-- A pair is represented either by the printed example or by one of the two
writable cells in its column. -/
def RepresentedInColumn
    (table : TopologyTableCompletion) (t : Topology)
    (p : MonomerCombination) : Prop :=
  suppliedPair? t = some p ∨
    table.upper t = .example p ∨
    table.lower t = .example p

/-- A new example must pass the source-independent admissibility test and must
not duplicate the printed example.  An `XXX` cell has the stronger universal
obligation that every admissible source monomer pair is already represented. -/
def FilledCellValid
    (table : TopologyTableCompletion) (t : Topology) : FilledCell → Prop
  | .example p => AdmissibleFor p t ∧ suppliedPair? t ≠ some p
  | .xxx => ∀ p : MonomerCombination, AdmissibleFor p t → RepresentedInColumn table t p

/-- The two writable examples in a column, if both are examples, must be new
relative to each other as well as relative to the supplied entry. -/
def WritableExamplesDistinct
    (table : TopologyTableCompletion) (t : Topology) : Prop :=
  ∀ p : MonomerCombination,
    table.upper t = .example p → table.lower t ≠ .example p

/-- Every printed example is itself checked against the same chemistry and
topology constraints as a newly proposed example. -/
def PrintedExamplesValid : Prop :=
  ∀ (t : Topology) (p : MonomerCombination),
    suppliedPair? t = some p → AdmissibleFor p t

/-- Full specification for a filled table.  Total functions supply every one
of the fourteen cells; the predicates enforce newness and justify every XXX. -/
def ValidTopologyTableCompletion (table : TopologyTableCompletion) : Prop :=
  MonomerLedgerConsistent ∧
  PrintedExamplesValid ∧
  ∀ t : Topology,
    FilledCellValid table t (table.upper t) ∧
      FilledCellValid table t (table.lower t) ∧
      WritableExamplesDistinct table t

/-- Candidate upper writable row, derived from the monomer and topology
ledgers. -/
def proposedUpperRow : Topology → FilledCell
  | .tetragonal1 => .example (combination .a2 .b1)
  | .tetragonal2 => .example (combination .a3 .b1)
  | .hexagonal1 => .example (combination .a1 .b2)
  | .hexagonal2 => .example (combination .a1 .b3)
  | .trigonal => .example (combination .c1 .d1)
  | .kagome => .xxx
  | .tetrahedral => .example (combination .a4 .b2)

/-- Candidate lower writable row, derived from the monomer and topology
ledgers. -/
def proposedLowerRow : Topology → FilledCell
  | .tetragonal1 => .example (combination .a3 .b2)
  | .tetragonal2 => .xxx
  | .hexagonal1 => .example (combination .c1 .d2)
  | .hexagonal2 => .xxx
  | .trigonal => .xxx
  | .kagome => .xxx
  | .tetrahedral => .example (combination .c1 .d3)

/-- The concrete answer candidate for all fourteen writable cells. -/
def proposedTopologyTable : TopologyTableCompletion :=
  ⟨proposedUpperRow, proposedLowerRow⟩

/-- An auditable finite classification: the listed combinations are exactly
all admissible combinations for a topology, not merely selected examples. -/
def ExhaustsAdmissiblePairs
    (t : Topology) (pairs : List MonomerCombination) : Prop :=
  ∀ p : MonomerCombination, AdmissibleFor p t ↔ p ∈ pairs

/-- The complete pair audit derived from all fifteen source monomers.  It is
stronger than the requested table: when a column has more examples than open
cells, a valid completion may select any two new ones. -/
def CompleteAdmissiblePairAudit : Prop :=
  ExhaustsAdmissiblePairs .tetragonal1
      [combination .a2 .b1, combination .a3 .b2, combination .c3 .d4] ∧
  ExhaustsAdmissiblePairs .tetragonal2
      [combination .a3 .b1] ∧
  ExhaustsAdmissiblePairs .hexagonal1
      [combination .a1 .b2, combination .a2 .b3,
        combination .c1 .d2, combination .e1 .d4] ∧
  ExhaustsAdmissiblePairs .hexagonal2
      [combination .a1 .b3, combination .e1 .d2] ∧
  ExhaustsAdmissiblePairs .trigonal
      [combination .c1 .d1] ∧
  ExhaustsAdmissiblePairs .kagome
      [combination .c2 .d4] ∧
  ExhaustsAdmissiblePairs .tetrahedral
      [combination .a4 .b2, combination .c1 .d3]

/-- Exact symbolic rendering of the proposed writable cells in source column
order.  This proposition is conjoined with validity in the reported contract,
so the displayed table cannot replace the chemistry/topology proof. -/
def ExactProposedTableDisplay (table : TopologyTableCompletion) : Prop :=
  table.upper .tetragonal1 = .example (combination .a2 .b1) ∧
  table.lower .tetragonal1 = .example (combination .a3 .b2) ∧
  table.upper .tetragonal2 = .example (combination .a3 .b1) ∧
  table.lower .tetragonal2 = .xxx ∧
  table.upper .hexagonal1 = .example (combination .a1 .b2) ∧
  table.lower .hexagonal1 = .example (combination .c1 .d2) ∧
  table.upper .hexagonal2 = .example (combination .a1 .b3) ∧
  table.lower .hexagonal2 = .xxx ∧
  table.upper .trigonal = .example (combination .c1 .d1) ∧
  table.lower .trigonal = .xxx ∧
  table.upper .kagome = .xxx ∧
  table.lower .kagome = .xxx ∧
  table.upper .tetrahedral = .example (combination .a4 .b2) ∧
  table.lower .tetrahedral = .example (combination .c1 .d3)

/-- Raw answer-blind result proposition: the selected table satisfies the full
source-derived specification. -/
def TopologyTableRawResult : Prop :=
  CompleteAdmissiblePairAudit ∧
    ValidTopologyTableCompletion proposedTopologyTable

/-- Reported exact-symbolic result proposition: the same valid raw result is
rendered with every writable cell fixed explicitly. -/
def TopologyTableReportedResult : Prop :=
  TopologyTableRawResult ∧ ExactProposedTableDisplay proposedTopologyTable

attribute [local instance] Fintype.decidableForallFintype

local instance instDecidableMonomerLedgerConsistent :
    Decidable MonomerLedgerConsistent :=
  Fintype.decidableForallFintype

local instance instDecidableCondensationCompatible
    (p : MonomerCombination) : Decidable (CondensationCompatible p) := by
  unfold CondensationCompatible
  infer_instance

local instance instDecidableRealizesProfile
    (m : Monomer) (profile : BuildingBlockProfile) :
    Decidable (RealizesProfile m profile) := by
  unfold RealizesProfile
  infer_instance

local instance instDecidableFitsTopology
    (p : MonomerCombination) (t : Topology) : Decidable (FitsTopology p t) := by
  unfold FitsTopology
  infer_instance

local instance instDecidableAdmissibleFor
    (p : MonomerCombination) (t : Topology) : Decidable (AdmissibleFor p t) := by
  unfold AdmissibleFor
  infer_instance

local instance instDecidableRepresentedInColumn
    (table : TopologyTableCompletion) (t : Topology) (p : MonomerCombination) :
    Decidable (RepresentedInColumn table t p) := by
  unfold RepresentedInColumn
  infer_instance

local instance instDecidableFilledCellValid
    (table : TopologyTableCompletion) (t : Topology) (cell : FilledCell) :
    Decidable (FilledCellValid table t cell) := by
  cases cell <;> simp only [FilledCellValid] <;> infer_instance

local instance instDecidableWritableExamplesDistinct
    (table : TopologyTableCompletion) (t : Topology) :
    Decidable (WritableExamplesDistinct table t) := by
  unfold WritableExamplesDistinct
  infer_instance

local instance instDecidablePrintedExamplesValid : Decidable PrintedExamplesValid := by
  unfold PrintedExamplesValid
  infer_instance

local instance instDecidableValidTopologyTableCompletion
    (table : TopologyTableCompletion) : Decidable (ValidTopologyTableCompletion table) := by
  unfold ValidTopologyTableCompletion
  infer_instance

local instance instDecidableExhaustsAdmissiblePairs
    (t : Topology) (pairs : List MonomerCombination) :
    Decidable (ExhaustsAdmissiblePairs t pairs) := by
  unfold ExhaustsAdmissiblePairs
  infer_instance

local instance instDecidableCompleteAdmissiblePairAudit :
    Decidable CompleteAdmissiblePairAudit := by
  unfold CompleteAdmissiblePairAudit
  infer_instance

local instance instDecidableExactProposedTableDisplay
    (table : TopologyTableCompletion) : Decidable (ExactProposedTableDisplay table) := by
  unfold ExactProposedTableDisplay
  infer_instance

local instance instDecidableTopologyTableRawResult : Decidable TopologyTableRawResult := by
  unfold TopologyTableRawResult
  infer_instance

local instance instDecidableTopologyTableReportedResult :
    Decidable TopologyTableReportedResult := by
  unfold TopologyTableReportedResult
  infer_instance

/-- Source-image inventory bridge. -/
theorem monomer_ledger_consistent : MonomerLedgerConsistent := by
  native_decide

/-- Exhaustive filtering bridge used to justify every proposed `XXX`. -/
theorem complete_admissible_pair_audit : CompleteAdmissiblePairAudit := by
  native_decide

/-- The source-provided examples pass the same independent filters. -/
theorem printed_examples_valid : PrintedExamplesValid := by
  native_decide

/-- Raw result contract for the requested topology table. -/
theorem topology_table_raw_result : TopologyTableRawResult := by
  native_decide

/-- Reported exact-symbolic result contract for the requested topology table. -/
theorem topology_table_reported_result : TopologyTableReportedResult := by
  native_decide

end IChO2026Problems.IChO2026T3A3
