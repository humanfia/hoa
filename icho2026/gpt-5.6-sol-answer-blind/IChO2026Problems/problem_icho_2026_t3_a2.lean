import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem T3-A2: internal diameter of the COF-2 pore

The source depicts a honeycomb pore whose vertices are boroxine rings and whose
edges contain para-phenylene linkers.  All lengths below are scalar numerical
values in angstroms, as required by the answer-blind numerical contract.

Assumptions/source data:
* arene C-C/C=C, C-B, and B-O lengths are respectively 1.39, 1.56, and 1.38 A;
* the problem image gives six degree-three boroxine nodes and six para-phenylene
  linkers on one pore boundary;
* one node-centre-to-node-centre edge has two boroxine radial contributions,
  two C-B bonds, and a para-phenylene chord of two arene bond lengths;
* linker width is neglected, and the inscribed diameter is `sqrt 3` times the
  hexagon side length.

Target:
derive the exact unrounded diameter from those facts and certify its final
three-significant-figure report.
-/

namespace IChO2026Problems
namespace ProblemIChO2026T3A2

noncomputable section

/-- Provenance tags used for the finite topology counts in this target. -/
inductive SourceProvenance where
  | problemText
  | problemImage
  | derivedTheorem
  deriving DecidableEq, Repr

/--
Source-first visual recount of one complete COF-2 honeycomb pore.

There is one precursor building-block type (`A2`) in the COF-2 panel, while the
product has two structural roles relevant to the metric calculation: boroxine
nodes and para-phenylene linkers.  The per-edge fields record every contribution
along the straight line joining adjacent boroxine centres.
-/
structure Cof2PoreTopologyLedger where
  precursorBuildingBlockTypes : ℕ
  productComponentRoles : ℕ
  boroxineNodesPerPore : ℕ
  paraPhenyleneLinkersPerPore : ℕ
  boroxineNodeDegree : ℕ
  crossBuildingBlockBondsPerPore : ℕ
  boroxineRadiusContributionsPerEdge : ℕ
  carbonBoronBondsPerEdge : ℕ
  areneBondLengthsInParaChord : ℕ
  provenance : SourceProvenance
  deriving DecidableEq, Repr

/-- The topology and bond-count data read from the COF-2 panel on T3 page 1. -/
def cof2PoreTopologyLedger : Cof2PoreTopologyLedger where
  precursorBuildingBlockTypes := 1
  productComponentRoles := 2
  boroxineNodesPerPore := 6
  paraPhenyleneLinkersPerPore := 6
  boroxineNodeDegree := 3
  crossBuildingBlockBondsPerPore := 12
  boroxineRadiusContributionsPerEdge := 2
  carbonBoronBondsPerEdge := 2
  areneBondLengthsInParaChord := 2
  provenance := .problemImage

/-- Named carrier for the complete visual recount used by the calculation. -/
theorem cof2PoreTopologyLedger_spec :
    cof2PoreTopologyLedger.precursorBuildingBlockTypes = 1 ∧
    cof2PoreTopologyLedger.productComponentRoles = 2 ∧
    cof2PoreTopologyLedger.boroxineNodesPerPore = 6 ∧
    cof2PoreTopologyLedger.paraPhenyleneLinkersPerPore = 6 ∧
    cof2PoreTopologyLedger.boroxineNodeDegree = 3 ∧
    cof2PoreTopologyLedger.crossBuildingBlockBondsPerPore = 12 ∧
    cof2PoreTopologyLedger.boroxineRadiusContributionsPerEdge = 2 ∧
    cof2PoreTopologyLedger.carbonBoronBondsPerEdge = 2 ∧
    cof2PoreTopologyLedger.areneBondLengthsInParaChord = 2 ∧
    cof2PoreTopologyLedger.provenance = .problemImage := by
  norm_num [cof2PoreTopologyLedger]

/-- Problem-stipulated arene C-C/C=C length, in angstroms. -/
def areneBondLengthAngstrom : ℝ := 139 / 100

/-- Problem-stipulated C-B length, in angstroms. -/
def carbonBoronBondLengthAngstrom : ℝ := 39 / 25

/-- Problem-stipulated B-O length, in angstroms. -/
def boronOxygenBondLengthAngstrom : ℝ := 69 / 50

/--
The radius of the depicted regular alternating B-O hexagon equals one of its
B-O side lengths.
-/
def boroxineRadiusAngstrom : ℝ := boronOxygenBondLengthAngstrom

/-- Straight para-carbon-to-para-carbon chord of the depicted arene linker. -/
def paraPhenyleneChordAngstrom : ℝ :=
  (cof2PoreTopologyLedger.areneBondLengthsInParaChord : ℝ) *
    areneBondLengthAngstrom

/-- The source directs us to neglect linker width, so its correction is zero. -/
def neglectedLinkerWidthCorrectionAngstrom : ℝ := 0

/-- Exact centre-to-centre side length of the idealized COF-2 honeycomb. -/
def cof2SideLengthAngstrom : ℝ :=
  (cof2PoreTopologyLedger.boroxineRadiusContributionsPerEdge : ℝ) *
      boroxineRadiusAngstrom +
    (cof2PoreTopologyLedger.carbonBoronBondsPerEdge : ℝ) *
      carbonBoronBondLengthAngstrom +
    paraPhenyleneChordAngstrom + neglectedLinkerWidthCorrectionAngstrom

/--
Exact unrounded requested diameter, in angstroms.  This is the source-derived
expression `sqrt 3 * (2*1.38 + 2*1.56 + 2*1.39)`, not a decimal answer.
-/
def cof2InternalDiameterRaw : ℝ :=
  Real.sqrt 3 * cof2SideLengthAngstrom

/--
Problem-specific derivation specification.  It exposes the image counts, all
three stipulated bond lengths, the zero-width idealization, the exact side
length, and the supplied regular-hexagon diameter law.
-/
def Cof2InternalDiameterDerivation : Prop :=
  cof2PoreTopologyLedger.provenance = .problemImage ∧
  cof2PoreTopologyLedger.boroxineNodesPerPore = 6 ∧
  cof2PoreTopologyLedger.paraPhenyleneLinkersPerPore = 6 ∧
  cof2PoreTopologyLedger.boroxineNodeDegree = 3 ∧
  cof2PoreTopologyLedger.crossBuildingBlockBondsPerPore = 12 ∧
  cof2PoreTopologyLedger.boroxineRadiusContributionsPerEdge = 2 ∧
  cof2PoreTopologyLedger.carbonBoronBondsPerEdge = 2 ∧
  cof2PoreTopologyLedger.areneBondLengthsInParaChord = 2 ∧
  areneBondLengthAngstrom = 139 / 100 ∧
  carbonBoronBondLengthAngstrom = 39 / 25 ∧
  boronOxygenBondLengthAngstrom = 69 / 50 ∧
  0 < areneBondLengthAngstrom ∧
  0 < carbonBoronBondLengthAngstrom ∧
  0 < boronOxygenBondLengthAngstrom ∧
  boroxineRadiusAngstrom = boronOxygenBondLengthAngstrom ∧
  paraPhenyleneChordAngstrom = 2 * areneBondLengthAngstrom ∧
  neglectedLinkerWidthCorrectionAngstrom = 0 ∧
  cof2SideLengthAngstrom =
    2 * boronOxygenBondLengthAngstrom +
      2 * carbonBoronBondLengthAngstrom + 2 * areneBondLengthAngstrom ∧
  cof2SideLengthAngstrom = 433 / 50 ∧
  cof2InternalDiameterRaw = Real.sqrt 3 * cof2SideLengthAngstrom

/--
Raw-result contract: the exact derivation holds and the irrational result has a
nondegenerate certified rational enclosure.  The enclosure is strong enough to
justify the separately stated reporting theorem without equating the raw value
to a terminating decimal.
-/
theorem cof2InternalDiameter_raw :
    Cof2InternalDiameterDerivation ∧
      (14999 : ℝ) / 1000 ≤ cof2InternalDiameterRaw ∧
      cof2InternalDiameterRaw ≤ 15 := by
  have hderivation : Cof2InternalDiameterDerivation := by
    norm_num [Cof2InternalDiameterDerivation, cof2PoreTopologyLedger,
      areneBondLengthAngstrom, carbonBoronBondLengthAngstrom,
      boronOxygenBondLengthAngstrom, boroxineRadiusAngstrom,
      paraPhenyleneChordAngstrom, neglectedLinkerWidthCorrectionAngstrom,
      cof2SideLengthAngstrom, cof2InternalDiameterRaw]
  have hside : cof2SideLengthAngstrom = (433 : ℝ) / 50 := by
    norm_num [cof2SideLengthAngstrom, cof2PoreTopologyLedger,
      areneBondLengthAngstrom, carbonBoronBondLengthAngstrom,
      boronOxygenBondLengthAngstrom, boroxineRadiusAngstrom,
      paraPhenyleneChordAngstrom, neglectedLinkerWidthCorrectionAngstrom]
  have hsqrt_lower : (14999 : ℝ) / 8660 ≤ Real.sqrt 3 := by
    apply Real.le_sqrt_of_sq_le
    norm_num [sq]
  have hsqrt_upper : Real.sqrt 3 ≤ (750 : ℝ) / 433 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num [sq]
  refine ⟨hderivation, ?_, ?_⟩
  · rw [cof2InternalDiameterRaw, hside]
    nlinarith
  · rw [cof2InternalDiameterRaw, hside]
    nlinarith

/-- Final three-significant-figure report, using a `0.1 A` last-place quantum. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"cof2_internal_diameter","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"15.0","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.ProblemIChO2026T3A2.cof2InternalDiameterRaw","reporting_declaration":"IChO2026Problems.ProblemIChO2026T3A2.cof2InternalDiameter_reported"}
theorem cof2InternalDiameter_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      cof2InternalDiameterRaw (15 : ℝ) ((1 : ℝ) / 10) := by
  rcases cof2InternalDiameter_raw with ⟨_, hlower, hupper⟩
  have hnonneg : 0 ≤ cof2InternalDiameterRaw := by
    linarith
  refine ⟨by norm_num, ⟨150, by norm_num⟩, ?_⟩
  rw [if_pos hnonneg]
  constructor <;> norm_num at * <;> linarith

end
end ProblemIChO2026T3A2
end IChO2026Problems
