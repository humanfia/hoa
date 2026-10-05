import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T3, part A2

This file formalizes the source-side calculation of the internal diameter of a
COF-2 honeycomb pore.  Every real-valued length below is expressed in Å.  The
three printed bond lengths are treated as exact stipulated constants, as
required by the source report.

The page-1 structure is represented by two explicit ledgers.  Around one
complete pore there are six three-connected boroxine vertex motifs and six
two-connected para-phenylene edge motifs.  One edge, measured from the centre
of one boroxine vertex motif to the centre of the next, contains two radial
B–O contributions, two C–B bonds, and the two C–C radial contributions making
the para distance across one arene.  The six remaining bonds at the
three-connected boroxine vertices continue into neighbouring pores.

The source asks us to neglect linker width, so no width correction is
subtracted from the centre-line geometry.  The supplied law for the circle
inscribed in a hexagon is then applied only after the pore-side ledger has been
assembled.
-/

namespace IChO2026Problems.T3A2

noncomputable section

/-- The stipulated arene C–C/C=C bond length, in Å. -/
def areneCCBondLengthAngstrom : ℝ := 139 / 100

/-- The stipulated C–B bond length, in Å. -/
def carbonBoronBondLengthAngstrom : ℝ := 156 / 100

/-- The stipulated B–O bond length, in Å. -/
def boronOxygenBondLengthAngstrom : ℝ := 138 / 100

/-- Source-first recount of the motifs and connections around one COF-2 pore. -/
structure COF2PoreTopologyLedger where
  boroxineVertexMotifs : ℕ
  paraPhenyleneEdgeMotifs : ℕ
  boroxineVertexConnectivity : ℕ
  paraPhenyleneConnectivity : ℕ
  outwardNetworkContinuationBonds : ℕ
  deriving DecidableEq

/-- The topology visible on page 1: a six-sided pore in the extended network. -/
def cof2PoreTopologyLedger : COF2PoreTopologyLedger where
  boroxineVertexMotifs := 6
  paraPhenyleneEdgeMotifs := 6
  boroxineVertexConnectivity := 3
  paraPhenyleneConnectivity := 2
  outwardNetworkContinuationBonds := 6

/-- Bond-length contributions along one centre-to-centre pore edge. -/
structure COF2PoreSideSegmentLedger where
  areneCCSegments : ℕ
  carbonBoronSegments : ℕ
  boroxineRadialSegments : ℕ
  deriving DecidableEq

/-- One page-1 pore edge has two contributions of each printed bond length. -/
def cof2PoreSideSegmentLedger : COF2PoreSideSegmentLedger where
  areneCCSegments := 2
  carbonBoronSegments := 2
  boroxineRadialSegments := 2

/-- Recombine a pore-side component ledger into a length in Å. -/
def COF2PoreSideSegmentLedger.lengthAngstrom
    (ledger : COF2PoreSideSegmentLedger) : ℝ :=
  (ledger.areneCCSegments : ℝ) * areneCCBondLengthAngstrom +
    (ledger.carbonBoronSegments : ℝ) * carbonBoronBondLengthAngstrom +
    (ledger.boroxineRadialSegments : ℝ) * boronOxygenBondLengthAngstrom

/-- The source-derived side length `a` of the idealized COF-2 honeycomb. -/
def cof2PoreSideLengthAngstrom : ℝ :=
  cof2PoreSideSegmentLedger.lengthAngstrom

/-- The width correction is zero because the question says to neglect it. -/
def cof2NeglectedLinkerWidthAngstrom : ℝ := 0

/-- The printed geometrical law `d = √3 a` for an inscribed circle. -/
def inscribedHexagonDiameterAngstrom (sideLengthAngstrom : ℝ) : ℝ :=
  Real.sqrt 3 * sideLengthAngstrom

/-- Exact, unrounded internal diameter obtained from the source data. -/
def cof2InternalDiameterRaw : ℝ :=
  inscribedHexagonDiameterAngstrom cof2PoreSideLengthAngstrom

/--
The source-to-result bridge.  It exposes the complete image recount, the three
stipulated constants, the component recombination for one pore side, the zero
width correction, and the supplied hexagon law.  In particular, the reported
decimal is not inserted as a premise or as the definition of the raw value.
-/
def cof2InternalDiameterDerivationSpec : Prop :=
  areneCCBondLengthAngstrom = (139 : ℝ) / 100 ∧
  carbonBoronBondLengthAngstrom = (156 : ℝ) / 100 ∧
  boronOxygenBondLengthAngstrom = (138 : ℝ) / 100 ∧
  cof2PoreTopologyLedger.boroxineVertexMotifs = 6 ∧
  cof2PoreTopologyLedger.paraPhenyleneEdgeMotifs = 6 ∧
  cof2PoreTopologyLedger.boroxineVertexConnectivity = 3 ∧
  cof2PoreTopologyLedger.paraPhenyleneConnectivity = 2 ∧
  cof2PoreTopologyLedger.outwardNetworkContinuationBonds = 6 ∧
  cof2PoreSideSegmentLedger.areneCCSegments = 2 ∧
  cof2PoreSideSegmentLedger.carbonBoronSegments = 2 ∧
  cof2PoreSideSegmentLedger.boroxineRadialSegments = 2 ∧
  cof2PoreSideLengthAngstrom =
    2 * areneCCBondLengthAngstrom +
      2 * carbonBoronBondLengthAngstrom +
      2 * boronOxygenBondLengthAngstrom ∧
  cof2PoreSideLengthAngstrom = (433 : ℝ) / 50 ∧
  cof2NeglectedLinkerWidthAngstrom = 0 ∧
  cof2InternalDiameterRaw =
    Real.sqrt 3 * cof2PoreSideLengthAngstrom ∧
  cof2InternalDiameterRaw = Real.sqrt 3 * ((433 : ℝ) / 50)

/--
Raw answer-blind result contract.  The finite decimal in the accompanying
candidate record is only an interval witness; this theorem retains the exact
irrational source expression and certifies a non-degenerate enclosure.
-/
theorem cof2InternalDiameterRawResult :
    cof2InternalDiameterDerivationSpec ∧
      ((14999 : ℝ) / 1000 ≤ cof2InternalDiameterRaw ∧
        cof2InternalDiameterRaw ≤ (15 : ℝ)) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    norm_num
  constructor
  · norm_num [cof2InternalDiameterDerivationSpec,
      areneCCBondLengthAngstrom, carbonBoronBondLengthAngstrom,
      boronOxygenBondLengthAngstrom, cof2PoreTopologyLedger,
      cof2PoreSideSegmentLedger, COF2PoreSideSegmentLedger.lengthAngstrom,
      cof2PoreSideLengthAngstrom, cof2NeglectedLinkerWidthAngstrom,
      cof2InternalDiameterRaw, inscribedHexagonDiameterAngstrom]
  · norm_num [cof2InternalDiameterRaw, inscribedHexagonDiameterAngstrom,
      cof2PoreSideLengthAngstrom, COF2PoreSideSegmentLedger.lengthAngstrom,
      cof2PoreSideSegmentLedger, areneCCBondLengthAngstrom,
      carbonBoronBondLengthAngstrom, boronOxygenBondLengthAngstrom]
    constructor <;> nlinarith

/-
Machine-readable binding for the controller's problem-only, three-significant-
figure reporting check.  The declaration names below are checked by Lean; the
quantum is derived independently from the sealed reporting policy.
-/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"cof2_internal_diameter","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"15","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T3A2.cof2InternalDiameterRaw","reporting_declaration":"IChO2026Problems.T3A2.cof2InternalDiameterReportedResult"}

/--
Final answer-blind reporting contract: three significant figures at this
magnitude use the `0.1 Å` quantum, with ties rounded away from zero.
-/
theorem cof2InternalDiameterReportedResult :
    IChO2026Chem.Reporting.ReportsAtQuantum
      cof2InternalDiameterRaw (15 : ℝ) ((1 : ℝ) / 10) := by
  rcases cof2InternalDiameterRawResult with ⟨_, hlower, hupper⟩
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  constructor
  · norm_num
  constructor
  · refine ⟨150, ?_⟩
    norm_num
  rw [if_pos]
  · constructor <;> norm_num at hlower hupper ⊢ <;> linarith
  · linarith

end

end IChO2026Problems.T3A2
