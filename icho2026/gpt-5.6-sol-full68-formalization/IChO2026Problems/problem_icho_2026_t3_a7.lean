import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, theory problem 3, part 7

This file formalizes the source-side derivation of the equilibrium absorption
capacity of COF-9 and the mean number of uranyl ions absorbed per honeycomb
pore.  The numerical inputs remain in their printed units until the explicit
unit conversions below.

The molecular formula needed for the pore count is derived here from the two
bound problem images.  No result from an earlier generated problem file is
imported.
-/

namespace IChO2026Problems.IChO2026T3A7

open IChO2026Chem.Reporting

noncomputable section

/-! ## Chemical identities and the equilibrium experiment -/

/-- The phases which are explicitly relevant to the adsorption experiment. -/
inductive MaterialPhase where
  | solid
  | aqueous
  deriving DecidableEq, Repr

/-- Atom and charge ledger for the uranium-bearing ion named by the source. -/
structure UraniumOxygenIon where
  uraniumAtoms : ℕ
  oxygenAtoms : ℕ
  charge : ℤ
  deriving DecidableEq, Repr

/-- The source-stipulated uranium species `UO₂²⁺`. -/
def uranylIon : UraniumOxygenIon := ⟨1, 2, 2⟩

/-- Explicit formula/charge carrier for the all-uranium-as-uranyl assumption. -/
def UranylIdentitySpec : Prop :=
  uranylIon.uraniumAtoms = 1 ∧
  uranylIon.oxygenAtoms = 2 ∧
  uranylIon.charge = 2

/--
The four displayed readings in the source experiment.  The type fixes the
dissolved uranium-bearing species to `UO₂²⁺`: this is the source's explicit
assumption that all uranium is present as uranyl ions.
-/
structure UranylAdsorptionExperiment where
  dissolvedSpecies : UraniumOxygenIon
  adsorbentPhase : MaterialPhase
  solutionPhase : MaterialPhase
  cof9MassMg : ℝ
  initialUranylConcentrationMgPerDm3 : ℝ
  solutionVolumeMl : ℝ
  equilibriumUranylConcentrationMgPerDm3 : ℝ

/-- The central values printed on page 7 of the bound problem. -/
def sourceExperiment : UranylAdsorptionExperiment where
  dissolvedSpecies := uranylIon
  adsorbentPhase := .solid
  solutionPhase := .aqueous
  cof9MassMg := 5.000
  initialUranylConcentrationMgPerDm3 := 19.90
  solutionVolumeMl := 200.0
  equilibriumUranylConcentrationMgPerDm3 := 9.225

/--
Interpret each experimental display at half of its last displayed quantum.
This carrier records the source report's measurement policy without rounding
an intermediate calculation.
-/
def ConsistentWithSourceDisplays (actual : UranylAdsorptionExperiment) : Prop :=
  actual.dissolvedSpecies = uranylIon ∧
  actual.adsorbentPhase = .solid ∧
  actual.solutionPhase = .aqueous ∧
  ConsistentMeasurement actual.cof9MassMg sourceExperiment.cof9MassMg 0.001 ∧
  ConsistentMeasurement
    actual.initialUranylConcentrationMgPerDm3
    sourceExperiment.initialUranylConcentrationMgPerDm3 0.01 ∧
  ConsistentMeasurement actual.solutionVolumeMl sourceExperiment.solutionVolumeMl 0.1 ∧
  ConsistentMeasurement
    actual.equilibriumUranylConcentrationMgPerDm3
    sourceExperiment.equilibriumUranylConcentrationMgPerDm3 0.001

/-- Convert the displayed solution volume from mL to dm³. -/
def solutionVolumeDm3 (e : UranylAdsorptionExperiment) : ℝ :=
  e.solutionVolumeMl / 1000

/--
Mass of uranyl removed from the *whole solution*, in mg.  The numerator is the
drop in uranyl mass concentration multiplied by total solution volume.
-/
def adsorbedUranylMassMg (e : UranylAdsorptionExperiment) : ℝ :=
  (e.initialUranylConcentrationMgPerDm3 -
      e.equilibriumUranylConcentrationMgPerDm3) * solutionVolumeDm3 e

/--
Equilibrium absorption capacity in mg of uranyl per g of the original COF-9
adsorbent.  In particular, the denominator is support mass, not total mass of
the post-adsorption mixture.
-/
def equilibriumAbsorptionCapacity (e : UranylAdsorptionExperiment) : ℝ :=
  adsorbedUranylMassMg e / (e.cof9MassMg / 1000)

/-! ## Source-first image and component accounting -/

/-- Counts of C, H, N, and O atoms in a molecular component. -/
structure CHNOComposition where
  carbon : ℕ
  hydrogen : ℕ
  nitrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq, Repr

namespace CHNOComposition

/-- Componentwise addition of molecular compositions. -/
def add (x y : CHNOComposition) : CHNOComposition where
  carbon := x.carbon + y.carbon
  hydrogen := x.hydrogen + y.hydrogen
  nitrogen := x.nitrogen + y.nitrogen
  oxygen := x.oxygen + y.oxygen

/-- `n` copies of a molecular composition. -/
def scale (n : ℕ) (x : CHNOComposition) : CHNOComposition where
  carbon := n * x.carbon
  hydrogen := n * x.hydrogen
  nitrogen := n * x.nitrogen
  oxygen := n * x.oxygen

/-- Componentwise removal of a known leaving composition. -/
def subtract (x y : CHNOComposition) : CHNOComposition where
  carbon := x.carbon - y.carbon
  hydrogen := x.hydrogen - y.hydrogen
  nitrogen := x.nitrogen - y.nitrogen
  oxygen := x.oxygen - y.oxygen

/-- The leaving composition is no larger than the input in every element. -/
def FitsIn (leaving input : CHNOComposition) : Prop :=
  leaving.carbon ≤ input.carbon ∧
  leaving.hydrogen ≤ input.hydrogen ∧
  leaving.nitrogen ≤ input.nitrogen ∧
  leaving.oxygen ≤ input.oxygen

end CHNOComposition

/--
The complete connected pore visible in the page-7 COF-9 panel has three red
E1-derived nodes and three black D2-derived nodes around its boundary.  Each is
trivalent; the third bond of every boundary node crosses into the surrounding
network.  Nodes are incident to three pores and perimeter links to two pores.
-/
structure PoreImageLedger where
  e1BoundaryNodes : ℕ
  d2BoundaryNodes : ℕ
  e1NodeDegree : ℕ
  d2NodeDegree : ℕ
  perimeterLinkages : ℕ
  outgoingCrossBoundaryBonds : ℕ
  poresIncidentPerNode : ℕ
  poresIncidentPerLinkage : ℕ
  nitrileSitesPerE1Node : ℕ
  deriving DecidableEq, Repr

/-- Recount of both bound figures, with provenance `problem_image`. -/
def sourcePoreImageLedger : PoreImageLedger where
  e1BoundaryNodes := 3
  d2BoundaryNodes := 3
  e1NodeDegree := 3
  d2NodeDegree := 3
  perimeterLinkages := 6
  outgoingCrossBoundaryBonds := 6
  poresIncidentPerNode := 3
  poresIncidentPerLinkage := 2
  nitrileSitesPerE1Node := 3

/-- Nontrivial incidence and cross-boundary check for the visual recount. -/
def SourcePoreImageLedgerSpec : Prop :=
  let l := sourcePoreImageLedger
  l.e1BoundaryNodes = 3 ∧
  l.d2BoundaryNodes = 3 ∧
  l.e1NodeDegree = 3 ∧
  l.d2NodeDegree = 3 ∧
  l.perimeterLinkages = 6 ∧
  l.outgoingCrossBoundaryBonds = 6 ∧
  l.poresIncidentPerNode = 3 ∧
  l.poresIncidentPerLinkage = 2 ∧
  l.nitrileSitesPerE1Node = 3 ∧
  l.e1NodeDegree * l.e1BoundaryNodes + l.d2NodeDegree * l.d2BoundaryNodes =
    2 * l.perimeterLinkages + l.outgoingCrossBoundaryBonds

/-- Effective E1-derived building blocks assigned to one pore after sharing. -/
def effectiveE1NodesPerPore : ℕ :=
  sourcePoreImageLedger.e1BoundaryNodes /
    sourcePoreImageLedger.poresIncidentPerNode

/-- Effective D2-derived building blocks assigned to one pore after sharing. -/
def effectiveD2NodesPerPore : ℕ :=
  sourcePoreImageLedger.d2BoundaryNodes /
    sourcePoreImageLedger.poresIncidentPerNode

/-- Effective condensation linkages assigned to one pore after edge sharing. -/
def effectiveLinkagesPerPore : ℕ :=
  sourcePoreImageLedger.perimeterLinkages /
    sourcePoreImageLedger.poresIncidentPerLinkage

/-- Nitrile sites converted to amidoxime sites in one effective pore unit. -/
def amidoximeSitesPerPore : ℕ :=
  effectiveE1NodesPerPore * sourcePoreImageLedger.nitrileSitesPerE1Node

/-!
Page 6 depicts E1 as a `C₆H₃` arene core bearing three `C₂H₂N`
cyanomethyl arms.  It depicts D2 as a `C₃N₃` triazine core bearing three
para-phenylene-plus-formyl arms.  These component definitions retain that
visual decomposition rather than inserting a final pore formula.
-/

def e1AreneCore : CHNOComposition := ⟨6, 3, 0, 0⟩
def cyanomethylArm : CHNOComposition := ⟨2, 2, 1, 0⟩
def e1Composition : CHNOComposition :=
  CHNOComposition.add e1AreneCore (CHNOComposition.scale 3 cyanomethylArm)

def d2TriazineCore : CHNOComposition := ⟨3, 0, 3, 0⟩
def paraPhenylene : CHNOComposition := ⟨6, 4, 0, 0⟩
def formylGroup : CHNOComposition := ⟨1, 1, 0, 1⟩
def d2Arm : CHNOComposition := CHNOComposition.add paraPhenylene formylGroup
def d2Composition : CHNOComposition :=
  CHNOComposition.add d2TriazineCore (CHNOComposition.scale 3 d2Arm)

def waterComposition : CHNOComposition := ⟨0, 2, 0, 1⟩
def hydroxylamineComposition : CHNOComposition := ⟨0, 3, 1, 1⟩

/-- E1 and D2 material assigned to one honeycomb pore before condensation. -/
def poreMonomerInputComposition : CHNOComposition :=
  CHNOComposition.add
    (CHNOComposition.scale effectiveE1NodesPerPore e1Composition)
    (CHNOComposition.scale effectiveD2NodesPerPore d2Composition)

/-- Three water losses from the three E1--D2 condensations per pore. -/
def poreCondensationLoss : CHNOComposition :=
  CHNOComposition.scale effectiveLinkagesPerPore waterComposition

/-- Composition of the source-depicted COF-8 unit assigned to one pore. -/
def cof8PoreComposition : CHNOComposition :=
  CHNOComposition.subtract poreMonomerInputComposition poreCondensationLoss

/-- Hydroxylamine added across every nitrile site in the depicted conversion. -/
def poreHydroxylamineInput : CHNOComposition :=
  CHNOComposition.scale amidoximeSitesPerPore hydroxylamineComposition

/-- Composition of the complete effective COF-9 pore unit. -/
def cof9PoreComposition : CHNOComposition :=
  CHNOComposition.add cof8PoreComposition poreHydroxylamineInput

/--
Outcome-decisive atom ledgers for the two quantitative material stages.  The
finite domain is exactly E1, D2, COF-8, water, hydroxylamine, and COF-9; no
anonymous stream is admitted.
-/
def CofFormationAndModificationAtomLedgers : Prop :=
  CHNOComposition.FitsIn poreCondensationLoss poreMonomerInputComposition ∧
  poreMonomerInputComposition =
    CHNOComposition.add cof8PoreComposition poreCondensationLoss ∧
  CHNOComposition.add cof8PoreComposition poreHydroxylamineInput =
    cof9PoreComposition

theorem sourcePoreTopologyAccounting :
    SourcePoreImageLedgerSpec ∧
    effectiveE1NodesPerPore = 1 ∧
    effectiveD2NodesPerPore = 1 ∧
    effectiveLinkagesPerPore = 3 ∧
    amidoximeSitesPerPore = 3 := by
  norm_num [SourcePoreImageLedgerSpec, sourcePoreImageLedger,
    effectiveE1NodesPerPore, effectiveD2NodesPerPore,
    effectiveLinkagesPerPore, amidoximeSitesPerPore]

theorem sourceBuildingBlockCompositions :
    e1Composition = ⟨12, 9, 3, 0⟩ ∧
    d2Composition = ⟨24, 15, 3, 3⟩ := by
  constructor <;> rfl

theorem quantitativeMaterialStageAtomAccounting :
    CofFormationAndModificationAtomLedgers ∧
    cof8PoreComposition = ⟨36, 18, 6, 0⟩ ∧
    cof9PoreComposition = ⟨36, 27, 9, 3⟩ := by
  norm_num [CofFormationAndModificationAtomLedgers,
    CHNOComposition.FitsIn, poreMonomerInputComposition,
    poreCondensationLoss, cof8PoreComposition, poreHydroxylamineInput,
    cof9PoreComposition, effectiveE1NodesPerPore,
    effectiveD2NodesPerPore, effectiveLinkagesPerPore,
    amidoximeSitesPerPore, sourcePoreImageLedger, e1Composition,
    e1AreneCore, cyanomethylArm, d2Composition, d2TriazineCore,
    d2Arm, paraPhenylene, formylGroup, waterComposition,
    hydroxylamineComposition, CHNOComposition.add,
    CHNOComposition.scale, CHNOComposition.subtract]

/-! ## Pinned conventional molar masses -/

/-
Offline registry provenance for the five exact conventional inputs below:
dataset ciaaw-abridged-2024+ame2020-subset+archon-templates-v1+
contest-interpretation-v1+trusted-empirical-rules-v1;
dataset SHA-256 11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5.
Atomic-weight record SHA-256 values:
C 0f558fc72d4299d061e9d29f394ebed43fc8246f7dbdb402bbb2a338cfbe4b8a;
H 8e5f2e512d11f6c3409197956a4f015f6144f43057a286107064436c64b4bce5;
N 5ca62d438a6594458420ed7f5d2072a583a9ae8c71a29d75b561edb28b6f065c;
O d55ad5591b6aebea80363701cf500c7e0a46a5f46fd4fcfef16cc331efcc0588;
U 18330650985fd5a061184983d3884beb83604e75446c7ec00dd6f33766382767.
-/

def carbonAtomicWeight : ℝ := 12.011
def hydrogenAtomicWeight : ℝ := 1.0080
def nitrogenAtomicWeight : ℝ := 14.007
def oxygenAtomicWeight : ℝ := 15.999
def uraniumAtomicWeight : ℝ := 238.03

/-- Molar mass in g mol⁻¹ calculated from a CHNO composition. -/
def chnoMolarMass (c : CHNOComposition) : ℝ :=
  c.carbon * carbonAtomicWeight +
  c.hydrogen * hydrogenAtomicWeight +
  c.nitrogen * nitrogenAtomicWeight +
  c.oxygen * oxygenAtomicWeight

/-- Conventional molar mass of the effective COF-9 pore unit, in g mol⁻¹. -/
def cof9PoreMolarMassGPerMol : ℝ := chnoMolarMass cof9PoreComposition

/-- Conventional molar mass of `UO₂²⁺`, in g mol⁻¹. -/
def uranylMolarMassGPerMol : ℝ :=
  uranylIon.uraniumAtoms * uraniumAtomicWeight +
    uranylIon.oxygenAtoms * oxygenAtomicWeight

/-
Independent aggregate registry cross-checks:
`C36H27N9O3` gives 633.672 g mol^-1, record SHA-256
4c08e5cc8fc09e3bd98e6c3572685f7893544144fde54c0f913c4b9f5ffde384;
`UO2` gives 270.028 g mol^-1, record SHA-256
f28469ce635cdd4a6cf12a345ce780b39df4f6ef5ff346c55cc3bb7312b54e18.
-/
theorem conventionalMolarMasses :
    cof9PoreMolarMassGPerMol = 633.672 ∧
    uranylMolarMassGPerMol = 270.028 := by
  constructor
  · change chnoMolarMass cof9PoreComposition = 633.672
    rw [quantitativeMaterialStageAtomAccounting.2.2]
    norm_num [chnoMolarMass, carbonAtomicWeight, hydrogenAtomicWeight,
      nitrogenAtomicWeight, oxygenAtomicWeight]
  · norm_num [uranylMolarMassGPerMol, uranylIon, uraniumAtomicWeight,
      oxygenAtomicWeight]

/-! ## Exact raw outputs -/

/-- Amount of adsorbed uranyl, in mol. -/
def adsorbedUranylMoles (e : UranylAdsorptionExperiment) : ℝ :=
  (adsorbedUranylMassMg e / 1000) / uranylMolarMassGPerMol

/-- Amount of effective honeycomb pores in the dry COF-9 sample, in mol. -/
def poreMolesInAdsorbent (e : UranylAdsorptionExperiment) : ℝ :=
  (e.cof9MassMg / 1000) / cof9PoreMolarMassGPerMol

/-- Mean uranyl-ion count per pore; the common Avogadro factor cancels. -/
def uranylIonsPerPore (e : UranylAdsorptionExperiment) : ℝ :=
  adsorbedUranylMoles e / poreMolesInAdsorbent e

/-- Source-derived, unrounded equilibrium capacity in mg g⁻¹. -/
def equilibriumAbsorptionCapacityRaw : ℝ :=
  equilibriumAbsorptionCapacity sourceExperiment

/-- Source-derived, unrounded mean number of uranyl ions per pore. -/
def uranylIonsPerPoreRaw : ℝ := uranylIonsPerPore sourceExperiment

theorem avogadroFactorCancels
    (entitiesPerMol : ℝ) (hEntitiesPerMol : 0 < entitiesPerMol) :
    (adsorbedUranylMoles sourceExperiment * entitiesPerMol) /
        (poreMolesInAdsorbent sourceExperiment * entitiesPerMol) =
      uranylIonsPerPoreRaw := by
  exact mul_div_mul_right _ _ (ne_of_gt hEntitiesPerMol)

theorem adsorbedUranylMassExact :
    adsorbedUranylMassMg sourceExperiment = 2.135 := by
  norm_num [adsorbedUranylMassMg, solutionVolumeDm3, sourceExperiment]

theorem equilibriumAbsorptionCapacityExact :
    equilibriumAbsorptionCapacityRaw = 427 := by
  norm_num [equilibriumAbsorptionCapacityRaw, equilibriumAbsorptionCapacity,
    adsorbedUranylMassMg, solutionVolumeDm3, sourceExperiment]

theorem uranylIonsPerPoreExact :
    uranylIonsPerPoreRaw = (33822243 : ℝ) / 33753500 := by
  unfold uranylIonsPerPoreRaw uranylIonsPerPore adsorbedUranylMoles
    poreMolesInAdsorbent
  rw [conventionalMolarMasses.1, conventionalMolarMasses.2]
  norm_num [adsorbedUranylMassMg, solutionVolumeDm3, sourceExperiment]

/-- The raw mixed-output semantic contract, in requested-output order. -/
def RawResultSpec : Prop :=
  UranylIdentitySpec ∧
  SourcePoreImageLedgerSpec ∧
  CofFormationAndModificationAtomLedgers ∧
  cof9PoreComposition = ⟨36, 27, 9, 3⟩ ∧
  adsorbedUranylMassMg sourceExperiment = 2.135 ∧
  equilibriumAbsorptionCapacityRaw = 427 ∧
  uranylIonsPerPoreRaw = (33822243 : ℝ) / 33753500

/-- Hash-bound raw mixed-output carrier for the answer-blind result record. -/
theorem rawResult :
    ("ae3a5906ac9314bb70d633986111e4fddfe8a1ba5e0a98c2baf56092a22d77f0" : String) =
        "ae3a5906ac9314bb70d633986111e4fddfe8a1ba5e0a98c2baf56092a22d77f0" ∧
      RawResultSpec := by
  constructor
  · rfl
  · unfold RawResultSpec
    exact ⟨by norm_num [UranylIdentitySpec, uranylIon],
      sourcePoreTopologyAccounting.1,
      quantitativeMaterialStageAtomAccounting.1,
      quantitativeMaterialStageAtomAccounting.2.2,
      adsorbedUranylMassExact, equilibriumAbsorptionCapacityExact,
      uranylIonsPerPoreExact⟩

/-! ## Final reporting, fixed before proof -/

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"equilibrium_absorption_capacity","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"427","reporting_quantum":"1","raw_declaration":"IChO2026Problems.IChO2026T3A7.equilibriumAbsorptionCapacityRaw","reporting_declaration":"IChO2026Problems.IChO2026T3A7.equilibriumAbsorptionCapacityReportsAtThreeSignificantFigures"}
theorem equilibriumAbsorptionCapacityReportsAtThreeSignificantFigures :
    ReportsAtQuantum equilibriumAbsorptionCapacityRaw 427 1 := by
  rw [equilibriumAbsorptionCapacityExact]
  unfold ReportsAtQuantum
  refine ⟨by norm_num, ⟨427, by norm_num⟩, ?_⟩
  norm_num

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"uranyl_ions_per_pore","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"1.00","reporting_quantum":"0.01","raw_declaration":"IChO2026Problems.IChO2026T3A7.uranylIonsPerPoreRaw","reporting_declaration":"IChO2026Problems.IChO2026T3A7.uranylIonsPerPoreReportsAtThreeSignificantFigures"}
theorem uranylIonsPerPoreReportsAtThreeSignificantFigures :
    ReportsAtQuantum uranylIonsPerPoreRaw 1 ((1 : ℝ) / 100) := by
  rw [uranylIonsPerPoreExact]
  unfold ReportsAtQuantum
  refine ⟨by norm_num, ⟨100, by norm_num⟩, ?_⟩
  norm_num

/-- The reported mixed-output semantic contract, in requested-output order. -/
def ReportedResultSpec : Prop :=
  RawResultSpec ∧
  ReportsAtQuantum equilibriumAbsorptionCapacityRaw 427 1 ∧
  ReportsAtQuantum uranylIonsPerPoreRaw 1 ((1 : ℝ) / 100)

/-- Hash-bound reported mixed-output carrier for the answer-blind result record. -/
theorem reportedResult :
    ("f0c6e5243b707d0c0911ec95287da9b85f0563f3bf08282b0b7cf1c5aac43770" : String) =
        "f0c6e5243b707d0c0911ec95287da9b85f0563f3bf08282b0b7cf1c5aac43770" ∧
      ReportedResultSpec := by
  constructor
  · rfl
  · exact ⟨rawResult.2,
      equilibriumAbsorptionCapacityReportsAtThreeSignificantFigures,
      uranylIonsPerPoreReportsAtThreeSignificantFigures⟩

/--
The printed measurement cells are narrow enough that every compatible actual
experiment has the same two requested three-significant-figure reports.
-/
theorem sourceMeasurementIntervalsPreserveReports
    (actual : UranylAdsorptionExperiment)
    (hActual : ConsistentWithSourceDisplays actual) :
    ReportsAtQuantum (equilibriumAbsorptionCapacity actual) 427 1 ∧
    ReportsAtQuantum (uranylIonsPerPore actual) 1 ((1 : ℝ) / 100) := by
  rcases hActual with ⟨_, _, _, hm, hci, hv, hce⟩
  rcases hm with ⟨_, hm⟩
  rcases hci with ⟨_, hci⟩
  rcases hv with ⟨_, hv⟩
  rcases hce with ⟨_, hce⟩
  rcases abs_le.mp hm with ⟨hmLower', hmUpper'⟩
  rcases abs_le.mp hci with ⟨hciLower', hciUpper'⟩
  rcases abs_le.mp hv with ⟨hvLower', hvUpper'⟩
  rcases abs_le.mp hce with ⟨hceLower', hceUpper'⟩
  norm_num [sourceExperiment] at hmLower' hmUpper' hciLower' hciUpper' hvLower' hvUpper' hceLower' hceUpper'
  have hmLower : (9999 : ℝ) / 2000 ≤ actual.cof9MassMg := by
    linarith
  have hmUpper : actual.cof9MassMg ≤ (10001 : ℝ) / 2000 := by
    linarith
  have hvLower : (3999 : ℝ) / 20 ≤ actual.solutionVolumeMl := by
    linarith
  have hvUpper : actual.solutionVolumeMl ≤ (4001 : ℝ) / 20 := by
    linarith
  have hDeltaLower :
      (21339 : ℝ) / 2000 ≤
        actual.initialUranylConcentrationMgPerDm3 -
          actual.equilibriumUranylConcentrationMgPerDm3 := by
    linarith
  have hDeltaUpper :
      actual.initialUranylConcentrationMgPerDm3 -
          actual.equilibriumUranylConcentrationMgPerDm3 ≤
        (21361 : ℝ) / 2000 := by
    linarith
  have hmPos : 0 < actual.cof9MassMg := by
    linarith
  have hvPos : 0 < actual.solutionVolumeMl := by
    linarith
  have hDeltaPos :
      0 < actual.initialUranylConcentrationMgPerDm3 -
        actual.equilibriumUranylConcentrationMgPerDm3 := by
    linarith
  have hProductLower :
      ((21339 : ℝ) / 2000) * ((3999 : ℝ) / 20) ≤
        (actual.initialUranylConcentrationMgPerDm3 -
            actual.equilibriumUranylConcentrationMgPerDm3) *
          actual.solutionVolumeMl := by
    exact mul_le_mul hDeltaLower hvLower (by norm_num) (le_of_lt hDeltaPos)
  have hProductUpper :
      (actual.initialUranylConcentrationMgPerDm3 -
            actual.equilibriumUranylConcentrationMgPerDm3) *
          actual.solutionVolumeMl ≤
        ((21361 : ℝ) / 2000) * ((4001 : ℝ) / 20) := by
    exact mul_le_mul hDeltaUpper hvUpper (le_of_lt hvPos) (by norm_num)
  have hMassDenominatorPos : 0 < actual.cof9MassMg / 1000 := by
    positivity
  have hCapacityLower :
      427 - (1 : ℝ) / 2 ≤ equilibriumAbsorptionCapacity actual := by
    unfold equilibriumAbsorptionCapacity
    apply (le_div_iff₀ hMassDenominatorPos).2
    unfold adsorbedUranylMassMg solutionVolumeDm3
    nlinarith [hProductLower, hmUpper]
  have hCapacityUpper :
      equilibriumAbsorptionCapacity actual < 427 + (1 : ℝ) / 2 := by
    unfold equilibriumAbsorptionCapacity
    apply (div_lt_iff₀ hMassDenominatorPos).2
    unfold adsorbedUranylMassMg solutionVolumeDm3
    nlinarith [hProductUpper, hmLower]
  have hCapacityNonnegative : 0 ≤ equilibriumAbsorptionCapacity actual := by
    linarith
  have hRatio :
      uranylIonsPerPore actual =
        equilibriumAbsorptionCapacity actual *
          (633.672 / (1000 * 270.028)) := by
    unfold uranylIonsPerPore adsorbedUranylMoles poreMolesInAdsorbent
      equilibriumAbsorptionCapacity
    rw [conventionalMolarMasses.1, conventionalMolarMasses.2]
    field_simp [ne_of_gt hmPos]
  have hRatioLower :
      1 - ((1 : ℝ) / 100) / 2 ≤ uranylIonsPerPore actual := by
    rw [hRatio]
    norm_num at hCapacityLower ⊢
    nlinarith
  have hRatioUpper :
      uranylIonsPerPore actual < 1 + ((1 : ℝ) / 100) / 2 := by
    rw [hRatio]
    norm_num at hCapacityUpper ⊢
    nlinarith
  have hRatioNonnegative : 0 ≤ uranylIonsPerPore actual := by
    linarith
  constructor
  · unfold ReportsAtQuantum
    refine ⟨by norm_num, ⟨427, by norm_num⟩, ?_⟩
    rw [if_pos hCapacityNonnegative]
    exact ⟨hCapacityLower, hCapacityUpper⟩
  · unfold ReportsAtQuantum
    refine ⟨by norm_num, ⟨100, by norm_num⟩, ?_⟩
    rw [if_pos hRatioNonnegative]
    exact ⟨hRatioLower, hRatioUpper⟩

/-- Complete formal target for T3-A7. -/
theorem problem_icho_2026_t3_a7 :
    RawResultSpec ∧ ReportedResultSpec := by
  exact ⟨rawResult.2, reportedResult.2⟩

end

end IChO2026Problems.IChO2026T3A7
