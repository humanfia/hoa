import AFPS2017.Flow.Quantity
import ChemistryLib.Thermodynamics.TemperatureAdapters

/-!
# AFPS flow protocol timing

This module transcribes the six flow stages of the AFPS cycle and keeps two
kinds of timing evidence separate: exact hydraulic arithmetic from the stage
table, and qualified timing statements reported in the paper.  In particular,
the numerical difference between the 40 s nominal record and the 37.8 s
hydraulic sum is exposed without assigning it a physical cause.

Source references:

* Sanitized protocol contract (`afps2017.flow.protocol:question`).
* Published article (`afps2017.main:DOI-10.1038/nchembio.2318`).
* Public Supplementary Information
  (`afps2017.supplement:sha256-f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e`).
-/

namespace AFPS2017.Flow

/-- The role of one of the six transcribed flow stages. -/
inductive StageKind : Type where
  | priming
  | couplingDelivery
  | flushing
  | firstWash
  | deprotection
  | secondWash

/-- Whether a stage belongs to the grouped priming-and-coupling segment. -/
def StageKind.inCouplingSegment : StageKind → Bool
  | .priming | .couplingDelivery => true
  | .flushing | .firstWash | .deprotection | .secondWash => false

/-- The qualification attached to a timing reported in prose. -/
inductive TimingQualifier : Type where
  | approximately
  | nominal

/-- A numerical temperature reading together with explicit unit semantics. -/
structure TemperatureRecord : Type where
  unit : TemperatureUnit
  reading : ℝ
  semantics : ChemistryLib.Thermodynamics.TemperatureReadingSemantics unit

/-- Interpret a recorded reading as an absolute temperature. -/
def TemperatureRecord.absoluteTemperature (record : TemperatureRecord) : Temperature :=
  record.semantics.toTemperature record.reading

/-- One source-tabulated stage of the flow protocol. -/
structure FlowStage : Type where
  kind : StageKind
  deliveredVolume : ChemistryLib.Foundations.Volume
  pumpSetpoint : FlowRate
  tabulatedDuration : Duration
  temperature : TemperatureRecord

/-- A cycle represented by its ordered flow stages. -/
structure CycleRecipe : Type where
  stages : List FlowStage

/-- A timing retained with the source's own qualification. -/
structure ReportedTiming : Type where
  qualifier : TimingQualifier
  seconds : ℚ

/-- The 80 mL/min pump setpoint used for all six tabulated stages. -/
noncomputable def afps80MillilitersPerMinute : FlowRate :=
  millilitersPerMinute 80 (by norm_num)

/-- Total delivered volume of all stages in a cycle. -/
def totalVolume (recipe : CycleRecipe) :
    ChemistryLib.Units.Quantity ChemistryLib.Units.ChemicalDimension.volume :=
  sumVolumes (recipe.stages.map FlowStage.deliveredVolume)

/-- Pure hydraulic duration obtained by summing volume divided by setpoint. -/
noncomputable def hydraulicDuration (recipe : CycleRecipe) : Duration :=
  sumDurations (recipe.stages.map fun stage =>
    hydraulicDurationAtRate stage.deliveredVolume stage.pumpSetpoint)

/-- Tabulated duration of the priming and coupling-delivery stages. -/
def couplingSegmentDuration (recipe : CycleRecipe) : Duration :=
  sumDurations ((recipe.stages.filter fun stage => stage.kind.inCouplingSegment).map
    FlowStage.tabulatedDuration)

/-- Delivered volume of the priming and coupling-delivery stages. -/
def couplingSegmentVolume (recipe : CycleRecipe) :
    ChemistryLib.Units.Quantity ChemistryLib.Units.ChemicalDimension.volume :=
  sumVolumes ((recipe.stages.filter fun stage => stage.kind.inCouplingSegment).map
    FlowStage.deliveredVolume)

/-- The paper's approximately seven-second amide-bond-formation record. -/
def reportedAmideBondFormation : ReportedTiming :=
  { qualifier := .approximately, seconds := 7 }

/-- The paper's nominal forty-second per-residue cycle record. -/
def reportedNominalCycle : ReportedTiming :=
  { qualifier := .nominal, seconds := 40 }

/--
The six-stage recipe transcribed at 80 mL/min: 4.0, 5.6, 4.0, 12.8, 11.2,
and 12.8 mL, with respective tabulated durations 3.0, 4.2, 3.0, 9.6,
8.4, and 9.6 seconds.
-/
noncomputable def detailedRecipe
    (temperature : StageKind → TemperatureRecord) : CycleRecipe :=
  { stages :=
      [ { kind := .priming
          deliveredVolume := milliliters 4 (by norm_num)
          pumpSetpoint := afps80MillilitersPerMinute
          tabulatedDuration := seconds 3
          temperature := temperature .priming }
      , { kind := .couplingDelivery
          deliveredVolume := milliliters (28 / 5) (by norm_num)
          pumpSetpoint := afps80MillilitersPerMinute
          tabulatedDuration := seconds (21 / 5)
          temperature := temperature .couplingDelivery }
      , { kind := .flushing
          deliveredVolume := milliliters 4 (by norm_num)
          pumpSetpoint := afps80MillilitersPerMinute
          tabulatedDuration := seconds 3
          temperature := temperature .flushing }
      , { kind := .firstWash
          deliveredVolume := milliliters (64 / 5) (by norm_num)
          pumpSetpoint := afps80MillilitersPerMinute
          tabulatedDuration := seconds (48 / 5)
          temperature := temperature .firstWash }
      , { kind := .deprotection
          deliveredVolume := milliliters (56 / 5) (by norm_num)
          pumpSetpoint := afps80MillilitersPerMinute
          tabulatedDuration := seconds (42 / 5)
          temperature := temperature .deprotection }
      , { kind := .secondWash
          deliveredVolume := milliliters (64 / 5) (by norm_num)
          pumpSetpoint := afps80MillilitersPerMinute
          tabulatedDuration := seconds (48 / 5)
          temperature := temperature .secondWash } ] }

/-- The six transcribed stages deliver exactly 50.4 mL in total. -/
theorem detailed_totalVolume_milliliters
    (temperature : StageKind → TemperatureRecord) :
    1000 * (totalVolume (detailedRecipe temperature)).value = (252 / 5 : ℝ) := by
  norm_num [totalVolume, detailedRecipe, sumVolumes, milliliters,
    ChemistryLib.Units.PositiveQuantity.ofReal, ChemistryLib.Units.Quantity.ofReal]

/-- The detailed volume-over-setpoint calculation totals exactly 37.8 s. -/
theorem detailed_hydraulicDuration_seconds
    (temperature : StageKind → TemperatureRecord) :
    (hydraulicDuration (detailedRecipe temperature)).value = (189 / 5 : ℝ) := by
  norm_num [hydraulicDuration, detailedRecipe, sumDurations, hydraulicDurationAtRate,
    afps80MillilitersPerMinute, millilitersPerMinute, milliliters,
    ChemistryLib.Units.PositiveQuantity.ofReal, ChemistryLib.Units.Quantity.ofReal]

/-- Every transcribed stage's tabulated time agrees with volume over setpoint. -/
theorem detailed_tabulatedDuration_matches_hydraulic
    (temperature : StageKind → TemperatureRecord) (flowStage : FlowStage)
    (membership : flowStage ∈ (detailedRecipe temperature).stages) :
    (hydraulicDurationAtRate flowStage.deliveredVolume flowStage.pumpSetpoint).value =
      flowStage.tabulatedDuration.value := by
  simp only [detailedRecipe, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with h | h | h | h | h | h
  all_goals subst flowStage
  all_goals norm_num [hydraulicDurationAtRate, afps80MillilitersPerMinute,
    millilitersPerMinute, milliliters, seconds,
    ChemistryLib.Units.PositiveQuantity.ofReal, ChemistryLib.Units.Quantity.ofReal]

/-- The grouped coupling segment delivers exactly 9.6 mL. -/
theorem grouped_couplingVolume_milliliters
    (temperature : StageKind → TemperatureRecord) :
    1000 * (couplingSegmentVolume (detailedRecipe temperature)).value =
      (48 / 5 : ℝ) := by
  norm_num [couplingSegmentVolume, detailedRecipe, StageKind.inCouplingSegment,
    sumVolumes, milliliters, ChemistryLib.Units.PositiveQuantity.ofReal,
    ChemistryLib.Units.Quantity.ofReal]

/-- The grouped coupling segment lasts exactly 7.2 s. -/
theorem grouped_couplingDuration_seconds
    (temperature : StageKind → TemperatureRecord) :
    (couplingSegmentDuration (detailedRecipe temperature)).value = (36 / 5 : ℝ) := by
  norm_num [couplingSegmentDuration, detailedRecipe, StageKind.inCouplingSegment,
    sumDurations, seconds, ChemistryLib.Units.Quantity.ofReal]

/-- The nominal 40 s record is not the exact 37.8 s hydraulic sum. -/
theorem hydraulicDuration_ne_reportedNominal
    (temperature : StageKind → TemperatureRecord) :
    (hydraulicDuration (detailedRecipe temperature)).value ≠
      (reportedNominalCycle.seconds : ℝ) := by
  rw [detailed_hydraulicDuration_seconds temperature]
  norm_num [reportedNominalCycle]

/-- The numerical nominal-minus-hydraulic difference is exactly 2.2 s. -/
theorem reported_nominal_minus_hydraulic_gap
    (temperature : StageKind → TemperatureRecord) :
    (reportedNominalCycle.seconds : ℝ) -
        (hydraulicDuration (detailedRecipe temperature)).value = (11 / 5 : ℝ) := by
  rw [detailed_hydraulicDuration_seconds temperature]
  norm_num [reportedNominalCycle]

end AFPS2017.Flow
