import Mathlib
import Physlib

namespace Ipho2026Gpt56solBlind

namespace ProblemIPhO2026_4_A_2

/-!
# IPhO 2026, experimental problem 4, part A.2

Part A.2 asks for a table of observations made during an experiment.  The
problem statement gives no numerical pressure--temperature readings, so those
readings are external input to the formalization.  The apparatus, true gas
states, ideal-gas law, and fixed sensor functions give that input its physical
provenance; they do not manufacture an empirical data set.

All dimensional quantities below are `WithDim` quantities over Physlib's
seven-base ISQ basis.  Their stored real values are coherent-SI coordinates.
In particular, no ISQ `HasDim` or `Dimensionful` instance is invented.
-/

/-! ## ISQ dimensions and coherent-SI quantities -/

/-- The ISQ length dimension. -/
def lengthDimension : Dimension ISQDimensionBase :=
  Dimension.single .length

/-- The ISQ mass dimension. -/
def massDimension : Dimension ISQDimensionBase :=
  Dimension.single .mass

/-- The ISQ time dimension. -/
def timeDimension : Dimension ISQDimensionBase :=
  Dimension.single .time

/-- The ISQ thermodynamic-temperature dimension. -/
def temperatureDimension : Dimension ISQDimensionBase :=
  Dimension.single .temperature

/-- The ISQ amount-of-substance dimension. -/
def amountDimension : Dimension ISQDimensionBase :=
  Dimension.single .amount

/-- Area has dimension `L^2`. -/
def areaDimension : Dimension ISQDimensionBase :=
  lengthDimension * lengthDimension

/-- Volume has dimension `L^3`. -/
def volumeDimension : Dimension ISQDimensionBase :=
  areaDimension * lengthDimension

/-- Mass density has dimension `M L^-3`. -/
def massDensityDimension : Dimension ISQDimensionBase :=
  massDimension * volumeDimension⁻¹

/-- Molar mass has dimension `M A^-1`. -/
def molarMassDimension : Dimension ISQDimensionBase :=
  massDimension * amountDimension⁻¹

/-- Pressure has dimension `M L^-1 T^-2`. -/
def pressureDimension : Dimension ISQDimensionBase :=
  massDimension * lengthDimension⁻¹ * timeDimension⁻¹ * timeDimension⁻¹

/-- A molar gas constant has dimension `M L^2 T^-2 A^-1 Θ^-1`. -/
def molarGasConstantDimension : Dimension ISQDimensionBase :=
  massDimension * areaDimension * timeDimension⁻¹ * timeDimension⁻¹ *
    amountDimension⁻¹ * temperatureDimension⁻¹

/-- An Avogadro-type conversion factor has inverse-amount dimension. -/
def inverseAmountDimension : Dimension ISQDimensionBase :=
  amountDimension⁻¹

/-- A real-valued length quantity. -/
abbrev Length := WithDim lengthDimension ℝ

/-- A real-valued area quantity. -/
abbrev Area := WithDim areaDimension ℝ

/-- A real-valued volume quantity. -/
abbrev Volume := WithDim volumeDimension ℝ

/-- A real-valued mass quantity. -/
abbrev Mass := WithDim massDimension ℝ

/-- A real-valued mass-density quantity. -/
abbrev MassDensity := WithDim massDensityDimension ℝ

/-- A real-valued molar-mass quantity. -/
abbrev MolarMass := WithDim molarMassDimension ℝ

/-- A real-valued amount-of-substance quantity. -/
abbrev AmountOfSubstance := WithDim amountDimension ℝ

/-- A typed absolute-temperature value or temperature sensor reading. -/
abbrev TemperatureMeasurement := WithDim temperatureDimension ℝ

/-- A typed pressure value or pressure sensor reading. -/
abbrev PressureMeasurement := WithDim pressureDimension ℝ

/-- A typed universal molar gas constant. -/
abbrev MolarGasConstant := WithDim molarGasConstantDimension ℝ

/-- A typed Avogadro conversion factor. -/
abbrev AvogadroConstant := WithDim inverseAmountDimension ℝ

/-- A real-valued dimensionless molecule count. -/
abbrev MoleculeCount := WithDim (1 : Dimension ISQDimensionBase) ℝ

/-- The one unit choice used for every stored coordinate in this model. -/
noncomputable def coherentSIUnits : SIUnitChoices := SIUnitChoices.SI

/-- The coherent-SI coordinate boundary for an ISQ `WithDim` quantity. -/
def SICoordinate {d : Dimension ISQDimensionBase} (quantity : WithDim d ℝ) : ℝ :=
  quantity.val

/-- Re-express a stored coherent-SI coordinate in another typed ISQ unit
choice.  Physical predicates below use `SICoordinate`; this definition records
the explicit bridge to Physlib's basis-parametric unit system. -/
noncomputable def coordinateIn (units : SIUnitChoices)
    {d : Dimension ISQDimensionBase} (quantity : WithDim d ℝ) : ℝ :=
  (SIUnitChoices.dimScale coherentSIUnits units d : ℝ) * quantity.val

/-! ## Source-unit coordinates -/

/-- Construct a length whose source coordinate is in millimetres. -/
noncomputable def LengthInMillimetres (x : ℝ) : Length := ⟨x / 1000⟩

/-- Construct a length whose source coordinate is in centimetres. -/
noncomputable def LengthInCentimetres (x : ℝ) : Length := ⟨x / 100⟩

/-- Construct a mass density whose source coordinate is in kilograms per
cubic metre. -/
def MassDensityInKilogramsPerCubicMetre (x : ℝ) : MassDensity := ⟨x⟩

/-- Construct a molar mass whose source coordinate is in grams per mole. -/
noncomputable def MolarMassInGramsPerMole (x : ℝ) : MolarMass := ⟨x / 1000⟩

/-- Construct an Avogadro conversion factor whose source coordinate is in
inverse moles. -/
def AvogadroConstantInPerMole (x : ℝ) : AvogadroConstant := ⟨x⟩

/-! ## Figure 17 geometry and confined-air volume -/

/-- `x` lies in the absolute-error interval with centre `centre` and
nonnegative half-width `tolerance`. -/
def WithinLengthTolerance (x centre tolerance : Length) : Prop :=
  0 ≤ SICoordinate tolerance ∧
    |SICoordinate x - SICoordinate centre| ≤ SICoordinate tolerance

/-- The displayed diameter and adjacent acrylic-wall thickness for one
cylinder.  For IC the displayed diameter is its clear inside diameter; for OC
it is its outside diameter. -/
structure CylinderDimensions where
  displayedDiameter : Length
  wallThickness : Length

/-- The two distinct cylinder measurements shown in the Figure 17
cross-section. -/
structure Figure17Dimensions where
  innerCylinder : CylinderDimensions
  outerCylinder : CylinderDimensions

/-- All four independent Figure 17 tolerance intervals, positivity of the
measured lengths, and the physical nesting of IC inside OC. -/
def SatisfiesFigure17Geometry (figure : Figure17Dimensions) : Prop :=
  WithinLengthTolerance figure.outerCylinder.displayedDiameter
    (LengthInMillimetres (748 / 10)) (LengthInMillimetres (1 / 10)) ∧
  WithinLengthTolerance figure.innerCylinder.displayedDiameter
    (LengthInMillimetres (337 / 10)) (LengthInMillimetres (1 / 10)) ∧
  WithinLengthTolerance figure.innerCylinder.wallThickness
    (LengthInMillimetres (34 / 10)) (LengthInMillimetres (1 / 10)) ∧
  WithinLengthTolerance figure.outerCylinder.wallThickness
    (LengthInMillimetres (34 / 10)) (LengthInMillimetres (1 / 10)) ∧
  0 < SICoordinate figure.outerCylinder.displayedDiameter ∧
  0 < SICoordinate figure.innerCylinder.displayedDiameter ∧
  0 < SICoordinate figure.innerCylinder.wallThickness ∧
  0 < SICoordinate figure.outerCylinder.wallThickness ∧
  SICoordinate figure.innerCylinder.displayedDiameter / 2 +
      SICoordinate figure.innerCylinder.wallThickness <
    SICoordinate figure.outerCylinder.displayedDiameter / 2 -
      SICoordinate figure.outerCylinder.wallThickness

/-- Clear cross-sectional area of IC, using its measured inside diameter. -/
noncomputable def innerCrossSectionArea (figure : Figure17Dimensions) : Area :=
  ⟨Real.pi * (SICoordinate figure.innerCylinder.displayedDiameter / 2) ^ 2⟩

/-- Internal connecting-hose volume and the volume displaced by the
temperature sensor inside IC.  The statement supplies no numerical value for
either nonnegative correction. -/
structure VolumeCorrectionModel where
  connectingHoseInternalVolume : Volume
  sensorDisplacedVolume : Volume
  connectingHoseInternalVolume_nonnegative :
    0 ≤ SICoordinate connectingHoseInternalVolume
  sensorDisplacedVolume_nonnegative :
    0 ≤ SICoordinate sensorDisplacedVolume

/-- Figure geometry, measured air height `H`, PG fill height `h`, correction
volumes, and the reference constants used to determine the air inventory. -/
structure ApparatusConstants where
  figure17 : Figure17Dimensions
  measuredAirHeight : Length
  propyleneGlycolFillHeight : Length
  volumeCorrection : VolumeCorrectionModel
  ambientAirDensity : MassDensity
  airMolarMass : MolarMass
  avogadroConstant : AvogadroConstant
  universalGasConstant : MolarGasConstant

/-- The stated approximation that hose volume and sensor-displacement volume
cancel.  It is a modeling idealization, not an asserted measured value for
either volume. -/
def UsesHoseSensorVolumeIdealization (apparatus : ApparatusConstants) : Prop :=
  apparatus.volumeCorrection.connectingHoseInternalVolume =
      apparatus.volumeCorrection.sensorDisplacedVolume ∧
    SICoordinate
      (apparatus.volumeCorrection.connectingHoseInternalVolume -
        apparatus.volumeCorrection.sensorDisplacedVolume) = 0

/-- The fixed CA volume is clear IC area times the already-measured post-fill
air height `H`.  The preparation height `h` is deliberately not subtracted a
second time. -/
noncomputable def confinedAirVolume (apparatus : ApparatusConstants) : Volume :=
  innerCrossSectionArea apparatus.figure17 * apparatus.measuredAirHeight

/-! ## Air inventory and prescribed procedure -/

/-- A positive confined-air inventory: mass, amount of substance, and molecule
count. -/
structure AirInventory where
  mass : Mass
  amount : AmountOfSubstance
  moleculeCount : MoleculeCount
  mass_positive : 0 < SICoordinate mass
  amount_positive : 0 < SICoordinate amount
  moleculeCount_positive : 0 < SICoordinate moleculeCount

/-- The dimensionally typed density-to-mass-to-moles-to-molecules chain.
Equalities are taken at the explicit coherent-SI coordinate boundary because
the three typed products have propositionally, rather than definitionally,
equivalent dimension expressions. -/
def IsConfinedAirInventory (apparatus : ApparatusConstants)
    (inventory : AirInventory) : Prop :=
  SICoordinate inventory.mass =
      SICoordinate (apparatus.ambientAirDensity * confinedAirVolume apparatus) ∧
  SICoordinate (inventory.amount * apparatus.airMolarMass) =
      SICoordinate inventory.mass ∧
  SICoordinate inventory.moleculeCount =
      SICoordinate (inventory.amount * apparatus.avogadroConstant)

/-- State of every action prescribed for the A.2 isochoric run. -/
structure ProcedureState where
  valveDClosed : Bool
  valveEClosed : Bool
  outerCylinderFilledNearTopWithRoomTemperatureWater : Bool
  heaterOn : Bool
  homogenizingPumpOn : Bool

/-! ## A named run, its true states, and its fixed sensors -/

/-- A true CA state, distinct from a sensor observation. -/
structure GasState where
  temperature : TemperatureMeasurement
  pressure : PressureMeasurement
  volume : Volume

/-- One simultaneous external temperature--pressure observation. -/
structure PressureTemperatureObservation where
  temperature : TemperatureMeasurement
  pressure : PressureMeasurement

/-- Fixed readout functions for the two sensors used throughout one named
run. -/
structure SensorModel where
  temperatureReadout : TemperatureMeasurement → TemperatureMeasurement
  pressureReadout : PressureMeasurement → PressureMeasurement

/-- The optional calibration condition.  It is defined for clarity but is not
assumed in A.2, since the statement warns that sensors may be decalibrated. -/
def SensorsCalibrated (sensors : SensorModel) : Prop :=
  (∀ temperature, sensors.temperatureReadout temperature = temperature) ∧
    ∀ pressure, sensors.pressureReadout pressure = pressure

/-- An observation has provenance from a true state through the fixed sensor
model.  No calibration identity is implied. -/
def SensorReadout (sensors : SensorModel) (state : GasState)
    (observation : PressureTemperatureObservation) : Prop :=
  observation.temperature = sensors.temperatureReadout state.temperature ∧
    observation.pressure = sensors.pressureReadout state.pressure

/-- One named physical run ties together a single apparatus, inventory,
procedure, sensor pair, and natural-number-indexed sequence of true states. -/
structure PhysicalRun where
  apparatus : ApparatusConstants
  inventory : AirInventory
  procedure : ProcedureState
  sensors : SensorModel
  trueStates : ℕ → GasState

/-- Complete preparation conditions for A.2.  These constrain geometry,
inventory, constants, and actions, but supply no observation. -/
def PreparedForA2 (run : PhysicalRun) : Prop :=
  SatisfiesFigure17Geometry run.apparatus.figure17 ∧
  0 < SICoordinate run.apparatus.measuredAirHeight ∧
  run.apparatus.propyleneGlycolFillHeight = LengthInCentimetres (9 / 2) ∧
  UsesHoseSensorVolumeIdealization run.apparatus ∧
  run.apparatus.ambientAirDensity =
    MassDensityInKilogramsPerCubicMetre (28 / 25) ∧
  run.apparatus.airMolarMass = MolarMassInGramsPerMole (724 / 25) ∧
  run.apparatus.avogadroConstant =
    AvogadroConstantInPerMole ((6022 / 1000) * 10 ^ (23 : ℕ)) ∧
  0 < SICoordinate run.apparatus.universalGasConstant ∧
  IsConfinedAirInventory run.apparatus run.inventory ∧
  run.procedure.valveDClosed = true ∧
  run.procedure.valveEClosed = true ∧
  run.procedure.outerCylinderFilledNearTopWithRoomTemperatureWater = true ∧
  run.procedure.heaterOn = true ∧
  run.procedure.homogenizingPumpOn = true

/-- A positive, isochoric true state satisfying `P V = n R T`.  Both products
are formed from typed ISQ quantities and compared only at their common
coherent-SI coordinate boundary. -/
def IdealGasEquationAt (run : PhysicalRun) (state : GasState) : Prop :=
  0 < SICoordinate state.temperature ∧
  0 < SICoordinate state.pressure ∧
  state.volume = confinedAirVolume run.apparatus ∧
  SICoordinate (state.pressure * state.volume) =
    SICoordinate
      ((run.inventory.amount * run.apparatus.universalGasConstant) *
        state.temperature)

/-! ## External observations and the exact requested table -/

/-- A nonempty finite series in sampling order.  The list index is temporal
order, not an imposed numerical sorting of readings. -/
structure MeasurementSeries where
  observations : List PressureTemperatureObservation
  nonempty : observations ≠ []
  temperaturePositive :
    ∀ observation ∈ observations, 0 < SICoordinate observation.temperature
  pressurePositive :
    ∀ observation ∈ observations, 0 < SICoordinate observation.pressure

/-- Each sampled true state behind the finite series satisfies the isochoric
ideal-gas law.  This does not identify a readout with its true value. -/
def SeriesObeysIdealGasLaw (run : PhysicalRun)
    (series : MeasurementSeries) : Prop :=
  ∀ j : Fin series.observations.length,
    IdealGasEquationAt run (run.trueStates j.val)

/-- Each external observation is the fixed-sensor readout of the true state at
the same sampling index in this named run. -/
def ObservationsOfRun (run : PhysicalRun) (series : MeasurementSeries) : Prop :=
  ∀ j : Fin series.observations.length,
    SensorReadout run.sensors (run.trueStates j.val)
      (series.observations.get j)

/-- One requested table row, with temperature followed by the simultaneously
recorded pressure. -/
structure PressureTemperatureTableRow where
  temperature : TemperatureMeasurement
  pressure : PressureMeasurement

/-- A finite ordered pressure--temperature table. -/
structure PressureTemperatureTable where
  rows : List PressureTemperatureTableRow

/-- Preserve both entries of one empirical observation exactly. -/
def PressureTemperatureTableRow.ofObservation
    (observation : PressureTemperatureObservation) :
    PressureTemperatureTableRow where
  temperature := observation.temperature
  pressure := observation.pressure

/-- `table` contains all and only the supplied observations, with sampling
order and multiplicity unchanged. -/
def ExactObservationMap (series : MeasurementSeries)
    (table : PressureTemperatureTable) : Prop :=
  table.rows =
    series.observations.map PressureTemperatureTableRow.ofObservation

/-- Answer-free solution predicate for A.2. -/
def IsA2Table (run : PhysicalRun) (series : MeasurementSeries)
    (table : PressureTemperatureTable) : Prop :=
  PreparedForA2 run ∧
  SeriesObeysIdealGasLaw run series ∧
  ObservationsOfRun run series ∧
  ExactObservationMap series table

end ProblemIPhO2026_4_A_2

/-- Every physically prepared, provenanced external series determines a unique
exact order-preserving table.  No numerical observation or calibration
identity occurs in the theorem contract. -/
theorem problem_IPhO_2026_4_A_2
    (run : ProblemIPhO2026_4_A_2.PhysicalRun)
    (series : ProblemIPhO2026_4_A_2.MeasurementSeries)
    (hPrepared : ProblemIPhO2026_4_A_2.PreparedForA2 run)
    (hIdealGas :
      ProblemIPhO2026_4_A_2.SeriesObeysIdealGasLaw run series)
    (hObservations :
      ProblemIPhO2026_4_A_2.ObservationsOfRun run series) :
    ∃! table : ProblemIPhO2026_4_A_2.PressureTemperatureTable,
      ProblemIPhO2026_4_A_2.IsA2Table run series table := by
  let table : ProblemIPhO2026_4_A_2.PressureTemperatureTable :=
    ⟨series.observations.map
      ProblemIPhO2026_4_A_2.PressureTemperatureTableRow.ofObservation⟩
  refine ⟨table, ?_, ?_⟩
  · exact ⟨hPrepared, hIdealGas, hObservations, rfl⟩
  · intro other hOther
    cases other with
    | mk rows =>
        have hRows := hOther.2.2.2
        change rows =
          series.observations.map
            ProblemIPhO2026_4_A_2.PressureTemperatureTableRow.ofObservation at hRows
        simpa [table] using
          congrArg ProblemIPhO2026_4_A_2.PressureTemperatureTable.mk hRows

end Ipho2026Gpt56solBlind
