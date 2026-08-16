import Mathlib
import Physlib

namespace Ipho2026Gpt56solBlind
namespace ProblemIPhO2026_4_C_1

noncomputable section

/-!
The quantities in this file use the seven-base ISQ dimension system.  Their
underlying real numbers are coherent-SI coordinates.  In particular, no
`HasDim` or `Dimensionful` instance is introduced for the ISQ basis; conversion
of an explicitly chosen ISQ unit system to SI is performed by `quantityInSI`.
-/

abbrev massDimension : Dimension ISQDimensionBase :=
  Dimension.single ISQDimensionBase.mass

abbrev lengthDimension : Dimension ISQDimensionBase :=
  Dimension.single ISQDimensionBase.length

abbrev timeDimension : Dimension ISQDimensionBase :=
  Dimension.single ISQDimensionBase.time

abbrev temperatureDimension : Dimension ISQDimensionBase :=
  Dimension.single ISQDimensionBase.temperature

abbrev areaDimension : Dimension ISQDimensionBase :=
  lengthDimension * lengthDimension

abbrev energyDimension : Dimension ISQDimensionBase :=
  massDimension * lengthDimension * lengthDimension * timeDimension⁻¹ * timeDimension⁻¹

abbrev heatRateDimension : Dimension ISQDimensionBase :=
  energyDimension * timeDimension⁻¹

abbrev thermalResistanceDimension : Dimension ISQDimensionBase :=
  temperatureDimension * heatRateDimension⁻¹

abbrev temperatureGradientDimension : Dimension ISQDimensionBase :=
  temperatureDimension * lengthDimension⁻¹

abbrev thermalConductivityDimension : Dimension ISQDimensionBase :=
  massDimension * lengthDimension * timeDimension⁻¹ * timeDimension⁻¹ * timeDimension⁻¹ *
    temperatureDimension⁻¹

abbrev heatCapacityDimension : Dimension ISQDimensionBase :=
  energyDimension * temperatureDimension⁻¹

/-- A real-valued ISQ time quantity. -/
abbrev TimeQuantity : Type := WithDim timeDimension ℝ

/-- A real-valued ISQ length quantity. -/
abbrev LengthQuantity : Type := WithDim lengthDimension ℝ

/-- A length interpreted as distance from the common cylinder axis. -/
abbrev RadiusQuantity : Type := LengthQuantity

/-- A real-valued ISQ area quantity. -/
abbrev AreaQuantity : Type := WithDim areaDimension ℝ

/-- A real-valued ISQ thermodynamic-temperature quantity. -/
abbrev AbsoluteTemperature : Type := WithDim temperatureDimension ℝ

/-- A signed temperature difference. -/
abbrev TemperatureDifference : Type := WithDim temperatureDimension ℝ

/-- A real-valued ISQ energy quantity. -/
abbrev EnergyQuantity : Type := WithDim energyDimension ℝ

/-- A signed heat rate, with dimension energy divided by time. -/
abbrev HeatRate : Type := WithDim heatRateDimension ℝ

/-- Thermal resistance, with dimension temperature difference divided by heat rate. -/
abbrev ThermalResistance : Type := WithDim thermalResistanceDimension ℝ

/-- An outward radial temperature derivative. -/
abbrev TemperatureGradient : Type := WithDim temperatureGradientDimension ℝ

/-- Thermal conductivity, so conductivity times area times gradient is a heat rate. -/
abbrev ThermalConductivity : Type := WithDim thermalConductivityDimension ℝ

/-- Heat capacity, with dimension energy divided by temperature difference. -/
abbrev HeatCapacity : Type := WithDim heatCapacityDimension ℝ

/--
Convert a numerical coordinate expressed in an explicitly chosen typed ISQ
unit system to the coherent SI coordinate used internally in this file.
-/
def quantityInSI {d : Dimension ISQDimensionBase}
    (sourceUnits : SIUnitChoices) (q : WithDim d ℝ) : WithDim d ℝ :=
  ⟨((SIUnitChoices.dimScale sourceUnits SIUnitChoices.SI d : NNReal) : ℝ) * q.val⟩

/-- The ISQ time whose coherent-SI coordinate is `s` seconds. -/
def TimeInSeconds (s : ℝ) : TimeQuantity :=
  quantityInSI SIUnitChoices.SI ⟨s⟩

/-- The ISQ length represented by a source reading of `x` centimetres. -/
def LengthInCentimetres (x : ℝ) : LengthQuantity :=
  quantityInSI SIUnitChoices.SI ⟨(1 / 100 : ℝ) * x⟩

/-- The ISQ length represented by a source reading of `x` millimetres. -/
def LengthInMillimetres (x : ℝ) : LengthQuantity :=
  quantityInSI SIUnitChoices.SI ⟨(1 / 1000 : ℝ) * x⟩

/--
The absolute thermodynamic temperature represented by a Celsius thermometer
reading.  Celsius is an affine coordinate, hence the `273.15` offset occurs
only here and cancels when two converted readings are subtracted.
-/
def TemperatureInCelsius (c : ℝ) : AbsoluteTemperature :=
  quantityInSI SIUnitChoices.SI ⟨c + 273.15⟩

/-- The four dimensional measurements printed in Figure 17. -/
structure Figure17Geometry where
  outerCylinderOuterDiameter_OC : LengthQuantity
  innerCylinderInnerDiameter_IC : LengthQuantity
  separatingInnerCylinderWallThickness_IC : LengthQuantity
  outerCylinderWallThickness_OC : LengthQuantity

/-- The IC-facing radius of the separating acrylic wall. -/
def innerWallInnerRadius (geometry : Figure17Geometry) : RadiusQuantity :=
  ⟨geometry.innerCylinderInnerDiameter_IC.val / 2⟩

/-- The OC-facing radius of the separating acrylic wall. -/
def innerWallOuterRadius (geometry : Figure17Geometry) : RadiusQuantity :=
  ⟨(innerWallInnerRadius geometry).val + geometry.separatingInnerCylinderWallThickness_IC.val⟩

/-- The inner-face radius of the outer-cylinder wall. -/
def outerWallInnerRadius (geometry : Figure17Geometry) : RadiusQuantity :=
  ⟨geometry.outerCylinderOuterDiameter_OC.val / 2 - geometry.outerCylinderWallThickness_OC.val⟩

/--
The four nominal Figure 17 dimensions with their stated `±0.1 mm`
tolerances, positivity, and the nesting required of the two cylinders.
-/
def SatisfiesFigure17Geometry (geometry : Figure17Geometry) : Prop :=
  abs (geometry.outerCylinderOuterDiameter_OC.val - (LengthInMillimetres 74.8).val) ≤
      (LengthInMillimetres 0.1).val ∧
    abs (geometry.innerCylinderInnerDiameter_IC.val - (LengthInMillimetres 33.7).val) ≤
      (LengthInMillimetres 0.1).val ∧
    abs (geometry.separatingInnerCylinderWallThickness_IC.val -
        (LengthInMillimetres 3.4).val) ≤ (LengthInMillimetres 0.1).val ∧
    abs (geometry.outerCylinderWallThickness_OC.val - (LengthInMillimetres 3.4).val) ≤
      (LengthInMillimetres 0.1).val ∧
    0 < geometry.outerCylinderOuterDiameter_OC ∧
    0 < geometry.innerCylinderInnerDiameter_IC ∧
    0 < geometry.separatingInnerCylinderWallThickness_IC ∧
    0 < geometry.outerCylinderWallThickness_OC ∧
    innerWallOuterRadius geometry < outerWallInnerRadius geometry

/--
The prescribed preparation of a named two-cylinder Part C run.  Event times
are relative to stopwatch start, rather than later sample times.
-/
structure PartCPreparation where
  geometry : Figure17Geometry
  outerWaterHeight_OC : LengthQuantity
  outerTemperatureAfterHeating_OC : AbsoluteTemperature
  innerWaterHeight_IC : LengthQuantity
  outerLevelSetAt : TimeQuantity
  outerHeatingAndHomogenizationCompletedAt : TimeQuantity
  innerLevelSetAndStopwatchStartedAt : TimeQuantity
  pumpUsedToHomogenizeOuterWater : Prop
  outerWaterHomogeneousAtStopwatchStart : Prop
  separatingWallIsAcrylic : Prop
  separatingWallIsCylindrical : Prop
  heatExchangeAcrossWallIsRadial : Prop

/--
The three source preparation steps, their temporal order relative to elapsed
time zero, and the positive, correctly nested apparatus conditions needed by
the C.1 recording task.  The numerical Figure 17 dimensions are not assumed
in this C.1 admissibility path.
-/
def FollowsPartCProcedure (preparation : PartCPreparation) : Prop :=
  0 < preparation.geometry.outerCylinderOuterDiameter_OC ∧
    0 < preparation.geometry.innerCylinderInnerDiameter_IC ∧
    0 < preparation.geometry.separatingInnerCylinderWallThickness_IC ∧
    0 < preparation.geometry.outerCylinderWallThickness_OC ∧
    innerWallOuterRadius preparation.geometry < outerWallInnerRadius preparation.geometry ∧
    preparation.outerWaterHeight_OC = LengthInCentimetres 15 ∧
    preparation.outerTemperatureAfterHeating_OC = TemperatureInCelsius 65 ∧
    preparation.innerWaterHeight_IC = LengthInCentimetres 10 ∧
    preparation.outerLevelSetAt ≤ preparation.outerHeatingAndHomogenizationCompletedAt ∧
    preparation.outerHeatingAndHomogenizationCompletedAt ≤ TimeInSeconds 0 ∧
    preparation.innerLevelSetAndStopwatchStartedAt = TimeInSeconds 0 ∧
    preparation.pumpUsedToHomogenizeOuterWater ∧
    preparation.outerWaterHomogeneousAtStopwatchStart ∧
    preparation.separatingWallIsAcrylic ∧
    preparation.separatingWallIsCylindrical ∧
    preparation.heatExchangeAcrossWallIsRadial

/-- The water cross-sections and common wetted height used in Part C. -/
structure PartCWaterGeometry where
  innerWaterCrossSectionArea_IC : AreaQuantity
  outerWaterAnnularCrossSectionArea_OC : AreaQuantity
  commonWettedHeight : LengthQuantity

def diskArea (radius : RadiusQuantity) : AreaQuantity :=
  ⟨Real.pi * radius.val ^ 2⟩

def annulusArea (innerRadius outerRadius : RadiusQuantity) : AreaQuantity :=
  ⟨Real.pi * (outerRadius.val ^ 2 - innerRadius.val ^ 2)⟩

/--
The water geometry induced by the apparatus radii and prepared water heights.
Positivity rules out a degenerate or incorrectly nested experimental volume.
-/
def MatchesPartCWaterGeometry
    (preparation : PartCPreparation) (waterGeometry : PartCWaterGeometry) : Prop :=
  waterGeometry.innerWaterCrossSectionArea_IC =
      diskArea (innerWallInnerRadius preparation.geometry) ∧
    waterGeometry.outerWaterAnnularCrossSectionArea_OC =
      annulusArea (innerWallOuterRadius preparation.geometry)
        (outerWallInnerRadius preparation.geometry) ∧
    waterGeometry.commonWettedHeight =
      ⟨min preparation.innerWaterHeight_IC.val preparation.outerWaterHeight_OC.val⟩ ∧
    0 < waterGeometry.innerWaterCrossSectionArea_IC ∧
    0 < waterGeometry.outerWaterAnnularCrossSectionArea_OC ∧
    0 < waterGeometry.commonWettedHeight

/-- The wetted conducting area of the separating wall at radius `radius`. -/
def cylindricalWallArea
    (waterGeometry : PartCWaterGeometry) (radius : RadiusQuantity) : AreaQuantity :=
  ⟨2 * Real.pi * radius.val * waterGeometry.commonWettedHeight.val⟩

/--
The later C.3--C.4 equilibrium idealization sets only the modeled apparatus
contribution to zero.  It deliberately says nothing of that kind about the
physical apparatus heat capacity and is not a data-acquisition assumption.
-/
def C3C4EquilibriumCapacityIdealization
    (_physicalApparatusHeatCapacity modeledApparatusContribution : HeatCapacity) : Prop :=
  modeledApparatusContribution = 0

/--
Heat capacities relevant to the named run.  The zero modeled contribution is
separately named and scoped to the later C.3--C.4 equilibrium calculation.
-/
structure PartCAnalysisContext where
  innerWaterHeatCapacity_IC : HeatCapacity
  outerWaterHeatCapacity_OC : HeatCapacity
  physicalApparatusHeatCapacity : HeatCapacity
  modeledApparatusContributionForC3C4 : HeatCapacity
  innerWaterHeatCapacity_pos : 0 < innerWaterHeatCapacity_IC
  outerWaterHeatCapacity_pos : 0 < outerWaterHeatCapacity_OC
  physicalApparatusHeatCapacity_nonnegative : 0 ≤ physicalApparatusHeatCapacity
  c3c4CapacityIdealization :
    C3C4EquilibriumCapacityIdealization physicalApparatusHeatCapacity
      modeledApparatusContributionForC3C4

/-- The two possible orientations of the radial coordinate through the wall. -/
inductive RadialOrientation where
  | increasingFromICToOC
  | increasingFromOCToIC
deriving DecidableEq

/--
A named physical run, including the measured bulk temperatures, the wall
profile, and heat accounting.  The resistance and conductivity requested in
later parts are deliberately not stored in this C.1 input record.
-/
structure PartCRun where
  runName : String
  preparation : PartCPreparation
  waterGeometry : PartCWaterGeometry
  analysisContext : PartCAnalysisContext
  internalTemperature_IC : TimeQuantity → AbsoluteTemperature
  externalTemperature_OC : TimeQuantity → AbsoluteTemperature
  wallTemperatureProfile : TimeQuantity → RadiusQuantity → AbsoluteTemperature
  outwardRadialTemperatureGradient : TimeQuantity → RadiusQuantity → TemperatureGradient
  cumulativeHeatReceivedByIC : TimeQuantity → EnergyQuantity
  heatRateIntoIC : TimeQuantity → HeatRate
  outwardHeatRate : TimeQuantity → HeatRate
  radialOrientation : RadialOrientation
  smallerWallBoundaryFacesIC : Prop
  largerWallBoundaryFacesOC : Prop

/-- A radius is in the closed radial domain of the separating wall. -/
def InWallRadialDomain (geometry : Figure17Geometry) (radius : RadiusQuantity) : Prop :=
  innerWallInnerRadius geometry ≤ radius ∧ radius ≤ innerWallOuterRadius geometry

/-- A radius is in the open domain on which the radial derivative is used. -/
def InWallRadialInterior (geometry : Figure17Geometry) (radius : RadiusQuantity) : Prop :=
  innerWallInnerRadius geometry < radius ∧ radius < innerWallOuterRadius geometry

/--
Increasing radius points from the IC water to the OC water; the smaller and
larger separating-wall faces have their stated physical meanings.
-/
def HasOutwardRadialOrientation (run : PartCRun) : Prop :=
  run.radialOrientation = RadialOrientation.increasingFromICToOC ∧
    run.smallerWallBoundaryFacesIC ∧
    run.largerWallBoundaryFacesOC ∧
    innerWallInnerRadius run.preparation.geometry < innerWallOuterRadius run.preparation.geometry

/--
The wall profile has the two bulk-water boundary values and its supplied
gradient is the derivative with respect to increasing (outward) radius.
-/
def HasRadialTemperatureProfile (run : PartCRun) : Prop :=
  HasOutwardRadialOrientation run ∧
    (∀ t, 0 ≤ t →
      (∀ r, InWallRadialDomain run.preparation.geometry r →
        0 < run.wallTemperatureProfile t r) ∧
      run.wallTemperatureProfile t (innerWallInnerRadius run.preparation.geometry) =
        run.internalTemperature_IC t ∧
      run.wallTemperatureProfile t (innerWallOuterRadius run.preparation.geometry) =
        run.externalTemperature_OC t ∧
      ∀ r, InWallRadialInterior run.preparation.geometry r →
        HasDerivAt
          (fun radiusInMetres : ℝ ↦
            (run.wallTemperatureProfile t (⟨radiusInMetres⟩ : RadiusQuantity)).val)
          (run.outwardRadialTemperatureGradient t r).val r.val)

/--
The signed heat rate into IC is the derivative of cumulative heat.  At
elapsed time zero the derivative is taken from the physical right-hand side.
-/
def HeatIntoInnerIsDerivative (run : PartCRun) : Prop :=
  (∀ t, 0 < t →
    HasDerivAt
      (fun elapsedSeconds : ℝ ↦
        (run.cumulativeHeatReceivedByIC (⟨elapsedSeconds⟩ : TimeQuantity)).val)
      (run.heatRateIntoIC t).val t.val) ∧
    HasDerivWithinAt
      (fun elapsedSeconds : ℝ ↦
        (run.cumulativeHeatReceivedByIC (⟨elapsedSeconds⟩ : TimeQuantity)).val)
      (run.heatRateIntoIC (TimeInSeconds 0)).val (Set.Ici 0) 0

/-- Positive heat received by IC is opposite to positive outward heat flow. -/
def HasHeatRateSignConvention (run : PartCRun) : Prop :=
  ∀ t, 0 ≤ t → run.heatRateIntoIC t = -run.outwardHeatRate t

def heatRateFromResistance
    (temperatureDifference : TemperatureDifference)
    (resistance : ThermalResistance) : HeatRate :=
  WithDim.cast (temperatureDifference / resistance)

/-- The effective resistance law for an explicit candidate resistance. -/
def SatisfiesThermalResistanceLaw (run : PartCRun)
    (wallThermalResistance : ThermalResistance) : Prop :=
  ∀ t, 0 ≤ t →
    run.heatRateIntoIC t =
      heatRateFromResistance
        (run.externalTemperature_OC t - run.internalTemperature_IC t)
        wallThermalResistance

def outwardFourierHeatRate
    (conductivity : ThermalConductivity) (area : AreaQuantity)
    (gradient : TemperatureGradient) : HeatRate :=
  WithDim.cast (-(conductivity * area * gradient))

/--
Fourier's law for positive outward radius.  Its minus sign belongs to the
outward flux law, while `HasHeatRateSignConvention` relates that flux to heat
received by IC.
-/
def SatisfiesOutwardFourierLaw (run : PartCRun)
    (acrylicThermalConductivity : ThermalConductivity) : Prop :=
  ∀ t, 0 ≤ t → ∀ r, InWallRadialInterior run.preparation.geometry r →
    run.outwardHeatRate t =
      outwardFourierHeatRate acrylicThermalConductivity
        (cylindricalWallArea run.waterGeometry r)
        (run.outwardRadialTemperatureGradient t r)

/--
A correctly prepared named run satisfying the geometry, domains, initial
conditions, temperature positivity, and signed heat accounting needed for the
C.1 recording task.  Later resistance and conductivity candidates are not
assumed here.
-/
def IsPreparedPartCRun (run : PartCRun) : Prop :=
  run.runName ≠ "" ∧
    FollowsPartCProcedure run.preparation ∧
    MatchesPartCWaterGeometry run.preparation run.waterGeometry ∧
    HasOutwardRadialOrientation run ∧
    HasRadialTemperatureProfile run ∧
    HeatIntoInnerIsDerivative run ∧
    HasHeatRateSignConvention run ∧
    run.externalTemperature_OC (TimeInSeconds 0) =
      run.preparation.outerTemperatureAfterHeating_OC ∧
    run.cumulativeHeatReceivedByIC (TimeInSeconds 0) = 0 ∧
    (∀ t, 0 ≤ t → 0 < run.internalTemperature_IC t) ∧
    ∀ t, 0 ≤ t → 0 < run.externalTemperature_OC t

/--
External paired thermometer observations, indexed by measurement number.
Their values are empirical inputs rather than consequences fabricated from
the governing laws.
-/
structure PairedTemperatureObservations (sampleCount : ℕ) where
  observedRunName : String
  nonempty : 0 < sampleCount
  sampleTime : Fin sampleCount → TimeQuantity
  internalTemperature_IC : Fin sampleCount → AbsoluteTemperature
  externalTemperature_OC : Fin sampleCount → AbsoluteTemperature
  sampleTime_nonnegative : ∀ j, 0 ≤ sampleTime j
  sampleTime_strictlyIncreasing : StrictMono sampleTime

/--
The observations are provenanced to the named run and agree with its two
bulk-water trajectories at every recorded elapsed time.
-/
def ObservationsOfRun {sampleCount : ℕ} (run : PartCRun)
    (observations : PairedTemperatureObservations sampleCount) : Prop :=
  observations.observedRunName = run.runName ∧
    ∀ j,
      observations.internalTemperature_IC j =
          run.internalTemperature_IC (observations.sampleTime j) ∧
        observations.externalTemperature_OC j =
          run.externalTemperature_OC (observations.sampleTime j)

/-- The requested time, IC-temperature, and OC-temperature columns. -/
structure RecordedTemperatureSeries (sampleCount : ℕ) where
  time : Fin sampleCount → TimeQuantity
  internalTemperature_IC : Fin sampleCount → AbsoluteTemperature
  externalTemperature_OC : Fin sampleCount → AbsoluteTemperature

/--
An exact, order-preserving recording of external observations from the named
prepared run.  Preparation and provenance constrain the setting without
predicting any empirical temperature value.
-/
def RecordingSolution {sampleCount : ℕ} (run : PartCRun)
    (observations : PairedTemperatureObservations sampleCount)
    (record : RecordedTemperatureSeries sampleCount) : Prop :=
  IsPreparedPartCRun run ∧
    ObservationsOfRun run observations ∧
    ∀ j,
      record.time j = observations.sampleTime j ∧
        record.internalTemperature_IC j = observations.internalTemperature_IC j ∧
        record.externalTemperature_OC j = observations.externalTemperature_OC j

/--
IPhO 2026 experimental problem 4, C.1: strictly time-ordered paired external
measurements from a prepared named run determine a unique exact record.  No
thermometer reading, fitted resistance, or conductivity appears in the
theorem signature as a derived answer.
-/
theorem problem_IPhO_2026_4_C_1 {sampleCount : ℕ}
    (run : PartCRun)
    (hrun : IsPreparedPartCRun run)
    (observations : PairedTemperatureObservations sampleCount)
    (hobservations : ObservationsOfRun run observations) :
    ∃! record : RecordedTemperatureSeries sampleCount,
      RecordingSolution run observations record := by
  let record : RecordedTemperatureSeries sampleCount :=
    { time := observations.sampleTime
      internalTemperature_IC := observations.internalTemperature_IC
      externalTemperature_OC := observations.externalTemperature_OC }
  refine ⟨record, ?_, ?_⟩
  · exact ⟨hrun, hobservations, fun _ ↦ ⟨rfl, rfl, rfl⟩⟩
  · intro other hother
    rcases hother with ⟨_, _, hcolumns⟩
    cases other with
    | mk otherTime otherInternal otherExternal =>
        apply congrArg id
        congr
        · funext j
          exact (hcolumns j).1
        · funext j
          exact (hcolumns j).2.1
        · funext j
          exact (hcolumns j).2.2

end

end ProblemIPhO2026_4_C_1
end Ipho2026Gpt56solBlind
