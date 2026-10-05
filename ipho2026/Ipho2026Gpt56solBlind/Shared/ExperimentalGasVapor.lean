import Mathlib.Tactic
import Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
import Ipho2026Gpt56solBlind.Shared.FiniteDataAndAffineFit

/-!
# Experimental gas and water-vapor model

This aggregate module re-exports the Figure 17 apparatus, finite-observation,
exact-graph, and affine-fit declarations.  It first states generic pointwise
gas and Clausius--Clapeyron laws, then connects them to one named Figure 17
cooling run through explicit provenance, calibration, modeling, and fit-
protocol boundaries.  Empirical readings and every requested inferred
quantity remain explicit inputs or solution candidates.
-/

namespace Ipho2026Gpt56solBlind.Shared

open ISQDimensions
open Figure17Apparatus
open FiniteObservations
open ExactGraph
open AffineFit

noncomputable section

/-! ## Generic pointwise laws -/

namespace GasVaporLaws

/-- Total pressure is the sum of the dry-air and water-vapor partial pressures. -/
def TotalPartialPressureBalance
    (totalPressure dryAirPressure vaporPressure : Pressure) : Prop :=
  totalPressure = dryAirPressure + vaporPressure

/-- The typed ideal-gas equation at one positive-temperature state. -/
def DryAirIdealGasEquationAt (pressure : Pressure) (volume : Volume)
    (amount : AmountOfSubstance) (gasConstant : MolarGasConstant)
    (temperature : Temperature) : Prop :=
  0 < coordinateInSI SIUnitChoices.SI temperature ∧
    coordinateInSI SIUnitChoices.SI pressure *
        coordinateInSI SIUnitChoices.SI volume =
      coordinateInSI SIUnitChoices.SI amount *
        coordinateInSI SIUnitChoices.SI gasConstant *
        coordinateInSI SIUnitChoices.SI temperature

/-- A molar latent heat has energy-per-amount dimension. -/
abbrev MolarLatentHeat : Type :=
  Quantity (energyDimension * amountDimension⁻¹)

/-- A mass-specific latent heat has energy-per-mass dimension. -/
abbrev MassSpecificLatentHeat : Type :=
  Quantity (energyDimension * massDimension⁻¹)

/-- A reference vapor pressure admissible as a logarithmic parameter. -/
def PositiveReferenceVaporPressure (referencePressure : Pressure) : Prop :=
  0 < coordinateInSI SIUnitChoices.SI referencePressure

/-- Positive generic parameters for the pointwise Clausius--Clapeyron law. -/
structure PositiveClausiusClapeyronParameters where
  gasConstant : MolarGasConstant
  referenceTemperature : Temperature
  pressureScale : Pressure
  referenceVaporPressure : Pressure
  gasConstant_positive : 0 < coordinateInSI SIUnitChoices.SI gasConstant
  referenceTemperature_positive :
    0 < coordinateInSI SIUnitChoices.SI referenceTemperature
  pressureScale_positive : 0 < coordinateInSI SIUnitChoices.SI pressureScale
  referenceVaporPressure_positive :
    PositiveReferenceVaporPressure referenceVaporPressure

/-- A positive typed temperature--vapor-pressure sample, without provenance. -/
structure PositiveClausiusClapeyronSample where
  temperature : Temperature
  vaporPressure : Pressure
  temperature_positive : 0 < coordinateInSI SIUnitChoices.SI temperature
  vaporPressure_positive : 0 < coordinateInSI SIUnitChoices.SI vaporPressure

/-- The pointwise Clausius--Clapeyron law, with its reference intercept retained. -/
def ClausiusClapeyronLawAt
    (parameters : PositiveClausiusClapeyronParameters)
    (sample : PositiveClausiusClapeyronSample)
    (molarLatentHeat : MolarLatentHeat) : Prop :=
  Real.log
        (coordinateInSI SIUnitChoices.SI sample.vaporPressure /
          coordinateInSI SIUnitChoices.SI parameters.pressureScale) =
    Real.log
        (coordinateInSI SIUnitChoices.SI parameters.referenceVaporPressure /
          coordinateInSI SIUnitChoices.SI parameters.pressureScale) -
      coordinateInSI SIUnitChoices.SI molarLatentHeat /
          coordinateInSI SIUnitChoices.SI parameters.gasConstant *
        (1 / coordinateInSI SIUnitChoices.SI sample.temperature -
          1 / coordinateInSI SIUnitChoices.SI parameters.referenceTemperature)

/-- Governing relation converting a positive molar latent heat to a positive
mass-specific latent heat using a positive molar mass. -/
def MassSpecificLatentHeatSolution (waterMolarMass : MolarMass)
    (molarLatentHeat : MolarLatentHeat)
    (massSpecificLatentHeat : MassSpecificLatentHeat) : Prop :=
  0 < coordinateInSI SIUnitChoices.SI massSpecificLatentHeat ∧
    coordinateInSI SIUnitChoices.SI massSpecificLatentHeat *
        coordinateInSI SIUnitChoices.SI waterMolarMass =
      coordinateInSI SIUnitChoices.SI molarLatentHeat

/-- Positive molar heat and molar mass determine exactly one positive
mass-specific latent heat. -/
theorem existsUnique_massSpecificLatentHeatSolution
    (waterMolarMass : MolarMass) (molarLatentHeat : MolarLatentHeat)
    (hWaterMolarMass : 0 < coordinateInSI SIUnitChoices.SI waterMolarMass)
    (hMolarLatentHeat : 0 < coordinateInSI SIUnitChoices.SI molarLatentHeat) :
    ∃! massSpecificLatentHeat : MassSpecificLatentHeat,
      MassSpecificLatentHeatSolution waterMolarMass molarLatentHeat
        massSpecificLatentHeat := by
  let candidate : MassSpecificLatentHeat :=
    ⟨coordinateInSI SIUnitChoices.SI molarLatentHeat /
      coordinateInSI SIUnitChoices.SI waterMolarMass⟩
  have hWaterMolarMassVal : 0 < waterMolarMass.val := by
    simpa only [coordinateInSI_self] using hWaterMolarMass
  have hMolarLatentHeatVal : 0 < molarLatentHeat.val := by
    simpa only [coordinateInSI_self] using hMolarLatentHeat
  refine ⟨candidate, ?_, ?_⟩
  · constructor
    · simp only [candidate, coordinateInSI_self]
      exact div_pos hMolarLatentHeatVal hWaterMolarMassVal
    · simp only [candidate, coordinateInSI_self]
      exact div_mul_cancel₀ _ (ne_of_gt hWaterMolarMassVal)
  · intro other hOther
    apply (coordinateInSI_eq_iff SIUnitChoices.SI other candidate).mp
    have hCoordinate :
        coordinateInSI SIUnitChoices.SI other =
          coordinateInSI SIUnitChoices.SI molarLatentHeat /
            coordinateInSI SIUnitChoices.SI waterMolarMass :=
      (eq_div_iff (ne_of_gt hWaterMolarMass)).2 hOther.2
    simpa only [candidate, coordinateInSI_self] using hCoordinate

end GasVaporLaws

/-! ## Figure 17 empirical adapter -/

namespace GasVapor

open GasVaporLaws

/-- The stated Part B reference temperature, 273.15 K. -/
def referenceTemperature : Temperature :=
  temperatureInKelvin 273.15

/-- The Part B reference temperature is physically positive. -/
theorem referenceTemperature_positive :
    0 < coordinateInSI SIUnitChoices.SI referenceTemperature := by
  norm_num [referenceTemperature, temperatureInKelvin]

/-- Discrete preparation and operating conditions for Part B cooling. -/
structure CoolingProcedure where
  initialInnerCylinderWaterHeight : Length
  outerCylinderFilledNearTop : Bool
  waterOnlySyringeAttachedToInnerCylinder : Bool
  valveEClosedAfterPressureEqualization : Bool
  hoseFreeOfAirBubbles : Bool
  syringeSecuredAtBathLevel : Bool
  bathHeatedTo65Celsius : Bool
  recirculatorUsed : Bool
  measurementsBeginDuringCooling : Bool

/-- One fixed pair of temperature and height sensor response functions. -/
structure CoolingSensorModel where
  temperatureResponse : Temperature → Temperature
  heightResponse : Length → Length

/-- Optional identity calibration of the two Part B sensors. -/
def CoolingSensorsCalibrated (sensors : CoolingSensorModel) : Prop :=
  (∀ temperature, sensors.temperatureResponse temperature = temperature) ∧
    ∀ height, sensors.heightResponse height = height

/-- A true dry-air--water-vapor state of a cooling run. -/
structure VaporState where
  temperature : Temperature
  liquidFreeHeight : Length
  totalPressure : Pressure
  dryAirPressure : Pressure
  vaporPressure : Pressure

/-- One externally supplied simultaneous temperature--height observation. -/
structure HeightTemperatureObservation where
  observedTemperature : Temperature
  observedHeight : Length

/-- Provenance of an observation as the fixed-sensor readout of a true state. -/
def CoolingSensorReadout (sensors : CoolingSensorModel) (state : VaporState)
    (observation : HeightTemperatureObservation) : Prop :=
  observation.observedTemperature =
      sensors.temperatureResponse state.temperature ∧
    observation.observedHeight = sensors.heightResponse state.liquidFreeHeight

/-- One named Part B cooling run with fixed apparatus, procedure, sensors,
dry-air inventory, and true-state family. -/
structure CoolingRun where
  apparatus : ApparatusData
  procedure : CoolingProcedure
  sensors : CoolingSensorModel
  atmosphericPressure : Pressure
  molarGasConstant : MolarGasConstant
  dryAirAmount : AmountOfSubstance
  trueStates : ℕ → VaporState

/-- Source preparation conditions for a Part B cooling run.  No calibration,
observation, fit, extrapolation, or inferred pressure is included. -/
def PreparedCoolingRun (run : CoolingRun) : Prop :=
  SatisfiesFigure17Geometry run.apparatus.measurements ∧
    0 < coordinateInSI SIUnitChoices.SI run.atmosphericPressure ∧
    0 < coordinateInSI SIUnitChoices.SI run.dryAirAmount ∧
    run.procedure.initialInnerCylinderWaterHeight = lengthInCentimetres 5.0 ∧
    run.procedure.outerCylinderFilledNearTop = true ∧
    run.procedure.waterOnlySyringeAttachedToInnerCylinder = true ∧
    run.procedure.valveEClosedAfterPressureEqualization = true ∧
    run.procedure.hoseFreeOfAirBubbles = true ∧
    run.procedure.syringeSecuredAtBathLevel = true ∧
    run.procedure.bathHeatedTo65Celsius = true ∧
    run.procedure.recirculatorUsed = true ∧
    run.procedure.measurementsBeginDuringCooling = true ∧
    run.molarGasConstant = molarGasConstantInJoulesPerMoleKelvin 8.31

/-- The gas-mixture volume at a supplied liquid-free height. -/
def liquidFreeVolume (run : CoolingRun) (height : Length) : Volume :=
  ⟨coordinateInSI SIUnitChoices.SI
        (innerClearCrossSectionArea run.apparatus.measurements) *
      coordinateInSI SIUnitChoices.SI height⟩

/-- The explicit idealization that total pressure equals the run's atmospheric
pressure parameter at this state. -/
def AtmosphericPressureIdealizationAt (run : CoolingRun)
    (state : VaporState) : Prop :=
  state.totalPressure = run.atmosphericPressure

/-- Positivity, geometry, pressure balance, atmospheric idealization, and the
fixed-inventory dry-air ideal-gas equation at one true state. -/
def VaporStateGoverningLaws (run : CoolingRun) (state : VaporState) : Prop :=
  0 < coordinateInSI SIUnitChoices.SI state.temperature ∧
    0 < coordinateInSI SIUnitChoices.SI state.liquidFreeHeight ∧
    0 < coordinateInSI SIUnitChoices.SI state.totalPressure ∧
    0 < coordinateInSI SIUnitChoices.SI state.dryAirPressure ∧
    0 ≤ coordinateInSI SIUnitChoices.SI state.vaporPressure ∧
    TotalPartialPressureBalance state.totalPressure state.dryAirPressure
      state.vaporPressure ∧
    AtmosphericPressureIdealizationAt run state ∧
    DryAirIdealGasEquationAt state.dryAirPressure
      (liquidFreeVolume run state.liquidFreeHeight) run.dryAirAmount
      run.molarGasConstant state.temperature

/-- Provenance for one indexed external height--temperature observation. -/
def HeightObservationProvenance (run : CoolingRun) (index : ℕ)
    (observation : HeightTemperatureObservation) : Prop :=
  VaporStateGoverningLaws run (run.trueStates index) ∧
    CoolingSensorReadout run.sensors (run.trueStates index) observation

/-- A finite nonempty Part B observation series retaining every indexed
occurrence and its named-run provenance. -/
abbrev HeightTemperatureSeries (q : ℕ) :=
  ObservationSeries q CoolingRun HeightTemperatureObservation
    (fun run index observation ↦
      HeightObservationProvenance run index.val observation)

/-- Exact readout graph with absolute temperature as predictor and height as
response, both expressed in coherent SI. -/
def HeightTemperatureGraphSolution {q : ℕ}
    (observations : HeightTemperatureSeries q)
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  ExactGraph observations
    (fun observation ↦
      coordinateInSI SIUnitChoices.SI observation.observedTemperature)
    (fun observation ↦
      coordinateInSI SIUnitChoices.SI observation.observedHeight)
    graph

/-- Each fixed cooling series determines one exact height--temperature graph. -/
theorem existsUnique_heightTemperatureGraphSolution {q : ℕ}
    (observations : HeightTemperatureSeries q) :
    ∃! graph : IndexedSeries q (ℝ × ℝ),
      HeightTemperatureGraphSolution observations graph := by
  simpa only [HeightTemperatureGraphSolution] using
    (existsUnique_exactGraph observations
      (fun observation ↦
        coordinateInSI SIUnitChoices.SI observation.observedTemperature)
      (fun observation ↦
        coordinateInSI SIUnitChoices.SI observation.observedHeight))

/-- A candidate height fit certified by a separately supplied, well-posed
data-only affine protocol. -/
def HeightTemperatureProtocolFitSolution {q : ℕ}
    (protocol : FitProtocol q) (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) (intercept slope : ℝ) : Prop :=
  let data := AffineData.ofGraph nonempty graph
  protocol.WellPosed data ∧ FitCertificate protocol data intercept slope

/-- A well-posed declared protocol determines one height-fit pair. -/
theorem existsUnique_heightTemperatureProtocolFitSolution {q : ℕ}
    (protocol : FitProtocol q) (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ))
    (hWellPosed : protocol.WellPosed (AffineData.ofGraph nonempty graph)) :
    ∃! pair : ℝ × ℝ,
      HeightTemperatureProtocolFitSolution protocol nonempty graph
        pair.1 pair.2 := by
  obtain ⟨pair, hPair, hUnique⟩ :=
    FitProtocol.existsUnique_fitCertificate protocol
      (AffineData.ofGraph nonempty graph) hWellPosed
  refine ⟨pair, ?_, ?_⟩
  · change protocol.WellPosed (AffineData.ofGraph nonempty graph) ∧
      FitCertificate protocol (AffineData.ofGraph nonempty graph) pair.1 pair.2
    exact ⟨hWellPosed, hPair⟩
  · intro other hOther
    change protocol.WellPosed (AffineData.ofGraph nonempty graph) ∧
      FitCertificate protocol (AffineData.ofGraph nonempty graph)
        other.1 other.2 at hOther
    exact hUnique other hOther.2

/-- Under an explicit OLS selection and predictor nondegeneracy, the generic
height-fit solution is exactly the normal-equation affine-fit relation. -/
lemma heightTemperatureProtocolFitSolution_ordinaryLeastSquaresProtocol_iff
    {q : ℕ} (nonempty : 0 < q) (graph : IndexedSeries q (ℝ × ℝ))
    (hNondegenerate :
      NondegeneratePredictor (AffineData.ofGraph nonempty graph))
    (intercept slope : ℝ) :
    HeightTemperatureProtocolFitSolution (ordinaryLeastSquaresProtocol q)
        nonempty graph intercept slope ↔
      IsAffineFit (AffineData.ofGraph nonempty graph) intercept slope := by
  have hPositiveVariance :
      0 < centeredPredictorVariance (AffineData.ofGraph nonempty graph) :=
    (positive_centeredPredictorVariance_iff_nondegeneratePredictor
      (AffineData.ofGraph nonempty graph)).2 hNondegenerate
  have hWellPosed := ordinaryLeastSquaresProtocol_wellPosed
    (AffineData.ofGraph nonempty graph) hPositiveVariance
  change
    ((ordinaryLeastSquaresProtocol q).WellPosed
        (AffineData.ofGraph nonempty graph) ∧
      FitCertificate (ordinaryLeastSquaresProtocol q)
        (AffineData.ofGraph nonempty graph) intercept slope) ↔
      IsAffineFit (AffineData.ofGraph nonempty graph) intercept slope
  constructor
  · exact fun h ↦
      (fitCertificate_ordinaryLeastSquaresProtocol_iff
        (AffineData.ofGraph nonempty graph) intercept slope).1 h.2
  · exact fun h ↦ ⟨hWellPosed,
      (fitCertificate_ordinaryLeastSquaresProtocol_iff
        (AffineData.ofGraph nonempty graph) intercept slope).2 h⟩

/-- Domain on which the declared height protocol has a unique certificate
whose extrapolation to the stated reference temperature is positive. -/
def PositiveProtocolHeightExtrapolationDomain {q : ℕ}
    (protocol : FitProtocol q) (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  let data := AffineData.ofGraph nonempty graph
  protocol.WellPosed data ∧
    ∀ intercept slope,
      FitCertificate protocol data intercept slope →
        0 < intercept +
          slope * coordinateInSI SIUnitChoices.SI referenceTemperature

/-- A positive B.3 reference-height candidate obtained by applying the
declared fit protocol to the exact B.2 readout graph. -/
def ExtrapolatedReferenceHeightSolution {q : ℕ}
    (observations : HeightTemperatureSeries q) (protocol : FitProtocol q)
    (graph : IndexedSeries q (ℝ × ℝ)) (height : Length) : Prop :=
  HeightTemperatureGraphSolution observations graph ∧
    0 < coordinateInSI SIUnitChoices.SI height ∧
    ∃ intercept slope,
      HeightTemperatureProtocolFitSolution protocol observations.nonempty graph
          intercept slope ∧
        coordinateInSI SIUnitChoices.SI height =
          intercept + slope *
            coordinateInSI SIUnitChoices.SI referenceTemperature

/-- An exact graph in the positive extrapolation domain determines one B.3
reference height. -/
theorem existsUnique_extrapolatedReferenceHeightSolution {q : ℕ}
    (observations : HeightTemperatureSeries q) (protocol : FitProtocol q)
    (graph : IndexedSeries q (ℝ × ℝ))
    (hGraph : HeightTemperatureGraphSolution observations graph)
    (hDomain : PositiveProtocolHeightExtrapolationDomain protocol
      observations.nonempty graph) :
    ∃! height : Length,
      ExtrapolatedReferenceHeightSolution observations protocol graph height := by
  change
    protocol.WellPosed (AffineData.ofGraph observations.nonempty graph) ∧
      (∀ intercept slope,
        FitCertificate protocol (AffineData.ofGraph observations.nonempty graph)
            intercept slope →
          0 < intercept + slope *
            coordinateInSI SIUnitChoices.SI referenceTemperature) at hDomain
  obtain ⟨pair, hFit, hFitUnique⟩ :=
    existsUnique_heightTemperatureProtocolFitSolution protocol
      observations.nonempty graph hDomain.1
  have hFitCertificate :
      FitCertificate protocol (AffineData.ofGraph observations.nonempty graph)
        pair.1 pair.2 := by
    change protocol.WellPosed
        (AffineData.ofGraph observations.nonempty graph) ∧
      FitCertificate protocol (AffineData.ofGraph observations.nonempty graph)
        pair.1 pair.2 at hFit
    exact hFit.2
  let candidate : Length :=
    ⟨pair.1 + pair.2 *
      coordinateInSI SIUnitChoices.SI referenceTemperature⟩
  refine ⟨candidate, ?_, ?_⟩
  · refine ⟨hGraph, ?_, pair.1, pair.2, hFit, ?_⟩
    · simpa only [candidate, coordinateInSI_self] using
        hDomain.2 pair.1 pair.2 hFitCertificate
    · simp only [candidate, coordinateInSI_self]
  · intro other hOther
    change HeightTemperatureGraphSolution observations graph ∧
        0 < coordinateInSI SIUnitChoices.SI other ∧
        ∃ intercept slope,
          HeightTemperatureProtocolFitSolution protocol observations.nonempty
              graph intercept slope ∧
            coordinateInSI SIUnitChoices.SI other =
              intercept + slope *
                coordinateInSI SIUnitChoices.SI referenceTemperature at hOther
    rcases hOther with ⟨_, _, intercept, slope, hOtherFit, hOtherCoordinate⟩
    have hPair : (intercept, slope) = pair :=
      hFitUnique (intercept, slope) hOtherFit
    cases hPair
    apply (coordinateInSI_eq_iff SIUnitChoices.SI other candidate).mp
    simpa only [candidate, coordinateInSI_self, Prod.fst, Prod.snd] using
      hOtherCoordinate

/-- Explicit bridge adding identity calibration to the provenance already
carried by a height--temperature series. -/
def CalibratedHeightSeriesBridge {q : ℕ}
    (observations : HeightTemperatureSeries q) : Prop :=
  CoolingSensorsCalibrated observations.run.sensors

/-- With the calibration bridge, every readout equals its same-index true
temperature and height. -/
lemma calibratedHeightSeriesBridge_readout_eq_state {q : ℕ}
    (observations : HeightTemperatureSeries q)
    (hCalibrated : CalibratedHeightSeriesBridge observations) (i : Fin q) :
    (observations.samples i).observedTemperature =
        (observations.run.trueStates i.val).temperature ∧
      (observations.samples i).observedHeight =
        (observations.run.trueStates i.val).liquidFreeHeight := by
  rcases hCalibrated with ⟨hTemperatureCalibrated, hHeightCalibrated⟩
  rcases observations.hasProvenance i with
    ⟨_, hTemperatureReadout, hHeightReadout⟩
  constructor
  · calc
      (observations.samples i).observedTemperature =
          observations.run.sensors.temperatureResponse
            (observations.run.trueStates i.val).temperature :=
        hTemperatureReadout
      _ = (observations.run.trueStates i.val).temperature :=
        hTemperatureCalibrated _
  · calc
      (observations.samples i).observedHeight =
          observations.run.sensors.heightResponse
            (observations.run.trueStates i.val).liquidFreeHeight :=
        hHeightReadout
      _ = (observations.run.trueStates i.val).liquidFreeHeight :=
        hHeightCalibrated _

/-- Deductive, prepared-run reference state with zero vapor pressure at the
stated reference temperature.  Its height is distinct from the B.3 fit. -/
def ZeroVaporReferenceState (run : CoolingRun) (height : Length) : Prop :=
  PreparedCoolingRun run ∧
    0 < coordinateInSI SIUnitChoices.SI height ∧
    TotalPartialPressureBalance run.atmosphericPressure
      run.atmosphericPressure (0 : Pressure) ∧
    DryAirIdealGasEquationAt run.atmosphericPressure
      (liquidFreeVolume run height) run.dryAirAmount run.molarGasConstant
      referenceTemperature

/-- Every prepared run has exactly one positive deductive zero-vapor
reference height. -/
theorem existsUnique_zeroVaporReferenceState (run : CoolingRun)
    (hPrepared : PreparedCoolingRun run) :
    ∃! height : Length, ZeroVaporReferenceState run height := by
  have hPreparedParts := hPrepared
  rcases hPreparedParts with
    ⟨hGeometry, hAtmosphericPressure, hDryAirAmount, _, _, _, _, _, _, _, _, _,
      hGasConstant⟩
  have hArea :
      0 < coordinateInSI SIUnitChoices.SI
        (innerClearCrossSectionArea run.apparatus.measurements) :=
    (clearCrossSectionAreas_positive run.apparatus.measurements hGeometry).1
  have hGasConstantPositive :
      0 < coordinateInSI SIUnitChoices.SI run.molarGasConstant := by
    rw [hGasConstant]
    norm_num [molarGasConstantInJoulesPerMoleKelvin]
  have hNumeratorPositive :
      0 < coordinateInSI SIUnitChoices.SI run.dryAirAmount *
          coordinateInSI SIUnitChoices.SI run.molarGasConstant *
          coordinateInSI SIUnitChoices.SI referenceTemperature :=
    mul_pos (mul_pos hDryAirAmount hGasConstantPositive)
      referenceTemperature_positive
  have hDenominatorPositive :
      0 < coordinateInSI SIUnitChoices.SI run.atmosphericPressure *
          coordinateInSI SIUnitChoices.SI
            (innerClearCrossSectionArea run.apparatus.measurements) :=
    mul_pos hAtmosphericPressure hArea
  have hAtmosphericPressureVal : 0 < run.atmosphericPressure.val := by
    simpa only [coordinateInSI_self] using hAtmosphericPressure
  have hAreaVal :
      0 < (innerClearCrossSectionArea run.apparatus.measurements).val := by
    simpa only [coordinateInSI_self] using hArea
  let candidate : Length :=
    ⟨(coordinateInSI SIUnitChoices.SI run.dryAirAmount *
          coordinateInSI SIUnitChoices.SI run.molarGasConstant *
          coordinateInSI SIUnitChoices.SI referenceTemperature) /
        (coordinateInSI SIUnitChoices.SI run.atmosphericPressure *
          coordinateInSI SIUnitChoices.SI
            (innerClearCrossSectionArea run.apparatus.measurements))⟩
  have hCandidate : ZeroVaporReferenceState run candidate := by
    refine ⟨hPrepared, ?_, ?_, ?_⟩
    · simpa only [candidate, coordinateInSI_self] using
        div_pos hNumeratorPositive hDenominatorPositive
    · simp [TotalPartialPressureBalance]
    · refine ⟨referenceTemperature_positive, ?_⟩
      simp only [liquidFreeVolume, candidate, coordinateInSI_self]
      field_simp [ne_of_gt hAtmosphericPressureVal, ne_of_gt hAreaVal]
  refine ⟨candidate, hCandidate, ?_⟩
  intro other hOther
  rcases hOther with ⟨_, _, _, hOtherGasLaw⟩
  have hOtherEquation := hOtherGasLaw.2
  have hCandidateEquation := hCandidate.2.2.2.2
  simp only [liquidFreeVolume, coordinateInSI_self] at hOtherEquation
  simp only [liquidFreeVolume, coordinateInSI_self] at hCandidateEquation
  have hProduct :
      (run.atmosphericPressure.val *
          (innerClearCrossSectionArea run.apparatus.measurements).val) *
          other.val =
        (run.atmosphericPressure.val *
          (innerClearCrossSectionArea run.apparatus.measurements).val) *
          candidate.val := by
    calc
      (run.atmosphericPressure.val *
          (innerClearCrossSectionArea run.apparatus.measurements).val) *
          other.val =
          run.atmosphericPressure.val *
            ((innerClearCrossSectionArea run.apparatus.measurements).val *
              other.val) := by ring
      _ = run.dryAirAmount.val * run.molarGasConstant.val *
          referenceTemperature.val := hOtherEquation
      _ = run.atmosphericPressure.val *
          ((innerClearCrossSectionArea run.apparatus.measurements).val *
            candidate.val) := hCandidateEquation.symm
      _ = (run.atmosphericPressure.val *
          (innerClearCrossSectionArea run.apparatus.measurements).val) *
          candidate.val := by ring
  have hCoordinate : other.val = candidate.val :=
    mul_left_cancel₀
      (mul_ne_zero (ne_of_gt hAtmosphericPressureVal) (ne_of_gt hAreaVal))
      hProduct
  apply (coordinateInSI_eq_iff SIUnitChoices.SI other candidate).mp
  simpa only [coordinateInSI_self] using hCoordinate

/-- Explicit approximation equating the empirical B.3 height with the
separately deduced zero-vapor reference height. -/
def ExtrapolatedIdealizedZeroVaporBridge {q : ℕ} (run : CoolingRun)
    (observations : HeightTemperatureSeries q) (protocol : FitProtocol q)
    (graph : IndexedSeries q (ℝ × ℝ)) (extrapolatedHeight idealizedHeight : Length) :
    Prop :=
  observations.run = run ∧
    ExtrapolatedReferenceHeightSolution observations protocol graph
      extrapolatedHeight ∧
    ZeroVaporReferenceState run idealizedHeight ∧
    extrapolatedHeight = idealizedHeight

/-- Known-data domain in which the fixed inventory demands a dry pressure
strictly below the atmospheric total. -/
def AdmissibleVaporDatum (run : CoolingRun) (temperature : Temperature)
    (height : Length) : Prop :=
  PreparedCoolingRun run ∧
    0 < coordinateInSI SIUnitChoices.SI temperature ∧
    0 < coordinateInSI SIUnitChoices.SI height ∧
    coordinateInSI SIUnitChoices.SI run.dryAirAmount *
        coordinateInSI SIUnitChoices.SI run.molarGasConstant *
        coordinateInSI SIUnitChoices.SI temperature <
      coordinateInSI SIUnitChoices.SI run.atmosphericPressure *
        coordinateInSI SIUnitChoices.SI (liquidFreeVolume run height)

/-- A positive vapor pressure constrained by total-pressure balance and the
same fixed dry-air inventory used in the reference state. -/
def VaporPressureSolution (run : CoolingRun) (idealizedHeight : Length)
    (temperature : Temperature) (height : Length) (vaporPressure : Pressure) : Prop :=
  PreparedCoolingRun run ∧
    ZeroVaporReferenceState run idealizedHeight ∧
    0 < coordinateInSI SIUnitChoices.SI temperature ∧
    0 < coordinateInSI SIUnitChoices.SI height ∧
    0 < coordinateInSI SIUnitChoices.SI vaporPressure ∧
    ∃ dryAirPressure : Pressure,
      0 < coordinateInSI SIUnitChoices.SI dryAirPressure ∧
        TotalPartialPressureBalance run.atmosphericPressure dryAirPressure
          vaporPressure ∧
        DryAirIdealGasEquationAt dryAirPressure (liquidFreeVolume run height)
          run.dryAirAmount run.molarGasConstant temperature

/-- Prepared reference data and the strict admissibility inequality determine
exactly one positive vapor pressure. -/
theorem existsUnique_vaporPressureSolution (run : CoolingRun)
    (idealizedHeight : Length) (temperature : Temperature) (height : Length)
    (hReference : ZeroVaporReferenceState run idealizedHeight)
    (hAdmissible : AdmissibleVaporDatum run temperature height) :
    ∃! vaporPressure : Pressure,
      VaporPressureSolution run idealizedHeight temperature height
        vaporPressure := by
  rcases hAdmissible with
    ⟨hPrepared, hTemperature, hHeight, hAdmissibilityInequality⟩
  have hPreparedParts := hPrepared
  rcases hPreparedParts with
    ⟨hGeometry, hAtmosphericPressure, hDryAirAmount, _, _, _, _, _, _, _, _, _,
      hGasConstant⟩
  have hArea :
      0 < coordinateInSI SIUnitChoices.SI
        (innerClearCrossSectionArea run.apparatus.measurements) :=
    (clearCrossSectionAreas_positive run.apparatus.measurements hGeometry).1
  have hGasConstantPositive :
      0 < coordinateInSI SIUnitChoices.SI run.molarGasConstant := by
    rw [hGasConstant]
    norm_num [molarGasConstantInJoulesPerMoleKelvin]
  have hVolume :
      0 < coordinateInSI SIUnitChoices.SI (liquidFreeVolume run height) := by
    simpa only [liquidFreeVolume, coordinateInSI_self] using
      mul_pos hArea hHeight
  have hDryNumerator :
      0 < coordinateInSI SIUnitChoices.SI run.dryAirAmount *
          coordinateInSI SIUnitChoices.SI run.molarGasConstant *
          coordinateInSI SIUnitChoices.SI temperature :=
    mul_pos (mul_pos hDryAirAmount hGasConstantPositive) hTemperature
  let dryAirPressure : Pressure :=
    ⟨(coordinateInSI SIUnitChoices.SI run.dryAirAmount *
        coordinateInSI SIUnitChoices.SI run.molarGasConstant *
        coordinateInSI SIUnitChoices.SI temperature) /
      coordinateInSI SIUnitChoices.SI (liquidFreeVolume run height)⟩
  let vaporPressure : Pressure :=
    ⟨coordinateInSI SIUnitChoices.SI run.atmosphericPressure -
      (coordinateInSI SIUnitChoices.SI run.dryAirAmount *
          coordinateInSI SIUnitChoices.SI run.molarGasConstant *
          coordinateInSI SIUnitChoices.SI temperature) /
        coordinateInSI SIUnitChoices.SI (liquidFreeVolume run height)⟩
  have hDryAirPressure :
      0 < coordinateInSI SIUnitChoices.SI dryAirPressure := by
    simpa only [dryAirPressure, coordinateInSI_self] using
      div_pos hDryNumerator hVolume
  have hDryBelowAtmospheric :
      (coordinateInSI SIUnitChoices.SI run.dryAirAmount *
          coordinateInSI SIUnitChoices.SI run.molarGasConstant *
          coordinateInSI SIUnitChoices.SI temperature) /
          coordinateInSI SIUnitChoices.SI (liquidFreeVolume run height) <
        coordinateInSI SIUnitChoices.SI run.atmosphericPressure :=
    (div_lt_iff₀ hVolume).2 hAdmissibilityInequality
  have hVaporPressure :
      0 < coordinateInSI SIUnitChoices.SI vaporPressure := by
    simpa only [vaporPressure, coordinateInSI_self] using
      sub_pos.mpr hDryBelowAtmospheric
  have hBalance :
      TotalPartialPressureBalance run.atmosphericPressure dryAirPressure
        vaporPressure := by
    unfold TotalPartialPressureBalance
    apply (coordinateInSI_eq_iff SIUnitChoices.SI
      run.atmosphericPressure (dryAirPressure + vaporPressure)).mp
    simp only [coordinateInSI_self, WithDim.val_add, dryAirPressure,
      vaporPressure]
    ring
  have hDryGasLaw :
      DryAirIdealGasEquationAt dryAirPressure (liquidFreeVolume run height)
        run.dryAirAmount run.molarGasConstant temperature := by
    refine ⟨hTemperature, ?_⟩
    simpa only [dryAirPressure, coordinateInSI_self] using
      div_mul_cancel₀
        (coordinateInSI SIUnitChoices.SI run.dryAirAmount *
          coordinateInSI SIUnitChoices.SI run.molarGasConstant *
          coordinateInSI SIUnitChoices.SI temperature)
        (ne_of_gt hVolume)
  have hCandidate :
      VaporPressureSolution run idealizedHeight temperature height
        vaporPressure :=
    ⟨hPrepared, hReference, hTemperature, hHeight, hVaporPressure,
      dryAirPressure, hDryAirPressure, hBalance, hDryGasLaw⟩
  refine ⟨vaporPressure, hCandidate, ?_⟩
  intro other hOther
  rcases hOther with
    ⟨_, _, _, _, _, otherDryAirPressure, _, hOtherBalance, hOtherDryGasLaw⟩
  have hDryProduct :
      coordinateInSI SIUnitChoices.SI otherDryAirPressure *
          coordinateInSI SIUnitChoices.SI (liquidFreeVolume run height) =
        coordinateInSI SIUnitChoices.SI dryAirPressure *
          coordinateInSI SIUnitChoices.SI (liquidFreeVolume run height) :=
    hOtherDryGasLaw.2.trans hDryGasLaw.2.symm
  have hDryCoordinate :
      coordinateInSI SIUnitChoices.SI otherDryAirPressure =
        coordinateInSI SIUnitChoices.SI dryAirPressure :=
    mul_right_cancel₀ (ne_of_gt hVolume) hDryProduct
  have hDryEquality : otherDryAirPressure = dryAirPressure :=
    (coordinateInSI_eq_iff SIUnitChoices.SI otherDryAirPressure
      dryAirPressure).mp hDryCoordinate
  rw [hDryEquality] at hOtherBalance
  exact add_left_cancel (hOtherBalance.symm.trans hBalance)

/-- On the admissible prepared domain, the governing vapor-pressure solution
is equivalent to the requested height formula. -/
theorem vaporPressureSolution_iff_heightFormula (run : CoolingRun)
    (idealizedHeight : Length) (temperature : Temperature) (height : Length)
    (vaporPressure : Pressure)
    (hReference : ZeroVaporReferenceState run idealizedHeight)
    (hAdmissible : AdmissibleVaporDatum run temperature height) :
    VaporPressureSolution run idealizedHeight temperature height vaporPressure ↔
      0 < coordinateInSI SIUnitChoices.SI vaporPressure ∧
      coordinateInSI SIUnitChoices.SI vaporPressure =
        coordinateInSI SIUnitChoices.SI run.atmosphericPressure *
          (1 -
            coordinateInSI SIUnitChoices.SI idealizedHeight *
                coordinateInSI SIUnitChoices.SI temperature /
              (coordinateInSI SIUnitChoices.SI height *
                coordinateInSI SIUnitChoices.SI referenceTemperature)) := by
  have hAdmissibleParts := hAdmissible
  rcases hAdmissibleParts with
    ⟨hPrepared, _, hHeight, _⟩
  have hReferenceParts := hReference
  rcases hReferenceParts with
    ⟨_, _, _, hReferenceGasLaw⟩
  have hArea :
      0 < coordinateInSI SIUnitChoices.SI
        (innerClearCrossSectionArea run.apparatus.measurements) :=
    (clearCrossSectionAreas_positive run.apparatus.measurements hPrepared.1).1
  have hAreaVal :
      0 < (innerClearCrossSectionArea run.apparatus.measurements).val := by
    simpa only [coordinateInSI_self] using hArea
  have hHeightVal : 0 < height.val := by
    simpa only [coordinateInSI_self] using hHeight
  have hReferenceTemperatureVal : 0 < referenceTemperature.val := by
    simpa only [coordinateInSI_self] using referenceTemperature_positive
  have hCharacterize : ∀ pressure : Pressure,
      VaporPressureSolution run idealizedHeight temperature height pressure →
        coordinateInSI SIUnitChoices.SI pressure =
          coordinateInSI SIUnitChoices.SI run.atmosphericPressure *
            (1 -
              coordinateInSI SIUnitChoices.SI idealizedHeight *
                  coordinateInSI SIUnitChoices.SI temperature /
                (coordinateInSI SIUnitChoices.SI height *
                  coordinateInSI SIUnitChoices.SI referenceTemperature)) := by
    intro pressure hSolution
    rcases hSolution with
      ⟨_, _, _, _, _, dryAirPressure, _, hBalance, hCurrentGasLaw⟩
    change run.atmosphericPressure = dryAirPressure + pressure at hBalance
    have hBalanceVal :
        run.atmosphericPressure.val = dryAirPressure.val + pressure.val := by
      have hCoordinateBalance :=
        congrArg (coordinateInSI SIUnitChoices.SI) hBalance
      simpa only [coordinateInSI_self, WithDim.val_add] using hCoordinateBalance
    have hReferenceEquation := hReferenceGasLaw.2
    have hCurrentEquation := hCurrentGasLaw.2
    simp only [liquidFreeVolume, coordinateInSI_self] at hReferenceEquation
    simp only [liquidFreeVolume, coordinateInSI_self] at hCurrentEquation
    have hCrossWithArea :
        (innerClearCrossSectionArea run.apparatus.measurements).val *
            (run.atmosphericPressure.val * idealizedHeight.val *
              temperature.val) =
          (innerClearCrossSectionArea run.apparatus.measurements).val *
            (dryAirPressure.val * height.val * referenceTemperature.val) := by
      calc
        (innerClearCrossSectionArea run.apparatus.measurements).val *
            (run.atmosphericPressure.val * idealizedHeight.val *
              temperature.val) =
            (run.atmosphericPressure.val *
              ((innerClearCrossSectionArea run.apparatus.measurements).val *
                idealizedHeight.val)) * temperature.val := by ring
        _ = (run.dryAirAmount.val * run.molarGasConstant.val *
              referenceTemperature.val) * temperature.val := by
          rw [hReferenceEquation]
        _ = (run.dryAirAmount.val * run.molarGasConstant.val *
              temperature.val) * referenceTemperature.val := by ring
        _ = (dryAirPressure.val *
              ((innerClearCrossSectionArea run.apparatus.measurements).val *
                height.val)) * referenceTemperature.val := by
          rw [hCurrentEquation]
        _ = (innerClearCrossSectionArea run.apparatus.measurements).val *
            (dryAirPressure.val * height.val * referenceTemperature.val) := by
          ring
    have hCross :
        run.atmosphericPressure.val * idealizedHeight.val * temperature.val =
          dryAirPressure.val * height.val * referenceTemperature.val :=
      mul_left_cancel₀ (ne_of_gt hAreaVal) hCrossWithArea
    have hHeightTemperatureNe :
        height.val * referenceTemperature.val ≠ 0 :=
      mul_ne_zero (ne_of_gt hHeightVal) (ne_of_gt hReferenceTemperatureVal)
    have hDryFormula :
        dryAirPressure.val =
          run.atmosphericPressure.val * idealizedHeight.val * temperature.val /
            (height.val * referenceTemperature.val) := by
      apply (eq_div_iff hHeightTemperatureNe).2
      calc
        dryAirPressure.val * (height.val * referenceTemperature.val) =
            dryAirPressure.val * height.val * referenceTemperature.val := by ring
        _ = run.atmosphericPressure.val * idealizedHeight.val *
            temperature.val := hCross.symm
    have hPressureFormula :
        pressure.val = run.atmosphericPressure.val *
          (1 - idealizedHeight.val * temperature.val /
            (height.val * referenceTemperature.val)) := by
      calc
        pressure.val = run.atmosphericPressure.val - dryAirPressure.val := by
          linarith
        _ = run.atmosphericPressure.val -
            run.atmosphericPressure.val * idealizedHeight.val * temperature.val /
              (height.val * referenceTemperature.val) := by rw [hDryFormula]
        _ = run.atmosphericPressure.val *
            (1 - idealizedHeight.val * temperature.val /
              (height.val * referenceTemperature.val)) := by ring
    simpa only [coordinateInSI_self] using hPressureFormula
  constructor
  · intro hSolution
    have hSolutionParts := hSolution
    rcases hSolutionParts with ⟨_, _, _, _, hPositive, _⟩
    exact ⟨hPositive, hCharacterize vaporPressure hSolution⟩
  · rintro ⟨_, hFormula⟩
    obtain ⟨solution, hSolution, _⟩ :=
      existsUnique_vaporPressureSolution run idealizedHeight temperature height
        hReference hAdmissible
    have hCoordinate :
        coordinateInSI SIUnitChoices.SI vaporPressure =
          coordinateInSI SIUnitChoices.SI solution :=
      hFormula.trans (hCharacterize solution hSolution).symm
    have hEquality : vaporPressure = solution :=
      (coordinateInSI_eq_iff SIUnitChoices.SI vaporPressure solution).mp
        hCoordinate
    rw [hEquality]
    exact hSolution

/-- Calibrated B.4 characterization at an original sample, after explicitly
identifying the B.3 and deductive zero-vapor reference heights. -/
theorem calibratedReadoutVaporPressureSolution_iff_heightFormula {q : ℕ}
    (observations : HeightTemperatureSeries q) (protocol : FitProtocol q)
    (graph : IndexedSeries q (ℝ × ℝ)) (extrapolatedHeight idealizedHeight : Length)
    (vaporPressure : Pressure) (i : Fin q)
    (hCalibrated : CalibratedHeightSeriesBridge observations)
    (hBridge : ExtrapolatedIdealizedZeroVaporBridge observations.run observations
      protocol graph extrapolatedHeight idealizedHeight)
    (hAdmissible : AdmissibleVaporDatum observations.run
      (observations.samples i).observedTemperature
      (observations.samples i).observedHeight) :
    VaporPressureSolution observations.run idealizedHeight
        (observations.samples i).observedTemperature
        (observations.samples i).observedHeight vaporPressure ↔
      0 < coordinateInSI SIUnitChoices.SI vaporPressure ∧
      coordinateInSI SIUnitChoices.SI vaporPressure =
        coordinateInSI SIUnitChoices.SI observations.run.atmosphericPressure *
          (1 -
            coordinateInSI SIUnitChoices.SI extrapolatedHeight *
                coordinateInSI SIUnitChoices.SI
                  (observations.samples i).observedTemperature /
              (coordinateInSI SIUnitChoices.SI
                  (observations.samples i).observedHeight *
                coordinateInSI SIUnitChoices.SI referenceTemperature)) := by
  have _hReadoutIdentity :=
    calibratedHeightSeriesBridge_readout_eq_state observations hCalibrated i
  rcases hBridge with
    ⟨_, _, hReference, hExtrapolatedEqualsIdealized⟩
  simpa only [hExtrapolatedEqualsIdealized] using
    (vaporPressureSolution_iff_heightFormula observations.run idealizedHeight
      (observations.samples i).observedTemperature
      (observations.samples i).observedHeight vaporPressure hReference
      hAdmissible)

/-- A typed temperature--vapor-pressure pair awaiting or carrying provenance. -/
structure VaporPressureSample where
  temperature : Temperature
  vaporPressure : Pressure

/-- Provenance of one derived vapor-pressure sample from an original calibrated
readout occurrence and the explicit B.3-to-zero-vapor bridge. -/
def VaporPressureProvenance {q : ℕ}
    (observations : HeightTemperatureSeries q) (protocol : FitProtocol q)
    (graph : IndexedSeries q (ℝ × ℝ)) (extrapolatedHeight idealizedHeight : Length)
    (index : Fin q) (sample : VaporPressureSample) : Prop :=
  CalibratedHeightSeriesBridge observations ∧
    ExtrapolatedIdealizedZeroVaporBridge observations.run observations protocol
      graph extrapolatedHeight idealizedHeight ∧
    sample.temperature = (observations.samples index).observedTemperature ∧
    VaporPressureSolution observations.run idealizedHeight
      (observations.samples index).observedTemperature
      (observations.samples index).observedHeight sample.vaporPressure

/-- Exact same-index transformation of an external height series to candidate
vapor-pressure samples, preserving order and multiplicity. -/
def VaporPressureSeries {q : ℕ} (observations : HeightTemperatureSeries q)
    (protocol : FitProtocol q) (graph : IndexedSeries q (ℝ × ℝ))
    (extrapolatedHeight idealizedHeight : Length)
    (series : ObservationSeries q CoolingRun VaporPressureSample
      (fun _ _ _ ↦ True)) : Prop :=
  series.run = observations.run ∧
    ∃ row : HeightTemperatureObservation → VaporPressureSample,
      ExactTable observations row series.samples ∧
        ∀ i, VaporPressureProvenance observations protocol graph
          extrapolatedHeight idealizedHeight i (series.samples i)

/-- Calibrated, bridged, admissible readouts determine exactly one same-index
vapor-pressure sample series. -/
theorem existsUnique_vaporPressureSeries {q : ℕ}
    (observations : HeightTemperatureSeries q) (protocol : FitProtocol q)
    (graph : IndexedSeries q (ℝ × ℝ)) (extrapolatedHeight idealizedHeight : Length)
    (hCalibrated : CalibratedHeightSeriesBridge observations)
    (hBridge : ExtrapolatedIdealizedZeroVaporBridge observations.run observations
      protocol graph extrapolatedHeight idealizedHeight)
    (hAdmissible : ∀ i, AdmissibleVaporDatum observations.run
      (observations.samples i).observedTemperature
      (observations.samples i).observedHeight) :
    ∃! series : ObservationSeries q CoolingRun VaporPressureSample
        (fun _ _ _ ↦ True),
      VaporPressureSeries observations protocol graph extrapolatedHeight
        idealizedHeight series := by
  have hBridgeParts := hBridge
  rcases hBridgeParts with ⟨_, _, hReference, _⟩
  let row : HeightTemperatureObservation → VaporPressureSample :=
    fun observation ↦
      ⟨observation.observedTemperature,
        ⟨coordinateInSI SIUnitChoices.SI observations.run.atmosphericPressure *
          (1 -
            coordinateInSI SIUnitChoices.SI idealizedHeight *
                coordinateInSI SIUnitChoices.SI observation.observedTemperature /
              (coordinateInSI SIUnitChoices.SI observation.observedHeight *
                coordinateInSI SIUnitChoices.SI referenceTemperature))⟩⟩
  have hRowSolution : ∀ i,
      VaporPressureSolution observations.run idealizedHeight
        (observations.samples i).observedTemperature
        (observations.samples i).observedHeight
        (row (observations.samples i)).vaporPressure := by
    intro i
    have hCharacterization :=
      vaporPressureSolution_iff_heightFormula observations.run idealizedHeight
        (observations.samples i).observedTemperature
        (observations.samples i).observedHeight
        (row (observations.samples i)).vaporPressure hReference
        (hAdmissible i)
    obtain ⟨solution, hSolution, _⟩ :=
      existsUnique_vaporPressureSolution observations.run idealizedHeight
        (observations.samples i).observedTemperature
        (observations.samples i).observedHeight hReference (hAdmissible i)
    have hSolutionFormula :=
      (vaporPressureSolution_iff_heightFormula observations.run idealizedHeight
        (observations.samples i).observedTemperature
        (observations.samples i).observedHeight solution hReference
        (hAdmissible i)).1 hSolution
    apply hCharacterization.2
    constructor
    · rw [hSolutionFormula.2] at hSolutionFormula
      simpa only [row, coordinateInSI_self] using hSolutionFormula.1
    · simp only [row, coordinateInSI_self]
  let series : ObservationSeries q CoolingRun VaporPressureSample
      (fun _ _ _ ↦ True) :=
    ⟨observations.nonempty, observations.run,
      canonicalMap observations row, fun _ ↦ True.intro⟩
  have hSeries :
      VaporPressureSeries observations protocol graph extrapolatedHeight
        idealizedHeight series := by
    refine ⟨rfl, row, ?_, ?_⟩
    · rfl
    · intro i
      refine ⟨hCalibrated, hBridge, ?_, ?_⟩
      · simp only [series, canonicalMap, row]
      · simpa only [series, canonicalMap] using hRowSolution i
  have sample_ext : ∀ a b : VaporPressureSample,
      a.temperature = b.temperature →
        a.vaporPressure = b.vaporPressure → a = b := by
    intro a b hTemperature hPressure
    cases a
    cases b
    simp_all
  have series_ext : ∀
      a b : ObservationSeries q CoolingRun VaporPressureSample
        (fun _ _ _ ↦ True),
      a.run = b.run → a.samples = b.samples → a = b := by
    intro a b hRun hSamples
    cases a
    cases b
    simp_all
  refine ⟨series, hSeries, ?_⟩
  intro other hOther
  rcases hOther with ⟨hRun, _, _, hOtherProvenance⟩
  have hRunEquality : other.run = series.run := by
    simpa only [series] using hRun
  have hSamplesEquality : other.samples = series.samples := by
    funext i
    rcases hOtherProvenance i with
      ⟨_, _, hOtherTemperature, hOtherPressureSolution⟩
    have hSeriesPressureSolution :
        VaporPressureSolution observations.run idealizedHeight
          (observations.samples i).observedTemperature
          (observations.samples i).observedHeight
          (series.samples i).vaporPressure := by
      simpa only [series, canonicalMap] using hRowSolution i
    obtain ⟨solution, _, hPressureUnique⟩ :=
      existsUnique_vaporPressureSolution observations.run idealizedHeight
        (observations.samples i).observedTemperature
        (observations.samples i).observedHeight hReference (hAdmissible i)
    have hPressureEquality :
        (other.samples i).vaporPressure =
          (series.samples i).vaporPressure :=
      (hPressureUnique (other.samples i).vaporPressure
        hOtherPressureSolution).trans
        (hPressureUnique (series.samples i).vaporPressure
          hSeriesPressureSolution).symm
    apply sample_ext
    · simpa only [series, canonicalMap, row] using hOtherTemperature
    · exact hPressureEquality
  exact series_ext other series hRunEquality hSamplesEquality

/-- Positive logarithmic domain for one exact vapor-pressure series and the
generic law parameters of its named cooling run. -/
def PositiveClausiusClapeyronDomain {q : ℕ}
    (series : ObservationSeries q CoolingRun VaporPressureSample
      (fun _ _ _ ↦ True)) (pressureScale : Pressure)
    (referenceVaporPressure : Pressure) : Prop :=
  0 < coordinateInSI SIUnitChoices.SI series.run.molarGasConstant ∧
    0 < coordinateInSI SIUnitChoices.SI referenceTemperature ∧
    0 < coordinateInSI SIUnitChoices.SI pressureScale ∧
    PositiveReferenceVaporPressure referenceVaporPressure ∧
    ∀ i,
      0 < coordinateInSI SIUnitChoices.SI (series.samples i).temperature ∧
        0 < coordinateInSI SIUnitChoices.SI (series.samples i).vaporPressure

/-- Exact same-index Clausius--Clapeyron transform of a vapor-pressure series. -/
def ClausiusClapeyronGraphSolution {q : ℕ}
    (series : ObservationSeries q CoolingRun VaporPressureSample
      (fun _ _ _ ↦ True))
    (pressureScale referenceVaporPressure : Pressure)
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  PositiveClausiusClapeyronDomain series pressureScale
      referenceVaporPressure ∧
    ExactGraph series
      (fun sample ↦
        1 / coordinateInSI SIUnitChoices.SI sample.temperature -
          1 / coordinateInSI SIUnitChoices.SI referenceTemperature)
      (fun sample ↦
        Real.log
          (coordinateInSI SIUnitChoices.SI sample.vaporPressure /
            coordinateInSI SIUnitChoices.SI pressureScale))
      graph

/-- Positive-domain samples determine one exact transformed graph. -/
theorem existsUnique_clausiusClapeyronGraphSolution {q : ℕ}
    (series : ObservationSeries q CoolingRun VaporPressureSample
      (fun _ _ _ ↦ True))
    (pressureScale referenceVaporPressure : Pressure)
    (hDomain : PositiveClausiusClapeyronDomain series pressureScale
      referenceVaporPressure) :
    ∃! graph : IndexedSeries q (ℝ × ℝ),
      ClausiusClapeyronGraphSolution series pressureScale
        referenceVaporPressure graph := by
  obtain ⟨graph, hExact, hUnique⟩ :=
    existsUnique_exactGraph series
      (fun sample ↦
        1 / coordinateInSI SIUnitChoices.SI sample.temperature -
          1 / coordinateInSI SIUnitChoices.SI referenceTemperature)
      (fun sample ↦
        Real.log
          (coordinateInSI SIUnitChoices.SI sample.vaporPressure /
            coordinateInSI SIUnitChoices.SI pressureScale))
  refine ⟨graph, ⟨hDomain, hExact⟩, ?_⟩
  intro other hOther
  exact hUnique other hOther.2

/-- A candidate fit of transformed data certified by a separately supplied,
well-posed protocol. -/
def ClausiusClapeyronProtocolFitSolution {q : ℕ}
    (protocol : FitProtocol q) (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) (intercept slope : ℝ) : Prop :=
  let data := AffineData.ofGraph nonempty graph
  protocol.WellPosed data ∧ FitCertificate protocol data intercept slope

/-- A well-posed declared protocol determines one transformed fit pair. -/
theorem existsUnique_clausiusClapeyronProtocolFitSolution {q : ℕ}
    (protocol : FitProtocol q) (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ))
    (hWellPosed : protocol.WellPosed (AffineData.ofGraph nonempty graph)) :
    ∃! pair : ℝ × ℝ,
      ClausiusClapeyronProtocolFitSolution protocol nonempty graph
        pair.1 pair.2 := by
  obtain ⟨pair, hPair, hUnique⟩ :=
    FitProtocol.existsUnique_fitCertificate protocol
      (AffineData.ofGraph nonempty graph) hWellPosed
  refine ⟨pair, ?_, ?_⟩
  · change protocol.WellPosed (AffineData.ofGraph nonempty graph) ∧
      FitCertificate protocol (AffineData.ofGraph nonempty graph) pair.1 pair.2
    exact ⟨hWellPosed, hPair⟩
  · intro other hOther
    change protocol.WellPosed (AffineData.ofGraph nonempty graph) ∧
      FitCertificate protocol (AffineData.ofGraph nonempty graph)
        other.1 other.2 at hOther
    exact hUnique other hOther.2

/-- Under explicit OLS selection and predictor nondegeneracy, the transformed
fit predicate is exactly the normal-equation affine-fit relation. -/
lemma clausiusClapeyronProtocolFitSolution_ordinaryLeastSquaresProtocol_iff
    {q : ℕ} (nonempty : 0 < q) (graph : IndexedSeries q (ℝ × ℝ))
    (hNondegenerate :
      NondegeneratePredictor (AffineData.ofGraph nonempty graph))
    (intercept slope : ℝ) :
    ClausiusClapeyronProtocolFitSolution (ordinaryLeastSquaresProtocol q)
        nonempty graph intercept slope ↔
      IsAffineFit (AffineData.ofGraph nonempty graph) intercept slope := by
  have hPositiveVariance :
      0 < centeredPredictorVariance (AffineData.ofGraph nonempty graph) :=
    (positive_centeredPredictorVariance_iff_nondegeneratePredictor
      (AffineData.ofGraph nonempty graph)).2 hNondegenerate
  have hWellPosed := ordinaryLeastSquaresProtocol_wellPosed
    (AffineData.ofGraph nonempty graph) hPositiveVariance
  change
    ((ordinaryLeastSquaresProtocol q).WellPosed
        (AffineData.ofGraph nonempty graph) ∧
      FitCertificate (ordinaryLeastSquaresProtocol q)
        (AffineData.ofGraph nonempty graph) intercept slope) ↔
      IsAffineFit (AffineData.ofGraph nonempty graph) intercept slope
  constructor
  · exact fun h ↦
      (fitCertificate_ordinaryLeastSquaresProtocol_iff
        (AffineData.ofGraph nonempty graph) intercept slope).1 h.2
  · exact fun h ↦ ⟨hWellPosed,
      (fitCertificate_ordinaryLeastSquaresProtocol_iff
        (AffineData.ofGraph nonempty graph) intercept slope).2 h⟩

/-- The pointwise physical law makes every point of the exact transform lie
on the same affine line, independently of any fit protocol. -/
lemma clausiusClapeyronLaw_implies_exactAffineRelation {q : ℕ}
    (series : ObservationSeries q CoolingRun VaporPressureSample
      (fun _ _ _ ↦ True))
    (pressureScale referenceVaporPressure : Pressure)
    (graph : IndexedSeries q (ℝ × ℝ))
    (molarLatentHeat : MolarLatentHeat)
    (hGraph : ClausiusClapeyronGraphSolution series pressureScale
      referenceVaporPressure graph)
    (hLaw : ∀ i,
      ∃ parameters : PositiveClausiusClapeyronParameters,
        parameters.gasConstant = series.run.molarGasConstant ∧
        parameters.referenceTemperature = referenceTemperature ∧
        parameters.pressureScale = pressureScale ∧
        parameters.referenceVaporPressure = referenceVaporPressure ∧
        ∃ sample : PositiveClausiusClapeyronSample,
          sample.temperature = (series.samples i).temperature ∧
          sample.vaporPressure = (series.samples i).vaporPressure ∧
          ClausiusClapeyronLawAt parameters sample molarLatentHeat) :
    ∀ i,
      (AffineData.ofGraph series.nonempty graph).response i =
        Real.log
            (coordinateInSI SIUnitChoices.SI referenceVaporPressure /
              coordinateInSI SIUnitChoices.SI pressureScale) +
          (-coordinateInSI SIUnitChoices.SI molarLatentHeat /
            coordinateInSI SIUnitChoices.SI series.run.molarGasConstant) *
            (AffineData.ofGraph series.nonempty graph).predictor i := by
  rcases hGraph with ⟨_, hExact⟩
  change graph = canonicalPairedMap series
      (fun sample ↦
        1 / coordinateInSI SIUnitChoices.SI sample.temperature -
          1 / coordinateInSI SIUnitChoices.SI referenceTemperature)
      (fun sample ↦
        Real.log
          (coordinateInSI SIUnitChoices.SI sample.vaporPressure /
            coordinateInSI SIUnitChoices.SI pressureScale)) at hExact
  intro i
  rcases hLaw i with
    ⟨parameters, hGasConstant, hReferenceTemperature, hPressureScale,
      hReferenceVaporPressure, sample, hSampleTemperature, hSampleVaporPressure,
      hPointLaw⟩
  unfold ClausiusClapeyronLawAt at hPointLaw
  rw [hGasConstant, hReferenceTemperature, hPressureScale,
    hReferenceVaporPressure, hSampleTemperature, hSampleVaporPressure] at hPointLaw
  rw [hExact]
  simp only [AffineData.ofGraph, canonicalPairedMap, canonicalMap]
  calc
    Real.log
        (coordinateInSI SIUnitChoices.SI (series.samples i).vaporPressure /
          coordinateInSI SIUnitChoices.SI pressureScale) =
      Real.log
          (coordinateInSI SIUnitChoices.SI referenceVaporPressure /
            coordinateInSI SIUnitChoices.SI pressureScale) -
        coordinateInSI SIUnitChoices.SI molarLatentHeat /
            coordinateInSI SIUnitChoices.SI series.run.molarGasConstant *
          (1 / coordinateInSI SIUnitChoices.SI (series.samples i).temperature -
            1 / coordinateInSI SIUnitChoices.SI referenceTemperature) := hPointLaw
    _ = Real.log
          (coordinateInSI SIUnitChoices.SI referenceVaporPressure /
            coordinateInSI SIUnitChoices.SI pressureScale) +
        (-coordinateInSI SIUnitChoices.SI molarLatentHeat /
          coordinateInSI SIUnitChoices.SI series.run.molarGasConstant) *
          (1 / coordinateInSI SIUnitChoices.SI (series.samples i).temperature -
            1 / coordinateInSI SIUnitChoices.SI referenceTemperature) := by ring

/-- A supplied protocol is compatible with exact affine data when it is well
posed, an exact line exists, and every exact line receives a certificate. -/
def ExactAffineCompatibleProtocol {q : ℕ} (protocol : FitProtocol q)
    (data : AffineData q) : Prop :=
  protocol.WellPosed data ∧
    (∃ intercept slope, ∀ i, data.response i = intercept + slope * data.predictor i) ∧
    ∀ intercept slope,
      (∀ i, data.response i = intercept + slope * data.predictor i) →
        FitCertificate protocol data intercept slope

/-- Explicitly selected OLS is exact-affine compatible whenever its predictor
is nondegenerate and an exact affine line exists. -/
lemma ordinaryLeastSquaresProtocol_exactAffineCompatible {q : ℕ}
    (data : AffineData q) (hNondegenerate : NondegeneratePredictor data)
    (hExact : ∃ intercept slope,
      ∀ i, data.response i = intercept + slope * data.predictor i) :
    ExactAffineCompatibleProtocol (ordinaryLeastSquaresProtocol q) data := by
  have hPositiveVariance : 0 < centeredPredictorVariance data :=
    (positive_centeredPredictorVariance_iff_nondegeneratePredictor data).2
      hNondegenerate
  have hWellPosed :=
    ordinaryLeastSquaresProtocol_wellPosed data hPositiveVariance
  refine ⟨hWellPosed, hExact, ?_⟩
  intro intercept slope hLine
  apply (fitCertificate_ordinaryLeastSquaresProtocol_iff
    data intercept slope).2
  unfold IsAffineFit AffineNormalEquations
  have hResidual : ∀ i, AffineFit.residual data intercept slope i = 0 := by
    intro i
    unfold AffineFit.residual
    rw [hLine i]
    ring
  constructor
  · simp only [hResidual, Finset.sum_const_zero]
  · simp only [hResidual, mul_zero, Finset.sum_const_zero]

/-- A common pointwise physical law is certified by every separately supplied
exact-affine-compatible protocol. -/
theorem clausiusClapeyronLaw_implies_protocolFit {q : ℕ}
    (protocol : FitProtocol q)
    (series : ObservationSeries q CoolingRun VaporPressureSample
      (fun _ _ _ ↦ True))
    (pressureScale referenceVaporPressure : Pressure)
    (graph : IndexedSeries q (ℝ × ℝ))
    (molarLatentHeat : MolarLatentHeat)
    (hGraph : ClausiusClapeyronGraphSolution series pressureScale
      referenceVaporPressure graph)
    (hCompatible : ExactAffineCompatibleProtocol protocol
      (AffineData.ofGraph series.nonempty graph))
    (hLaw : ∀ i,
      ∃ parameters : PositiveClausiusClapeyronParameters,
        parameters.gasConstant = series.run.molarGasConstant ∧
        parameters.referenceTemperature = referenceTemperature ∧
        parameters.pressureScale = pressureScale ∧
        parameters.referenceVaporPressure = referenceVaporPressure ∧
        ∃ sample : PositiveClausiusClapeyronSample,
          sample.temperature = (series.samples i).temperature ∧
          sample.vaporPressure = (series.samples i).vaporPressure ∧
          ClausiusClapeyronLawAt parameters sample molarLatentHeat) :
    ClausiusClapeyronProtocolFitSolution protocol series.nonempty graph
      (Real.log
        (coordinateInSI SIUnitChoices.SI referenceVaporPressure /
          coordinateInSI SIUnitChoices.SI pressureScale))
      (-coordinateInSI SIUnitChoices.SI molarLatentHeat /
        coordinateInSI SIUnitChoices.SI series.run.molarGasConstant) := by
  rcases hCompatible with ⟨hWellPosed, _, hCertifiesExactLine⟩
  change protocol.WellPosed (AffineData.ofGraph series.nonempty graph) ∧
    FitCertificate protocol (AffineData.ofGraph series.nonempty graph)
      (Real.log
        (coordinateInSI SIUnitChoices.SI referenceVaporPressure /
          coordinateInSI SIUnitChoices.SI pressureScale))
      (-coordinateInSI SIUnitChoices.SI molarLatentHeat /
        coordinateInSI SIUnitChoices.SI series.run.molarGasConstant)
  refine ⟨hWellPosed, hCertifiesExactLine _ _ ?_⟩
  exact clausiusClapeyronLaw_implies_exactAffineRelation series pressureScale
    referenceVaporPressure graph molarLatentHeat hGraph hLaw

/-- Nonvacuous domain exhibiting a certificate-bearing negative-slope fit. -/
def HasNegativeSlopeProtocolFit {q : ℕ} (protocol : FitProtocol q)
    (nonempty : 0 < q) (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  ∃ intercept slope,
    ClausiusClapeyronProtocolFitSolution protocol nonempty graph
      intercept slope ∧ slope < 0

/-- A positive molar latent-heat candidate constrained by the gas constant and
the negative slope certified by the declared fit protocol. -/
def MolarLatentHeatSolution {q : ℕ} (run : CoolingRun)
    (protocol : FitProtocol q) (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) (molarLatentHeat : MolarLatentHeat) : Prop :=
  0 < coordinateInSI SIUnitChoices.SI molarLatentHeat ∧
    ∃ intercept slope,
      ClausiusClapeyronProtocolFitSolution protocol nonempty graph
          intercept slope ∧
        slope < 0 ∧
        coordinateInSI SIUnitChoices.SI molarLatentHeat =
          -coordinateInSI SIUnitChoices.SI run.molarGasConstant * slope

/-- A prepared run and a certificate-bearing negative fit determine exactly
one inferred molar latent heat. -/
theorem existsUnique_molarLatentHeatSolution {q : ℕ} (run : CoolingRun)
    (protocol : FitProtocol q) (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ))
    (hPrepared : PreparedCoolingRun run)
    (hNegative : HasNegativeSlopeProtocolFit protocol nonempty graph) :
    ∃! molarLatentHeat : MolarLatentHeat,
      MolarLatentHeatSolution run protocol nonempty graph molarLatentHeat := by
  rcases hNegative with ⟨intercept, slope, hFit, hSlope⟩
  have hPreparedParts := hPrepared
  rcases hPreparedParts with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hGasConstant⟩
  have hGasConstantPositive :
      0 < coordinateInSI SIUnitChoices.SI run.molarGasConstant := by
    rw [hGasConstant]
    norm_num [molarGasConstantInJoulesPerMoleKelvin]
  have hCandidateCoordinatePositive :
      0 < -coordinateInSI SIUnitChoices.SI run.molarGasConstant * slope :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos hGasConstantPositive) hSlope
  let candidate : MolarLatentHeat :=
    ⟨-coordinateInSI SIUnitChoices.SI run.molarGasConstant * slope⟩
  have hCandidate :
      MolarLatentHeatSolution run protocol nonempty graph candidate := by
    refine ⟨?_, intercept, slope, hFit, hSlope, ?_⟩
    · simpa only [candidate, coordinateInSI_self] using
        hCandidateCoordinatePositive
    · simp only [candidate, coordinateInSI_self]
  have hFitParts := hFit
  change protocol.WellPosed (AffineData.ofGraph nonempty graph) ∧
    FitCertificate protocol (AffineData.ofGraph nonempty graph)
      intercept slope at hFitParts
  obtain ⟨_, _, hFitUnique⟩ :=
    existsUnique_clausiusClapeyronProtocolFitSolution protocol nonempty graph
      hFitParts.1
  refine ⟨candidate, hCandidate, ?_⟩
  intro other hOther
  rcases hOther with
    ⟨_, otherIntercept, otherSlope, hOtherFit, _, hOtherCoordinate⟩
  have hPairEquality : (otherIntercept, otherSlope) = (intercept, slope) :=
    (hFitUnique (otherIntercept, otherSlope) hOtherFit).trans
      (hFitUnique (intercept, slope) hFit).symm
  cases hPairEquality
  apply (coordinateInSI_eq_iff SIUnitChoices.SI other candidate).mp
  simpa only [candidate, coordinateInSI_self] using hOtherCoordinate

/-- Complete protocol-inferred molar-to-mass latent-heat solution chain. -/
def LatentHeatSolutionChain {q : ℕ} (run : CoolingRun)
    (protocol : FitProtocol q) (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) (waterMolarMass : MolarMass)
    (molarLatentHeat : MolarLatentHeat)
    (massSpecificLatentHeat : MassSpecificLatentHeat) : Prop :=
  MolarLatentHeatSolution run protocol nonempty graph molarLatentHeat ∧
    MassSpecificLatentHeatSolution waterMolarMass molarLatentHeat
      massSpecificLatentHeat

/-- Under the two positive governing domains, the complete molar-to-mass
solution chain is unique. -/
theorem existsUnique_latentHeatSolutionChain {q : ℕ} (run : CoolingRun)
    (protocol : FitProtocol q) (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) (waterMolarMass : MolarMass)
    (hPrepared : PreparedCoolingRun run)
    (hNegative : HasNegativeSlopeProtocolFit protocol nonempty graph)
    (hWaterMolarMass : 0 < coordinateInSI SIUnitChoices.SI waterMolarMass) :
    ∃! pair : MolarLatentHeat × MassSpecificLatentHeat,
      LatentHeatSolutionChain run protocol nonempty graph waterMolarMass
        pair.1 pair.2 := by
  obtain ⟨molarLatentHeat, hMolarLatentHeat, hMolarUnique⟩ :=
    existsUnique_molarLatentHeatSolution run protocol nonempty graph hPrepared
      hNegative
  obtain ⟨massSpecificLatentHeat, hMassSpecificLatentHeat,
      hMassSpecificUnique⟩ :=
    existsUnique_massSpecificLatentHeatSolution waterMolarMass molarLatentHeat
      hWaterMolarMass hMolarLatentHeat.1
  refine ⟨(molarLatentHeat, massSpecificLatentHeat),
    ⟨hMolarLatentHeat, hMassSpecificLatentHeat⟩, ?_⟩
  rintro ⟨otherMolarLatentHeat, otherMassSpecificLatentHeat⟩
    ⟨hOtherMolarLatentHeat, hOtherMassSpecificLatentHeat⟩
  have hMolarEquality : otherMolarLatentHeat = molarLatentHeat :=
    hMolarUnique otherMolarLatentHeat hOtherMolarLatentHeat
  subst otherMolarLatentHeat
  have hMassSpecificEquality :
      otherMassSpecificLatentHeat = massSpecificLatentHeat :=
    hMassSpecificUnique otherMassSpecificLatentHeat
      hOtherMassSpecificLatentHeat
  subst otherMassSpecificLatentHeat
  rfl

end GasVapor

end

end Ipho2026Gpt56solBlind.Shared
