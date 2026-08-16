import Mathlib.Data.Real.Basic
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
import Ipho2026Gpt56solBlind.Shared.FiniteDataAndAffineFit
import Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

/-!
# IPhO 2026 problem 4, part C.7

Answer-blind reconstruction of the raw adjacent-temperature graph, its
unweighted ordinary-least-squares fit, the inner-water heat capacity and
effective wall resistance, followed by the radial Fourier-law
characterization of acrylic thermal conductivity.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_7

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
open Ipho2026Gpt56solBlind.Shared.AffineFit
open Ipho2026Gpt56solBlind.Shared.RadialConductionCore
open Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

noncomputable section

/-! ## Raw adjacent temperature-rate graph -/

/--
The ordered C.5 graph before fitting: adjacent average outer-minus-inner
temperature difference against the inner-temperature forward rate.  The two
coordinates use the same interval, and no heat capacity is applied here.
-/
def rawAdjacentRateGraph {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) :
    Fin m → ℝ × ℝ :=
  fun index ↦
    (siValue
        (adjacentAverageTemperatureDifference observations valid index),
      siValue (adjacentInnerTemperatureRate observations valid index))

/-- Nonempty affine data containing the ordered raw adjacent-rate graph. -/
def rawAdjacentRateData {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) : AffineData m :=
  AffineData.ofGraph valid.1 (rawAdjacentRateGraph observations valid)

/-- The displayed raw coordinate families determine exactly one affine data set. -/
theorem existsUnique_rawAdjacentRateData {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) :
    ∃! data : AffineData m,
      (∀ index,
        data.predictor index =
          (rawAdjacentRateGraph observations valid index).1) ∧
      (∀ index,
        data.response index =
          (rawAdjacentRateGraph observations valid index).2) := by
  refine ⟨rawAdjacentRateData observations valid, ?_, ?_⟩
  · constructor <;> intro index <;>
      rfl
  · intro data hData
    apply AffineData.ext_coordinates
    · intro index
      exact hData.1 index
    · intro index
      exact hData.2 index

/-! ## Answer-free experimental input -/

/--
Prepared Figure 17 Part-C observations and the two primitive empirical facts
needed to infer a positive raw OLS slope.  No fitted coefficient, geometry
witness, heat capacity, resistance or conductivity is stored in the input.
-/
structure AcrylicConductivityExperiment (m : ℕ) where
  run : Figure17PartCRadialRun (m + 1)
  prepared : PreparedFigure17PartCRadialRun run
  observations : RadialObservationSeries (m + 1)
  observations_run : observations.run = run
  validGaps : ValidRadialSuccessiveTimeGaps observations
  waterMassDensity_si : siValue run.apparatus.waterMassDensity = 1000
  waterSpecificHeatCapacity_si :
    siValue run.apparatus.waterSpecificHeatCapacity = 4.184 * 10 ^ 3
  predictor_distinct :
    ∃ i j : Fin m,
      (rawAdjacentRateData observations validGaps).predictor i ≠
        (rawAdjacentRateData observations validGaps).predictor j
  centeredCrossSum_pos :
    0 < centeredPredictorResponseSum
      (rawAdjacentRateData observations validGaps)

/-- Primitive predictor nonconstancy makes the raw predictor nondegenerate. -/
lemma rawPredictor_nondegenerate {m : ℕ}
    (experiment : AcrylicConductivityExperiment m) :
    NondegeneratePredictor
      (rawAdjacentRateData experiment.observations experiment.validGaps) := by
  exact
    (nondegeneratePredictor_iff_exists_ne
      (rawAdjacentRateData experiment.observations experiment.validGaps)).2
      experiment.predictor_distinct

/-! ## Explicit unweighted ordinary least squares -/

/--
An affine fit with an intercept satisfying both unweighted normal equations
and the global residual-sum-of-squares minimum condition.
-/
def RawOLSFit {m : ℕ} (data : AffineData m)
    (intercept slope : ℝ) : Prop :=
  AffineNormalEquations data intercept slope ∧
    IsLeastResidual data intercept slope

/-- The data-only positive cross-sum forces every raw OLS slope to be positive. -/
lemma rawOLSFit_slope_pos {m : ℕ}
    (experiment : AcrylicConductivityExperiment m)
    {intercept slope : ℝ}
    (fit : RawOLSFit
      (rawAdjacentRateData experiment.observations experiment.validGaps)
      intercept slope) :
    0 < slope ∧ slope ≠ 0 := by
  let data :=
    rawAdjacentRateData experiment.observations experiment.validGaps
  have hNondegenerate : NondegeneratePredictor data :=
    rawPredictor_nondegenerate experiment
  have hCentered :=
    (normalEquations_iff_centered data intercept slope).1 fit.1
  have hProduct :
      0 < slope * centeredPredictorSumSquares data := by
    rw [hCentered.2]
    exact experiment.centeredCrossSum_pos
  have hSlopePos : 0 < slope := by
    rcases (mul_pos_iff.mp hProduct) with hPositive | hNegative
    · exact hPositive.1
    · exact (False.elim ((not_lt_of_ge (le_of_lt hNondegenerate)) hNegative.2))
  exact ⟨hSlopePos, ne_of_gt hSlopePos⟩

/-- Every prepared experiment determines one positive raw OLS coefficient pair. -/
theorem existsUnique_positiveRawOLSFit {m : ℕ}
    (experiment : AcrylicConductivityExperiment m) :
    ∃! pair : ℝ × ℝ,
      RawOLSFit
          (rawAdjacentRateData experiment.observations experiment.validGaps)
          pair.1 pair.2 ∧
        0 < pair.2 := by
  let data :=
    rawAdjacentRateData experiment.observations experiment.validGaps
  have hNondegenerate : NondegeneratePredictor data :=
    rawPredictor_nondegenerate experiment
  rcases existsUnique_isAffineFit data hNondegenerate with
    ⟨pair, hFit, hUnique⟩
  have hLeast : IsLeastResidual data pair.1 pair.2 :=
    (isAffineFit_iff_isLeastResidual data hNondegenerate pair.1 pair.2).1 hFit
  have hRawFit : RawOLSFit data pair.1 pair.2 := ⟨hFit, hLeast⟩
  refine ⟨pair, ⟨hRawFit, (rawOLSFit_slope_pos experiment hRawFit).1⟩, ?_⟩
  intro other hOther
  exact hUnique other hOther.1.1

/-! ## Figure 17 geometry, water capacity and effective resistance -/

/-- The prepared apparatus determines its wall and inner-water geometry uniquely. -/
theorem existsUnique_figure17Geometry {m : ℕ}
    (experiment : AcrylicConductivityExperiment m) :
    ∃! pair : CylindricalWall × InnerWaterGeometry,
      Figure17PartCGeometryBridge experiment.run.apparatus pair.1 pair.2 := by
  exact
    existsUnique_figure17PartCGeometryBridge experiment.run.apparatus
      experiment.run.procedure experiment.prepared

/--
The bridged inner-water heat capacity has the cylindrical-volume formula and
is strictly positive in coherent SI.
-/
lemma bridgedInnerWaterHeatCapacity_pos {m : ℕ}
    (experiment : AcrylicConductivityExperiment m)
    {wall : CylindricalWall} {geometry : InnerWaterGeometry}
    (bridge :
      Figure17PartCGeometryBridge experiment.run.apparatus wall geometry) :
    siValue (innerWaterHeatCapacity geometry) =
        siValue geometry.waterMassDensity * Real.pi *
          siValue wall.innerRadius ^ 2 *
          siValue geometry.innerWaterHeight *
          siValue geometry.waterSpecificHeatCapacity ∧
      0 < siValue (innerWaterHeatCapacity geometry) := by
  constructor
  · have hWall : geometry.wall = wall := bridge.2.2.2.2.1
    simp only [innerWaterHeatCapacity, innerWaterMass, innerWaterVolume,
      siValue, coordinateInSI_self]
    rw [hWall]
    ring
  · exact (innerWaterHeatCapacity_pos geometry).2.2

/--
A positive typed wall resistance is characterized from a positive raw OLS
slope only after rescaling the rate slope by the derived water heat capacity.
-/
def RawSlopeResistanceCharacterization {m : ℕ}
    (experiment : AcrylicConductivityExperiment m)
    (geometry : InnerWaterGeometry) (resistance : ThermalResistance) : Prop :=
  0 < siValue resistance ∧
    ∃ intercept slope : ℝ,
      RawOLSFit
          (rawAdjacentRateData experiment.observations experiment.validGaps)
          intercept slope ∧
        0 < slope ∧
        siValue (innerWaterHeatCapacity geometry) * slope *
            siValue resistance = 1

/-- A resistance solution is tied to the uniquely bridged Figure 17 geometry. -/
def EffectiveWallResistanceSolution {m : ℕ}
    (experiment : AcrylicConductivityExperiment m)
    (resistance : ThermalResistance) : Prop :=
  ∃ wall : CylindricalWall, ∃ geometry : InnerWaterGeometry,
    Figure17PartCGeometryBridge experiment.run.apparatus wall geometry ∧
      RawSlopeResistanceCharacterization experiment geometry resistance

/-- The raw observations and prepared apparatus determine one effective resistance. -/
theorem existsUnique_effectiveWallResistance {m : ℕ}
    (experiment : AcrylicConductivityExperiment m) :
    ∃! resistance : ThermalResistance,
      EffectiveWallResistanceSolution experiment resistance := by
  rcases existsUnique_figure17Geometry experiment with
    ⟨geometryPair, hBridge, hBridgeUnique⟩
  rcases existsUnique_positiveRawOLSFit experiment with
    ⟨coefficientPair, hFit, hFitUnique⟩
  have hCapacityPos :
      0 < siValue (innerWaterHeatCapacity geometryPair.2) :=
    (bridgedInnerWaterHeatCapacity_pos experiment hBridge).2
  have hCoefficientPos :
      0 < siValue (innerWaterHeatCapacity geometryPair.2) * coefficientPair.2 :=
    mul_pos hCapacityPos hFit.2
  let resistance : ThermalResistance :=
    ⟨1 / (siValue (innerWaterHeatCapacity geometryPair.2) *
      coefficientPair.2)⟩
  have hResistancePos : 0 < siValue resistance := by
    simpa only [resistance, siValue, coordinateInSI_self] using
      one_div_pos.mpr hCoefficientPos
  have hProduct :
      siValue (innerWaterHeatCapacity geometryPair.2) * coefficientPair.2 *
          siValue resistance = 1 := by
    simp only [resistance, siValue, coordinateInSI_self, one_div]
    exact mul_inv_cancel₀ (by
      simpa only [siValue, coordinateInSI_self] using
        ne_of_gt hCoefficientPos)
  have hCharacterization :
      RawSlopeResistanceCharacterization experiment geometryPair.2
        resistance :=
    ⟨hResistancePos, coefficientPair.1, coefficientPair.2,
      hFit.1, hFit.2, hProduct⟩
  refine
    ⟨resistance,
      ⟨geometryPair.1, geometryPair.2, hBridge, hCharacterization⟩, ?_⟩
  intro other hOther
  rcases hOther with
    ⟨otherWall, otherGeometry, hOtherBridge, hOtherCharacterization⟩
  rcases hOtherCharacterization.2 with
    ⟨otherIntercept, otherSlope, hOtherFit, hOtherSlopePos,
      hOtherProduct⟩
  have hGeometryPair :
      (otherWall, otherGeometry) = geometryPair :=
    hBridgeUnique (otherWall, otherGeometry) hOtherBridge
  have hGeometry : otherGeometry = geometryPair.2 :=
    congrArg Prod.snd hGeometryPair
  have hCoefficientPair :
      (otherIntercept, otherSlope) = coefficientPair :=
    hFitUnique (otherIntercept, otherSlope) ⟨hOtherFit, hOtherSlopePos⟩
  have hSlope : otherSlope = coefficientPair.2 :=
    congrArg Prod.snd hCoefficientPair
  apply
    (coordinateInSI_eq_iff SIUnitChoices.SI other resistance).mp
  change siValue other = siValue resistance
  apply mul_left_cancel₀ (ne_of_gt hCoefficientPos)
  calc
    (siValue (innerWaterHeatCapacity geometryPair.2) * coefficientPair.2) *
          siValue other =
        siValue (innerWaterHeatCapacity otherGeometry) * otherSlope *
          siValue other := by rw [hGeometry, hSlope]
    _ = 1 := hOtherProduct
    _ = (siValue (innerWaterHeatCapacity geometryPair.2) * coefficientPair.2) *
          siValue resistance := hProduct.symm

/-! ## Radial Fourier law and acrylic conductivity -/

/--
A conductivity solution couples the reconstructed raw-slope resistance to the
integrated, outward-oriented cylindrical Fourier-law characterization.
-/
def AcrylicConductivitySolution {m : ℕ}
    (experiment : AcrylicConductivityExperiment m)
    (conductivity : ThermalConductivity) : Prop :=
  ∃ wall : CylindricalWall, ∃ geometry : InnerWaterGeometry,
    ∃ resistance : ThermalResistance,
      Figure17PartCGeometryBridge experiment.run.apparatus wall geometry ∧
        RawSlopeResistanceCharacterization experiment geometry resistance ∧
        ConductivityCharacterization wall resistance conductivity

/-- Every answer-free experiment determines a unique positive acrylic conductivity. -/
theorem existsUnique_acrylicThermalConductivity {m : ℕ}
    (experiment : AcrylicConductivityExperiment m) :
    ∃! conductivity : ThermalConductivity,
      AcrylicConductivitySolution experiment conductivity := by
  rcases existsUnique_effectiveWallResistance experiment with
    ⟨resistance, hResistanceSolution, hResistanceUnique⟩
  rcases hResistanceSolution with
    ⟨wall, geometry, hBridge, hResistanceCharacterization⟩
  rcases existsUnique_conductivityCharacterization wall resistance
      hResistanceCharacterization.1 with
    ⟨conductivity, hConductivity, hConductivityUnique⟩
  refine
    ⟨conductivity,
      ⟨wall, geometry, resistance, hBridge,
        hResistanceCharacterization, hConductivity⟩, ?_⟩
  intro other hOther
  rcases hOther with
    ⟨otherWall, otherGeometry, otherResistance, hOtherBridge,
      hOtherResistanceCharacterization, hOtherConductivity⟩
  have hResistance : otherResistance = resistance :=
    hResistanceUnique otherResistance
      ⟨otherWall, otherGeometry, hOtherBridge,
        hOtherResistanceCharacterization⟩
  rcases existsUnique_figure17Geometry experiment with
    ⟨geometryPair, hGeometryBridge, hGeometryUnique⟩
  have hWallGeometry :
      (otherWall, otherGeometry) = (wall, geometry) :=
    (hGeometryUnique (otherWall, otherGeometry) hOtherBridge).trans
      (hGeometryUnique (wall, geometry) hBridge).symm
  have hWall : otherWall = wall := congrArg Prod.fst hWallGeometry
  apply hConductivityUnique other
  simpa only [hWall, hResistance] using hOtherConductivity

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_7
