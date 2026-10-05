import Mathlib.Algebra.BigOperators.Field
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.FiniteDataAndAffineFit
import Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

/-!
# IPhO 2026 Problem 4, part C.6

This module keeps the graph from C.5 as the raw inner-temperature-rate graph.
It specifies unweighted affine ordinary least squares on that indexed graph,
then couples the fitted raw slope to the full typed inner-water heat capacity
and a genuinely quantified thermal resistance.

No fitted coefficient or resistance is stored in the observations or supplied
as a premise.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_6

open scoped BigOperators

open Ipho2026Gpt56solBlind.Shared
open Ipho2026Gpt56solBlind.Shared.AffineFit
open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.RadialConductionCore
open Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

noncomputable section

/-! ## The raw adjacent graph from C.5 -/

/--
The ordered C.5 graph.  Each retained index uses one common adjacent interval:
the predictor is the endpoint-average of `T_OC - T_IC`, and the response is the
raw forward inner-temperature rate.  Both are coherent-SI scalar coordinates.
-/
def rawC5Graph {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) :
    Fin m → ℝ × ℝ :=
  fun index ↦
    (siValue (adjacentAverageTemperatureDifference observations valid index),
      siValue (adjacentInnerTemperatureRate observations valid index))

/--
The nonempty ordered affine data extracted from the raw C.5 graph.  The
response is still a temperature rate; no capacity scaling or fit is performed.
-/
def rawC5AffineData {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) : AffineData m :=
  AffineData.ofGraph valid.1 (rawC5Graph observations valid)

/-- Fixed prepared provenance and valid gaps determine exactly the raw data. -/
theorem existsUnique_rawC5AffineData {m : ℕ}
    (run : Figure17PartCRadialRun (m + 1))
    (observations : RadialObservationSeries (m + 1))
    (hPrepared : PreparedFigure17PartCRadialRun run)
    (hRun : observations.run = run)
    (valid : ValidRadialSuccessiveTimeGaps observations) :
    ∃! data : AffineData m,
      (∀ index,
        data.predictor index = (rawC5Graph observations valid index).1) ∧
      ∀ index,
        data.response index = (rawC5Graph observations valid index).2 := by
  let canonical := rawC5AffineData observations valid
  refine ⟨canonical, ?_, ?_⟩
  · constructor <;> intro index <;> rfl
  · intro data hData
    apply AffineData.ext_coordinates
    · intro index
      exact hData.1 index
    · intro index
      exact hData.2 index

/--
Multiplying only the raw response by the full inner-water heat capacity gives
the Shared heat-rate graph at the same retained occurrence.  This is not a
second fit and does not replace the raw data fitted below.
-/
lemma heatRateFitGraph_eq_capacityScaledRawC5Graph {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (geometry : InnerWaterGeometry) (index : Fin m) :
    heatRateFitGraph observations valid geometry index =
      ((rawC5Graph observations valid index).1,
        siValue (innerWaterHeatCapacity geometry) *
          (rawC5Graph observations valid index).2) := by
  apply Prod.ext
  · rfl
  · exact coordinateInSI_self _

/-! ## Explicit unweighted affine OLS on the raw graph -/

/-- Arithmetic mean of all raw predictor occurrences. -/
def rawC5PredictorMean {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) : ℝ :=
  predictorMean (rawC5AffineData observations valid)

/-- Arithmetic mean of all raw response occurrences. -/
def rawC5ResponseMean {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) : ℝ :=
  responseMean (rawC5AffineData observations valid)

/-- The centered raw predictor sum of squares `S_xx`. -/
def rawC5Sxx {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) : ℝ :=
  centeredPredictorSumSquares (rawC5AffineData observations valid)

/-- The centered raw predictor-response cross-sum `S_xy`. -/
def rawC5Sxy {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) : ℝ :=
  centeredPredictorResponseSum (rawC5AffineData observations valid)

/--
Primitive data-only predictor nonconstancy: two retained predictor occurrences
have distinct coherent-SI coordinates.
-/
def RawC5PredictorNonconstant {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) : Prop :=
  ∃ i j : Fin m,
    (rawC5Graph observations valid i).1 ≠
      (rawC5Graph observations valid j).1

/--
The data-only domain in which the unique fitted raw slope will be positive.
It contains no fitted coefficient and no resistance.
-/
def RawC5PositiveSlopeDomain {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) : Prop :=
  RawC5PredictorNonconstant observations valid ∧
    0 < rawC5Sxy observations valid

/-- Primitive raw predictor nonconstancy is exactly positivity of `S_xx`. -/
lemma rawC5PredictorNonconstant_iff_sxx_pos {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations) :
    RawC5PredictorNonconstant observations valid ↔
      0 < rawC5Sxx observations valid := by
  exact
    (nondegeneratePredictor_iff_exists_ne
      (rawC5AffineData observations valid)).symm

/-- Residual of an affine intercept-slope candidate at one raw occurrence. -/
def rawC5Residual {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (intercept slope : ℝ) (index : Fin m) : ℝ :=
  residual (rawC5AffineData observations valid) intercept slope index

/-- Unweighted sum of squared residuals over every indexed occurrence. -/
def rawC5RSS {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (intercept slope : ℝ) : ℝ :=
  residualSumSquares (rawC5AffineData observations valid) intercept slope

/-- Both explicit affine normal equations for the raw C.5 data. -/
def RawC5NormalEquations {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (intercept slope : ℝ) : Prop :=
  AffineNormalEquations (rawC5AffineData observations valid) intercept slope

/-- A candidate has globally least raw unweighted RSS. -/
def RawC5LeastRSS {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (intercept slope : ℝ) : Prop :=
  IsLeastResidual (rawC5AffineData observations valid) intercept slope

/-- The raw normal equations are equivalent to their centered two-equation form. -/
lemma rawC5NormalEquations_iff_centered {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (intercept slope : ℝ) :
    RawC5NormalEquations observations valid intercept slope ↔
      intercept + slope * rawC5PredictorMean observations valid =
          rawC5ResponseMean observations valid ∧
        slope * rawC5Sxx observations valid =
          rawC5Sxy observations valid := by
  exact
    normalEquations_iff_centered
      (rawC5AffineData observations valid) intercept slope

/-- Under primitive nonconstancy, the normal equations are exactly global OLS. -/
theorem rawC5NormalEquations_iff_leastRSS {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (hNonconstant : RawC5PredictorNonconstant observations valid)
    (intercept slope : ℝ) :
    RawC5NormalEquations observations valid intercept slope ↔
      RawC5LeastRSS observations valid intercept slope := by
  have hSxx : 0 < rawC5Sxx observations valid :=
    (rawC5PredictorNonconstant_iff_sxx_pos observations valid).1 hNonconstant
  have hNondegenerate :
      NondegeneratePredictor (rawC5AffineData observations valid) := by
    exact hSxx
  exact
    isAffineFit_iff_isLeastResidual
      (rawC5AffineData observations valid) hNondegenerate intercept slope

/-- Primitive predictor nonconstancy determines one raw OLS intercept-slope pair. -/
theorem existsUnique_rawC5OLSFit {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (hNonconstant : RawC5PredictorNonconstant observations valid) :
    ∃! fit : ℝ × ℝ,
      RawC5NormalEquations observations valid fit.1 fit.2 := by
  have hSxx : 0 < rawC5Sxx observations valid :=
    (rawC5PredictorNonconstant_iff_sxx_pos observations valid).1 hNonconstant
  have hNondegenerate :
      NondegeneratePredictor (rawC5AffineData observations valid) := by
    exact hSxx
  exact
    existsUnique_isAffineFit
      (rawC5AffineData observations valid) hNondegenerate

/--
In the data-only positive-slope domain, the unique OLS slope is the displayed
data statistic ratio and is strictly positive.
-/
theorem existsUnique_positiveSlopeRawC5OLSFit {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (hDomain : RawC5PositiveSlopeDomain observations valid) :
    ∃! fit : ℝ × ℝ,
      RawC5NormalEquations observations valid fit.1 fit.2 ∧
        fit.2 = rawC5Sxy observations valid / rawC5Sxx observations valid ∧
        0 < fit.2 := by
  rcases hDomain with ⟨hNonconstant, hSxy⟩
  have hSxx : 0 < rawC5Sxx observations valid :=
    (rawC5PredictorNonconstant_iff_sxx_pos observations valid).1 hNonconstant
  rcases existsUnique_rawC5OLSFit observations valid hNonconstant with
    ⟨fit, hFit, hFitUnique⟩
  have hSlopeEquation :
      fit.2 * rawC5Sxx observations valid = rawC5Sxy observations valid :=
    ((rawC5NormalEquations_iff_centered observations valid fit.1 fit.2).1
      hFit).2
  have hSlopeFormula :
      fit.2 = rawC5Sxy observations valid / rawC5Sxx observations valid :=
    (eq_div_iff (ne_of_gt hSxx)).2 hSlopeEquation
  have hSlopePositive : 0 < fit.2 := by
    rw [hSlopeFormula]
    exact div_pos hSxy hSxx
  refine ⟨fit, ⟨hFit, hSlopeFormula, hSlopePositive⟩, ?_⟩
  intro other hOther
  exact hFitUnique other hOther.1

/-! ## Typed water capacity and the C.6 resistance -/

/-- The two supplied Part-C water reference coordinates. -/
def C6UsesStatedWaterData (apparatus : Figure17PartCApparatusData) : Prop :=
  siValue apparatus.waterMassDensity = 1000 ∧
    siValue apparatus.waterSpecificHeatCapacity = 4.184 * 10 ^ 3

/--
The coefficient equation obtained by combining the full inner-water balance
with the effective-resistance law from Equation (4).  The fitted raw slope is
a coherent-SI inverse-time scalar; the capacity and resistance remain typed.
-/
def C6PhysicalCoefficientRelation (geometry : InnerWaterGeometry)
    (rawSlope : ℝ) (resistance : ThermalResistance) : Prop :=
  siValue (innerWaterHeatCapacity geometry) * rawSlope *
      siValue resistance = 1

/--
A positive C.6 resistance solution is coupled to the run's Figure 17 geometry,
the supplied water material values, the concrete global raw OLS fit, and the
physical coefficient equation.  The resistance is not defined by a stored
number or reciprocal formula.
-/
def C6ResistanceSolution {m : ℕ}
    (run : Figure17PartCRadialRun (m + 1))
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (resistance : ThermalResistance) : Prop :=
  ∃ wall : CylindricalWall,
    ∃ geometry : InnerWaterGeometry,
      ∃ fit : ℝ × ℝ,
        C6UsesStatedWaterData run.apparatus ∧
          Figure17PartCGeometryBridge run.apparatus wall geometry ∧
          0 < siValue resistance ∧
          RawC5NormalEquations observations valid fit.1 fit.2 ∧
          RawC5LeastRSS observations valid fit.1 fit.2 ∧
          0 < fit.2 ∧
          C6PhysicalCoefficientRelation geometry fit.2 resistance

/--
A prepared named Part-C run with raw data in the positive-slope domain
determines exactly one positive typed effective thermal resistance.
-/
theorem existsUnique_c6ThermalResistance {m : ℕ}
    (run : Figure17PartCRadialRun (m + 1))
    (observations : RadialObservationSeries (m + 1))
    (hPrepared : PreparedFigure17PartCRadialRun run)
    (hRun : observations.run = run)
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (hWaterData : C6UsesStatedWaterData run.apparatus)
    (hDomain : RawC5PositiveSlopeDomain observations valid) :
    ∃! resistance : ThermalResistance,
      C6ResistanceSolution run observations valid resistance := by
  rcases
      existsUnique_figure17PartCGeometryBridge run.apparatus run.procedure
        hPrepared with
    ⟨bridgePair, hBridge, hBridgeUnique⟩
  rcases
      existsUnique_rawC5OLSFit observations valid hDomain.1 with
    ⟨fit, hFit, hFitUnique⟩
  have hSxx : 0 < rawC5Sxx observations valid :=
    (rawC5PredictorNonconstant_iff_sxx_pos observations valid).1 hDomain.1
  have hSlopeEquation :
      fit.2 * rawC5Sxx observations valid = rawC5Sxy observations valid :=
    ((rawC5NormalEquations_iff_centered observations valid fit.1 fit.2).1
      hFit).2
  have hSlopeFormula :
      fit.2 = rawC5Sxy observations valid / rawC5Sxx observations valid :=
    (eq_div_iff (ne_of_gt hSxx)).2 hSlopeEquation
  have hSlopePositive : 0 < fit.2 := by
    rw [hSlopeFormula]
    exact div_pos hDomain.2 hSxx
  have hLeast : RawC5LeastRSS observations valid fit.1 fit.2 :=
    (rawC5NormalEquations_iff_leastRSS observations valid hDomain.1
      fit.1 fit.2).1 hFit
  have hCapacityPositive :
      0 < siValue (innerWaterHeatCapacity bridgePair.2) :=
    (innerWaterHeatCapacity_pos bridgePair.2).2.2
  have hFactorPositive :
      0 < siValue (innerWaterHeatCapacity bridgePair.2) * fit.2 :=
    mul_pos hCapacityPositive hSlopePositive
  let resistance : ThermalResistance :=
    ⟨1 / (siValue (innerWaterHeatCapacity bridgePair.2) * fit.2)⟩
  have hResistanceCoordinate :
      siValue resistance =
        1 / (siValue (innerWaterHeatCapacity bridgePair.2) * fit.2) := by
    simp only [resistance, siValue, coordinateInSI_self]
  have hResistancePositive : 0 < siValue resistance := by
    rw [hResistanceCoordinate]
    exact one_div_pos.mpr hFactorPositive
  have hCoefficient :
      C6PhysicalCoefficientRelation bridgePair.2 fit.2 resistance := by
    unfold C6PhysicalCoefficientRelation
    rw [hResistanceCoordinate]
    field_simp [ne_of_gt hFactorPositive]
  refine ⟨resistance, ?_, ?_⟩
  · refine ⟨bridgePair.1, bridgePair.2, fit, ?_⟩
    exact
      ⟨hWaterData, hBridge, hResistancePositive, hFit, hLeast,
        hSlopePositive, hCoefficient⟩
  · intro other hOther
    rcases hOther with
      ⟨otherWall, otherGeometry, otherFit, _hOtherWater, hOtherBridge,
        _hOtherResistancePositive, hOtherFit, _hOtherLeast,
        _hOtherSlopePositive, hOtherCoefficient⟩
    have hBridgeEquality :
        (otherWall, otherGeometry) = bridgePair :=
      hBridgeUnique (otherWall, otherGeometry) hOtherBridge
    have hGeometryEquality : otherGeometry = bridgePair.2 :=
      congrArg Prod.snd hBridgeEquality
    have hFitEquality : otherFit = fit :=
      hFitUnique otherFit hOtherFit
    subst otherGeometry
    subst otherFit
    unfold C6PhysicalCoefficientRelation at hOtherCoefficient hCoefficient
    have hCoordinateEquality : siValue other = siValue resistance := by
      exact
        (mul_right_inj' (ne_of_gt hFactorPositive)).mp
          (hOtherCoefficient.trans hCoefficient.symm)
    exact
      (coordinateInSI_eq_iff SIUnitChoices.SI other resistance).mp
        hCoordinateEquality

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_6
