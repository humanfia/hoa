import Mathlib.Data.Real.Basic
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

/-!
# IPhO 2026 Problem 4, Part C.4

This file gives an answer-blind model of the equilibrium-temperature inference
from the two Part C.3 temperature-difference traces.  The observations retain
their occurrence indices, the two graph traces are reconstructed from the same
samples, and their affine laws are selected by an explicit unweighted OLS
protocol.  The requested equilibrium temperature remains a quantified,
dimensioned output.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_4

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.FiniteObservations
open Ipho2026Gpt56solBlind.Shared.ExactGraph
open Ipho2026Gpt56solBlind.Shared.AffineFit
open Ipho2026Gpt56solBlind.Shared.RadialConductionCore
open Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

noncomputable section

/-- The prepared Part-C record, its Figure 17 wall/inner-water geometry, and
the capacity accounting used for the C.3--C.4 idealization. -/
structure C4SourceData (q : ℕ) where
  observations : RadialObservationSeries q
  wall : CylindricalWall
  innerWaterGeometry : InnerWaterGeometry
  capacityContext : CapacityContext
  preparedRun : PreparedFigure17PartCRadialRun observations.run
  geometryBridge :
    Figure17PartCGeometryBridge observations.run.apparatus wall innerWaterGeometry
  capacityGeometry : capacityContext.innerWaterGeometry = innerWaterGeometry

/-- The coherent-SI outer-minus-inner temperature difference at one recorded
occurrence. -/
def temperatureDifferenceCoordinate (sample : TemperatureSample) : ℝ :=
  siValue sample.outerTemperature - siValue sample.innerTemperature

/-- The C.3 trace with outer temperature as predictor. -/
def outerDifferenceTrace {q : ℕ} (D : C4SourceData q) :
    IndexedSeries q (ℝ × ℝ) :=
  canonicalPairedMap D.observations
    (fun sample ↦ siValue sample.outerTemperature)
    temperatureDifferenceCoordinate

/-- The C.3 trace with inner temperature as predictor.  It uses the same
observation occurrences, order, and multiplicity as `outerDifferenceTrace`. -/
def innerDifferenceTrace {q : ℕ} (D : C4SourceData q) :
    IndexedSeries q (ℝ × ℝ) :=
  canonicalPairedMap D.observations
    (fun sample ↦ siValue sample.innerTemperature)
    temperatureDifferenceCoordinate

/-- The two occurrence-wise C.3 coordinate prescriptions determine exactly
one ordered pair of traces. -/
theorem existsUnique_exactC3Traces {q : ℕ} (D : C4SourceData q) :
    ∃! traces :
        IndexedSeries q (ℝ × ℝ) × IndexedSeries q (ℝ × ℝ),
      ExactGraph D.observations
          (fun sample ↦ siValue sample.outerTemperature)
          temperatureDifferenceCoordinate traces.1 ∧
        ExactGraph D.observations
          (fun sample ↦ siValue sample.innerTemperature)
          temperatureDifferenceCoordinate traces.2 := by
  refine ⟨(outerDifferenceTrace D, innerDifferenceTrace D), ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · intro traces hTraces
    apply Prod.ext
    · exact hTraces.1
    · exact hTraces.2

/-- Nonempty affine data extracted without sorting or deduplicating the outer
temperature trace. -/
def outerTraceAffineData {q : ℕ} (D : C4SourceData q) : AffineData q :=
  AffineData.ofGraph D.observations.nonempty (outerDifferenceTrace D)

/-- Nonempty affine data extracted without sorting or deduplicating the inner
temperature trace. -/
def innerTraceAffineData {q : ℕ} (D : C4SourceData q) : AffineData q :=
  AffineData.ofGraph D.observations.nonempty (innerDifferenceTrace D)

/-- Primitive, data-only predictor variation for both reconstructed traces. -/
def PrimitiveTraceNondegeneracy {q : ℕ} (D : C4SourceData q) : Prop :=
  (∃ i j : Fin q,
      siValue (D.observations.samples i).outerTemperature ≠
        siValue (D.observations.samples j).outerTemperature) ∧
    ∃ k l : Fin q,
      siValue (D.observations.samples k).innerTemperature ≠
        siValue (D.observations.samples l).innerTemperature

/-- Primitive occurrence-wise variation gives positive centered predictor sum
of squares for both affine data sets. -/
lemma primitiveTraceNondegeneracy_implies_nondegenerate {q : ℕ}
    (D : C4SourceData q) (hVariation : PrimitiveTraceNondegeneracy D) :
    NondegeneratePredictor (outerTraceAffineData D) ∧
      NondegeneratePredictor (innerTraceAffineData D) := by
  constructor
  · apply
      (nondegeneratePredictor_iff_exists_ne
        (outerTraceAffineData D)).2
    exact hVariation.1
  · apply
      (nondegeneratePredictor_iff_exists_ne
        (innerTraceAffineData D)).2
    exact hVariation.2

/-- Explicit unweighted ordinary-least-squares coefficients `(intercept,
slope)` for nonempty affine data.  Each indexed occurrence has weight one. -/
def unweightedOLSCoefficients {q : ℕ} (data : AffineData q) : ℝ × ℝ :=
  let slope :=
    centeredPredictorResponseSum data / centeredPredictorSumSquares data
  (responseMean data - slope * predictorMean data, slope)

/-- Under predictor nondegeneracy, the displayed coefficients satisfy the two
unweighted normal equations and every other solution is the same pair. -/
theorem unweightedOLSCoefficients_unique {q : ℕ} (data : AffineData q)
    (hNondegenerate : NondegeneratePredictor data) :
    IsAffineFit data (unweightedOLSCoefficients data).1
        (unweightedOLSCoefficients data).2 ∧
      ∀ pair : ℝ × ℝ,
        IsAffineFit data pair.1 pair.2 →
          pair = unweightedOLSCoefficients data := by
  have hSquaresNe : centeredPredictorSumSquares data ≠ 0 :=
    ne_of_gt hNondegenerate
  have hFit :
      IsAffineFit data (unweightedOLSCoefficients data).1
        (unweightedOLSCoefficients data).2 := by
    change
      AffineNormalEquations data (unweightedOLSCoefficients data).1
        (unweightedOLSCoefficients data).2
    apply
      (normalEquations_iff_centered data
        (unweightedOLSCoefficients data).1
        (unweightedOLSCoefficients data).2).2
    constructor
    · change
        responseMean data -
              centeredPredictorResponseSum data /
                  centeredPredictorSumSquares data * predictorMean data +
            centeredPredictorResponseSum data /
                centeredPredictorSumSquares data * predictorMean data =
          responseMean data
      ring
    · change
        centeredPredictorResponseSum data /
              centeredPredictorSumSquares data *
            centeredPredictorSumSquares data =
          centeredPredictorResponseSum data
      exact div_mul_cancel₀ _ hSquaresNe
  refine ⟨hFit, ?_⟩
  intro pair hPair
  rcases existsUnique_isAffineFit data hNondegenerate with
    ⟨fit, hFitExists, hFitUnique⟩
  exact
    (hFitUnique pair hPair).trans
      (hFitUnique (unweightedOLSCoefficients data) hFit).symm

/-- In the no-environment two-water model, the sampled total water energy is
the same at every pair of recorded occurrences. -/
def SampledWaterEnergyConservation {q : ℕ} (D : C4SourceData q) : Prop :=
  let innerCapacity :=
    siValue (innerWaterHeatCapacity D.capacityContext.innerWaterGeometry)
  let outerCapacity := siValue D.capacityContext.outerWaterHeatCapacity
  ∀ r s : Fin q,
    innerCapacity * siValue (D.observations.samples r).innerTemperature +
          outerCapacity * siValue (D.observations.samples r).outerTemperature =
      innerCapacity * siValue (D.observations.samples s).innerTemperature +
        outerCapacity * siValue (D.observations.samples s).outerTemperature

/-- The C.4 governing assumptions: only the separately named modeled
apparatus capacity is ignored, sampled two-water energy is conserved, and the
two recorded predictors vary. -/
def C4GoverningConditions {q : ℕ} (D : C4SourceData q) : Prop :=
  C3C4ApparatusCapacityIdealization D.capacityContext ∧
    SampledWaterEnergyConservation D ∧
    PrimitiveTraceNondegeneracy D

/-- The scoped model idealization preserves positive water capacities and the
nonnegative physical apparatus capacity. -/
lemma c4GoverningConditions_capacityScope {q : ℕ} (D : C4SourceData q)
    (hGoverning : C4GoverningConditions D) :
    0 < siValue
        (innerWaterHeatCapacity D.capacityContext.innerWaterGeometry) ∧
      0 < siValue D.capacityContext.outerWaterHeatCapacity ∧
      0 ≤ siValue D.capacityContext.physicalApparatusHeatCapacity ∧
      siValue D.capacityContext.c3c4ModeledApparatusHeatCapacity = 0 := by
  exact
    c3c4Idealization_capacity_scope D.capacityContext hGoverning.1

/-- A positive, dimensioned absolute temperature. -/
structure PositiveTemperature where
  temperature : Temperature
  positive : 0 < siValue temperature

/-- A positive candidate satisfies the two-water equilibrium energy balance
when every sampled energy equals the energy at the candidate common
temperature. -/
def WaterEnergyBalance {q : ℕ} (D : C4SourceData q)
    (candidate : PositiveTemperature) : Prop :=
  let innerCapacity :=
    siValue (innerWaterHeatCapacity D.capacityContext.innerWaterGeometry)
  let outerCapacity := siValue D.capacityContext.outerWaterHeatCapacity
  ∀ i : Fin q,
    innerCapacity * siValue (D.observations.samples i).innerTemperature +
          outerCapacity * siValue (D.observations.samples i).outerTemperature =
      (innerCapacity + outerCapacity) * siValue candidate.temperature

/-- A real temperature-axis coordinate is a common zero of the two
data-derived unweighted OLS trace laws. -/
def CommonTraceZero {q : ℕ} (D : C4SourceData q) (coordinate : ℝ) : Prop :=
  let outerCoefficients :=
    unweightedOLSCoefficients (outerTraceAffineData D)
  let innerCoefficients :=
    unweightedOLSCoefficients (innerTraceAffineData D)
  outerCoefficients.1 + outerCoefficients.2 * coordinate = 0 ∧
    innerCoefficients.1 + innerCoefficients.2 * coordinate = 0

/-- Conservation and a candidate energy balance determine both fitted trace
laws. -/
theorem conservation_determines_traceOLSCoefficients {q : ℕ}
    (D : C4SourceData q) (candidate : PositiveTemperature)
    (hGoverning : C4GoverningConditions D)
    (hBalance : WaterEnergyBalance D candidate) :
    let innerCapacity :=
      siValue (innerWaterHeatCapacity D.capacityContext.innerWaterGeometry)
    let outerCapacity := siValue D.capacityContext.outerWaterHeatCapacity
    let totalCapacity := innerCapacity + outerCapacity
    let equilibriumCoordinate := siValue candidate.temperature
    unweightedOLSCoefficients (outerTraceAffineData D) =
        (-(totalCapacity * equilibriumCoordinate) / innerCapacity,
          totalCapacity / innerCapacity) ∧
      unweightedOLSCoefficients (innerTraceAffineData D) =
        (totalCapacity * equilibriumCoordinate / outerCapacity,
          -(totalCapacity / outerCapacity)) := by
  let innerCapacity : ℝ :=
    siValue (innerWaterHeatCapacity D.capacityContext.innerWaterGeometry)
  let outerCapacity : ℝ :=
    siValue D.capacityContext.outerWaterHeatCapacity
  let totalCapacity : ℝ := innerCapacity + outerCapacity
  let equilibriumCoordinate : ℝ := siValue candidate.temperature
  change
    unweightedOLSCoefficients (outerTraceAffineData D) =
        (-(totalCapacity * equilibriumCoordinate) / innerCapacity,
          totalCapacity / innerCapacity) ∧
      unweightedOLSCoefficients (innerTraceAffineData D) =
        (totalCapacity * equilibriumCoordinate / outerCapacity,
          -(totalCapacity / outerCapacity))
  have hScope := c4GoverningConditions_capacityScope D hGoverning
  have hInnerCapacityPos : 0 < innerCapacity := by
    simpa only [innerCapacity] using hScope.1
  have hOuterCapacityPos : 0 < outerCapacity := by
    simpa only [outerCapacity] using hScope.2.1
  have hInnerCapacityNe : innerCapacity ≠ 0 :=
    ne_of_gt hInnerCapacityPos
  have hOuterCapacityNe : outerCapacity ≠ 0 :=
    ne_of_gt hOuterCapacityPos
  have hNondegenerate :=
    primitiveTraceNondegeneracy_implies_nondegenerate D hGoverning.2.2
  have hBalanceAt (i : Fin q) :
      innerCapacity *
            siValue (D.observations.samples i).innerTemperature +
          outerCapacity *
            siValue (D.observations.samples i).outerTemperature =
        totalCapacity * equilibriumCoordinate := by
    exact hBalance i
  have hOuterLine :
      ∀ i : Fin q,
        (outerTraceAffineData D).response i =
          -(totalCapacity * equilibriumCoordinate) / innerCapacity +
            (totalCapacity / innerCapacity) *
              (outerTraceAffineData D).predictor i := by
    intro i
    change
      siValue (D.observations.samples i).outerTemperature -
          siValue (D.observations.samples i).innerTemperature =
        -(totalCapacity * equilibriumCoordinate) / innerCapacity +
          totalCapacity / innerCapacity *
            siValue (D.observations.samples i).outerTemperature
    field_simp [hInnerCapacityNe]
    nlinarith [hBalanceAt i]
  have hInnerLine :
      ∀ i : Fin q,
        (innerTraceAffineData D).response i =
          totalCapacity * equilibriumCoordinate / outerCapacity -
            (totalCapacity / outerCapacity) *
              (innerTraceAffineData D).predictor i := by
    intro i
    change
      siValue (D.observations.samples i).outerTemperature -
          siValue (D.observations.samples i).innerTemperature =
        totalCapacity * equilibriumCoordinate / outerCapacity -
          totalCapacity / outerCapacity *
            siValue (D.observations.samples i).innerTemperature
    field_simp [hOuterCapacityNe]
    nlinarith [hBalanceAt i]
  have hOuterFit :
      IsAffineFit (outerTraceAffineData D)
        (-(totalCapacity * equilibriumCoordinate) / innerCapacity)
        (totalCapacity / innerCapacity) := by
    unfold IsAffineFit AffineNormalEquations
    have hResidual :
        ∀ i : Fin q,
          Ipho2026Gpt56solBlind.Shared.AffineFit.residual
            (outerTraceAffineData D)
              (-(totalCapacity * equilibriumCoordinate) / innerCapacity)
              (totalCapacity / innerCapacity) i = 0 := by
      intro i
      unfold Ipho2026Gpt56solBlind.Shared.AffineFit.residual
      rw [hOuterLine i]
      ring
    constructor
    · simp only [hResidual, Finset.sum_const_zero]
    · simp only [hResidual, mul_zero, Finset.sum_const_zero]
  have hInnerFit :
      IsAffineFit (innerTraceAffineData D)
        (totalCapacity * equilibriumCoordinate / outerCapacity)
        (-(totalCapacity / outerCapacity)) := by
    unfold IsAffineFit AffineNormalEquations
    have hResidual :
        ∀ i : Fin q,
          Ipho2026Gpt56solBlind.Shared.AffineFit.residual
            (innerTraceAffineData D)
              (totalCapacity * equilibriumCoordinate / outerCapacity)
              (-(totalCapacity / outerCapacity)) i = 0 := by
      intro i
      unfold Ipho2026Gpt56solBlind.Shared.AffineFit.residual
      rw [hInnerLine i]
      ring
    constructor
    · simp only [hResidual, Finset.sum_const_zero]
    · simp only [hResidual, mul_zero, Finset.sum_const_zero]
  constructor
  · exact
      ((unweightedOLSCoefficients_unique (outerTraceAffineData D)
        hNondegenerate.1).2
          (-(totalCapacity * equilibriumCoordinate) / innerCapacity,
            totalCapacity / innerCapacity) hOuterFit).symm
  · exact
      ((unweightedOLSCoefficients_unique (innerTraceAffineData D)
        hNondegenerate.2).2
          (totalCapacity * equilibriumCoordinate / outerCapacity,
            -(totalCapacity / outerCapacity)) hInnerFit).symm

/-- The candidate coordinate is the common graph zero, and a zero of either
fitted line identifies that same coordinate. -/
theorem conservation_identifies_uniqueCommonTraceZero {q : ℕ}
    (D : C4SourceData q) (candidate : PositiveTemperature)
    (hGoverning : C4GoverningConditions D)
    (hBalance : WaterEnergyBalance D candidate) :
    let outerCoefficients :=
      unweightedOLSCoefficients (outerTraceAffineData D)
    let innerCoefficients :=
      unweightedOLSCoefficients (innerTraceAffineData D)
    let equilibriumCoordinate := siValue candidate.temperature
    CommonTraceZero D equilibriumCoordinate ∧
      ∀ coordinate : ℝ,
        (outerCoefficients.1 + outerCoefficients.2 * coordinate = 0 ∨
            innerCoefficients.1 + innerCoefficients.2 * coordinate = 0) →
          coordinate = equilibriumCoordinate := by
  let innerCapacity : ℝ :=
    siValue (innerWaterHeatCapacity D.capacityContext.innerWaterGeometry)
  let outerCapacity : ℝ :=
    siValue D.capacityContext.outerWaterHeatCapacity
  let totalCapacity : ℝ := innerCapacity + outerCapacity
  let equilibriumCoordinate : ℝ := siValue candidate.temperature
  let outerCoefficients : ℝ × ℝ :=
    unweightedOLSCoefficients (outerTraceAffineData D)
  let innerCoefficients : ℝ × ℝ :=
    unweightedOLSCoefficients (innerTraceAffineData D)
  change
    CommonTraceZero D equilibriumCoordinate ∧
      ∀ coordinate : ℝ,
        (outerCoefficients.1 + outerCoefficients.2 * coordinate = 0 ∨
            innerCoefficients.1 + innerCoefficients.2 * coordinate = 0) →
          coordinate = equilibriumCoordinate
  have hScope := c4GoverningConditions_capacityScope D hGoverning
  have hInnerCapacityPos : 0 < innerCapacity := by
    simpa only [innerCapacity] using hScope.1
  have hOuterCapacityPos : 0 < outerCapacity := by
    simpa only [outerCapacity] using hScope.2.1
  have hTotalCapacityPos : 0 < totalCapacity := by
    exact add_pos hInnerCapacityPos hOuterCapacityPos
  have hInnerCapacityNe : innerCapacity ≠ 0 :=
    ne_of_gt hInnerCapacityPos
  have hOuterCapacityNe : outerCapacity ≠ 0 :=
    ne_of_gt hOuterCapacityPos
  have hCoefficients :=
    conservation_determines_traceOLSCoefficients
      D candidate hGoverning hBalance
  change
    outerCoefficients =
        (-(totalCapacity * equilibriumCoordinate) / innerCapacity,
          totalCapacity / innerCapacity) ∧
      innerCoefficients =
        (totalCapacity * equilibriumCoordinate / outerCapacity,
          -(totalCapacity / outerCapacity)) at hCoefficients
  constructor
  · change
      outerCoefficients.1 +
            outerCoefficients.2 * equilibriumCoordinate = 0 ∧
        innerCoefficients.1 +
            innerCoefficients.2 * equilibriumCoordinate = 0
    rw [hCoefficients.1, hCoefficients.2]
    constructor
    · dsimp only
      field_simp [hInnerCapacityNe]
      ring
    · dsimp only
      field_simp [hOuterCapacityNe]
      ring
  · intro coordinate hZero
    rw [hCoefficients.1, hCoefficients.2] at hZero
    rcases hZero with hOuterZero | hInnerZero
    · dsimp only at hOuterZero
      field_simp [hInnerCapacityNe] at hOuterZero
      nlinarith
    · dsimp only at hInnerZero
      field_simp [hOuterCapacityNe] at hInnerZero
      nlinarith

/-- A C.4 solution is a positive dimensioned temperature satisfying both the
two-water balance and the explicit common-zero graph inference. -/
def EquilibriumTemperatureSolution {q : ℕ} (D : C4SourceData q)
    (candidate : PositiveTemperature) : Prop :=
  WaterEnergyBalance D candidate ∧
    CommonTraceZero D (siValue candidate.temperature)

/-- Every source datum satisfying the C.4 governing conditions has exactly
one equilibrium-temperature solution. -/
theorem existsUnique_equilibriumTemperatureSolution {q : ℕ}
    (D : C4SourceData q) (hGoverning : C4GoverningConditions D) :
    ∃! candidate : PositiveTemperature,
      EquilibriumTemperatureSolution D candidate := by
  let innerCapacity : ℝ :=
    siValue (innerWaterHeatCapacity D.capacityContext.innerWaterGeometry)
  let outerCapacity : ℝ :=
    siValue D.capacityContext.outerWaterHeatCapacity
  let totalCapacity : ℝ := innerCapacity + outerCapacity
  let referenceIndex : Fin q := ⟨0, D.observations.nonempty⟩
  let referenceEnergy : ℝ :=
    innerCapacity *
          siValue
            (D.observations.samples referenceIndex).innerTemperature +
      outerCapacity *
        siValue (D.observations.samples referenceIndex).outerTemperature
  let equilibriumCoordinate : ℝ := referenceEnergy / totalCapacity
  let equilibriumTemperature : Temperature := ⟨equilibriumCoordinate⟩
  have hScope := c4GoverningConditions_capacityScope D hGoverning
  have hInnerCapacityPos : 0 < innerCapacity := by
    simpa only [innerCapacity] using hScope.1
  have hOuterCapacityPos : 0 < outerCapacity := by
    simpa only [outerCapacity] using hScope.2.1
  have hTotalCapacityPos : 0 < totalCapacity := by
    exact add_pos hInnerCapacityPos hOuterCapacityPos
  have hTotalCapacityNe : totalCapacity ≠ 0 :=
    ne_of_gt hTotalCapacityPos
  have hReferenceEnergyPos : 0 < referenceEnergy := by
    dsimp only [referenceEnergy]
    exact
      add_pos
        (mul_pos hInnerCapacityPos
          (D.observations.samples referenceIndex).innerTemperature_pos)
        (mul_pos hOuterCapacityPos
          (D.observations.samples referenceIndex).outerTemperature_pos)
  have hEquilibriumCoordinatePos : 0 < equilibriumCoordinate := by
    exact div_pos hReferenceEnergyPos hTotalCapacityPos
  have hEquilibriumTemperatureCoordinate :
      siValue equilibriumTemperature = equilibriumCoordinate := by
    simp only [equilibriumTemperature, siValue, coordinateInSI_self]
  have hEquilibriumTemperaturePos :
      0 < siValue equilibriumTemperature := by
    rw [hEquilibriumTemperatureCoordinate]
    exact hEquilibriumCoordinatePos
  let equilibrium : PositiveTemperature :=
    ⟨equilibriumTemperature, hEquilibriumTemperaturePos⟩
  have hConservation : SampledWaterEnergyConservation D :=
    hGoverning.2.1
  have hEnergyConservation (i j : Fin q) :
      innerCapacity *
            siValue (D.observations.samples i).innerTemperature +
          outerCapacity *
            siValue (D.observations.samples i).outerTemperature =
        innerCapacity *
              siValue (D.observations.samples j).innerTemperature +
          outerCapacity *
            siValue (D.observations.samples j).outerTemperature := by
    exact hConservation i j
  have hBalance : WaterEnergyBalance D equilibrium := by
    change
      ∀ i : Fin q,
        innerCapacity *
              siValue (D.observations.samples i).innerTemperature +
            outerCapacity *
              siValue (D.observations.samples i).outerTemperature =
          totalCapacity * siValue equilibrium.temperature
    intro i
    calc
      innerCapacity *
              siValue (D.observations.samples i).innerTemperature +
            outerCapacity *
              siValue (D.observations.samples i).outerTemperature =
          referenceEnergy := by
            simpa only [referenceEnergy] using
              hEnergyConservation i referenceIndex
      _ = totalCapacity * siValue equilibrium.temperature := by
        have hCoordinate :
            siValue equilibrium.temperature = equilibriumCoordinate := by
          simpa only [equilibrium] using
            hEquilibriumTemperatureCoordinate
        rw [hCoordinate]
        dsimp only [equilibriumCoordinate]
        field_simp [hTotalCapacityNe]
  have hCommonZero :
      CommonTraceZero D (siValue equilibrium.temperature) :=
    (conservation_identifies_uniqueCommonTraceZero
      D equilibrium hGoverning hBalance).1
  refine ⟨equilibrium, ⟨hBalance, hCommonZero⟩, ?_⟩
  intro other hOther
  have hOtherBalance : WaterEnergyBalance D other := hOther.1
  have hOtherAtReference :
      innerCapacity *
            siValue
              (D.observations.samples referenceIndex).innerTemperature +
          outerCapacity *
            siValue
              (D.observations.samples referenceIndex).outerTemperature =
        totalCapacity * siValue other.temperature := by
    exact hOtherBalance referenceIndex
  have hEquilibriumAtReference :
      innerCapacity *
            siValue
              (D.observations.samples referenceIndex).innerTemperature +
          outerCapacity *
            siValue
              (D.observations.samples referenceIndex).outerTemperature =
        totalCapacity * siValue equilibrium.temperature := by
    exact hBalance referenceIndex
  have hScaledCoordinates :
      totalCapacity * siValue other.temperature =
        totalCapacity * siValue equilibrium.temperature :=
    hOtherAtReference.symm.trans hEquilibriumAtReference
  have hCoordinates :
      siValue other.temperature = siValue equilibrium.temperature := by
    apply mul_left_cancel₀ hTotalCapacityNe
    exact hScaledCoordinates
  have hTemperatures : other.temperature = equilibrium.temperature := by
    apply
      (coordinateInSI_eq_iff SIUnitChoices.SI
        other.temperature equilibrium.temperature).mp
    simpa only [siValue] using hCoordinates
  dsimp only [equilibrium] at hTemperatures ⊢
  cases other with
  | mk otherTemperature otherPositive =>
      exact
        Eq.mpr (PositiveTemperature.mk.injEq _ _ _ _) hTemperatures

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_4
