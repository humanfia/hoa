import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.ExperimentalGasVapor
import Ipho2026Gpt56solBlind.Shared.FiniteDataAndAffineFit
import Ipho2026Gpt56solBlind.Shared.FiniteObservations
import Ipho2026Gpt56solBlind.Shared.ISQDimensions

/-!
# IPhO 2026 Problem 4, Part B.5

This file gives an answer-blind model of the experimental determination of the
molar latent heat of vaporization.  Recorded temperature--height occurrences
remain indexed, the B.4 pressure reduction is pointwise at the same index, and
the requested Clausius--Clapeyron graph and latent heat are quantified outputs.
The numerical fit is fixed to unweighted affine ordinary least squares.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_B_5

open Shared
open Shared.ISQDimensions
open Shared.FiniteObservations
open Shared.AffineFit
open Shared.GasVaporLaws

open scoped BigOperators

noncomputable section

/-- The primitive B.5 inputs: an occurrence-indexed cooling record, the
atmospheric pressure used in Part B, and the positive reference vapor pressure
from the Clausius--Clapeyron law. -/
structure B5SourceData (q : ℕ) where
  observations : Shared.GasVapor.HeightTemperatureSeries q
  atmosphericPressure : Pressure
  referenceVaporPressure : Pressure

/-- The fixed B.3 extrapolation, made reproducible as an unweighted affine OLS
fit of the measured coherent-SI height against absolute temperature. -/
def B4ReductionSolution {q : ℕ} (data : B5SourceData q)
    (heightIntercept heightSlope : ℝ) (referenceHeight : Length) : Prop :=
  let heightData : AffineData q :=
    { nonempty := data.observations.nonempty
      predictor := fun i ↦
        coordinateInSI SIUnitChoices.SI
          (data.observations.samples i).observedTemperature
      response := fun i ↦
        coordinateInSI SIUnitChoices.SI
          (data.observations.samples i).observedHeight }
  IsAffineFit heightData heightIntercept heightSlope ∧
    coordinateInSI SIUnitChoices.SI referenceHeight =
      heightIntercept + heightSlope *
        coordinateInSI SIUnitChoices.SI
          Shared.GasVapor.referenceTemperature

/-- Primitive positivity, fixed-constant, atmospheric-pressure, and
nondegeneracy conditions.  The final clause is the directly checkable
positivity domain of the B.4 pressure formula for every admissible B.3
extrapolation; it contains no pressure series, graph, fit coefficient, or
latent-heat candidate. -/
def B5SourceDomain {q : ℕ} (data : B5SourceData q) : Prop :=
  0 < coordinateInSI SIUnitChoices.SI
      Shared.GasVapor.referenceTemperature ∧
    0 < coordinateInSI SIUnitChoices.SI data.atmosphericPressure ∧
    0 < coordinateInSI SIUnitChoices.SI data.referenceVaporPressure ∧
    data.observations.run.molarGasConstant =
      Shared.Figure17Apparatus.molarGasConstantInJoulesPerMoleKelvin 8.31 ∧
    data.observations.run.atmosphericPressure = data.atmosphericPressure ∧
    (∀ i : Fin q,
      (data.observations.run.trueStates i.val).totalPressure =
        data.atmosphericPressure) ∧
    (∀ i : Fin q,
      0 < coordinateInSI SIUnitChoices.SI
          (data.observations.samples i).observedTemperature ∧
        0 < coordinateInSI SIUnitChoices.SI
          (data.observations.samples i).observedHeight) ∧
    (∃ i j : Fin q,
      coordinateInSI SIUnitChoices.SI
          (data.observations.samples i).observedTemperature ≠
        coordinateInSI SIUnitChoices.SI
          (data.observations.samples j).observedTemperature) ∧
    ∀ heightIntercept heightSlope referenceHeight,
      B4ReductionSolution data heightIntercept heightSlope referenceHeight →
        0 < coordinateInSI SIUnitChoices.SI referenceHeight ∧
          ∀ i : Fin q,
            0 < coordinateInSI SIUnitChoices.SI data.atmosphericPressure *
              (1 -
                coordinateInSI SIUnitChoices.SI referenceHeight *
                    coordinateInSI SIUnitChoices.SI
                      (data.observations.samples i).observedTemperature /
                  (coordinateInSI SIUnitChoices.SI
                      (data.observations.samples i).observedHeight *
                    coordinateInSI SIUnitChoices.SI
                      Shared.GasVapor.referenceTemperature))

/-- Two distinct recorded temperatures make the fixed B.3 normal equations
well posed, and evaluation at the fixed reference temperature determines one
typed reference height. -/
theorem existsUnique_b4ReductionSolution {q : ℕ} (data : B5SourceData q)
    (hDomain : B5SourceDomain data) :
    ∃! solution : ℝ × (ℝ × Length),
      B4ReductionSolution data solution.1 solution.2.1 solution.2.2 := by
  rcases hDomain with
    ⟨_, _, _, _, _, _, _, hDistinctTemperatures, _⟩
  let heightData : AffineData q :=
    { nonempty := data.observations.nonempty
      predictor := fun i ↦
        coordinateInSI SIUnitChoices.SI
          (data.observations.samples i).observedTemperature
      response := fun i ↦
        coordinateInSI SIUnitChoices.SI
          (data.observations.samples i).observedHeight }
  have hNondegenerate : NondegeneratePredictor heightData :=
    (nondegeneratePredictor_iff_exists_ne heightData).2 (by
      simpa only [heightData] using hDistinctTemperatures)
  obtain ⟨pair, hPairFit, hPairUnique⟩ :=
    existsUnique_isAffineFit heightData hNondegenerate
  let referenceHeight : Length :=
    ⟨pair.1 + pair.2 *
      coordinateInSI SIUnitChoices.SI Shared.GasVapor.referenceTemperature⟩
  refine ⟨(pair.1, (pair.2, referenceHeight)), ?_, ?_⟩
  · change IsAffineFit heightData pair.1 pair.2 ∧
      coordinateInSI SIUnitChoices.SI referenceHeight =
        pair.1 + pair.2 *
          coordinateInSI SIUnitChoices.SI Shared.GasVapor.referenceTemperature
    exact ⟨hPairFit, by simp only [referenceHeight, coordinateInSI_self]⟩
  · intro other hOther
    change IsAffineFit heightData other.1 other.2.1 ∧
      coordinateInSI SIUnitChoices.SI other.2.2 =
        other.1 + other.2.1 *
          coordinateInSI SIUnitChoices.SI Shared.GasVapor.referenceTemperature at hOther
    have hPair : (other.1, other.2.1) = pair :=
      hPairUnique (other.1, other.2.1) hOther.1
    have hIntercept : other.1 = pair.1 := congrArg Prod.fst hPair
    have hSlope : other.2.1 = pair.2 := congrArg Prod.snd hPair
    apply Prod.ext
    · exact hIntercept
    · apply Prod.ext
      · exact hSlope
      · apply (coordinateInSI_eq_iff SIUnitChoices.SI _ _).mp
        rw [hOther.2, hIntercept, hSlope]
        simp only [referenceHeight, coordinateInSI_self]

/-- A same-index B.4 vapor-pressure series.  Temperatures are copied from the
original occurrences, while pressures obey the dry-air/vapor balance formula
obtained using the zero-vapor reference inventory at `T₀`. -/
def B5VaporPressureSeriesSolution {q : ℕ} (data : B5SourceData q)
    (referenceHeight : Length)
    (series : IndexedSeries q Shared.GasVapor.VaporPressureSample) : Prop :=
  ∀ i : Fin q,
    (series i).temperature =
        (data.observations.samples i).observedTemperature ∧
      coordinateInSI SIUnitChoices.SI (series i).vaporPressure =
        coordinateInSI SIUnitChoices.SI data.atmosphericPressure *
          (1 -
            coordinateInSI SIUnitChoices.SI referenceHeight *
                coordinateInSI SIUnitChoices.SI
                  (data.observations.samples i).observedTemperature /
              (coordinateInSI SIUnitChoices.SI
                  (data.observations.samples i).observedHeight *
                coordinateInSI SIUnitChoices.SI
                  Shared.GasVapor.referenceTemperature))

/-- A B.3 reference height determines exactly one occurrence-preserving B.4
pressure series, and the primitive pressure-domain inequality makes every
derived pressure positive. -/
theorem existsUnique_b5VaporPressureSeriesSolution {q : ℕ}
    (data : B5SourceData q) (heightIntercept heightSlope : ℝ)
    (referenceHeight : Length) (hDomain : B5SourceDomain data)
    (hReduction :
      B4ReductionSolution data heightIntercept heightSlope referenceHeight) :
    (∃! series : IndexedSeries q Shared.GasVapor.VaporPressureSample,
      B5VaporPressureSeriesSolution data referenceHeight series) ∧
      ∀ series : IndexedSeries q Shared.GasVapor.VaporPressureSample,
        B5VaporPressureSeriesSolution data referenceHeight series →
          ∀ i : Fin q,
            0 < coordinateInSI SIUnitChoices.SI (series i).vaporPressure := by
  rcases hDomain with ⟨_, _, _, _, _, _, _, _, hFormulaPositive⟩
  let candidate : IndexedSeries q Shared.GasVapor.VaporPressureSample :=
    fun i ↦
      { temperature :=
          (data.observations.samples i).observedTemperature
        vaporPressure :=
          ⟨coordinateInSI SIUnitChoices.SI data.atmosphericPressure *
            (1 -
              coordinateInSI SIUnitChoices.SI referenceHeight *
                  coordinateInSI SIUnitChoices.SI
                    (data.observations.samples i).observedTemperature /
                (coordinateInSI SIUnitChoices.SI
                    (data.observations.samples i).observedHeight *
                  coordinateInSI SIUnitChoices.SI
                    Shared.GasVapor.referenceTemperature))⟩ }
  have hCandidate :
      B5VaporPressureSeriesSolution data referenceHeight candidate := by
    intro i
    constructor
    · rfl
    · simp only [candidate, coordinateInSI_self]
  constructor
  · refine ⟨candidate, hCandidate, ?_⟩
    intro other hOther
    funext i
    have hTemperature :
        (other i).temperature = (candidate i).temperature :=
      (hOther i).1.trans (hCandidate i).1.symm
    have hPressure :
        (other i).vaporPressure = (candidate i).vaporPressure :=
      (coordinateInSI_eq_iff SIUnitChoices.SI _ _).mp
        ((hOther i).2.trans (hCandidate i).2.symm)
    exact congrArg₂ Shared.GasVapor.VaporPressureSample.mk
      hTemperature hPressure
  · intro other hOther i
    rw [(hOther i).2]
    exact (hFormulaPositive _ _ _ hReduction).2 i

/-- Positivity needed for reciprocal temperatures and logarithmic pressure
ratios follows from the primitive domain and the pointwise B.4 equations. -/
lemma positiveClausiusClapeyronDomain_of_b5VaporPressureSeriesSolution
    {q : ℕ} (data : B5SourceData q) (heightIntercept heightSlope : ℝ)
    (referenceHeight : Length)
    (series : IndexedSeries q Shared.GasVapor.VaporPressureSample)
    (hDomain : B5SourceDomain data)
    (hReduction :
      B4ReductionSolution data heightIntercept heightSlope referenceHeight)
    (hSeries : B5VaporPressureSeriesSolution data referenceHeight series) :
    0 < coordinateInSI SIUnitChoices.SI
        Shared.GasVapor.referenceTemperature ∧
      0 < coordinateInSI SIUnitChoices.SI data.referenceVaporPressure ∧
      ∀ i : Fin q,
        0 < coordinateInSI SIUnitChoices.SI (series i).temperature ∧
          0 < coordinateInSI SIUnitChoices.SI
            (series i).vaporPressure := by
  rcases hDomain with
    ⟨hReferenceTemperature, _, hReferencePressure, _, _, _,
      hObservationPositive, _, hFormulaPositive⟩
  refine ⟨hReferenceTemperature, hReferencePressure, ?_⟩
  intro i
  constructor
  · rw [(hSeries i).1]
    exact (hObservationPositive i).1
  · rw [(hSeries i).2]
    exact (hFormulaPositive _ _ _ hReduction).2 i

/-- The exact occurrence-preserving Clausius--Clapeyron graph.  Both
coordinates at index `i` are computed from the same B.4 occurrence. -/
def B5GraphSolution {q : ℕ} (data : B5SourceData q)
    (series : IndexedSeries q Shared.GasVapor.VaporPressureSample)
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  ∀ i : Fin q,
    graph i =
      (1 / coordinateInSI SIUnitChoices.SI (series i).temperature -
          1 / coordinateInSI SIUnitChoices.SI
            Shared.GasVapor.referenceTemperature,
        Real.log
          (coordinateInSI SIUnitChoices.SI (series i).vaporPressure /
            coordinateInSI SIUnitChoices.SI data.referenceVaporPressure))

/-- The exact coordinate equations determine one and only one transformed
graph without sorting or deduplicating the source occurrences. -/
theorem existsUnique_b5GraphSolution {q : ℕ} (data : B5SourceData q)
    (heightIntercept heightSlope : ℝ) (referenceHeight : Length)
    (series : IndexedSeries q Shared.GasVapor.VaporPressureSample)
    (hDomain : B5SourceDomain data)
    (hReduction :
      B4ReductionSolution data heightIntercept heightSlope referenceHeight)
    (hSeries : B5VaporPressureSeriesSolution data referenceHeight series) :
    ∃! graph : IndexedSeries q (ℝ × ℝ),
      B5GraphSolution data series graph := by
  let candidate : IndexedSeries q (ℝ × ℝ) :=
    fun i ↦
      (1 / coordinateInSI SIUnitChoices.SI (series i).temperature -
          1 / coordinateInSI SIUnitChoices.SI
            Shared.GasVapor.referenceTemperature,
        Real.log
          (coordinateInSI SIUnitChoices.SI (series i).vaporPressure /
            coordinateInSI SIUnitChoices.SI data.referenceVaporPressure))
  refine ⟨candidate, ?_, ?_⟩
  · intro i
    rfl
  · intro other hOther
    funext i
    simpa only [candidate] using hOther i

/-- The concrete unweighted affine OLS relation on a transformed graph,
expressed by the shared pair of normal equations. -/
def B5OLSFitSolution {q : ℕ} (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) (intercept slope : ℝ) : Prop :=
  IsAffineFit (AffineData.ofGraph nonempty graph) intercept slope

/-- Primitive predictor nonconstancy: two transformed occurrences have
different reciprocal-temperature coordinates. -/
def B5PredictorNonconstant {q : ℕ}
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  ∃ i j : Fin q, (graph i).1 ≠ (graph j).1

/-- Under predictor nonconstancy, the two normal equations are exactly the
global least-residual semantics for the fixed unweighted affine fit. -/
theorem b5OLSFitSolution_iff_isLeastResidual {q : ℕ} (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ))
    (hNonconstant : B5PredictorNonconstant graph) (intercept slope : ℝ) :
    B5OLSFitSolution nonempty graph intercept slope ↔
      IsLeastResidual (AffineData.ofGraph nonempty graph) intercept slope := by
  have hNondegenerate :
      NondegeneratePredictor (AffineData.ofGraph nonempty graph) :=
    (nondegeneratePredictor_iff_exists_ne
      (AffineData.ofGraph nonempty graph)).2 (by
        exact hNonconstant)
  exact isAffineFit_iff_isLeastResidual
    (AffineData.ofGraph nonempty graph) hNondegenerate intercept slope

/-- A nonconstant transformed predictor determines exactly one affine OLS
intercept--slope pair. -/
theorem existsUnique_b5OLSFitSolution {q : ℕ} (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ))
    (hNonconstant : B5PredictorNonconstant graph) :
    ∃! pair : ℝ × ℝ,
      B5OLSFitSolution nonempty graph pair.1 pair.2 := by
  have hNondegenerate :
      NondegeneratePredictor (AffineData.ofGraph nonempty graph) :=
    (nondegeneratePredictor_iff_exists_ne
      (AffineData.ofGraph nonempty graph)).2 (by
        exact hNonconstant)
  exact existsUnique_isAffineFit
    (AffineData.ofGraph nonempty graph) hNondegenerate

/-- A data-only domain ensuring that the OLS slope is negative.  It mentions
only predictor nonconstancy and the centered predictor--response cross-sum of
the transformed observations. -/
def B5NegativeOLSDataDomain {q : ℕ} (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  B5PredictorNonconstant graph ∧
    centeredPredictorResponseSum (AffineData.ofGraph nonempty graph) < 0

/-- In the negative-cross-sum domain, the fixed OLS protocol has a
certificate-bearing fit whose slope is negative. -/
lemma b5NegativeOLSDataDomain_implies_hasNegativeSlopeProtocolFit
    {q : ℕ} (nonempty : 0 < q) (graph : IndexedSeries q (ℝ × ℝ))
    (hNegative : B5NegativeOLSDataDomain nonempty graph) :
    ∃ intercept slope : ℝ,
      B5OLSFitSolution nonempty graph intercept slope ∧ slope < 0 := by
  rcases hNegative with ⟨hNonconstant, hCrossNegative⟩
  obtain ⟨pair, hPairFit, _⟩ :=
    existsUnique_b5OLSFitSolution nonempty graph hNonconstant
  have hNondegenerate :
      NondegeneratePredictor (AffineData.ofGraph nonempty graph) :=
    (nondegeneratePredictor_iff_exists_ne
      (AffineData.ofGraph nonempty graph)).2 (by
        exact hNonconstant)
  have hSlopeEquation :=
    (normalEquations_iff_centered (AffineData.ofGraph nonempty graph)
      pair.1 pair.2).1 hPairFit |>.2
  refine ⟨pair.1, pair.2, hPairFit, ?_⟩
  have hProductNegative :
      pair.2 * centeredPredictorSumSquares
          (AffineData.ofGraph nonempty graph) < 0 := by
    rw [hSlopeEquation]
    exact hCrossNegative
  rcases (mul_neg_iff.mp hProductNegative) with
      ⟨_, hSquaresNegative⟩ | ⟨hSlopeNegative, _⟩
  · exact False.elim (not_lt_of_ge (le_of_lt hNondegenerate) hSquaresNegative)
  · exact hSlopeNegative

/-- Complete data-only analysis domain.  Every equation-derived chain from a
B.3 extrapolation through a B.4 series to its exact graph must have a
nonconstant predictor and negative centered cross-sum. -/
def B5AnalysisDomain {q : ℕ} (data : B5SourceData q) : Prop :=
  ∀ heightIntercept heightSlope referenceHeight
      (series : IndexedSeries q Shared.GasVapor.VaporPressureSample)
      (graph : IndexedSeries q (ℝ × ℝ)),
    B4ReductionSolution data heightIntercept heightSlope referenceHeight →
      B5VaporPressureSeriesSolution data referenceHeight series →
      B5GraphSolution data series graph →
      B5NegativeOLSDataDomain data.observations.nonempty graph

/-- A typed molar latent heat extracted from the negative slope of the fixed
OLS fit using the run's source-fixed value `R = 8.31 J/(mol K)`. -/
def B5MolarLatentHeatSolution {q : ℕ} (data : B5SourceData q)
    (graph : IndexedSeries q (ℝ × ℝ))
    (molarLatentHeat : MolarLatentHeat) : Prop :=
  ∃ intercept slope : ℝ,
    B5OLSFitSolution data.observations.nonempty graph intercept slope ∧
      slope < 0 ∧
      coordinateInSI SIUnitChoices.SI molarLatentHeat =
        -coordinateInSI SIUnitChoices.SI
            data.observations.run.molarGasConstant * slope

/-- Primitive source constants and negative-slope transformed data determine
one typed molar latent heat, whose coherent-SI coordinate is positive. -/
theorem existsUnique_b5MolarLatentHeatSolution {q : ℕ}
    (data : B5SourceData q) (graph : IndexedSeries q (ℝ × ℝ))
    (hSource : B5SourceDomain data)
    (hNegative :
      B5NegativeOLSDataDomain data.observations.nonempty graph) :
    (∃! molarLatentHeat : MolarLatentHeat,
      B5MolarLatentHeatSolution data graph molarLatentHeat) ∧
      ∀ molarLatentHeat : MolarLatentHeat,
        B5MolarLatentHeatSolution data graph molarLatentHeat →
          0 < coordinateInSI SIUnitChoices.SI molarLatentHeat := by
  rcases hSource with ⟨_, _, _, hGasConstant, _, _, _, _, _⟩
  obtain ⟨intercept, slope, hFit, hSlopeNegative⟩ :=
    b5NegativeOLSDataDomain_implies_hasNegativeSlopeProtocolFit
      data.observations.nonempty graph hNegative
  obtain ⟨fitPair, _, hFitUnique⟩ :=
    existsUnique_b5OLSFitSolution data.observations.nonempty graph hNegative.1
  let candidate : MolarLatentHeat :=
    ⟨-coordinateInSI SIUnitChoices.SI
        data.observations.run.molarGasConstant * slope⟩
  have hCandidate : B5MolarLatentHeatSolution data graph candidate := by
    refine ⟨intercept, slope, hFit, hSlopeNegative, ?_⟩
    simp only [candidate, coordinateInSI_self]
  have hGasConstantPositive :
      0 < coordinateInSI SIUnitChoices.SI
        data.observations.run.molarGasConstant := by
    rw [hGasConstant]
    norm_num [Shared.Figure17Apparatus.molarGasConstantInJoulesPerMoleKelvin]
  constructor
  · refine ⟨candidate, hCandidate, ?_⟩
    intro other hOther
    rcases hOther with
      ⟨otherIntercept, otherSlope, hOtherFit, _, hOtherCoordinate⟩
    have hOtherPair : (otherIntercept, otherSlope) = fitPair :=
      hFitUnique (otherIntercept, otherSlope) hOtherFit
    have hCandidatePair : (intercept, slope) = fitPair :=
      hFitUnique (intercept, slope) hFit
    have hSlope : otherSlope = slope :=
      congrArg Prod.snd (hOtherPair.trans hCandidatePair.symm)
    apply (coordinateInSI_eq_iff SIUnitChoices.SI other candidate).mp
    rw [hOtherCoordinate, hSlope]
    simp only [candidate, coordinateInSI_self]
  · intro other hOther
    rcases hOther with ⟨_, otherSlope, _, hOtherSlopeNegative, hCoordinate⟩
    rw [hCoordinate]
    exact mul_pos_of_neg_of_neg
      (neg_lt_zero.mpr hGasConstantPositive) hOtherSlopeNegative

/-- A complete B.5 output consists of the exact transformed graph and the
typed molar latent heat, with the B.3 fit, B.4 series, and OLS coefficients
remaining quantified intermediate witnesses. -/
def B5Solution {q : ℕ} (data : B5SourceData q)
    (graph : IndexedSeries q (ℝ × ℝ))
    (molarLatentHeat : MolarLatentHeat) : Prop :=
  ∃ heightIntercept heightSlope : ℝ,
    ∃ referenceHeight : Length,
      ∃ series : IndexedSeries q Shared.GasVapor.VaporPressureSample,
        B4ReductionSolution data heightIntercept heightSlope referenceHeight ∧
          B5VaporPressureSeriesSolution data referenceHeight series ∧
          B5GraphSolution data series graph ∧
          B5MolarLatentHeatSolution data graph molarLatentHeat

/-- The primitive and data-only analysis domains determine exactly one
occurrence-preserving Clausius--Clapeyron graph and one typed molar latent
heat.  No numerical answer is present in the theorem signature. -/
theorem existsUnique_b5Solution {q : ℕ} (data : B5SourceData q)
    (hSource : B5SourceDomain data) (hAnalysis : B5AnalysisDomain data) :
    ∃! output : IndexedSeries q (ℝ × ℝ) × MolarLatentHeat,
      B5Solution data output.1 output.2 := by
  obtain ⟨reduction, hReduction, hReductionUnique⟩ :=
    existsUnique_b4ReductionSolution data hSource
  obtain ⟨⟨series, hSeries, hSeriesUnique⟩, _⟩ :=
    existsUnique_b5VaporPressureSeriesSolution data reduction.1 reduction.2.1
      reduction.2.2 hSource hReduction
  obtain ⟨graph, hGraph, hGraphUnique⟩ :=
    existsUnique_b5GraphSolution data reduction.1 reduction.2.1
      reduction.2.2 series hSource hReduction hSeries
  have hNegative :
      B5NegativeOLSDataDomain data.observations.nonempty graph :=
    hAnalysis reduction.1 reduction.2.1 reduction.2.2 series graph
      hReduction hSeries hGraph
  obtain ⟨⟨molarLatentHeat, hMolarLatentHeat, hMolarLatentHeatUnique⟩, _⟩ :=
    existsUnique_b5MolarLatentHeatSolution data graph hSource hNegative
  refine ⟨(graph, molarLatentHeat), ?_, ?_⟩
  · exact
      ⟨reduction.1, reduction.2.1, reduction.2.2, series,
        hReduction, hSeries, hGraph, hMolarLatentHeat⟩
  · rintro ⟨otherGraph, otherMolarLatentHeat⟩ hOther
    rcases hOther with
      ⟨otherIntercept, otherSlope, otherReferenceHeight, otherSeries,
        hOtherReduction, hOtherSeries, hOtherGraph, hOtherMolarLatentHeat⟩
    have hReductionEquality :
        (otherIntercept, (otherSlope, otherReferenceHeight)) = reduction :=
      hReductionUnique
        (otherIntercept, (otherSlope, otherReferenceHeight)) hOtherReduction
    have hReferenceHeight : otherReferenceHeight = reduction.2.2 :=
      congrArg (fun solution : ℝ × (ℝ × Length) ↦ solution.2.2)
        hReductionEquality
    have hOtherSeriesCanonical :
        B5VaporPressureSeriesSolution data reduction.2.2 otherSeries := by
      rw [← hReferenceHeight]
      exact hOtherSeries
    have hSeriesEquality : otherSeries = series :=
      hSeriesUnique otherSeries hOtherSeriesCanonical
    have hOtherGraphCanonical :
        B5GraphSolution data series otherGraph := by
      rw [← hSeriesEquality]
      exact hOtherGraph
    have hGraphEquality : otherGraph = graph :=
      hGraphUnique otherGraph hOtherGraphCanonical
    have hOtherMolarLatentHeatCanonical :
        B5MolarLatentHeatSolution data graph otherMolarLatentHeat := by
      rw [← hGraphEquality]
      exact hOtherMolarLatentHeat
    have hMolarLatentHeatEquality :
        otherMolarLatentHeat = molarLatentHeat :=
      hMolarLatentHeatUnique otherMolarLatentHeat
        hOtherMolarLatentHeatCanonical
    exact Prod.ext hGraphEquality hMolarLatentHeatEquality

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_B_5
