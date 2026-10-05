import Mathlib.Algebra.BigOperators.Field
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.ExperimentalGasVapor
import Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
import Ipho2026Gpt56solBlind.Shared.FiniteDataAndAffineFit
import Ipho2026Gpt56solBlind.Shared.FiniteObservations
import Ipho2026Gpt56solBlind.Shared.ISQDimensions

/-!
# IPhO 2026 Problem 4, Part B.6

This file formalizes the answer-blind inference of the mass-specific latent
heat of vaporization.  The preceding B.5 value is not supplied as data:
instead, the original cooling observations, their same-index transformed
Clausius--Clapeyron graph, and a concrete unweighted affine OLS protocol
determine a molar latent heat.  The supplied water molar mass then determines
the requested mass-specific latent heat through a dimensioned solution chain.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_B_6

open scoped BigOperators

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.FiniteObservations
open Ipho2026Gpt56solBlind.Shared.AffineFit
open Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
open Ipho2026Gpt56solBlind.Shared.GasVaporLaws
open Ipho2026Gpt56solBlind.Shared.GasVapor

noncomputable section

/--
The source-side data used by B.6.  It contains the complete observation and
graph domain needed to infer the B.5 molar latent heat, but contains no fitted
coefficient and no latent-heat value.
-/
structure SourceData (q : ℕ) where
  heightTemperatureObservations : HeightTemperatureSeries q
  heightTemperatureGraph : IndexedSeries q (ℝ × ℝ)
  extrapolatedReferenceHeight : Length
  idealizedReferenceHeight : Length
  vaporPressureSeries :
    ObservationSeries q CoolingRun VaporPressureSample (fun _ _ _ ↦ True)
  referenceVaporPressure : Pressure
  clausiusClapeyronGraph : IndexedSeries q (ℝ × ℝ)
  waterMolarMass : MolarMass

/-- The local B.5 affine residual at an original graph occurrence. -/
def b5Residual {q : ℕ} (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) (intercept slope : ℝ)
    (i : Fin q) : ℝ :=
  let data := AffineData.ofGraph nonempty graph
  data.response i - intercept - slope * data.predictor i

/-- The unweighted sum of squared local B.5 residuals. -/
def b5ResidualSumSquares {q : ℕ} (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) (intercept slope : ℝ) : ℝ :=
  ∑ i : Fin q, (b5Residual nonempty graph intercept slope i) ^ 2

/-- The concrete two normal equations for the local affine B.5 fit. -/
def B5AffineNormalEquations {q : ℕ} (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) (intercept slope : ℝ) : Prop :=
  (∑ i : Fin q, b5Residual nonempty graph intercept slope i) = 0 ∧
    (∑ i : Fin q,
      (AffineData.ofGraph nonempty graph).predictor i *
        b5Residual nonempty graph intercept slope i) = 0

/-- A data-only witness that two B.5 predictor occurrences are distinct. -/
def B5PredictorNonconstant {q : ℕ}
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  ∃ i j : Fin q, (graph i).1 ≠ (graph j).1

/-- Global least-residual semantics for the local B.5 affine fit. -/
def B5LeastResidual {q : ℕ} (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) (intercept slope : ℝ) : Prop :=
  ∀ intercept' slope' : ℝ,
    b5ResidualSumSquares nonempty graph intercept slope ≤
      b5ResidualSumSquares nonempty graph intercept' slope'

/-- The local B.5 normal equations are the shared affine-fit equations. -/
lemma b5AffineNormalEquations_iff_isAffineFit {q : ℕ}
    (nonempty : 0 < q) (graph : IndexedSeries q (ℝ × ℝ))
    (intercept slope : ℝ) :
    B5AffineNormalEquations nonempty graph intercept slope ↔
      IsAffineFit (AffineData.ofGraph nonempty graph) intercept slope := by
  have hResidual : ∀ i : Fin q,
      b5Residual nonempty graph intercept slope i =
        Ipho2026Gpt56solBlind.Shared.AffineFit.residual
          (AffineData.ofGraph nonempty graph)
          intercept slope i := by
    intro i
    unfold b5Residual Ipho2026Gpt56solBlind.Shared.AffineFit.residual
    ring
  unfold B5AffineNormalEquations IsAffineFit AffineNormalEquations
  constructor
  · rintro ⟨hZero, hWeightedZero⟩
    constructor
    · calc
        (∑ i : Fin q,
            Ipho2026Gpt56solBlind.Shared.AffineFit.residual
              (AffineData.ofGraph nonempty graph) intercept slope i) =
            ∑ i : Fin q, b5Residual nonempty graph intercept slope i := by
              apply Finset.sum_congr rfl
              intro i _
              exact (hResidual i).symm
        _ = 0 := hZero
    · calc
        (∑ i : Fin q,
            (AffineData.ofGraph nonempty graph).predictor i *
              Ipho2026Gpt56solBlind.Shared.AffineFit.residual
                (AffineData.ofGraph nonempty graph) intercept slope i) =
            ∑ i : Fin q,
              (AffineData.ofGraph nonempty graph).predictor i *
                b5Residual nonempty graph intercept slope i := by
              apply Finset.sum_congr rfl
              intro i _
              exact congrArg
                (fun value : ℝ ↦
                  (AffineData.ofGraph nonempty graph).predictor i * value)
                (hResidual i).symm
        _ = 0 := hWeightedZero
  · rintro ⟨hZero, hWeightedZero⟩
    constructor
    · calc
        (∑ i : Fin q, b5Residual nonempty graph intercept slope i) =
            ∑ i : Fin q,
              Ipho2026Gpt56solBlind.Shared.AffineFit.residual
                (AffineData.ofGraph nonempty graph) intercept slope i := by
              apply Finset.sum_congr rfl
              intro i _
              exact hResidual i
        _ = 0 := hZero
    · calc
        (∑ i : Fin q,
            (AffineData.ofGraph nonempty graph).predictor i *
              b5Residual nonempty graph intercept slope i) =
            ∑ i : Fin q,
              (AffineData.ofGraph nonempty graph).predictor i *
                Ipho2026Gpt56solBlind.Shared.AffineFit.residual
                  (AffineData.ofGraph nonempty graph) intercept slope i := by
              apply Finset.sum_congr rfl
              intro i _
              exact congrArg
                (fun value : ℝ ↦
                  (AffineData.ofGraph nonempty graph).predictor i * value)
                (hResidual i)
        _ = 0 := hWeightedZero

/-- Under primitive predictor nonconstancy, local normal equations are exactly
the global least-RSS condition. -/
theorem b5AffineNormalEquations_iff_leastResidual {q : ℕ}
    (nonempty : 0 < q) (graph : IndexedSeries q (ℝ × ℝ))
    (hNonconstant : B5PredictorNonconstant graph) (intercept slope : ℝ) :
    B5AffineNormalEquations nonempty graph intercept slope ↔
      B5LeastResidual nonempty graph intercept slope := by
  let data := AffineData.ofGraph nonempty graph
  have hNondegenerate : NondegeneratePredictor data := by
    apply (nondegeneratePredictor_iff_exists_ne data).2
    rcases hNonconstant with ⟨i, j, hij⟩
    exact ⟨i, j, hij⟩
  have hResidualSumSquares : ∀ intercept' slope' : ℝ,
      b5ResidualSumSquares nonempty graph intercept' slope' =
        residualSumSquares data intercept' slope' := by
    intro intercept' slope'
    unfold b5ResidualSumSquares residualSumSquares b5Residual
      Ipho2026Gpt56solBlind.Shared.AffineFit.residual
    apply Finset.sum_congr rfl
    intro i hi
    apply congrArg (fun value : ℝ ↦ value ^ 2)
    ring
  rw [b5AffineNormalEquations_iff_isAffineFit]
  rw [isAffineFit_iff_isLeastResidual data hNondegenerate]
  constructor
  · intro hLeast intercept' slope'
    calc
      b5ResidualSumSquares nonempty graph intercept slope =
          residualSumSquares data intercept slope :=
        hResidualSumSquares intercept slope
      _ ≤ residualSumSquares data intercept' slope' :=
        hLeast intercept' slope'
      _ = b5ResidualSumSquares nonempty graph intercept' slope' :=
        (hResidualSumSquares intercept' slope').symm
  · intro hLeast intercept' slope'
    calc
      residualSumSquares data intercept slope =
          b5ResidualSumSquares nonempty graph intercept slope :=
        (hResidualSumSquares intercept slope).symm
      _ ≤ b5ResidualSumSquares nonempty graph intercept' slope' :=
        hLeast intercept' slope'
      _ = residualSumSquares data intercept' slope' :=
        hResidualSumSquares intercept' slope'

/-- A nonconstant B.5 predictor determines a unique normal-equation pair. -/
theorem existsUnique_b5AffineNormalEquations {q : ℕ}
    (nonempty : 0 < q) (graph : IndexedSeries q (ℝ × ℝ))
    (hNonconstant : B5PredictorNonconstant graph) :
    ∃! pair : ℝ × ℝ,
      B5AffineNormalEquations nonempty graph pair.1 pair.2 := by
  let data := AffineData.ofGraph nonempty graph
  have hNondegenerate : NondegeneratePredictor data := by
    apply (nondegeneratePredictor_iff_exists_ne data).2
    rcases hNonconstant with ⟨i, j, hij⟩
    exact ⟨i, j, hij⟩
  obtain ⟨pair, hPair, hUnique⟩ :=
    existsUnique_isAffineFit data hNondegenerate
  refine ⟨pair, ?_, ?_⟩
  · exact
      (b5AffineNormalEquations_iff_isAffineFit
        nonempty graph pair.1 pair.2).2 hPair
  · intro other hOther
    apply hUnique other
    exact
      (b5AffineNormalEquations_iff_isAffineFit
        nonempty graph other.1 other.2).1 hOther

/-- The purely data-based sign condition selecting a negative B.5 OLS slope. -/
def B5NegativeSlopeDataCondition {q : ℕ} (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  centeredPredictorResponseSum (AffineData.ofGraph nonempty graph) < 0

/-- Primitive nonconstancy makes the centered predictor sum of squares
strictly positive. -/
lemma b5PredictorNonconstant_centeredPredictorSumSquares_pos {q : ℕ}
    (nonempty : 0 < q) (graph : IndexedSeries q (ℝ × ℝ))
    (hNonconstant : B5PredictorNonconstant graph) :
    0 < centeredPredictorSumSquares (AffineData.ofGraph nonempty graph) := by
  apply
    (nondegeneratePredictor_iff_exists_ne
      (AffineData.ofGraph nonempty graph)).2
  rcases hNonconstant with ⟨i, j, hij⟩
  exact ⟨i, j, hij⟩

/-- A local normal-equation slope is the centered quotient and is negative on
the selected data-only domain. -/
lemma b5AffineNormalEquations_slope_eq_div_and_neg {q : ℕ}
    (nonempty : 0 < q) (graph : IndexedSeries q (ℝ × ℝ))
    (intercept slope : ℝ)
    (hNonconstant : B5PredictorNonconstant graph)
    (hNegative : B5NegativeSlopeDataCondition nonempty graph)
    (hNormal : B5AffineNormalEquations nonempty graph intercept slope) :
    0 < centeredPredictorSumSquares (AffineData.ofGraph nonempty graph) ∧
      slope =
        centeredPredictorResponseSum (AffineData.ofGraph nonempty graph) /
          centeredPredictorSumSquares (AffineData.ofGraph nonempty graph) ∧
      slope < 0 := by
  let data := AffineData.ofGraph nonempty graph
  have hSquaresPositive : 0 < centeredPredictorSumSquares data :=
    b5PredictorNonconstant_centeredPredictorSumSquares_pos
      nonempty graph hNonconstant
  have hFit : IsAffineFit data intercept slope :=
    (b5AffineNormalEquations_iff_isAffineFit
      nonempty graph intercept slope).1 hNormal
  have hCentered :=
    (normalEquations_iff_centered data intercept slope).1 hFit
  have hSlope :
      slope = centeredPredictorResponseSum data /
        centeredPredictorSumSquares data :=
    (eq_div_iff (ne_of_gt hSquaresPositive)).2 hCentered.2
  refine ⟨hSquaresPositive, hSlope, ?_⟩
  rw [hSlope]
  exact div_neg_of_neg_of_pos hNegative hSquaresPositive

/-- The data-only domain on which the selected local B.5 OLS fit is unique and
has negative slope. -/
def B5OrdinaryLeastSquaresDomain {q : ℕ} (nonempty : 0 < q)
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  B5PredictorNonconstant graph ∧
    B5NegativeSlopeDataCondition nonempty graph

/--
Agreement of supplied data with the complete B.5--B.6 statement.  The clauses
retain the prepared cooling run, the same-index B.4 vapor-pressure derivation,
the exact Clausius--Clapeyron graph with one common pressure scale, the
data-only OLS domain, and the stated water molar mass.  No latent heat or fit
coefficient occurs here.
-/
def MatchesStatement {q : ℕ} (source : SourceData q) : Prop :=
  PreparedCoolingRun source.heightTemperatureObservations.run ∧
    VaporPressureSeries source.heightTemperatureObservations
      (ordinaryLeastSquaresProtocol q) source.heightTemperatureGraph
      source.extrapolatedReferenceHeight source.idealizedReferenceHeight
      source.vaporPressureSeries ∧
    ClausiusClapeyronGraphSolution source.vaporPressureSeries
      source.referenceVaporPressure source.referenceVaporPressure
      source.clausiusClapeyronGraph ∧
    B5OrdinaryLeastSquaresDomain
      source.heightTemperatureObservations.nonempty
      source.clausiusClapeyronGraph ∧
    source.waterMolarMass = molarMassInGramsPerMole 18.02

/-- The primitive B.5 domain supplies the certificate-bearing negative fit
expected by the shared latent-heat inference. -/
lemma b5OrdinaryLeastSquaresDomain_hasNegativeSlopeProtocolFit {q : ℕ}
    (nonempty : 0 < q) (graph : IndexedSeries q (ℝ × ℝ))
    (hDomain : B5OrdinaryLeastSquaresDomain nonempty graph) :
    HasNegativeSlopeProtocolFit (ordinaryLeastSquaresProtocol q)
      nonempty graph := by
  rcases hDomain with ⟨hNonconstant, hNegative⟩
  obtain ⟨pair, hNormal, _⟩ :=
    existsUnique_b5AffineNormalEquations nonempty graph hNonconstant
  have hNondegenerate :
      NondegeneratePredictor (AffineData.ofGraph nonempty graph) := by
    apply
      (nondegeneratePredictor_iff_exists_ne
        (AffineData.ofGraph nonempty graph)).2
    rcases hNonconstant with ⟨i, j, hij⟩
    exact ⟨i, j, hij⟩
  have hFit :
      IsAffineFit (AffineData.ofGraph nonempty graph) pair.1 pair.2 :=
    (b5AffineNormalEquations_iff_isAffineFit
      nonempty graph pair.1 pair.2).1 hNormal
  have hProtocolFit :
      ClausiusClapeyronProtocolFitSolution
        (ordinaryLeastSquaresProtocol q) nonempty graph pair.1 pair.2 :=
    (clausiusClapeyronProtocolFitSolution_ordinaryLeastSquaresProtocol_iff
      nonempty graph hNondegenerate pair.1 pair.2).2 hFit
  have hSlopeNegative : pair.2 < 0 :=
    (b5AffineNormalEquations_slope_eq_div_and_neg nonempty graph
      pair.1 pair.2 hNonconstant hNegative hNormal).2.2
  exact ⟨pair.1, pair.2, hProtocolFit, hSlopeNegative⟩

/-- A requested B.5--B.6 output pair satisfies the full typed molar-to-mass
latent-heat solution chain. -/
def IsRequestedLatentHeatPair {q : ℕ} (source : SourceData q)
    (molarLatentHeat : MolarLatentHeat)
    (massSpecificLatentHeat : MassSpecificLatentHeat) : Prop :=
  LatentHeatSolutionChain source.heightTemperatureObservations.run
    (ordinaryLeastSquaresProtocol q)
    source.heightTemperatureObservations.nonempty
    source.clausiusClapeyronGraph source.waterMolarMass
    molarLatentHeat massSpecificLatentHeat

/-- Matching source data determine exactly one dimensioned molar and
mass-specific latent-heat pair. -/
theorem requestedLatentHeatPair_existsUnique {q : ℕ}
    (source : SourceData q) (hMatches : MatchesStatement source) :
    ∃! pair : MolarLatentHeat × MassSpecificLatentHeat,
      IsRequestedLatentHeatPair source pair.1 pair.2 := by
  rcases hMatches with
    ⟨hPrepared, _, _, hOlsDomain, hWaterMolarMass⟩
  have hNegative :
      HasNegativeSlopeProtocolFit (ordinaryLeastSquaresProtocol q)
        source.heightTemperatureObservations.nonempty
        source.clausiusClapeyronGraph :=
    b5OrdinaryLeastSquaresDomain_hasNegativeSlopeProtocolFit
      source.heightTemperatureObservations.nonempty
      source.clausiusClapeyronGraph hOlsDomain
  have hWaterMolarMassPositive :
      0 < coordinateInSI SIUnitChoices.SI source.waterMolarMass := by
    rw [hWaterMolarMass]
    have hMolarMass :
        molarMassInGramsPerMole (18.02 : ℝ) =
          (⟨(18.02 : ℝ) / 1000⟩ : MolarMass) := by
      exact quantityInSI_self _
    rw [hMolarMass, coordinateInSI_self]
    norm_num
  exact
    existsUnique_latentHeatSolutionChain
      source.heightTemperatureObservations.run
      (ordinaryLeastSquaresProtocol q)
      source.heightTemperatureObservations.nonempty
      source.clausiusClapeyronGraph source.waterMolarMass
      hPrepared hNegative hWaterMolarMassPositive

/-- A requested mass-specific latent heat retains its quantified molar
precursor and the complete B.5 fit characterization. -/
def IsRequestedMassSpecificLatentHeat {q : ℕ} (source : SourceData q)
    (massSpecificLatentHeat : MassSpecificLatentHeat) : Prop :=
  ∃ molarLatentHeat : MolarLatentHeat,
    IsRequestedLatentHeatPair source molarLatentHeat massSpecificLatentHeat

/-- Matching source data determine exactly one mass-specific component. -/
theorem requestedMassSpecificLatentHeat_existsUnique {q : ℕ}
    (source : SourceData q) (hMatches : MatchesStatement source) :
    ∃! massSpecificLatentHeat : MassSpecificLatentHeat,
      IsRequestedMassSpecificLatentHeat source massSpecificLatentHeat := by
  obtain ⟨pair, hPair, hUnique⟩ :=
    requestedLatentHeatPair_existsUnique source hMatches
  refine ⟨pair.2, ?_, ?_⟩
  · exact ⟨pair.1, hPair⟩
  · intro other hOther
    rcases hOther with ⟨otherMolarLatentHeat, hOtherPair⟩
    have hPairEquality :
        (otherMolarLatentHeat, other) = pair :=
      hUnique (otherMolarLatentHeat, other) hOtherPair
    exact congrArg Prod.snd hPairEquality

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_B_6
