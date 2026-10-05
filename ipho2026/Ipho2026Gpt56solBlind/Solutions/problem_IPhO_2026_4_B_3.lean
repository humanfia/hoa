import Mathlib.Data.Real.Basic
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.ExperimentalGasVapor
import Ipho2026Gpt56solBlind.Shared.GeometricOptics

/-!
# IPhO 2026 Problem 4, Part B.3

This file gives an answer-blind specification of the extrapolation requested in
Part B.3.  The supplied Part B observations and their exact Part B.2 graph are
kept as external data.  Because the statement describes the graph as only
approximately linear and does not prescribe an estimator, the requested height
is characterized here by an explicitly selected unweighted affine
least-squares fit with an intercept, evaluated at the stated reference
temperature.

No fitted coefficient or extrapolated height is included in the source data or
in a theorem hypothesis.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_B_3

open Shared.ISQDimensions
open Shared.FiniteObservations
open Shared.AffineFit
open Shared.GasVapor

noncomputable section

/-- External data for Part B.3: the nonempty, provenance-carrying cooling
observations together with the indexed graph supplied by Part B.2.  Agreement
between the two is imposed separately, so this structure contains no fit or
extrapolated value. -/
structure SourceData (q : ℕ) where
  observations : HeightTemperatureSeries q
  graph : IndexedSeries q (ℝ × ℝ)

/-- The supplied observations and graph agree with the experimental statement:
the named cooling run was prepared as prescribed, the graph is the exact
same-index coherent-SI image of the observations, and its temperature
predictor genuinely varies. -/
def MatchesStatement {q : ℕ} (source : SourceData q) : Prop :=
  PreparedCoolingRun source.observations.run ∧
    HeightTemperatureGraphSolution source.observations source.graph ∧
    NondegeneratePredictor
      (AffineData.ofGraph source.observations.nonempty source.graph)

/-- A typed height is the requested Part B.3 result when it is the value at
`273.15 K` of the unweighted OLS affine fit to the exact supplied graph.  The
shared `IsAffineFit` predicate is the pair of OLS normal equations; it does not
assert that every observation lies on the fitted line. -/
def IsRequestedReferenceHeight {q : ℕ} (source : SourceData q)
    (height : Length) : Prop :=
  ∃ intercept slope : ℝ,
    IsAffineFit
        (AffineData.ofGraph source.observations.nonempty source.graph)
        intercept slope ∧
      coordinateInSI SIUnitChoices.SI height =
        intercept + slope *
          coordinateInSI SIUnitChoices.SI referenceTemperature

/-- For a nondegenerate predictor, the normal-equation formulation of the
requested extrapolation is equivalent to global minimization of the unweighted
residual sum of squares. -/
lemma requestedReferenceHeight_iff_leastResidualExtrapolation {q : ℕ}
    (source : SourceData q)
    (hNondegenerate :
      NondegeneratePredictor
        (AffineData.ofGraph source.observations.nonempty source.graph))
    (height : Length) :
    IsRequestedReferenceHeight source height ↔
      ∃ intercept slope : ℝ,
        IsLeastResidual
            (AffineData.ofGraph source.observations.nonempty source.graph)
            intercept slope ∧
          coordinateInSI SIUnitChoices.SI height =
            intercept + slope *
              coordinateInSI SIUnitChoices.SI referenceTemperature := by
  unfold IsRequestedReferenceHeight
  constructor
  · rintro ⟨intercept, slope, hFit, hCoordinate⟩
    exact
      ⟨intercept, slope,
        (isAffineFit_iff_isLeastResidual
          (AffineData.ofGraph source.observations.nonempty source.graph)
          hNondegenerate intercept slope).mp hFit,
        hCoordinate⟩
  · rintro ⟨intercept, slope, hLeast, hCoordinate⟩
    exact
      ⟨intercept, slope,
        (isAffineFit_iff_isLeastResidual
          (AffineData.ofGraph source.observations.nonempty source.graph)
          hNondegenerate intercept slope).mpr hLeast,
        hCoordinate⟩

/-- Matching supplied data determine exactly one typed reference height.  The
unknown remains existential: the statement exposes neither a fitted pair nor a
numerical extrapolated value. -/
theorem requestedReferenceHeight_existsUnique {q : ℕ}
    (source : SourceData q) (hMatches : MatchesStatement source) :
    ∃! height : Length, IsRequestedReferenceHeight source height := by
  have hNondegenerate :
      NondegeneratePredictor
        (AffineData.ofGraph source.observations.nonempty source.graph) :=
    hMatches.2.2
  rcases existsUnique_isAffineFit
      (AffineData.ofGraph source.observations.nonempty source.graph)
      hNondegenerate with
    ⟨pair, hPairFit, hPairUnique⟩
  let height : Length :=
    Shared.GeometricOptics.quantityFromSICoordinate SIUnitChoices.SI
      lengthDimension
      (pair.1 + pair.2 *
        coordinateInSI SIUnitChoices.SI referenceTemperature)
  have hHeightCoordinate :
      coordinateInSI SIUnitChoices.SI height =
        pair.1 + pair.2 *
          coordinateInSI SIUnitChoices.SI referenceTemperature := by
    dsimp [height]
    exact
      (Shared.GeometricOptics.quantityFromSICoordinate_roundtrip
        SIUnitChoices.SI lengthDimension
        (pair.1 + pair.2 *
          coordinateInSI SIUnitChoices.SI referenceTemperature)
        (⟨0⟩ : Length)).1
  refine ⟨height, ?_, ?_⟩
  · exact ⟨pair.1, pair.2, hPairFit, hHeightCoordinate⟩
  · intro other hOther
    rcases hOther with
      ⟨intercept, slope, hOtherFit, hOtherCoordinate⟩
    have hPair : (intercept, slope) = pair := by
      exact hPairUnique (intercept, slope) hOtherFit
    have hIntercept : intercept = pair.1 :=
      congrArg Prod.fst hPair
    have hSlope : slope = pair.2 :=
      congrArg Prod.snd hPair
    apply (coordinateInSI_eq_iff SIUnitChoices.SI other height).mp
    rw [hOtherCoordinate, hHeightCoordinate, hIntercept, hSlope]

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_B_3
