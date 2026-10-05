import Mathlib.Data.Real.Basic
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.ExactGraph
import Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

/-!
# IPhO 2026 Problem 4, C.5

This module formalizes the exact graph requested from one prepared,
provenanced Part-C temperature record.  The response coordinate is the raw
inner-water temperature rate.  No heat-capacity rescaling, affine fit, thermal
resistance, or conductivity is part of this contract.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_5

open Ipho2026Gpt56solBlind.Shared.FiniteObservations
open Ipho2026Gpt56solBlind.Shared.ExactGraph
open Ipho2026Gpt56solBlind.Shared.RadialConductionCore
open Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

noncomputable section

/--
The externally supplied observation series is the ordered, provenanced record
belonging to the prepared named Figure 17 Part-C run.

Strict successive time gaps are deliberately not included here; they are a
separate fact about the supplied measurements.
-/
def MatchesStatement {m : ℕ}
    (run : Figure17PartCRadialRun (m + 1))
    (observations : RadialObservationSeries (m + 1)) : Prop :=
  PreparedFigure17PartCRadialRun run ∧ observations.run = run

/--
The exact C.5 graph.  At each adjacent interval, the horizontal coordinate is
the coherent-SI coordinate of the average outer-minus-inner temperature
difference and the vertical coordinate is the coherent-SI coordinate of the
raw inner-temperature forward rate from that same interval.
-/
def IsRequestedGraph {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (graph : IndexedSeries m (ℝ × ℝ)) : Prop :=
  (∀ index,
      (graph index).1 =
        siValue
          (adjacentAverageTemperatureDifference observations valid index)) ∧
    ∀ index,
      (graph index).2 =
        siValue (adjacentInnerTemperatureRate observations valid index)

/-- The problem-specific coordinate predicate is the shared exact adjacent graph. -/
lemma isRequestedGraph_iff_exactDifferenceAverageGraph {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (graph : IndexedSeries m (ℝ × ℝ)) :
    IsRequestedGraph observations valid graph ↔
      ExactDifferenceAverageGraph observations
        (fun sample ↦ siValue sample.elapsedTime)
        (fun sample ↦
          siValue sample.outerTemperature - siValue sample.innerTemperature)
        (fun sample ↦ siValue sample.innerTemperature)
        valid graph := by
  have hPredictorCoordinate (index : Fin m) :
      siValue (adjacentAverageTemperatureDifference observations valid index) =
        adjacentAverageSeries observations
          (fun sample ↦ siValue sample.elapsedTime)
          (fun sample ↦
            siValue sample.outerTemperature - siValue sample.innerTemperature)
          valid index := by
    calc
      siValue (adjacentAverageTemperatureDifference observations valid index) =
          (adjacentAverageTemperatureDifference observations valid index).val :=
        Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI_self _
      _ = adjacentAverageSeries observations
          (fun sample ↦ siValue sample.elapsedTime)
          (fun sample ↦
            siValue sample.outerTemperature - siValue sample.innerTemperature)
          valid index := rfl
  have hResponseCoordinate (index : Fin m) :
      siValue (adjacentInnerTemperatureRate observations valid index) =
        forwardDifferenceSeries observations
          (fun sample ↦ siValue sample.elapsedTime)
          (fun sample ↦ siValue sample.innerTemperature) valid index := by
    calc
      siValue (adjacentInnerTemperatureRate observations valid index) =
          (adjacentInnerTemperatureRate observations valid index).val :=
        Ipho2026Gpt56solBlind.Shared.ISQDimensions.coordinateInSI_self _
      _ = forwardDifferenceSeries observations
          (fun sample ↦ siValue sample.elapsedTime)
          (fun sample ↦ siValue sample.innerTemperature) valid index := rfl
  constructor
  · intro hRequested
    unfold ExactDifferenceAverageGraph
    funext index
    apply Prod.ext
    · exact (hRequested.1 index).trans (hPredictorCoordinate index)
    · exact (hRequested.2 index).trans (hResponseCoordinate index)
  · intro hExact
    unfold ExactDifferenceAverageGraph at hExact
    constructor
    · intro index
      have hCoordinate := congrArg Prod.fst (congrFun hExact index)
      exact hCoordinate.trans (hPredictorCoordinate index).symm
    · intro index
      have hCoordinate := congrArg Prod.snd (congrFun hExact index)
      exact hCoordinate.trans (hResponseCoordinate index).symm

/-- The first coordinate of every requested point is the raw adjacent predictor. -/
lemma requestedGraph_predictorCoordinate {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (graph : IndexedSeries m (ℝ × ℝ))
    (hGraph : IsRequestedGraph observations valid graph) (index : Fin m) :
    (graph index).1 =
      siValue
        (adjacentAverageTemperatureDifference observations valid index) := by
  exact hGraph.1 index

/-- The second coordinate is the raw inner-temperature rate, not a heat rate. -/
lemma requestedGraph_responseCoordinate {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (graph : IndexedSeries m (ℝ × ℝ))
    (hGraph : IsRequestedGraph observations valid graph) (index : Fin m) :
    (graph index).2 =
      siValue (adjacentInnerTemperatureRate observations valid index) := by
  exact hGraph.2 index

/-- A prepared, provenanced record with valid gaps determines exactly one C.5 graph. -/
theorem existsUnique_requestedGraph {m : ℕ}
    (run : Figure17PartCRadialRun (m + 1))
    (observations : RadialObservationSeries (m + 1))
    (hMatches : MatchesStatement run observations)
    (valid : ValidRadialSuccessiveTimeGaps observations) :
    ∃! graph : IndexedSeries m (ℝ × ℝ),
      IsRequestedGraph observations valid graph := by
  obtain ⟨graph, hGraph, hUnique⟩ :=
    existsUnique_exactDifferenceAverageGraph observations
      (fun sample ↦ siValue sample.elapsedTime)
      (fun sample ↦
        siValue sample.outerTemperature - siValue sample.innerTemperature)
      (fun sample ↦ siValue sample.innerTemperature) valid
  refine ⟨graph, ?_, ?_⟩
  · exact
      (isRequestedGraph_iff_exactDifferenceAverageGraph observations valid graph).2
        hGraph
  · intro other hOther
    apply hUnique other
    exact
      (isRequestedGraph_iff_exactDifferenceAverageGraph observations valid other).1
        hOther

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_5
