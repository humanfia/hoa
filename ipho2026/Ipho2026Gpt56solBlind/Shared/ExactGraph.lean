import Mathlib.Data.Real.Basic
import Ipho2026Gpt56solBlind.Shared.FiniteObservations

/-!
# Exact finite tables, graphs, and adjacent finite differences

This module gives exact, answer-free constructions from a provenanced finite
observation series.  Every construction retains the original `Fin` index, so
sampling order and repeated occurrences are preserved.  Adjacent finite
differences are available only in a context where successive sampling times
are strictly increasing.
-/

namespace Ipho2026Gpt56solBlind.Shared.ExactGraph

open Ipho2026Gpt56solBlind.Shared.FiniteObservations

noncomputable section

-- The pinned graph predicate intentionally shares the module's final name.
set_option linter.dupNamespace false

universe uRun uSample uValue uLeft uRight

/--
An indexed table is exact when it is the canonical row map of the supplied
observation occurrences.
-/
def ExactTable {n : ℕ} {RunId : Type uRun} {Sample : Type uSample}
    {Value : Type uValue} {Provenance : RunId → Fin n → Sample → Prop}
    (observations : ObservationSeries n RunId Sample Provenance)
    (row : Sample → Value) (table : IndexedSeries n Value) : Prop :=
  table = canonicalMap observations row

/-- A fixed observation series and row constructor determine one exact table. -/
theorem existsUnique_exactTable {n : ℕ} {RunId : Type uRun}
    {Sample : Type uSample} {Value : Type uValue}
    {Provenance : RunId → Fin n → Sample → Prop}
    (observations : ObservationSeries n RunId Sample Provenance)
    (row : Sample → Value) :
    ∃! table : IndexedSeries n Value, ExactTable observations row table := by
  simpa only [ExactTable] using
    (existsUnique_eq :
      ∃! table : IndexedSeries n Value,
        table = canonicalMap observations row)

/--
An indexed graph is exact when both coordinates are obtained from each common
sample occurrence by the canonical paired map.
-/
def ExactGraph {n : ℕ} {RunId : Type uRun} {Sample : Type uSample}
    {Left : Type uLeft} {Right : Type uRight}
    {Provenance : RunId → Fin n → Sample → Prop}
    (observations : ObservationSeries n RunId Sample Provenance)
    (left : Sample → Left) (right : Sample → Right)
    (graph : IndexedSeries n (Left × Right)) : Prop :=
  graph = canonicalPairedMap observations left right

/-- Fixed coordinate constructors determine one exact finite graph. -/
theorem existsUnique_exactGraph {n : ℕ} {RunId : Type uRun}
    {Sample : Type uSample} {Left : Type uLeft} {Right : Type uRight}
    {Provenance : RunId → Fin n → Sample → Prop}
    (observations : ObservationSeries n RunId Sample Provenance)
    (left : Sample → Left) (right : Sample → Right) :
    ∃! graph : IndexedSeries n (Left × Right),
      ExactGraph observations left right graph := by
  simpa only [ExactGraph] using
    (existsUnique_eq :
      ∃! graph : IndexedSeries n (Left × Right),
        graph = canonicalPairedMap observations left right)

/--
Successive time gaps in a series of length `m + 1` are valid when there is at
least one adjacent interval and every adjacent sampling-time increment is
strictly positive.
-/
def ValidSuccessiveTimeGaps {m : ℕ} {RunId : Type uRun}
    {Sample : Type uSample}
    {Provenance : RunId → Fin (m + 1) → Sample → Prop}
    (observations : ObservationSeries (m + 1) RunId Sample Provenance)
    (time : Sample → ℝ) : Prop :=
  0 < m ∧
    ∀ i : Fin m,
      0 < time (observations.samples (Fin.succ i)) -
        time (observations.samples (Fin.castSucc i))

/-- Every valid successive sampling-time increment is nonzero. -/
lemma successiveTimeGap_ne_zero {m : ℕ} {RunId : Type uRun}
    {Sample : Type uSample}
    {Provenance : RunId → Fin (m + 1) → Sample → Prop}
    (observations : ObservationSeries (m + 1) RunId Sample Provenance)
    (time : Sample → ℝ) (valid : ValidSuccessiveTimeGaps observations time)
    (i : Fin m) :
    time (observations.samples (Fin.succ i)) -
        time (observations.samples (Fin.castSucc i)) ≠ 0 := by
  exact ne_of_gt (valid.2 i)

/--
The forward difference over each adjacent interval, in the original sampling
order.  The validity argument records that every displayed denominator is
nonzero.
-/
def forwardDifferenceSeries {m : ℕ} {RunId : Type uRun}
    {Sample : Type uSample}
    {Provenance : RunId → Fin (m + 1) → Sample → Prop}
    (observations : ObservationSeries (m + 1) RunId Sample Provenance)
    (time response : Sample → ℝ)
    (_valid : ValidSuccessiveTimeGaps observations time) : IndexedSeries m ℝ :=
  fun i ↦
    (response (observations.samples (Fin.succ i)) -
        response (observations.samples (Fin.castSucc i))) /
      (time (observations.samples (Fin.succ i)) -
        time (observations.samples (Fin.castSucc i)))

/-- The adjacent forward-difference equations determine one indexed series. -/
theorem existsUnique_forwardDifferenceSeries {m : ℕ}
    {RunId : Type uRun} {Sample : Type uSample}
    {Provenance : RunId → Fin (m + 1) → Sample → Prop}
    (observations : ObservationSeries (m + 1) RunId Sample Provenance)
    (time response : Sample → ℝ)
    (valid : ValidSuccessiveTimeGaps observations time) :
    ∃! differences : IndexedSeries m ℝ,
      ∀ i,
        differences i = forwardDifferenceSeries observations time response valid i := by
  refine ⟨forwardDifferenceSeries observations time response valid, ?_, ?_⟩
  · intro i
    rfl
  · intro differences hdifferences
    funext i
    exact hdifferences i

/--
For each adjacent interval, the corresponding predictor is the arithmetic
mean of its two endpoint values.
-/
def adjacentAverageSeries {m : ℕ} {RunId : Type uRun}
    {Sample : Type uSample}
    {Provenance : RunId → Fin (m + 1) → Sample → Prop}
    (observations : ObservationSeries (m + 1) RunId Sample Provenance)
    (time predictor : Sample → ℝ)
    (_valid : ValidSuccessiveTimeGaps observations time) : IndexedSeries m ℝ :=
  fun i ↦
    (predictor (observations.samples (Fin.castSucc i)) +
        predictor (observations.samples (Fin.succ i))) /
      2

/-- The corresponding adjacent-average equations determine one series. -/
theorem existsUnique_adjacentAverageSeries {m : ℕ}
    {RunId : Type uRun} {Sample : Type uSample}
    {Provenance : RunId → Fin (m + 1) → Sample → Prop}
    (observations : ObservationSeries (m + 1) RunId Sample Provenance)
    (time predictor : Sample → ℝ)
    (valid : ValidSuccessiveTimeGaps observations time) :
    ∃! averages : IndexedSeries m ℝ,
      ∀ i,
        averages i = adjacentAverageSeries observations time predictor valid i := by
  refine ⟨adjacentAverageSeries observations time predictor valid, ?_, ?_⟩
  · intro i
    rfl
  · intro averages haverages
    funext i
    exact haverages i

/--
Pair each predictor average with the forward response difference from the
same adjacent interval.
-/
def differenceAveragePairs {m : ℕ} {RunId : Type uRun}
    {Sample : Type uSample}
    {Provenance : RunId → Fin (m + 1) → Sample → Prop}
    (observations : ObservationSeries (m + 1) RunId Sample Provenance)
    (time predictor response : Sample → ℝ)
    (valid : ValidSuccessiveTimeGaps observations time) :
    IndexedSeries m (ℝ × ℝ) :=
  fun i ↦
    (adjacentAverageSeries observations time predictor valid i,
      forwardDifferenceSeries observations time response valid i)

/-- Valid input data determine one paired average--difference series. -/
theorem existsUnique_differenceAveragePairs {m : ℕ}
    {RunId : Type uRun} {Sample : Type uSample}
    {Provenance : RunId → Fin (m + 1) → Sample → Prop}
    (observations : ObservationSeries (m + 1) RunId Sample Provenance)
    (time predictor response : Sample → ℝ)
    (valid : ValidSuccessiveTimeGaps observations time) :
    ∃! points : IndexedSeries m (ℝ × ℝ),
      ∀ i,
        points i =
          (adjacentAverageSeries observations time predictor valid i,
            forwardDifferenceSeries observations time response valid i) := by
  refine ⟨differenceAveragePairs observations time predictor response valid, ?_, ?_⟩
  · intro i
    rfl
  · intro points hpoints
    funext i
    exact hpoints i

/--
An adjacent-difference graph is exact when it is the canonical paired series
of adjacent predictor averages and response forward differences.
-/
def ExactDifferenceAverageGraph {m : ℕ} {RunId : Type uRun}
    {Sample : Type uSample}
    {Provenance : RunId → Fin (m + 1) → Sample → Prop}
    (observations : ObservationSeries (m + 1) RunId Sample Provenance)
    (time predictor response : Sample → ℝ)
    (valid : ValidSuccessiveTimeGaps observations time)
    (graph : IndexedSeries m (ℝ × ℝ)) : Prop :=
  graph = differenceAveragePairs observations time predictor response valid

/-- Fixed valid input data determine one exact adjacent-difference graph. -/
theorem existsUnique_exactDifferenceAverageGraph {m : ℕ}
    {RunId : Type uRun} {Sample : Type uSample}
    {Provenance : RunId → Fin (m + 1) → Sample → Prop}
    (observations : ObservationSeries (m + 1) RunId Sample Provenance)
    (time predictor response : Sample → ℝ)
    (valid : ValidSuccessiveTimeGaps observations time) :
    ∃! graph : IndexedSeries m (ℝ × ℝ),
      ExactDifferenceAverageGraph observations time predictor response valid graph := by
  simpa only [ExactDifferenceAverageGraph] using
    (existsUnique_eq :
      ∃! graph : IndexedSeries m (ℝ × ℝ),
        graph = differenceAveragePairs observations time predictor response valid)

end

end Ipho2026Gpt56solBlind.Shared.ExactGraph
