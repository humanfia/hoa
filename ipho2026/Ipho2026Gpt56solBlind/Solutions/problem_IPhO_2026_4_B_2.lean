import Mathlib.Data.Real.Basic
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.ExperimentalGasVapor

/-!
# IPhO 2026 Problem 4, Part B.2

This file specifies the requested height--temperature plot as the exact graph
of the observations supplied by Part B.1.  The `Fin q` index is retained, so
the construction preserves sampling order, repetitions, and multiplicity.
No fit, extrapolation, or additional observation is introduced.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_B_2

open Shared.FiniteObservations
open Shared.GasVapor

/-- The external B.1 data used to construct the graph requested in B.2. -/
structure SourceData (q : ℕ) where
  observations : HeightTemperatureSeries q

/-- The supplied observations come from a run satisfying the stated Part B
preparation and operating conditions.  Observation provenance and governing
laws remain carried by `source.observations`. -/
def MatchesStatement {q : ℕ} (source : SourceData q) : Prop :=
  PreparedCoolingRun source.observations.run

/-- A candidate is the requested graph exactly when it is the shared
occurrence-preserving graph of the supplied observations.  Its coordinates are
the coherent-SI values of observed absolute temperature and observed
liquid-free height, respectively. -/
def IsRequestedHeightTemperatureGraph {q : ℕ} (source : SourceData q)
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  HeightTemperatureGraphSolution source.observations graph

/-- The problem-specific graph predicate is exactly the shared exact-graph
predicate. -/
lemma requestedHeightTemperatureGraph_iff_shared {q : ℕ}
    (source : SourceData q) (graph : IndexedSeries q (ℝ × ℝ)) :
    IsRequestedHeightTemperatureGraph source graph ↔
      HeightTemperatureGraphSolution source.observations graph := by
  rfl

/-- Every matching supplied B.1 observation series determines exactly one
height--temperature graph of the requested form. -/
theorem requestedHeightTemperatureGraph_existsUnique {q : ℕ}
    (source : SourceData q) (_hMatches : MatchesStatement source) :
    ∃! graph : IndexedSeries q (ℝ × ℝ),
      IsRequestedHeightTemperatureGraph source graph := by
  change ∃! graph : IndexedSeries q (ℝ × ℝ),
    HeightTemperatureGraphSolution source.observations graph
  exact existsUnique_heightTemperatureGraphSolution source.observations

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_B_2
