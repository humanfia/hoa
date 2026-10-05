import Mathlib
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic
import Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

/-!
# IPhO 2026 Problem 4 C.2

This file specifies the requested common-axis plot directly from the externally
supplied Part-C temperature record.  The graph retains the record's `Fin`
index, so sampling order, repeated values, and multiplicity are unchanged.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_2

open Ipho2026Gpt56solBlind.Shared.FiniteObservations
open Ipho2026Gpt56solBlind.Shared.ExactGraph
open Ipho2026Gpt56solBlind.Shared.RadialConductionCore
open Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

noncomputable section

/-- The Part-C source record supplied to the plotting task. -/
structure SourceData (q : ℕ) where
  observations : RadialObservationSeries q

/-- The supplied observations belong to the prepared named Figure 17 Part-C
run.  The observation-series provenance separately identifies every sample
with the external-record entry at the same index. -/
def MatchesStatement {q : ℕ} (source : SourceData q) : Prop :=
  PreparedFigure17PartCRadialRun source.observations.run

/-- An exact graph of elapsed time against the paired inner- and
outer-cylinder temperatures, all expressed in coherent SI coordinates. -/
def IsRequestedTwoTraceGraph {q : ℕ} (source : SourceData q)
    (graph : IndexedSeries q (ℝ × (ℝ × ℝ))) : Prop :=
  ExactGraph source.observations
    (fun sample ↦ siValue sample.elapsedTime)
    (fun sample ↦
      (siValue sample.innerTemperature, siValue sample.outerTemperature))
    graph

/-- Every matching source record determines exactly one requested two-trace
graph. -/
theorem requestedTwoTraceGraph_existsUnique {q : ℕ} (source : SourceData q)
    (_matches : MatchesStatement source) :
    ∃! graph : IndexedSeries q (ℝ × (ℝ × ℝ)),
      IsRequestedTwoTraceGraph source graph := by
  change ∃! graph : IndexedSeries q (ℝ × (ℝ × ℝ)),
    ExactGraph source.observations
      (fun sample ↦ siValue sample.elapsedTime)
      (fun sample ↦
        (siValue sample.innerTemperature, siValue sample.outerTemperature))
      graph
  exact
    existsUnique_exactGraph source.observations
      (fun sample ↦ siValue sample.elapsedTime)
      (fun sample ↦
        (siValue sample.innerTemperature, siValue sample.outerTemperature))

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_2
