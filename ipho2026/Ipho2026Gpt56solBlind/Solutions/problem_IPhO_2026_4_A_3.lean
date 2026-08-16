import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.ExactGraph
import Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
import Ipho2026Gpt56solBlind.Shared.ISQDimensions

/-!
# IPhO 2026 Problem 4, Part A.3

This file gives an answer-free specification of the pressure--temperature
graph requested from the externally supplied Part A.2 observations.  The
graph is the exact occurrence-preserving indexed graph of the observed
temperature and pressure coordinates in coherent SI; no calibration,
sorting, interpolation, or fit is imposed.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_A_3

open Ipho2026Gpt56solBlind.Shared.ExactGraph
open Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
open Ipho2026Gpt56solBlind.Shared.ISQDimensions

noncomputable section

/--
The Part A.2 pressure--temperature observations supplied to the graphing
task.  Their run, order, multiplicity, and per-occurrence provenance are
carried by `PressureTemperatureSeries`.
-/
structure SourceData (q : ℕ) where
  observations : PressureTemperatureSeries q

/-- The supplied observations come from a prepared Part A isochoric run. -/
def MatchesStatement {q : ℕ} (source : SourceData q) : Prop :=
  PreparedIsochoricRun source.observations.run

/--
A candidate is the requested graph exactly when each point consists of the
coherent-SI temperature and pressure readings from the same supplied
observation occurrence.
-/
def IsRequestedPressureTemperatureGraph {q : ℕ} (source : SourceData q)
    (graph : Fin q → ℝ × ℝ) : Prop :=
  ExactGraph source.observations
    (fun observation ↦
      coordinateInSI SIUnitChoices.SI observation.observedTemperature)
    (fun observation ↦
      coordinateInSI SIUnitChoices.SI observation.observedPressure)
    graph

/-- The requested-graph predicate is precisely the generic exact graph. -/
lemma requestedPressureTemperatureGraph_iff_exactGraph {q : ℕ}
    (source : SourceData q) (_hMatches : MatchesStatement source)
    (graph : Fin q → ℝ × ℝ) :
    IsRequestedPressureTemperatureGraph source graph ↔
      ExactGraph source.observations
        (fun observation ↦
          coordinateInSI SIUnitChoices.SI observation.observedTemperature)
        (fun observation ↦
          coordinateInSI SIUnitChoices.SI observation.observedPressure)
        graph := by
  rfl

/-- Matching source data determine exactly one requested indexed graph. -/
theorem requestedPressureTemperatureGraph_existsUnique {q : ℕ}
    (source : SourceData q) (_hMatches : MatchesStatement source) :
    ∃! graph : Fin q → ℝ × ℝ,
      IsRequestedPressureTemperatureGraph source graph := by
  change ∃! graph : Fin q → ℝ × ℝ,
    ExactGraph source.observations
      (fun observation ↦
        coordinateInSI SIUnitChoices.SI observation.observedTemperature)
      (fun observation ↦
        coordinateInSI SIUnitChoices.SI observation.observedPressure)
      graph
  exact
    existsUnique_exactGraph source.observations
      (fun observation ↦
        coordinateInSI SIUnitChoices.SI observation.observedTemperature)
      (fun observation ↦
        coordinateInSI SIUnitChoices.SI observation.observedPressure)

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_A_3
