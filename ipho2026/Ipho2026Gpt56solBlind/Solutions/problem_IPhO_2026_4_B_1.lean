import Mathlib
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic
import Ipho2026Gpt56solBlind.Shared.ExperimentalGasVapor

/-!
# IPhO 2026 Problem 4, Part B.1

This file models the requested table as the exact, dimensioned record of an
externally supplied cooling-run observation series.  It does not infer,
interpolate, sort, or otherwise invent experimental readings.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_B_1

open Shared
open Shared.ISQDimensions
open Shared.FiniteObservations
open Shared.ExactGraph
open Shared.GasVapor

/-- The externally supplied, ordered temperature--height observations from one
named Part B cooling run. -/
abbrev SourceData (q : ℕ) := HeightTemperatureSeries q

/-- The supplied observations belong to a run prepared according to the stated
experimental procedure.  Nonemptiness and per-occurrence provenance are
already carried by `SourceData`. -/
def MatchesStatement {q : ℕ} (source : SourceData q) : Prop :=
  PreparedCoolingRun source.run

/-- A candidate is the requested B.1 table exactly when each row is the typed
temperature--height pair from the supplied observation at the same index. -/
def IsRequestedHeightTemperatureRecord {q : ℕ} (source : SourceData q)
    (record : IndexedSeries q (Temperature × Length)) : Prop :=
  ExactTable source
    (fun observation ↦
      (observation.observedTemperature, observation.observedHeight))
    record

/-- Every matching supplied cooling series determines exactly one requested
dimensioned temperature--height record. -/
theorem requestedHeightTemperatureRecord_existsUnique (q : ℕ)
    (source : SourceData q) (hMatches : MatchesStatement source) :
    ∃! record : IndexedSeries q (Temperature × Length),
      IsRequestedHeightTemperatureRecord source record := by
  change ∃! record : IndexedSeries q (Temperature × Length),
    ExactTable source
      (fun observation ↦
        (observation.observedTemperature, observation.observedHeight))
      record
  exact
    existsUnique_exactTable source
      (fun observation ↦
        (observation.observedTemperature, observation.observedHeight))

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_B_1
