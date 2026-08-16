import Mathlib.Data.Fin.Basic

/-!
# Finite provenanced observations

This module records externally supplied finite observation runs.  Indexing by
`Fin n` retains sampling order and multiplicity: two equal payloads at distinct
indices remain distinct occurrences.  The provenance relation is an input to
the model and does not determine any payload value.
-/

namespace Ipho2026Gpt56solBlind.Shared.FiniteObservations

universe uRun uSample uValue uLeft uRight

/-- A sample family whose `Fin n` index is its sampling order. -/
abbrev IndexedSeries (n : ℕ) (Sample : Type uSample) := Fin n → Sample

/--
A named, nonempty observation run with externally certified provenance at
every sample occurrence.

The index occurs in `Provenance`, so a provenance certificate can distinguish
equal payloads recorded at different positions in the run.
-/
structure ObservationSeries (n : ℕ) (RunId : Type uRun) (Sample : Type uSample)
    (Provenance : RunId → Fin n → Sample → Prop) where
  nonempty : 0 < n
  run : RunId
  samples : IndexedSeries n Sample
  hasProvenance : ∀ i, Provenance run i (samples i)

/-- Apply a payload map without changing the observation index. -/
def canonicalMap {n : ℕ} {RunId : Type uRun} {Sample : Type uSample}
    {Value : Type uValue} {Provenance : RunId → Fin n → Sample → Prop}
    (observations : ObservationSeries n RunId Sample Provenance)
    (f : Sample → Value) : IndexedSeries n Value :=
  fun i => f (observations.samples i)

/--
Apply two coordinate maps to each common sample occurrence, without sorting or
deduplicating the resulting pairs.
-/
def canonicalPairedMap {n : ℕ} {RunId : Type uRun} {Sample : Type uSample}
    {Left : Type uLeft} {Right : Type uRight}
    {Provenance : RunId → Fin n → Sample → Prop}
    (observations : ObservationSeries n RunId Sample Provenance)
    (left : Sample → Left) (right : Sample → Right) :
    IndexedSeries n (Left × Right) :=
  fun i => (canonicalMap observations left i, canonicalMap observations right i)

end Ipho2026Gpt56solBlind.Shared.FiniteObservations
