import Mathlib.Data.Real.Basic
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.ExactGraph
import Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

/-!
# IPhO 2026 Problem 4, Part C.3

This file formalizes the requested pair of temperature-difference traces from
one finite, provenanced Part-C observation series.  Both plotted points at an
index are computed from the same recorded occurrence, so sampling order,
repetitions, and multiplicity are retained.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_3

open Ipho2026Gpt56solBlind.Shared.ExactGraph
open Ipho2026Gpt56solBlind.Shared.FiniteObservations
open Ipho2026Gpt56solBlind.Shared.RadialConductionCore
open Ipho2026Gpt56solBlind.Shared.RadialHeatFlow

noncomputable section

/-- The one common finite record of elapsed time and both temperatures supplied
by Part C.1. -/
abbrev SourceData (q : ℕ) := RadialObservationSeries q

/-- Agreement of the observations with the prepared Part-C run, together with
the separately scoped C.3/C.4 apparatus-capacity idealization. -/
def MatchesStatement {q : ℕ} (observations : SourceData q)
    (context : CapacityContext) : Prop :=
  PreparedFigure17PartCRadialRun observations.run ∧
    (∀ i : Fin q,
      Figure17PartCObservationProvenance observations.run i
        (observations.samples i)) ∧
    C3C4ApparatusCapacityIdealization context

/-- The point of the temperature-difference trace whose horizontal coordinate
is the outer-cylinder temperature. -/
def outerDifferencePoint (sample : TemperatureSample) : ℝ × ℝ :=
  (siValue sample.outerTemperature,
    siValue sample.outerTemperature - siValue sample.innerTemperature)

/-- The point of the temperature-difference trace whose horizontal coordinate
is the inner-cylinder temperature. -/
def innerDifferencePoint (sample : TemperatureSample) : ℝ × ℝ :=
  (siValue sample.innerTemperature,
    siValue sample.outerTemperature - siValue sample.innerTemperature)

/-- A graph is the requested common-axis graph exactly when it is the canonical
paired map of the two point constructors over the common observation series. -/
def IsRequestedDualTraceGraph {q : ℕ} (observations : SourceData q)
    (graph : IndexedSeries q ((ℝ × ℝ) × (ℝ × ℝ))) : Prop :=
  ExactGraph observations outerDifferencePoint innerDifferencePoint graph

/-- Pointwise coordinate characterization of the exact dual-trace graph. -/
lemma isRequestedDualTraceGraph_iff_coordinates {q : ℕ}
    (observations : SourceData q)
    (graph : IndexedSeries q ((ℝ × ℝ) × (ℝ × ℝ))) :
    IsRequestedDualTraceGraph observations graph ↔
      ∀ i : Fin q,
        graph i =
          ((siValue (observations.samples i).outerTemperature,
              siValue (observations.samples i).outerTemperature -
                siValue (observations.samples i).innerTemperature),
            (siValue (observations.samples i).innerTemperature,
              siValue (observations.samples i).outerTemperature -
                siValue (observations.samples i).innerTemperature)) := by
  constructor
  · intro hGraph i
    have hAtIndex := congrFun hGraph i
    exact hAtIndex
  · intro hCoordinates
    change graph = canonicalPairedMap observations outerDifferencePoint
      innerDifferencePoint
    funext i
    exact hCoordinates i

/-- The C.3/C.4 idealization zeroes only its modeled apparatus contribution;
both water capacities remain positive and the physical apparatus capacity
remains nonnegative. -/
lemma matchesStatement_capacityScope {q : ℕ}
    (observations : SourceData q) (context : CapacityContext)
    (hMatches : MatchesStatement observations context) :
    0 < siValue (innerWaterHeatCapacity context.innerWaterGeometry) ∧
      0 < siValue context.outerWaterHeatCapacity ∧
      0 ≤ siValue context.physicalApparatusHeatCapacity ∧
      siValue context.c3c4ModeledApparatusHeatCapacity = 0 := by
  exact c3c4Idealization_capacity_scope context hMatches.2.2

/-- The supplied common observation series determines exactly one requested
paired graph. -/
theorem requestedDualTraceGraph_existsUnique {q : ℕ}
    (observations : SourceData q) (context : CapacityContext)
    (hMatches : MatchesStatement observations context) :
    ∃! graph : IndexedSeries q ((ℝ × ℝ) × (ℝ × ℝ)),
      IsRequestedDualTraceGraph observations graph := by
  exact existsUnique_exactGraph observations outerDifferencePoint innerDifferencePoint

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_C_3
