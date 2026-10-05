import Mathlib
import Ipho2026Gpt56solBlind.Shared.RefrigeratorCycle
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, Problem 3, Part C.4

This file gives an answer-free specification of the operating time needed for
constant-power Carnot cooling.  The requested time is characterized by the
existence of a regular continuous cooling history satisfying the local Carnot,
first-law, constant-power, and constant-heat-capacity equations from the shared
model.
-/

noncomputable section

open scoped Interval

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_3_C_4

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics
open Ipho2026Gpt56solBlind.Shared.RefrigeratorCycle

/-- The source data for C.4: a constant-power cooling protocol and the two
endpoint temperatures.  In particular, no elapsed time is stored here. -/
structure SourceData where
  protocol : CoolingProtocol
  initialTemperature : Temperature
  finalTemperature : Temperature

/-- The physical and ordering assumptions stated for the cooling experiment.
All inequalities are compared in the protocol's common coherent-SI
coordinate. -/
def MatchesStatement (S : SourceData) : Prop :=
  S.protocol.IsPhysical ∧
    0 < coherentCoordinate S.protocol.unitSystem S.finalTemperature ∧
    coherentCoordinate S.protocol.unitSystem S.finalTemperature <
      coherentCoordinate S.protocol.unitSystem S.initialTemperature ∧
    coherentCoordinate S.protocol.unitSystem S.initialTemperature <
      coherentCoordinate S.protocol.unitSystem
        S.protocol.hotReservoirTemperature

/-- A candidate is a requested elapsed time precisely when it is positive and
is realized by a regular continuous history obeying the governing cooling
laws with the prescribed endpoints. -/
def IsRequestedElapsedTime (S : SourceData) (tau : Time) : Prop :=
  IsElapsedTimeSolution S.protocol S.initialTemperature S.finalTemperature tau

/-- The requested-time predicate is characterized by the separated governing
equation, with its physical integral deliberately left unevaluated. -/
theorem requestedElapsedTime_iff_integral (S : SourceData)
    (hS : MatchesStatement S) (tau : Time) :
    IsRequestedElapsedTime S tau ↔
      0 < coherentCoordinate S.protocol.unitSystem tau ∧
      coherentCoordinate S.protocol.unitSystem S.protocol.inputPower *
          coherentCoordinate S.protocol.unitSystem tau =
        coherentCoordinate S.protocol.unitSystem
            S.protocol.coldBodyHeatCapacity *
          ∫ x in coherentCoordinate S.protocol.unitSystem S.finalTemperature..
              coherentCoordinate S.protocol.unitSystem S.initialTemperature,
            (coherentCoordinate S.protocol.unitSystem
                S.protocol.hotReservoirTemperature - x) / x := by
  exact elapsedTime_solution_characterization S.protocol
    S.initialTemperature S.finalTemperature tau hS.1 hS.2

/-- Every source datum matching C.4 determines exactly one dimensioned
elapsed time through the governing-history predicate. -/
theorem requestedElapsedTime_existsUnique (S : SourceData)
    (hS : MatchesStatement S) :
    ∃! tau : Time, IsRequestedElapsedTime S tau := by
  exact elapsedTime_existsUnique S.protocol S.initialTemperature
    S.finalTemperature hS.1 hS.2

end Ipho2026Gpt56solBlind.ProblemIPhO2026_3_C_4
