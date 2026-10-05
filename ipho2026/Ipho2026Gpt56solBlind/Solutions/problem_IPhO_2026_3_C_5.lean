import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic
import Ipho2026Gpt56solBlind.Shared.RefrigeratorCycle

/-!
# IPhO 2026 Problem 3, part C.5

This file gives an answer-free model of the overall coefficient of performance
of the continuously operated Carnot refrigerator.  A candidate coefficient is
characterized by the cumulative cold heat and cumulative input work of a full
cooling history; no evaluated coefficient is included in the source data or in
the target theorem's signature.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_3_C_5

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics
open Ipho2026Gpt56solBlind.Shared.RefrigeratorCycle

/-- The data supplied by C.5 and its natural-language C.4 prerequisite.
Elapsed time, transfer histories, cumulative transfers, and COP are outputs,
not fields of this structure. -/
structure SourceData where
  protocol : CoolingProtocol
  initialTemperature : Temperature
  finalTemperature : Temperature

/-- The protocol is nondegenerate and the cooling endpoints form a nonempty
positive-temperature interval lying below the fixed hot reservoir. -/
def MatchesStatement (S : SourceData) : Prop :=
  S.protocol.IsPhysical ∧
  0 < coherentCoordinate S.protocol.unitSystem S.finalTemperature ∧
  coherentCoordinate S.protocol.unitSystem S.finalTemperature <
    coherentCoordinate S.protocol.unitSystem S.initialTemperature ∧
  coherentCoordinate S.protocol.unitSystem S.initialTemperature <
    coherentCoordinate S.protocol.unitSystem
      S.protocol.hotReservoirTemperature

/-- A full history starts at the prescribed initial temperature, finishes at
the prescribed final temperature, obeys the constant-power Carnot cooling
laws, and has positive duration. -/
def IsFullCoolingHistory (S : SourceData)
    (H : ContinuousCoolingHistory) : Prop :=
  0 < coherentCoordinate H.unitSystem H.duration ∧
  SatisfiesCoolingProtocol S.protocol H ∧
  HasCoolingEndpoints H S.initialTemperature S.finalTemperature

/-- Answer-free characterization of the requested overall COP.  The equation
uses the cumulative transfers over the entire positive-duration history and
is cross-multiplied so that no denominator is used before work positivity is
established. -/
def IsRequestedOverallCOP (S : SourceData) (κ : ℝ) : Prop :=
  ∃ H : ContinuousCoolingHistory,
    IsFullCoolingHistory S H ∧
    κ * coherentCoordinate H.unitSystem
          (continuousCumulativeWork H
            (coherentCoordinate H.unitSystem H.duration)) =
      coherentCoordinate H.unitSystem
        (continuousCumulativeColdHeat H
          (coherentCoordinate H.unitSystem H.duration))

/-- The duration of a full history is an elapsed-time solution for the same
protocol and endpoints. -/
lemma fullCoolingHistory_isElapsedTimeSolution (S : SourceData)
    (H : ContinuousCoolingHistory) (hH : IsFullCoolingHistory S H) :
    IsElapsedTimeSolution S.protocol S.initialTemperature
      S.finalTemperature H.duration := by
  rcases hH with ⟨hDuration, hSatisfies, hEndpoints⟩
  have hUnits : H.unitSystem = S.protocol.unitSystem := hSatisfies.2.1
  refine ⟨?_, H, rfl, hSatisfies, hEndpoints⟩
  simpa only [hUnits] using hDuration

/-- On a full history, cumulative work is constant input power times elapsed
time, expressed in coherent-SI coordinates. -/
lemma fullCoolingHistory_workCoordinate (S : SourceData)
    (H : ContinuousCoolingHistory) (hH : IsFullCoolingHistory S H) :
    coherentCoordinate H.unitSystem
        (continuousCumulativeWork H
          (coherentCoordinate H.unitSystem H.duration)) =
      coherentCoordinate S.protocol.unitSystem S.protocol.inputPower *
        coherentCoordinate H.unitSystem H.duration := by
  rcases hH with ⟨hDuration, hSatisfies, _⟩
  rcases hSatisfies with ⟨_, _, _, _, hLaws⟩
  have hIntegral :
      (∫ r in (0 : ℝ)..coherentCoordinate H.unitSystem H.duration,
          coherentCoordinate H.unitSystem (H.workRate r)) =
        ∫ _r in (0 : ℝ)..coherentCoordinate H.unitSystem H.duration,
          coherentCoordinate S.protocol.unitSystem S.protocol.inputPower := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le hDuration.le] at hr
    exact (hLaws r hr).2.2.1
  simp only [continuousCumulativeWork,
    coherentCoordinate_quantityFromCoherentCoordinate]
  rw [hIntegral]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

/-- On a full history, cumulative cold heat is the constant body heat
capacity times the prescribed temperature decrease. -/
lemma fullCoolingHistory_coldHeatCoordinate (S : SourceData)
    (H : ContinuousCoolingHistory) (hH : IsFullCoolingHistory S H) :
    coherentCoordinate H.unitSystem
        (continuousCumulativeColdHeat H
          (coherentCoordinate H.unitSystem H.duration)) =
      coherentCoordinate S.protocol.unitSystem
          S.protocol.coldBodyHeatCapacity *
        (coherentCoordinate S.protocol.unitSystem S.initialTemperature -
          coherentCoordinate S.protocol.unitSystem S.finalTemperature) := by
  rcases hH with ⟨_, hSatisfies, hEndpoints⟩
  have hUnits : H.unitSystem = S.protocol.unitSystem := hSatisfies.2.1
  rcases hSatisfies with
    ⟨_, _, hDurationNonnegative,
      ⟨_, _, hInterval, hTemperatureSmooth, _, _, _⟩, hLaws⟩
  let duration := coherentCoordinate H.unitSystem H.duration
  let temperature : ℝ → ℝ := fun r =>
    coherentCoordinate H.unitSystem (H.temperature r)
  let capacity := coherentCoordinate S.protocol.unitSystem
    S.protocol.coldBodyHeatCapacity
  have hTemperatureSmooth' :
      ContDiffOn ℝ 1 temperature (Set.Icc 0 duration) := by
    exact hTemperatureSmooth.mono hInterval
  have hFundamental :
      (∫ r in (0 : ℝ)..duration, deriv temperature r) =
        temperature duration - temperature 0 :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc
      hTemperatureSmooth' hDurationNonnegative
  have hColdIntegral :
      (∫ r in (0 : ℝ)..duration,
          coherentCoordinate H.unitSystem (H.coldHeatRate r)) =
        ∫ r in (0 : ℝ)..duration, -capacity * deriv temperature r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le hDurationNonnegative] at hr
    have hEnergyLaw := (hLaws r hr).2.2.2.2.2.2.2
    dsimp [capacity, temperature] at hEnergyLaw ⊢
    linarith
  simp only [continuousCumulativeColdHeat,
    coherentCoordinate_quantityFromCoherentCoordinate]
  rw [hColdIntegral, intervalIntegral.integral_const_mul, hFundamental]
  dsimp [duration, temperature, capacity]
  rw [hEndpoints.2, hEndpoints.1, hUnits]
  ring

/-- Any two full histories for one matching source have the same duration and
the same full-duration cumulative transfers. -/
lemma fullCoolingHistory_transfersInvariant (S : SourceData)
    (hS : MatchesStatement S)
    (H₁ H₂ : ContinuousCoolingHistory)
    (hH₁ : IsFullCoolingHistory S H₁)
    (hH₂ : IsFullCoolingHistory S H₂) :
    H₁.duration = H₂.duration ∧
      continuousCumulativeWork H₁
          (coherentCoordinate H₁.unitSystem H₁.duration) =
        continuousCumulativeWork H₂
          (coherentCoordinate H₂.unitSystem H₂.duration) ∧
      continuousCumulativeColdHeat H₁
          (coherentCoordinate H₁.unitSystem H₁.duration) =
        continuousCumulativeColdHeat H₂
          (coherentCoordinate H₂.unitSystem H₂.duration) := by
  rcases hS with
    ⟨hPhysical, hFinalPositive, hFinalInitial, hInitialHot⟩
  have hSolution₁ :=
    fullCoolingHistory_isElapsedTimeSolution S H₁ hH₁
  have hSolution₂ :=
    fullCoolingHistory_isElapsedTimeSolution S H₂ hH₂
  obtain ⟨τ, _, hUnique⟩ :=
    elapsedTime_existsUnique S.protocol S.initialTemperature
      S.finalTemperature hPhysical
      ⟨hFinalPositive, hFinalInitial, hInitialHot⟩
  have hDuration : H₁.duration = H₂.duration :=
    (hUnique H₁.duration hSolution₁).trans
      (hUnique H₂.duration hSolution₂).symm
  have hUnits₁ : H₁.unitSystem = S.protocol.unitSystem :=
    (hH₁.2.1).2.1
  have hUnits₂ : H₂.unitSystem = S.protocol.unitSystem :=
    (hH₂.2.1).2.1
  have hWorkCoordinate :
      coherentCoordinate H₁.unitSystem
          (continuousCumulativeWork H₁
            (coherentCoordinate H₁.unitSystem H₁.duration)) =
        coherentCoordinate H₂.unitSystem
          (continuousCumulativeWork H₂
            (coherentCoordinate H₂.unitSystem H₂.duration)) := by
    rw [fullCoolingHistory_workCoordinate S H₁ hH₁,
      fullCoolingHistory_workCoordinate S H₂ hH₂]
    rw [hUnits₁, hUnits₂, hDuration]
  have hWorkCoordinate' :
      coherentCoordinate S.protocol.unitSystem
          (continuousCumulativeWork H₁
            (coherentCoordinate H₁.unitSystem H₁.duration)) =
        coherentCoordinate S.protocol.unitSystem
          (continuousCumulativeWork H₂
            (coherentCoordinate H₂.unitSystem H₂.duration)) := by
    simpa only [hUnits₁, hUnits₂] using hWorkCoordinate
  have hWork :
      continuousCumulativeWork H₁
          (coherentCoordinate H₁.unitSystem H₁.duration) =
        continuousCumulativeWork H₂
          (coherentCoordinate H₂.unitSystem H₂.duration) :=
    (coordinateInSI_eq_iff S.protocol.unitSystem _ _).mp hWorkCoordinate'
  have hColdCoordinate :
      coherentCoordinate H₁.unitSystem
          (continuousCumulativeColdHeat H₁
            (coherentCoordinate H₁.unitSystem H₁.duration)) =
        coherentCoordinate H₂.unitSystem
          (continuousCumulativeColdHeat H₂
            (coherentCoordinate H₂.unitSystem H₂.duration)) := by
    rw [fullCoolingHistory_coldHeatCoordinate S H₁ hH₁,
      fullCoolingHistory_coldHeatCoordinate S H₂ hH₂]
  have hColdCoordinate' :
      coherentCoordinate S.protocol.unitSystem
          (continuousCumulativeColdHeat H₁
            (coherentCoordinate H₁.unitSystem H₁.duration)) =
        coherentCoordinate S.protocol.unitSystem
          (continuousCumulativeColdHeat H₂
            (coherentCoordinate H₂.unitSystem H₂.duration)) := by
    simpa only [hUnits₁, hUnits₂] using hColdCoordinate
  have hCold :
      continuousCumulativeColdHeat H₁
          (coherentCoordinate H₁.unitSystem H₁.duration) =
        continuousCumulativeColdHeat H₂
          (coherentCoordinate H₂.unitSystem H₂.duration) :=
    (coordinateInSI_eq_iff S.protocol.unitSystem _ _).mp hColdCoordinate'
  exact ⟨hDuration, hWork, hCold⟩

/-- Scaling the positive capacity and power of a protocol does not change the
requested overall COP when the initial, final, and hot temperatures agree in
coherent SI.  Each temperature is interpreted through its own protocol's unit
system; the unit systems and raw dimensioned values need not be equal. -/
theorem requestedOverallCOP_protocolInvariant
    (S₁ S₂ : SourceData)
    (hS₁ : MatchesStatement S₁) (hS₂ : MatchesStatement S₂)
    (hInitial :
      coherentCoordinate S₁.protocol.unitSystem S₁.initialTemperature =
        coherentCoordinate S₂.protocol.unitSystem S₂.initialTemperature)
    (hFinal :
      coherentCoordinate S₁.protocol.unitSystem S₁.finalTemperature =
        coherentCoordinate S₂.protocol.unitSystem S₂.finalTemperature)
    (hHot :
      coherentCoordinate S₁.protocol.unitSystem
          S₁.protocol.hotReservoirTemperature =
        coherentCoordinate S₂.protocol.unitSystem
          S₂.protocol.hotReservoirTemperature)
    (κ₁ κ₂ : ℝ)
    (hκ₁ : IsRequestedOverallCOP S₁ κ₁)
    (hκ₂ : IsRequestedOverallCOP S₂ κ₂) :
    κ₁ = κ₂ := by
  rcases hS₁ with
    ⟨hPhysical₁, hFinalPositive₁, hFinalInitial₁, hInitialHot₁⟩
  rcases hS₂ with
    ⟨hPhysical₂, hFinalPositive₂, hFinalInitial₂, hInitialHot₂⟩
  rcases hκ₁ with ⟨H₁, hFull₁, hCandidate₁⟩
  rcases hκ₂ with ⟨H₂, hFull₂, hCandidate₂⟩
  have hUnits₁ : H₁.unitSystem = S₁.protocol.unitSystem :=
    (hFull₁.2.1).2.1
  have hUnits₂ : H₂.unitSystem = S₂.protocol.unitSystem :=
    (hFull₂.2.1).2.1
  let work₁ := coherentCoordinate H₁.unitSystem
    (continuousCumulativeWork H₁
      (coherentCoordinate H₁.unitSystem H₁.duration))
  let work₂ := coherentCoordinate H₂.unitSystem
    (continuousCumulativeWork H₂
      (coherentCoordinate H₂.unitSystem H₂.duration))
  let cold₁ := coherentCoordinate H₁.unitSystem
    (continuousCumulativeColdHeat H₁
      (coherentCoordinate H₁.unitSystem H₁.duration))
  let cold₂ := coherentCoordinate H₂.unitSystem
    (continuousCumulativeColdHeat H₂
      (coherentCoordinate H₂.unitSystem H₂.duration))
  let capacity₁ := coherentCoordinate S₁.protocol.unitSystem
    S₁.protocol.coldBodyHeatCapacity
  let capacity₂ := coherentCoordinate S₂.protocol.unitSystem
    S₂.protocol.coldBodyHeatCapacity
  let elapsedIntegral₁ :=
    ∫ x in coherentCoordinate S₁.protocol.unitSystem S₁.finalTemperature..
        coherentCoordinate S₁.protocol.unitSystem S₁.initialTemperature,
      (coherentCoordinate S₁.protocol.unitSystem
          S₁.protocol.hotReservoirTemperature - x) / x
  let elapsedIntegral₂ :=
    ∫ x in coherentCoordinate S₂.protocol.unitSystem S₂.finalTemperature..
        coherentCoordinate S₂.protocol.unitSystem S₂.initialTemperature,
      (coherentCoordinate S₂.protocol.unitSystem
          S₂.protocol.hotReservoirTemperature - x) / x
  have hElapsed₁ :=
    elapsedTime_integral_of_history S₁.protocol S₁.initialTemperature
      S₁.finalTemperature H₁.duration
      (fullCoolingHistory_isElapsedTimeSolution S₁ H₁ hFull₁)
      ⟨hFinalPositive₁, hFinalInitial₁, hInitialHot₁⟩
  have hElapsed₂ :=
    elapsedTime_integral_of_history S₂.protocol S₂.initialTemperature
      S₂.finalTemperature H₂.duration
      (fullCoolingHistory_isElapsedTimeSolution S₂ H₂ hFull₂)
      ⟨hFinalPositive₂, hFinalInitial₂, hInitialHot₂⟩
  have hWorkIntegral₁ : work₁ = capacity₁ * elapsedIntegral₁ := by
    dsimp [work₁, capacity₁, elapsedIntegral₁]
    rw [fullCoolingHistory_workCoordinate S₁ H₁ hFull₁, hUnits₁]
    exact hElapsed₁
  have hWorkIntegral₂ : work₂ = capacity₂ * elapsedIntegral₂ := by
    dsimp [work₂, capacity₂, elapsedIntegral₂]
    rw [fullCoolingHistory_workCoordinate S₂ H₂ hFull₂, hUnits₂]
    exact hElapsed₂
  have hElapsedIntegral : elapsedIntegral₁ = elapsedIntegral₂ := by
    dsimp [elapsedIntegral₁, elapsedIntegral₂]
    rw [hFinal, hInitial, hHot]
  have hWorkScale : capacity₂ * work₁ = capacity₁ * work₂ := by
    rw [hWorkIntegral₁, hWorkIntegral₂, hElapsedIntegral]
    ring
  have hColdFormula₁ :
      cold₁ = capacity₁ *
        (coherentCoordinate S₁.protocol.unitSystem S₁.initialTemperature -
          coherentCoordinate S₁.protocol.unitSystem S₁.finalTemperature) := by
    simpa only [cold₁, capacity₁] using
      fullCoolingHistory_coldHeatCoordinate S₁ H₁ hFull₁
  have hColdFormula₂ :
      cold₂ = capacity₂ *
        (coherentCoordinate S₂.protocol.unitSystem S₂.initialTemperature -
          coherentCoordinate S₂.protocol.unitSystem S₂.finalTemperature) := by
    simpa only [cold₂, capacity₂] using
      fullCoolingHistory_coldHeatCoordinate S₂ H₂ hFull₂
  have hColdScale : capacity₂ * cold₁ = capacity₁ * cold₂ := by
    rw [hColdFormula₁, hColdFormula₂, hInitial, hFinal]
    ring
  have hCandidate₁' : κ₁ * work₁ = cold₁ := by
    simpa only [work₁, cold₁] using hCandidate₁
  have hCandidate₂' : κ₂ * work₂ = cold₂ := by
    simpa only [work₂, cold₂] using hCandidate₂
  have hCapacityPositive₁ : 0 < capacity₁ := by
    exact hPhysical₁.1
  have hWorkPositive₂ : 0 < work₂ := by
    exact continuousCumulativeWork_pos S₂.protocol H₂ hFull₂.2.1
      (coherentCoordinate H₂.unitSystem H₂.duration)
      ⟨hFull₂.1, le_rfl⟩
  have hScaled :
      κ₁ * (capacity₁ * work₂) =
        κ₂ * (capacity₁ * work₂) := by
    calc
      κ₁ * (capacity₁ * work₂) =
          κ₁ * (capacity₂ * work₁) := by rw [hWorkScale]
      _ = capacity₂ * (κ₁ * work₁) := by ring
      _ = capacity₂ * cold₁ := by rw [hCandidate₁']
      _ = capacity₁ * cold₂ := hColdScale
      _ = capacity₁ * (κ₂ * work₂) := by rw [hCandidate₂']
      _ = κ₂ * (capacity₁ * work₂) := by ring
  exact mul_right_cancel₀
    (ne_of_gt (mul_pos hCapacityPositive₁ hWorkPositive₂)) hScaled

/-- A matching source determines exactly one cumulative, full-history
coefficient of performance. -/
theorem requestedOverallCOP_existsUnique (S : SourceData)
    (hS : MatchesStatement S) :
    ∃! κ : ℝ, IsRequestedOverallCOP S κ := by
  obtain ⟨τ, hSolution, _⟩ :=
    elapsedTime_existsUnique S.protocol S.initialTemperature
      S.finalTemperature hS.1
      ⟨hS.2.1, hS.2.2.1, hS.2.2.2⟩
  rcases hSolution with
    ⟨hTimePositive, H, hDuration, hSatisfies, hEndpoints⟩
  have hUnits : H.unitSystem = S.protocol.unitSystem := hSatisfies.2.1
  have hDurationPositive :
      0 < coherentCoordinate H.unitSystem H.duration := by
    rw [hDuration, hUnits]
    exact hTimePositive
  have hFull : IsFullCoolingHistory S H :=
    ⟨hDurationPositive, hSatisfies, hEndpoints⟩
  let work := coherentCoordinate H.unitSystem
    (continuousCumulativeWork H
      (coherentCoordinate H.unitSystem H.duration))
  let cold := coherentCoordinate H.unitSystem
    (continuousCumulativeColdHeat H
      (coherentCoordinate H.unitSystem H.duration))
  have hWorkPositive : 0 < work := by
    exact continuousCumulativeWork_pos S.protocol H hSatisfies
      (coherentCoordinate H.unitSystem H.duration)
      ⟨hDurationPositive, le_rfl⟩
  have hWorkNonzero : work ≠ 0 := ne_of_gt hWorkPositive
  have hRequested : IsRequestedOverallCOP S (cold / work) := by
    refine ⟨H, hFull, ?_⟩
    exact div_mul_cancel₀ cold hWorkNonzero
  refine ⟨cold / work, hRequested, ?_⟩
  intro κ hκ
  rcases hκ with ⟨H₂, hFull₂, hCandidate⟩
  have hUnits₂ : H₂.unitSystem = S.protocol.unitSystem :=
    (hFull₂.2.1).2.1
  rcases fullCoolingHistory_transfersInvariant S hS H₂ H hFull₂ hFull with
    ⟨_, hWorkEqual, hColdEqual⟩
  have hCandidate' : κ * work = cold := by
    rw [hWorkEqual, hColdEqual] at hCandidate
    rw [hUnits₂] at hCandidate
    simpa only [work, cold, hUnits] using hCandidate
  exact (eq_div_iff hWorkNonzero).2 hCandidate'

end Ipho2026Gpt56solBlind.ProblemIPhO2026_3_C_5
