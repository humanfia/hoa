import Mathlib.Data.Real.Basic
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.ISQDimensions
import Ipho2026Gpt56solBlind.Shared.FiniteObservations
import Ipho2026Gpt56solBlind.Shared.ExactGraph
import Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
import Ipho2026Gpt56solBlind.Shared.FiniteDataAndAffineFit

/-!
# IPhO 2026, Problem 4, Part A.4

This module gives an answer-free specification of the experimental molar gas
constant determined from the observed pressure--temperature graph.  The graph
coordinates are sensor readouts, so the requested experimental value is not
identified with the latent gas constant of the true isochoric run.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_A_4

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.FiniteObservations
open Ipho2026Gpt56solBlind.Shared.ExactGraph
open Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
open Ipho2026Gpt56solBlind.Shared.AffineFit

noncomputable section

/--
The externally supplied A.2 observation series together with the externally
supplied A.3 pressure-versus-temperature graph.  This source datum contains no
fit parameters and no candidate gas constant.
-/
abbrev SourceData (q : ℕ) :=
  PressureTemperatureSeries q × IndexedSeries q (ℝ × ℝ)

/--
The A.3 graph consists exactly of the coherent-SI observed-temperature and
observed-pressure coordinates at the original observation occurrences.
-/
def ObservedPressureTemperatureGraphSolution {q : ℕ}
    (observations : PressureTemperatureSeries q)
    (graph : IndexedSeries q (ℝ × ℝ)) : Prop :=
  ExactGraph observations
    (fun observation ↦
      coordinateInSI SIUnitChoices.SI observation.observedTemperature)
    (fun observation ↦
      coordinateInSI SIUnitChoices.SI observation.observedPressure)
    graph

/--
The supplied run and graph match the Part A.4 experiment.  In particular, the
predictor variation is a primitive condition on the supplied observations,
not a hidden assertion that a fitted pair already exists.
-/
def MatchesStatement {q : ℕ} (source : SourceData q) : Prop :=
  PreparedIsochoricRun source.1.run ∧
    ObservedPressureTemperatureGraphSolution source.1 source.2 ∧
    NondegeneratePredictor
      (AffineData.ofGraph source.1.nonempty source.2)

/--
A typed experimental gas constant is requested when an unweighted affine OLS
fit with intercept satisfies `n * R_exp = V * slope` in coherent SI.  The
predicate neither calibrates the sensors nor equates the candidate with the
latent true gas constant of the run.
-/
def IsRequestedExperimentalGasConstant {q : ℕ} (source : SourceData q)
    (experimentalGasConstant : MolarGasConstant) : Prop :=
  ∃ intercept slope : ℝ,
    IsAffineFit (AffineData.ofGraph source.1.nonempty source.2)
        intercept slope ∧
      coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount *
          coordinateInSI SIUnitChoices.SI experimentalGasConstant =
        coordinateInSI SIUnitChoices.SI
            (confinedAirVolume source.1.run.apparatus) * slope

/--
For matching source data, the requested-candidate predicate may equivalently
be accompanied by the independently established cancellation and predictor
conditions.
-/
lemma requestedExperimentalGasConstant_iff_fitLaw {q : ℕ}
    (source : SourceData q) (hMatches : MatchesStatement source)
    (experimentalGasConstant : MolarGasConstant) :
    IsRequestedExperimentalGasConstant source experimentalGasConstant ↔
      0 < coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount ∧
      0 < coordinateInSI SIUnitChoices.SI
        (confinedAirVolume source.1.run.apparatus) ∧
      NondegeneratePredictor
        (AffineData.ofGraph source.1.nonempty source.2) ∧
      ∃ intercept slope : ℝ,
        IsAffineFit (AffineData.ofGraph source.1.nonempty source.2)
            intercept slope ∧
          coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount *
              coordinateInSI SIUnitChoices.SI experimentalGasConstant =
            coordinateInSI SIUnitChoices.SI
                (confinedAirVolume source.1.run.apparatus) * slope := by
  have hPrepared : PreparedIsochoricRun source.1.run := hMatches.1
  have hAmount :
      0 < coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount :=
    hPrepared.2.2.2.1.2.1
  have hVolume :
      0 < coordinateInSI SIUnitChoices.SI
        (confinedAirVolume source.1.run.apparatus) :=
    confinedAirVolume_positive source.1.run.apparatus hPrepared.1
  have hNondegenerate :
      NondegeneratePredictor
        (AffineData.ofGraph source.1.nonempty source.2) :=
    hMatches.2.2
  constructor
  · intro hRequested
    exact ⟨hAmount, hVolume, hNondegenerate, hRequested⟩
  · rintro ⟨_, _, _, hRequested⟩
    exact hRequested

/--
On matching observed data, the displayed affine normal equations characterize
exactly the global minimizers of the unweighted residual sum of squares.
-/
lemma observedPressureTemperatureFit_iff_isLeastResidual {q : ℕ}
    (source : SourceData q) (hMatches : MatchesStatement source)
    (intercept slope : ℝ) :
    IsAffineFit (AffineData.ofGraph source.1.nonempty source.2)
        intercept slope ↔
      IsLeastResidual (AffineData.ofGraph source.1.nonempty source.2)
        intercept slope := by
  exact
    isAffineFit_iff_isLeastResidual
      (AffineData.ofGraph source.1.nonempty source.2) hMatches.2.2
      intercept slope

/--
Every matching observed graph determines exactly one typed experimental molar
gas constant, without asserting that it equals the latent true constant.
-/
theorem requestedExperimentalGasConstant_existsUnique {q : ℕ}
    (source : SourceData q) (hMatches : MatchesStatement source) :
    ∃! experimentalGasConstant : MolarGasConstant,
      IsRequestedExperimentalGasConstant source experimentalGasConstant := by
  have hPrepared : PreparedIsochoricRun source.1.run := hMatches.1
  have hAmount :
      0 < coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount :=
    hPrepared.2.2.2.1.2.1
  have hAmountNe :
      coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount ≠ 0 :=
    ne_of_gt hAmount
  rcases
      existsUnique_isAffineFit
        (AffineData.ofGraph source.1.nonempty source.2) hMatches.2.2 with
    ⟨pair, hPairFit, hPairUnique⟩
  let candidate : MolarGasConstant :=
    ⟨coordinateInSI SIUnitChoices.SI
          (confinedAirVolume source.1.run.apparatus) * pair.2 /
        coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount⟩
  have hCandidateLaw :
      coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount *
          coordinateInSI SIUnitChoices.SI candidate =
        coordinateInSI SIUnitChoices.SI
            (confinedAirVolume source.1.run.apparatus) * pair.2 := by
    have hAmountValNe : source.1.run.inventory.amount.val ≠ 0 := by
      rw [coordinateInSI_self] at hAmountNe
      exact hAmountNe
    calc
      coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount *
            coordinateInSI SIUnitChoices.SI candidate =
          source.1.run.inventory.amount.val * candidate.val :=
        congrArg₂ (fun x y : ℝ ↦ x * y)
          (coordinateInSI_self source.1.run.inventory.amount)
          (coordinateInSI_self candidate)
      _ = source.1.run.inventory.amount.val *
          (coordinateInSI SIUnitChoices.SI
                (confinedAirVolume source.1.run.apparatus) * pair.2 /
            coordinateInSI SIUnitChoices.SI
              source.1.run.inventory.amount) := by
        dsimp [candidate]
      _ = source.1.run.inventory.amount.val *
          (coordinateInSI SIUnitChoices.SI
                (confinedAirVolume source.1.run.apparatus) * pair.2 /
            source.1.run.inventory.amount.val) := by
        exact congrArg
          (fun denominator : ℝ ↦
            source.1.run.inventory.amount.val *
              (coordinateInSI SIUnitChoices.SI
                    (confinedAirVolume source.1.run.apparatus) * pair.2 /
                denominator))
          (coordinateInSI_self source.1.run.inventory.amount)
      _ = coordinateInSI SIUnitChoices.SI
              (confinedAirVolume source.1.run.apparatus) * pair.2 :=
        mul_div_cancel₀ _ hAmountValNe
  refine ⟨candidate, ?_, ?_⟩
  · exact ⟨pair.1, pair.2, hPairFit, hCandidateLaw⟩
  · intro other hOther
    rcases hOther with ⟨intercept, slope, hFit, hLaw⟩
    have hPairEquality : (intercept, slope) = pair :=
      hPairUnique (intercept, slope) hFit
    have hSlopeEquality : slope = pair.2 :=
      congrArg Prod.snd hPairEquality
    apply
      (coordinateInSI_eq_iff SIUnitChoices.SI other candidate).mp
    apply mul_left_cancel₀ hAmountNe
    calc
      coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount *
            coordinateInSI SIUnitChoices.SI other =
          coordinateInSI SIUnitChoices.SI
              (confinedAirVolume source.1.run.apparatus) * slope := hLaw
      _ = coordinateInSI SIUnitChoices.SI
              (confinedAirVolume source.1.run.apparatus) * pair.2 := by
            rw [hSlopeEquality]
      _ = coordinateInSI SIUnitChoices.SI source.1.run.inventory.amount *
            coordinateInSI SIUnitChoices.SI candidate := hCandidateLaw.symm

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_A_4
