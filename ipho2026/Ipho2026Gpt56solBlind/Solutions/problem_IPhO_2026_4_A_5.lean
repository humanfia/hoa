import Mathlib.Data.Real.Basic
import Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
import Ipho2026Gpt56solBlind.Shared.FiniteDataAndAffineFit
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026 Problem 4 A.5: thermal pressure coefficient

This file gives an answer-blind specification of the requested constant-volume
thermal pressure coefficient.  The experimental observations and their
designated graph are external inputs.  The requested coefficient is selected
by an unweighted affine ordinary-least-squares fit to that exact graph and by
the defining pressure-times-coefficient law; no fitted or evaluated answer is
stored in the source data.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_A_5

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.FiniteObservations
open Ipho2026Gpt56solBlind.Shared.ExactGraph
open Ipho2026Gpt56solBlind.Shared.AffineFit
open Ipho2026Gpt56solBlind.Shared.Figure17Apparatus

noncomputable section

/-- The thermal pressure coefficient has inverse-temperature dimension. -/
def thermalPressureCoefficientDimension : Dimension ISQDimensionBase :=
  temperatureDimension⁻¹

/-- Typed candidates for the constant-volume thermal pressure coefficient. -/
abbrev ThermalPressureCoefficient :=
  Quantity thermalPressureCoefficientDimension

/-- Multiplying pressure by a thermal pressure coefficient gives the
pressure-per-temperature dimension of a pressure-on-temperature slope. -/
lemma pressure_mul_thermalPressureCoefficient_dimension :
    pressureDimension * thermalPressureCoefficientDimension =
      pressureDimension * temperatureDimension⁻¹ := by
  rfl

/-- Externally supplied observations, their designated coherent-SI graph, and
the typed reference state.  No fit parameter or requested coefficient occurs
in this record. -/
structure SourceData (q : ℕ) where
  observations : PressureTemperatureSeries q
  observedGraph : IndexedSeries q (ℝ × ℝ)
  referenceTemperature : Temperature
  referencePressure : Pressure

/-- The designated graph is exactly the occurrence-preserving coherent-SI
temperature-pressure graph of the supplied observations. -/
def ObservedPressureTemperatureGraphSolution {q : ℕ}
    (source : SourceData q) : Prop :=
  ExactGraph source.observations
    (fun observation ↦
      coordinateInSI SIUnitChoices.SI observation.observedTemperature)
    (fun observation ↦
      coordinateInSI SIUnitChoices.SI observation.observedPressure)
    source.observedGraph

/-- Ordered affine data obtained by projecting the fixed graph coordinates.
The observation-series nonemptiness supplies the data nonemptiness proof. -/
def SourceData.affineData {q : ℕ} (source : SourceData q) : AffineData q :=
  AffineData.ofGraph source.observations.nonempty source.observedGraph

/-- The supplied run and reference state agree with the fixed-volume A.5
setup, the graph is exact, and the observed temperatures are nondegenerate for
an affine fit.  The reference coordinates are in kelvin and pascals. -/
def MatchesStatement {q : ℕ} (source : SourceData q) : Prop :=
  PreparedIsochoricRun source.observations.run ∧
    ObservedPressureTemperatureGraphSolution source ∧
    NondegeneratePredictor source.affineData ∧
    0 < coordinateInSI SIUnitChoices.SI source.referenceTemperature ∧
    0 < coordinateInSI SIUnitChoices.SI source.referencePressure ∧
    coordinateInSI SIUnitChoices.SI source.referenceTemperature = 273.15 ∧
    coordinateInSI SIUnitChoices.SI source.referencePressure = 101300

/-- A candidate is requested exactly when some unweighted affine OLS fit to
the observed graph has slope equal to reference pressure times the candidate's
coherent-SI inverse-temperature coordinate. -/
def IsRequestedThermalPressureCoefficient {q : ℕ}
    (source : SourceData q) (coefficient : ThermalPressureCoefficient) : Prop :=
  ∃ intercept slope : ℝ,
    IsAffineFit source.affineData intercept slope ∧
      coordinateInSI SIUnitChoices.SI source.referencePressure *
          coordinateInSI SIUnitChoices.SI coefficient =
        slope

/-- Under the positive reference-pressure clause, the cross-multiplied source
law is equivalent to its quotient form, without evaluating the fitted slope. -/
lemma requestedThermalPressureCoefficient_iff_fitLaw {q : ℕ}
    (source : SourceData q) (hMatches : MatchesStatement source)
    (coefficient : ThermalPressureCoefficient) :
    ((IsRequestedThermalPressureCoefficient source coefficient ↔
        ∃ intercept slope : ℝ,
          IsAffineFit source.affineData intercept slope ∧
            coordinateInSI SIUnitChoices.SI source.referencePressure *
                coordinateInSI SIUnitChoices.SI coefficient =
              slope) ∧
      (IsRequestedThermalPressureCoefficient source coefficient ↔
        ∃ intercept slope : ℝ,
          IsAffineFit source.affineData intercept slope ∧
            coordinateInSI SIUnitChoices.SI coefficient =
              slope /
                coordinateInSI SIUnitChoices.SI source.referencePressure)) := by
  constructor
  · rfl
  · have hPressureNe :
        coordinateInSI SIUnitChoices.SI source.referencePressure ≠ 0 :=
      ne_of_gt hMatches.2.2.2.2.1
    unfold IsRequestedThermalPressureCoefficient
    constructor
    · rintro ⟨intercept, slope, hFit, hLaw⟩
      refine ⟨intercept, slope, hFit, ?_⟩
      apply (eq_div_iff hPressureNe).2
      calc
        coordinateInSI SIUnitChoices.SI coefficient *
              coordinateInSI SIUnitChoices.SI source.referencePressure =
            coordinateInSI SIUnitChoices.SI source.referencePressure *
              coordinateInSI SIUnitChoices.SI coefficient := by ring
        _ = slope := hLaw
    · rintro ⟨intercept, slope, hFit, hLaw⟩
      refine ⟨intercept, slope, hFit, ?_⟩
      have hCross := (eq_div_iff hPressureNe).1 hLaw
      calc
        coordinateInSI SIUnitChoices.SI source.referencePressure *
              coordinateInSI SIUnitChoices.SI coefficient =
            coordinateInSI SIUnitChoices.SI coefficient *
              coordinateInSI SIUnitChoices.SI source.referencePressure := by ring
        _ = slope := hCross

/-- For nondegenerate observed temperatures, the two affine normal equations
are equivalent to global minimization of the unweighted residual sum of
squares. -/
lemma affineFit_iff_leastResidual {q : ℕ} (source : SourceData q)
    (hNondegenerate : NondegeneratePredictor source.affineData)
    (intercept slope : ℝ) :
    IsAffineFit source.affineData intercept slope ↔
      IsLeastResidual source.affineData intercept slope := by
  exact
    isAffineFit_iff_isLeastResidual source.affineData hNondegenerate
      intercept slope

/-- Every matching experiment determines exactly one typed constant-volume
thermal pressure coefficient, without stating its fitted or numerical value. -/
theorem requestedThermalPressureCoefficient_existsUnique {q : ℕ}
    (source : SourceData q) (hMatches : MatchesStatement source) :
    ∃! coefficient : ThermalPressureCoefficient,
      IsRequestedThermalPressureCoefficient source coefficient := by
  have hNondegenerate : NondegeneratePredictor source.affineData :=
    hMatches.2.2.1
  have hPressurePos :
      0 < coordinateInSI SIUnitChoices.SI source.referencePressure :=
    hMatches.2.2.2.2.1
  have hPressureNe :
      coordinateInSI SIUnitChoices.SI source.referencePressure ≠ 0 :=
    ne_of_gt hPressurePos
  rcases existsUnique_isAffineFit source.affineData hNondegenerate with
    ⟨fit, hFit, hFitUnique⟩
  let coefficient : ThermalPressureCoefficient :=
    ⟨fit.2 / coordinateInSI SIUnitChoices.SI source.referencePressure⟩
  refine ⟨coefficient, ?_, ?_⟩
  · refine ⟨fit.1, fit.2, hFit, ?_⟩
    simp only [coefficient, coordinateInSI_self]
    rw [mul_comm]
    apply div_mul_cancel₀
    simpa only [coordinateInSI_self] using hPressureNe
  · intro other hOther
    rcases hOther with ⟨intercept, slope, hOtherFit, hOtherLaw⟩
    have hFitEq : (intercept, slope) = fit :=
      hFitUnique (intercept, slope) hOtherFit
    have hSlopeEq : slope = fit.2 := congrArg Prod.snd hFitEq
    apply (coordinateInSI_eq_iff SIUnitChoices.SI other coefficient).mp
    have hCoordinate :
        coordinateInSI SIUnitChoices.SI other =
          fit.2 /
            coordinateInSI SIUnitChoices.SI source.referencePressure := by
      apply (eq_div_iff hPressureNe).2
      calc
        coordinateInSI SIUnitChoices.SI other *
              coordinateInSI SIUnitChoices.SI source.referencePressure =
            coordinateInSI SIUnitChoices.SI source.referencePressure *
              coordinateInSI SIUnitChoices.SI other := by ring
        _ = slope := hOtherLaw
        _ = fit.2 := hSlopeEq
    simpa only [coefficient, coordinateInSI_self] using hCoordinate

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_A_5
