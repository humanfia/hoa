import Chemlib.Foundations.Amount

/-!
# Flow quantity accounting

This module provides dimension-indexed duration, volume, and positive flow-rate
arithmetic using the released Chemlib quantity types. Numerical volume is
stored in liters and duration in seconds; the named constructors convert
milliliters and milliliters per minute to those common units.

Constant delivered flow is not inferred from a pump setpoint. It is carried by
an explicit `ConstantFlowModel` whose law states that actual flow remains at
the supplied setpoint.

Source references:

* Sanitized flow-protocol contract (`afps2017.flow.protocol:question`).
* Public Supplementary Information
  (`afps2017.supplement:sha256-f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e`).
-/

namespace AFPS2017.Flow

/-- The chemical dimension of volume per unit time. -/
def flowRateDimension : Chemlib.Units.ChemicalDimension :=
  Chemlib.Units.ChemicalDimension.volume /
    Chemlib.Units.ChemicalDimension.time

/-- A signed duration whose numerical value is measured in seconds. -/
abbrev Duration : Type :=
  Chemlib.Units.Quantity Chemlib.Units.ChemicalDimension.time

/-- A strictly positive volume flow rate. -/
abbrev FlowRate : Type :=
  Chemlib.Units.PositiveQuantity flowRateDimension

/-- Explicit evidence that actual flow is constant at a positive pump setpoint. -/
structure ConstantFlowModel (pumpSetpoint : FlowRate) : Type where
  /-- The actual flow at a given time. -/
  actualFlow : ℝ → FlowRate
  /-- Actual flow remains equal to the pump setpoint at every time. -/
  constantAtSetpoint : ∀ t, actualFlow t = pumpSetpoint

/-- Convert seconds to a dimension-indexed duration. -/
def seconds (value : ℝ) : Duration :=
  Chemlib.Units.Quantity.ofReal
    Chemlib.Units.ChemicalDimension.time value

/-- Convert a positive number of milliliters to liters. -/
noncomputable def milliliters (value : ℝ) (positive : 0 < value) :
    Chemlib.Foundations.Volume :=
  Chemlib.Units.PositiveQuantity.ofReal (value / 1000) (by positivity)

/-- Convert a positive rate in milliliters per minute to liters per second. -/
noncomputable def millilitersPerMinute (value : ℝ) (positive : 0 < value) : FlowRate :=
  Chemlib.Units.PositiveQuantity.ofReal (value / 60000) (by positivity)

/-- Multiply a positive flow rate by a duration to obtain delivered volume. -/
def flowVolume (rate : FlowRate) (duration : Duration) :
    Chemlib.Units.Quantity Chemlib.Units.ChemicalDimension.volume :=
  ⟨rate.1.value * duration.value⟩

/-- The numerical value of flow volume is rate times duration. -/
theorem flowVolume_value (rate : FlowRate) (duration : Duration) :
    (flowVolume rate duration).value = rate.1.value * duration.value :=
  rfl

/-- The hydraulic duration required to deliver a volume at a positive rate. -/
noncomputable def hydraulicDurationAtRate (volume : Chemlib.Foundations.Volume)
    (rate : FlowRate) : Duration :=
  ⟨volume.1.value / rate.1.value⟩

/-- Hydraulic duration has numerical value volume divided by rate. -/
theorem hydraulicDurationAtRate_value
    (volume : Chemlib.Foundations.Volume) (rate : FlowRate) :
    (hydraulicDurationAtRate volume rate).value =
      volume.1.value / rate.1.value :=
  rfl

/-- Flowing for the constructed hydraulic duration returns the supplied volume. -/
theorem flowVolume_hydraulicDuration_value
    (volume : Chemlib.Foundations.Volume) (rate : FlowRate) :
    (flowVolume rate (hydraulicDurationAtRate volume rate)).value =
      volume.1.value := by
  simp only [flowVolume_value, hydraulicDurationAtRate_value]
  field_simp [ne_of_gt rate.2]

/-- Replacing actual flow by its certified setpoint leaves flow volume unchanged. -/
theorem flowVolume_under_constantFlow {pumpSetpoint : FlowRate}
    (model : ConstantFlowModel pumpSetpoint) (t : ℝ) (duration : Duration) :
    flowVolume (model.actualFlow t) duration =
      flowVolume pumpSetpoint duration := by
  rw [model.constantAtSetpoint t]

/-- A constant-flow model delivers the requested volume over its hydraulic duration. -/
theorem deliveredVolume_under_constantFlow {pumpSetpoint : FlowRate}
    (model : ConstantFlowModel pumpSetpoint) (t : ℝ)
    (volume : Chemlib.Foundations.Volume) :
    (flowVolume (model.actualFlow t)
      (hydraulicDurationAtRate volume pumpSetpoint)).value = volume.1.value := by
  rw [model.constantAtSetpoint t]
  exact flowVolume_hydraulicDuration_value volume pumpSetpoint

/-- Sum duration values while retaining the time dimension. -/
def sumDurations (durations : List Duration) : Duration :=
  durations.foldr (fun duration total => ⟨duration.value + total.value⟩) ⟨0⟩

/-- Sum positive volumes into an unrestricted volume quantity. -/
def sumVolumes (volumes : List Chemlib.Foundations.Volume) :
    Chemlib.Units.Quantity Chemlib.Units.ChemicalDimension.volume :=
  volumes.foldr (fun volume total => ⟨volume.1.value + total.value⟩) ⟨0⟩

end AFPS2017.Flow
