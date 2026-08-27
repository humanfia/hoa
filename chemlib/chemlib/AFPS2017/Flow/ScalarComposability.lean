import AFPS2017.Flow.Quantity
import AFPS2017.Flow.SourceLint

/-!
# Scalar composition for flow quantities

This module exposes scalar and mapped forms of the released hydraulic value
identity. Statements about actual delivered volume remain conditional on an
explicit `ConstantFlowModel`. It also composes the separately reported and
computed amino-acid amount results without identifying those two quantities.

Source references:

* Sanitized flow-protocol contract (`afps2017.flow.protocol:question`).
* Sanitized source-lint question (`afps2017.source_lint:question`).
* Public Supplementary Information
  (`afps2017.supplement:sha256-f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e`).
-/

namespace AFPS2017.Flow

/-- The reported scalar, factor-ten relation, and typed amount conflict. -/
theorem aminoAcidAmount_sourceConflict_certificate :
    (1000 * AFPS2017.Flow.reportedAminoAcidAmount.1.value = (28 / 5 : ℝ)) ∧
      (AFPS2017.Flow.reportedAminoAcidAmount.1.value =
        10 * AFPS2017.Flow.computedAminoAcidAmount.1.value) ∧
      AFPS2017.Flow.reportedAminoAcidAmount ≠
        AFPS2017.Flow.computedAminoAcidAmount := by
  refine ⟨?_, reportedAminoAcidAmount_is_ten_times_computed,
    reportedAminoAcidAmount_inconsistent⟩
  calc
    1000 * reportedAminoAcidAmount.1.value =
        10 * (1000 * computedAminoAcidAmount.1.value) := by
      rw [reportedAminoAcidAmount_is_ten_times_computed]
      ring
    _ = 10 * (14 / 25 : ℝ) := by
      rw [computedAminoAcidAmount_millimoles]
    _ = (28 / 5 : ℝ) := by norm_num

/-- Scaling a model-certified delivered-volume equality preserves it. -/
theorem deliveredVolume_under_constantFlow_scaled_value :
    {pumpSetpoint : AFPS2017.Flow.FlowRate} →
      (model : AFPS2017.Flow.ConstantFlowModel pumpSetpoint) →
      (t : ℝ) → (scale : ℝ) →
      (volume : Chemlib.Foundations.Volume) →
      scale * (AFPS2017.Flow.flowVolume (model.actualFlow t)
        (AFPS2017.Flow.hydraulicDurationAtRate volume pumpSetpoint)).value =
        scale * volume.1.value := by
  intro pumpSetpoint model t scale volume
  rw [deliveredVolume_under_constantFlow model t volume]

/-- Applying a real-valued map preserves a model-certified volume equality. -/
theorem deliveredVolume_under_constantFlow_value_map :
    {pumpSetpoint : AFPS2017.Flow.FlowRate} →
      (model : AFPS2017.Flow.ConstantFlowModel pumpSetpoint) →
      (t : ℝ) → (map : ℝ → ℝ) →
      (volume : Chemlib.Foundations.Volume) →
      map (AFPS2017.Flow.flowVolume (model.actualFlow t)
        (AFPS2017.Flow.hydraulicDurationAtRate volume pumpSetpoint)).value =
        map volume.1.value := by
  intro pumpSetpoint model t map volume
  exact congrArg map (deliveredVolume_under_constantFlow model t volume)

/-- The ideal hydraulic volume identity expressed after milliliter scaling. -/
theorem flowVolume_hydraulicDuration_milliliters :
    (volume : Chemlib.Foundations.Volume) →
      (rate : AFPS2017.Flow.FlowRate) →
      1000 * (AFPS2017.Flow.flowVolume rate
        (AFPS2017.Flow.hydraulicDurationAtRate volume rate)).value =
        1000 * volume.1.value := by
  intro volume rate
  rw [flowVolume_hydraulicDuration_value volume rate]

/-- Arbitrary real scaling preserves the ideal hydraulic volume identity. -/
theorem flowVolume_hydraulicDuration_scaled_value :
    (scale : ℝ) → (volume : Chemlib.Foundations.Volume) →
      (rate : AFPS2017.Flow.FlowRate) →
      scale * (AFPS2017.Flow.flowVolume rate
        (AFPS2017.Flow.hydraulicDurationAtRate volume rate)).value =
        scale * volume.1.value := by
  intro scale volume rate
  rw [flowVolume_hydraulicDuration_value volume rate]

/-- Applying any real-valued map preserves the ideal hydraulic value identity. -/
theorem flowVolume_hydraulicDuration_value_map :
    (map : ℝ → ℝ) → (volume : Chemlib.Foundations.Volume) →
      (rate : AFPS2017.Flow.FlowRate) →
      map (AFPS2017.Flow.flowVolume rate
        (AFPS2017.Flow.hydraulicDurationAtRate volume rate)).value =
        map volume.1.value := by
  intro map volume rate
  exact congrArg map (flowVolume_hydraulicDuration_value volume rate)

/-- The separately reported amino-acid amount is exactly `5.6 mmol`. -/
theorem reportedAminoAcidAmount_millimoles :
    1000 * AFPS2017.Flow.reportedAminoAcidAmount.1.value =
      (28 / 5 : ℝ) := by
  calc
    1000 * reportedAminoAcidAmount.1.value =
        10 * (1000 * computedAminoAcidAmount.1.value) := by
      rw [reportedAminoAcidAmount_is_ten_times_computed]
      ring
    _ = 10 * (14 / 25 : ℝ) := by
      rw [computedAminoAcidAmount_millimoles]
    _ = (28 / 5 : ℝ) := by norm_num

/-- The reported factor-ten equality remains valid after arbitrary scaling. -/
theorem reportedAminoAcidAmount_scaled_is_ten_times_computed :
    (scale : ℝ) →
      scale * AFPS2017.Flow.reportedAminoAcidAmount.1.value =
        10 * (scale * AFPS2017.Flow.computedAminoAcidAmount.1.value) := by
  intro scale
  rw [reportedAminoAcidAmount_is_ten_times_computed]
  ring

end AFPS2017.Flow
