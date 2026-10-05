import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Units.ISQDimensionBase
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026 Problem 3, part B.1

This file gives an answer-blind model of the isothermal process undergone by the
paramagnetic torus.  The process parameter `tau` is dimensionless and runs from
`0` to `1`.  Every physical quantity below carries its ISQ dimension; `.val` is
its numerical coordinate in one fixed coherent system of units.
-/

namespace Ipho2026Gpt56solBlind.Problem3B1

open Dimension
open Set

/-! ## Dimensional roles -/

abbrev lengthDimension : Dimension ISQDimensionBase :=
  single ISQDimensionBase.length

abbrev massDimension : Dimension ISQDimensionBase :=
  single ISQDimensionBase.mass

abbrev timeDimension : Dimension ISQDimensionBase :=
  single ISQDimensionBase.time

abbrev currentDimension : Dimension ISQDimensionBase :=
  single ISQDimensionBase.current

abbrev temperatureDimension : Dimension ISQDimensionBase :=
  single ISQDimensionBase.temperature

abbrev amountDimension : Dimension ISQDimensionBase :=
  single ISQDimensionBase.amount

/-- Thermodynamic temperature, with ISQ temperature dimension. -/
abbrev Temperature := WithDim temperatureDimension ℝ

/-- Volume, with dimension `length^3`. -/
abbrev Volume := WithDim (lengthDimension ^ 3) ℝ

/-- The magnitude of either `H` or `M`, both measured as current per length. -/
abbrev MagneticIntensity := WithDim (currentDimension * lengthDimension⁻¹) ℝ

/-- Vacuum permeability, with dimension `mass * length * time⁻² * current⁻²`. -/
abbrev Permeability := WithDim
  (massDimension * lengthDimension * timeDimension⁻¹ * timeDimension⁻¹ *
    currentDimension⁻¹ * currentDimension⁻¹) ℝ

/-- Amount of substance. -/
abbrev AmountOfSubstance := WithDim amountDimension ℝ

/-- The constant `K` in `T M V = n K H`, with dimension
`temperature * volume / amount`. -/
abbrev CurieParameter := WithDim
  (temperatureDimension * lengthDimension ^ 3 * amountDimension⁻¹) ℝ

/-- The coefficient `lambda` in `C_M = n lambda / T^2`, with dimension
`energy * temperature / amount`. -/
abbrev HeatCapacityCoefficient := WithDim
  (massDimension * lengthDimension ^ 2 * timeDimension⁻¹ * timeDimension⁻¹ *
    temperatureDimension * amountDimension⁻¹) ℝ

/-- Energy, and also energy per unit dimensionless process parameter. -/
abbrev Energy := WithDim
  (massDimension * lengthDimension ^ 2 * timeDimension⁻¹ * timeDimension⁻¹) ℝ

/-- Heat capacity, with dimension energy per temperature. -/
abbrev HeatCapacity := WithDim
  (massDimension * lengthDimension ^ 2 * timeDimension⁻¹ * timeDimension⁻¹ *
    temperatureDimension⁻¹) ℝ

/-! ## Torus states and material data -/

/-- Fixed material and apparatus data for the paramagnetic torus. -/
structure TorusData where
  /-- Vacuum permeability `mu_0`. -/
  permeability : Permeability
  /-- Amount of paramagnetic material `n`. -/
  amount : AmountOfSubstance
  /-- The fixed torus volume `V`. -/
  volume : Volume
  /-- The material parameter `K` in the equation of state. -/
  curieParameter : CurieParameter
  /-- The coefficient `lambda` in the constant-magnetization heat capacity. -/
  heatCapacityCoefficient : HeatCapacityCoefficient

namespace TorusData

/-- Positivity assumptions for physical material and apparatus data. -/
def IsValid (data : TorusData) : Prop :=
  0 < data.permeability.val ∧
  0 < data.amount.val ∧
  0 < data.volume.val ∧
  0 < data.curieParameter.val ∧
  0 < data.heatCapacityCoefficient.val

end TorusData

/-- An equilibrium state of the torus along a quasistatic process. -/
structure TorusState where
  temperature : Temperature
  /-- Magnitude of the applied magnetic field `H`. -/
  fieldStrength : MagneticIntensity
  /-- Magnitude of the magnetization `M`. -/
  magnetization : MagneticIntensity
  volume : Volume
  internalEnergy : Energy

namespace TorusState

/-- The positive physical domain for a torus state.  Internal energy is not
required to be positive because its zero is conventional. -/
def IsValid (state : TorusState) : Prop :=
  0 < state.temperature.val ∧
  0 < state.fieldStrength.val ∧
  0 < state.magnetization.val ∧
  0 < state.volume.val

end TorusState

/-- The paramagnetic equation of state `T M V = n K H`. -/
def SatisfiesEquationOfState (data : TorusData) (state : TorusState) : Prop :=
  state.temperature.val * state.magnetization.val * state.volume.val =
    data.amount.val * data.curieParameter.val * state.fieldStrength.val

/-- The stated heat capacity at constant magnetization,
`C_M = n lambda / T^2`. -/
noncomputable def heatCapacityAtConstantMagnetization
    (data : TorusData) (temperature : Temperature) : HeatCapacity :=
  ⟨data.amount.val * data.heatCapacityCoefficient.val / temperature.val ^ 2⟩

/-! ## Processes and differential laws -/

/-- A parametrized thermodynamic history.  `workEntering` and `heatEntering`
are signed energy increments per unit increase of the dimensionless path
parameter; their names record the source convention that positive means energy
entering the torus. -/
structure TorusProcess where
  state : ℝ → TorusState
  workEntering : ℝ → Energy
  heatEntering : ℝ → Energy

namespace TorusProcess

/-- Regularity needed to interpret the differential laws and integrate heat.
Only behavior on `[0, 1]` is physically used. -/
def IsRegular (process : TorusProcess) : Prop :=
  Differentiable ℝ (fun tau ↦ (process.state tau).temperature.val) ∧
  Differentiable ℝ (fun tau ↦ (process.state tau).fieldStrength.val) ∧
  Differentiable ℝ (fun tau ↦ (process.state tau).magnetization.val) ∧
  Differentiable ℝ (fun tau ↦ (process.state tau).volume.val) ∧
  Differentiable ℝ (fun tau ↦ (process.state tau).internalEnergy.val) ∧
  IntervalIntegrable (fun tau ↦ (process.workEntering tau).val)
    MeasureTheory.volume 0 1 ∧
  IntervalIntegrable (fun tau ↦ (process.heatEntering tau).val)
    MeasureTheory.volume 0 1

end TorusProcess

/-- The differential internal-energy law `dU = C_M dT`. -/
def SatisfiesInternalEnergyLaw (data : TorusData) (process : TorusProcess) : Prop :=
  ∀ tau ∈ Icc (0 : ℝ) 1,
    deriv (fun x ↦ (process.state x).internalEnergy.val) tau =
      (heatCapacityAtConstantMagnetization data
        (process.state tau).temperature).val *
        deriv (fun x ↦ (process.state x).temperature.val) tau

/-- The magnetic work law `dW = mu_0 V H dM`, with `dW > 0` interpreted as
work entering the material. -/
def SatisfiesElectromagneticWorkLaw
    (data : TorusData) (process : TorusProcess) : Prop :=
  ∀ tau ∈ Icc (0 : ℝ) 1,
    (process.workEntering tau).val =
      data.permeability.val * (process.state tau).volume.val *
        (process.state tau).fieldStrength.val *
        deriv (fun x ↦ (process.state x).magnetization.val) tau

/-- First law with the source sign convention: signed heat and signed work
entering the torus both occur with a plus sign in `dU = delta Q + delta W`. -/
def SatisfiesFirstLawWithEnteringPositive (process : TorusProcess) : Prop :=
  ∀ tau ∈ Icc (0 : ℝ) 1,
    deriv (fun x ↦ (process.state x).internalEnergy.val) tau =
      (process.heatEntering tau).val + (process.workEntering tau).val

/-- A quasistatic fixed-temperature, fixed-volume process in which the field
magnitude changes from `H_i` to `H_f`.  The normalized parameter interval is
`[0, 1]`; no unmentioned monotonicity assumption is imposed. -/
def IsFixedTemperatureProcess
    (data : TorusData) (temperature : Temperature)
    (H_i H_f : MagneticIntensity) (process : TorusProcess) : Prop :=
  data.IsValid ∧
  process.IsRegular ∧
  (process.state 0).fieldStrength = H_i ∧
  (process.state 1).fieldStrength = H_f ∧
  (∀ tau ∈ Icc (0 : ℝ) 1,
    (process.state tau).temperature = temperature) ∧
  (∀ tau ∈ Icc (0 : ℝ) 1,
    (process.state tau).volume = data.volume) ∧
  (∀ tau ∈ Icc (0 : ℝ) 1, (process.state tau).IsValid) ∧
  (∀ tau ∈ Icc (0 : ℝ) 1,
    SatisfiesEquationOfState data (process.state tau)) ∧
  SatisfiesInternalEnergyLaw data process ∧
  SatisfiesElectromagneticWorkLaw data process ∧
  SatisfiesFirstLawWithEnteringPositive process

/-- `Q` is the signed heat transferred into the torus along this process. -/
def HasNetHeatEntering (process : TorusProcess) (Q : Energy) : Prop :=
  Q.val = ∫ tau in (0 : ℝ)..1, (process.heatEntering tau).val

/-- Answer-free characterization of the requested heat.  It requires at least
one admissible process and says that `Q` is the net entering heat for every
admissible quasistatic path with the prescribed endpoints.  Thus this predicate
does not encode a closed form and also makes path independence explicit. -/
def IsHeatSolution
    (data : TorusData) (temperature : Temperature)
    (H_i H_f : MagneticIntensity) (Q : Energy) : Prop :=
  (∃ process : TorusProcess,
    IsFixedTemperatureProcess data temperature H_i H_f process) ∧
  ∀ process : TorusProcess,
    IsFixedTemperatureProcess data temperature H_i H_f process →
      HasNetHeatEntering process Q

/-- IPhO 2026 Problem 3 B.1, stated without placing the requested heat in the
signature: positive physical data and endpoint field magnitudes determine a
unique signed heat transfer through the governing thermodynamic laws. -/
theorem problem_IPhO_2026_3_B_1
    (data : TorusData) (temperature : Temperature)
    (H_i H_f : MagneticIntensity)
    (hdata : data.IsValid)
    (htemperature : 0 < temperature.val)
    (hH_i : 0 < H_i.val) (hH_f : 0 < H_f.val) :
    ∃! Q : Energy, IsHeatSolution data temperature H_i H_f Q := by
  classical
  have hasDerivAt_affine (a b x : ℝ) :
      HasDerivAt (fun y : ℝ ↦ a + b * y) b x := by
    rw [hasDerivAt_iff_isLittleO]
    refine (Asymptotics.isLittleO_zero (fun y : ℝ ↦ y - x) (nhds x)).congr ?_
      (fun _ ↦ rfl)
    intro y
    dsimp
    ring
  have differentiable_affine (a b : ℝ) :
      Differentiable ℝ (fun x : ℝ ↦ a + b * x) :=
    fun x ↦ (hasDerivAt_affine a b x).differentiableAt
  have deriv_affine (a b x : ℝ) :
      deriv (fun y : ℝ ↦ a + b * y) x = b :=
    (hasDerivAt_affine a b x).deriv
  have hasDerivAt_const_mul (c : ℝ) (f : ℝ → ℝ) (f' x : ℝ)
      (hf : HasDerivAt f f' x) :
      HasDerivAt (fun y ↦ c * f y) (c * f') x := by
    rw [hasDerivAt_iff_isLittleO] at hf ⊢
    refine (hf.const_mul_left c).congr ?_ (fun _ ↦ rfl)
    intro y
    dsimp
    ring

  rcases hdata with ⟨hpermeability, hamount, hvolume, hcurie, hheatCapacity⟩
  let dH : ℝ := H_f.val - H_i.val
  let susceptibility : ℝ :=
    data.amount.val * data.curieParameter.val /
      (temperature.val * data.volume.val)
  have hsusceptibility : 0 < susceptibility := by
    dsimp [susceptibility]
    exact div_pos (mul_pos hamount hcurie) (mul_pos htemperature hvolume)
  let fieldValue : ℝ → ℝ := fun tau ↦ H_i.val + dH * tau
  let magnetizationValue : ℝ → ℝ := fun tau ↦ susceptibility * fieldValue tau
  let workValue : ℝ → ℝ := fun tau ↦
    data.permeability.val * data.volume.val * fieldValue tau *
      (susceptibility * dH)
  let state : ℝ → TorusState := fun tau ↦
    { temperature := temperature
      fieldStrength := ⟨fieldValue tau⟩
      magnetization := ⟨magnetizationValue tau⟩
      volume := data.volume
      internalEnergy := ⟨0⟩ }
  let process : TorusProcess :=
    { state := state
      workEntering := fun tau ↦ ⟨workValue tau⟩
      heatEntering := fun tau ↦ ⟨-workValue tau⟩ }

  have hfieldValue_pos (tau : ℝ) (htau : tau ∈ Icc (0 : ℝ) 1) :
      0 < fieldValue tau := by
    have htau_nonneg : 0 ≤ tau := htau.1
    have hone_sub_nonneg : 0 ≤ 1 - tau := sub_nonneg.mpr htau.2
    have hleft : 0 ≤ (1 - tau) * H_i.val := mul_nonneg hone_sub_nonneg hH_i.le
    have hright : 0 ≤ tau * H_f.val := mul_nonneg htau_nonneg hH_f.le
    have hsum_pos : 0 < (1 - tau) * H_i.val + tau * H_f.val := by
      rcases htau_nonneg.eq_or_lt with rfl | htau_pos
      · simpa using hH_i
      · exact add_pos_of_nonneg_of_pos hleft (mul_pos htau_pos hH_f)
    rw [show fieldValue tau = (1 - tau) * H_i.val + tau * H_f.val by
      dsimp [fieldValue, dH]
      ring]
    exact hsum_pos

  have hmagnetization_deriv (tau : ℝ) :
      deriv magnetizationValue tau = susceptibility * dH := by
    rw [show magnetizationValue = fun x ↦
        susceptibility * H_i.val + (susceptibility * dH) * x by
      funext x
      simp only [magnetizationValue, fieldValue]
      ring]
    exact deriv_affine (susceptibility * H_i.val) (susceptibility * dH) tau

  have hprocess_exists :
      ∃ p : TorusProcess,
        IsFixedTemperatureProcess data temperature H_i H_f p := by
    refine ⟨process, ?_⟩
    unfold IsFixedTemperatureProcess
    refine ⟨⟨hpermeability, hamount, hvolume, hcurie, hheatCapacity⟩, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold TorusProcess.IsRegular
      dsimp [process, state]
      have hfieldContinuous : Continuous fieldValue := by
        change Continuous (fun tau : ℝ ↦ H_i.val + dH * tau)
        exact (differentiable_affine H_i.val dH).continuous
      have hworkContinuous : Continuous workValue := by
        change Continuous (fun tau : ℝ ↦
          (data.permeability.val * data.volume.val) * fieldValue tau *
            (susceptibility * dH))
        exact (continuous_const.mul hfieldContinuous).mul continuous_const
      refine ⟨differentiable_const _, ?_, ?_, differentiable_const _,
        differentiable_const _, ?_, ?_⟩
      · simpa only [fieldValue] using differentiable_affine H_i.val dH
      · have hmag : Differentiable ℝ
            (fun tau : ℝ ↦ susceptibility * H_i.val +
              (susceptibility * dH) * tau) :=
          differentiable_affine (susceptibility * H_i.val) (susceptibility * dH)
        change Differentiable ℝ magnetizationValue
        have hmagnetizationValue : magnetizationValue =
            fun tau : ℝ ↦ susceptibility * H_i.val +
              (susceptibility * dH) * tau := by
          funext tau
          dsimp [magnetizationValue, fieldValue]
          ring
        rw [hmagnetizationValue]
        exact hmag
      · exact hworkContinuous.intervalIntegrable 0 1
      · exact hworkContinuous.neg.intervalIntegrable 0 1
    · apply WithDim.ext
      change fieldValue 0 = H_i.val
      dsimp [fieldValue]
      ring
    · apply WithDim.ext
      change fieldValue 1 = H_f.val
      dsimp [fieldValue, dH]
      ring
    · intro tau _
      rfl
    · intro tau _
      rfl
    · intro tau htau
      unfold TorusState.IsValid
      dsimp [process, state, magnetizationValue]
      exact ⟨htemperature, hfieldValue_pos tau htau,
        mul_pos hsusceptibility (hfieldValue_pos tau htau), hvolume⟩
    · intro tau _
      unfold SatisfiesEquationOfState
      dsimp [process, state, magnetizationValue, susceptibility]
      have hden : temperature.val * data.volume.val ≠ 0 :=
        mul_ne_zero htemperature.ne' hvolume.ne'
      calc
        temperature.val *
              (data.amount.val * data.curieParameter.val /
                  (temperature.val * data.volume.val) * fieldValue tau) *
            data.volume.val =
            (data.amount.val * data.curieParameter.val /
                (temperature.val * data.volume.val)) *
              (temperature.val * data.volume.val) * fieldValue tau := by
                ring
        _ = data.amount.val * data.curieParameter.val * fieldValue tau := by
          rw [div_mul_cancel₀ _ hden]
    · intro tau _
      dsimp [process, state]
      change deriv (fun _ : ℝ ↦ (0 : ℝ)) tau =
        (heatCapacityAtConstantMagnetization data temperature).val *
          deriv (fun _ : ℝ ↦ temperature.val) tau
      rw [deriv_const, deriv_const, mul_zero]
    · intro tau _
      dsimp [process, state, workValue]
      rw [hmagnetization_deriv]
    · intro tau _
      dsimp [process, state]
      change deriv (fun _ : ℝ ↦ (0 : ℝ)) tau =
        -workValue tau + workValue tau
      rw [deriv_const]
      ring

  have newtonLeibniz_mul_deriv
      (H q : ℝ → ℝ) (c : ℝ)
      (hH : Differentiable ℝ H)
      (hqint : IntervalIntegrable q MeasureTheory.volume 0 1)
      (hq : ∀ x ∈ Ioo (0 : ℝ) 1,
        q x = -c * H x * deriv H x) :
      (∫ x in (0 : ℝ)..1, q x) =
        -(c / 2) * (H 1 ^ 2 - H 0 ^ 2) :=
      open MeasureTheory MeasureTheory.Measure in by
    /- The frozen imports contain the measure-theoretic primitives used by
    Mathlib's FTC-2, but not the packaged interval-integral theorem.  We first
    specialize the Vitali--Caratheodory majorant construction needed in its
    proof. -/
    have simple_exists_le_lowerSemicontinuous_lintegral_ge
        (mu : Measure ℝ) [WeaklyRegular mu]
        (f : SimpleFunc ℝ NNReal) {epsilon : ENNReal} (hepsilon : epsilon ≠ 0) :
        ∃ g : ℝ → NNReal, (∀ x, f x ≤ g x) ∧ LowerSemicontinuous g ∧
          (∫⁻ x, g x ∂mu) ≤ (∫⁻ x, f x ∂mu) + epsilon := by
      induction f using MeasureTheory.SimpleFunc.induction generalizing epsilon with
      | @const d s hs =>
        let f := SimpleFunc.piecewise s hs (SimpleFunc.const ℝ d) (SimpleFunc.const ℝ 0)
        by_cases htop : ∫⁻ x, f x ∂mu = ⊤
        · refine ⟨fun _ ↦ d, fun x ↦ ?_, lowerSemicontinuous_const, ?_⟩
          · classical
            dsimp [f]
            change (if x ∈ s then d else 0) ≤ d
            by_cases hx : x ∈ s
            · rw [if_pos hx]
            · rw [if_neg hx]
              exact bot_le
          · rw [htop]
            calc
              (∫⁻ x, ((fun _ : ℝ ↦ d) x : ENNReal) ∂mu) ≤ ⊤ := le_top
              _ = ⊤ + epsilon := (top_add epsilon).symm
        by_cases hd : d = 0
        · subst d
          refine ⟨fun _ ↦ 0, ?_, lowerSemicontinuous_const, ?_⟩
          · classical
            intro x
            dsimp [f]
            change (if x ∈ s then (0 : NNReal) else 0) ≤ 0
            by_cases hx : x ∈ s
            · rw [if_pos hx]
            · rw [if_neg hx]
          · change (∫⁻ _x : ℝ, (0 : ENNReal) ∂mu) ≤ _
            rw [lintegral_zero]
            exact zero_le
        have hfunction : (fun x ↦ (f x : ENNReal)) =
            Set.indicator s (fun _ ↦ (d : ENNReal)) := by
          classical
          funext x
          dsimp [f]
          by_cases hx : x ∈ s
          · rw [Set.indicator_of_mem hx]
            change ((if x ∈ s then d else 0 : NNReal) : ENNReal) = (d : ENNReal)
            rw [if_pos hx]
          · rw [Set.indicator_of_notMem hx]
            change ((if x ∈ s then d else 0 : NNReal) : ENNReal) = 0
            rw [if_neg hx]
            exact ENNReal.coe_zero
        have hintegral : (∫⁻ x, f x ∂mu) = (d : ENNReal) * mu s := by
          rw [hfunction]
          exact lintegral_indicator_const hs (d : ENNReal)
        have hmus : mu s ≠ ⊤ := by
          intro hmus
          apply htop
          rw [hintegral, hmus]
          exact ENNReal.mul_top (ENNReal.coe_ne_zero.2 hd)
        have hlt : mu s < mu s + epsilon / d := by
          have hpos : (0 : ENNReal) < epsilon / d :=
            ENNReal.div_pos_iff.2 ⟨hepsilon, ENNReal.coe_ne_top⟩
          calc
            mu s = mu s + 0 := (add_zero _).symm
            _ < mu s + epsilon / d := ENNReal.add_lt_add_left hmus hpos
        obtain ⟨u, hsu, huopen, hmu⟩ :
            ∃ u : Set ℝ, u ⊇ s ∧ IsOpen u ∧ mu u < mu s + epsilon / d :=
          s.exists_isOpen_lt_of_lt _ hlt
        refine ⟨Set.indicator u (fun _ ↦ d), fun x ↦ ?_,
          huopen.lowerSemicontinuous_indicator zero_le, ?_⟩
        · classical
          dsimp [f]
          change (if x ∈ s then d else 0) ≤ (if x ∈ u then d else 0)
          by_cases hx : x ∈ s
          · rw [if_pos hx, if_pos (hsu hx)]
          · rw [if_neg hx]
            exact bot_le
        · suffices (d : ENNReal) * mu u ≤ d * mu s + epsilon by
            classical
            have huFunction :
                (fun x ↦ ((Set.indicator u (fun _ ↦ d)) x : ENNReal)) =
                  Set.indicator u (fun _ ↦ (d : ENNReal)) := by
              funext x
              by_cases hx : x ∈ u
              · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
              · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
                exact ENNReal.coe_zero
            have huIntegral :
                (∫⁻ x, ((Set.indicator u (fun _ ↦ d)) x : ENNReal) ∂mu) =
                  (d : ENNReal) * mu u := by
              rw [huFunction]
              exact lintegral_indicator_const huopen.measurableSet (d : ENNReal)
            rw [huIntegral, hintegral]
            exact this
          calc
            (d : ENNReal) * mu u ≤ d * (mu s + epsilon / d) := by grw [hmu]
            _ = d * mu s + epsilon := by
              simp_rw [mul_add]
              rw [ENNReal.mul_div_cancel _ ENNReal.coe_ne_top]
              exact ENNReal.coe_ne_zero.2 hd
      | @add f1 f2 _ h1 h2 =>
        rcases h1 (ENNReal.half_pos hepsilon).ne' with ⟨g1, hf1, hg1cont, hg1int⟩
        rcases h2 (ENNReal.half_pos hepsilon).ne' with ⟨g2, hf2, hg2cont, hg2int⟩
        refine ⟨fun x ↦ g1 x + g2 x, fun x ↦ add_le_add (hf1 x) (hf2 x),
          hg1cont.add hg2cont, ?_⟩
        simp only [SimpleFunc.coe_add, ENNReal.coe_add, Pi.add_apply]
        rw [lintegral_add_left f1.measurable.coe_nnreal_ennreal,
          lintegral_add_left hg1cont.measurable.coe_nnreal_ennreal]
        convert! add_le_add hg1int hg2int using 1
        conv_lhs => rw [← ENNReal.add_halves epsilon]
        ac_rfl

    have exists_le_lowerSemicontinuous_lintegral_ge
        (mu : Measure ℝ) [WeaklyRegular mu]
        (f : ℝ → ENNReal) (hf : Measurable f) {epsilon : ENNReal}
        (hepsilon : epsilon ≠ 0) :
        ∃ g : ℝ → ENNReal, (∀ x, f x ≤ g x) ∧ LowerSemicontinuous g ∧
          (∫⁻ x, g x ∂mu) ≤ (∫⁻ x, f x ∂mu) + epsilon := by
      rcases ENNReal.exists_pos_sum_of_countable' hepsilon ℕ with
        ⟨delta, hdelta_pos, hdelta⟩
      have happrox : ∀ n, ∃ g : ℝ → NNReal,
          (∀ x, SimpleFunc.eapproxDiff f n x ≤ g x) ∧
          LowerSemicontinuous g ∧
          (∫⁻ x, g x ∂mu) ≤
            (∫⁻ x, SimpleFunc.eapproxDiff f n x ∂mu) + delta n :=
        fun n ↦ simple_exists_le_lowerSemicontinuous_lintegral_ge mu
          (SimpleFunc.eapproxDiff f n) (hdelta_pos n).ne'
      choose g hf_le_g hgcont hgint using happrox
      refine ⟨fun x ↦ ∑' n, g n x, fun x ↦ ?_, ?_, ?_⟩
      · rw [← SimpleFunc.tsum_eapproxDiff f hf]
        exact ENNReal.tsum_le_tsum fun n ↦ ENNReal.coe_le_coe.2 (hf_le_g n x)
      · refine lowerSemicontinuous_tsum fun n ↦ ?_
        exact ENNReal.continuous_coe.comp_lowerSemicontinuous (hgcont n) fun _ _ hxy ↦
          ENNReal.coe_le_coe.2 hxy
      · calc
          ∫⁻ x, ∑' n : ℕ, g n x ∂mu = ∑' n, ∫⁻ x, g n x ∂mu := by
            rw [lintegral_tsum fun n ↦ (hgcont n).measurable.coe_nnreal_ennreal.aemeasurable]
          _ ≤ ∑' n, ((∫⁻ x, SimpleFunc.eapproxDiff f n x ∂mu) + delta n) :=
            ENNReal.tsum_le_tsum hgint
          _ = (∑' n, ∫⁻ x, SimpleFunc.eapproxDiff f n x ∂mu) + ∑' n, delta n :=
            ENNReal.tsum_add
          _ ≤ (∫⁻ x, f x ∂mu) + epsilon := by
            refine add_le_add ?_ hdelta.le
            rw [← lintegral_tsum]
            · exact lintegral_mono fun x ↦
                (SimpleFunc.tsum_eapproxDiff f hf x).le
            · intro n
              exact (SimpleFunc.measurable _).coe_nnreal_ennreal.aemeasurable

    have exists_lt_lowerSemicontinuous_lintegral_ge
        (mu : Measure ℝ) [WeaklyRegular mu] [SigmaFinite mu]
        (f : ℝ → NNReal) (hf : Measurable f) {epsilon : ENNReal}
        (hepsilon : epsilon ≠ 0) :
        ∃ g : ℝ → ENNReal, (∀ x, (f x : ENNReal) < g x) ∧
          LowerSemicontinuous g ∧
          (∫⁻ x, g x ∂mu) ≤ (∫⁻ x, f x ∂mu) + epsilon := by
      have hhalf : epsilon / 2 ≠ 0 := (ENNReal.half_pos hepsilon).ne'
      rcases exists_pos_lintegral_lt_of_sigmaFinite mu hhalf with
        ⟨w, hwpos, hwmeas, hwint⟩
      let f' x := ((f x + w x : NNReal) : ENNReal)
      rcases exists_le_lowerSemicontinuous_lintegral_ge mu f'
          (hf.add hwmeas).coe_nnreal_ennreal hhalf with
        ⟨g, hle, hgcont, hgint⟩
      refine ⟨g, fun x ↦ ?_, hgcont, ?_⟩
      · calc
          (f x : ENNReal) < f' x := by
            change (f x : ENNReal) < ((f x + w x : NNReal) : ENNReal)
            apply ENNReal.coe_lt_coe.2
            calc
              f x = f x + 0 := (add_zero (f x)).symm
              _ < f x + w x := add_lt_add_right (hwpos x) (f x)
          _ ≤ g x := hle x
      · calc
          (∫⁻ x, g x ∂mu) ≤ (∫⁻ x, f x + w x ∂mu) + epsilon / 2 := hgint
          _ = ((∫⁻ x, f x ∂mu) + ∫⁻ x, w x ∂mu) + epsilon / 2 := by
            rw [lintegral_add_right _ hwmeas.coe_nnreal_ennreal]
          _ ≤ (∫⁻ x, f x ∂mu) + epsilon / 2 + epsilon / 2 := by grw [hwint]
          _ = (∫⁻ x, f x ∂mu) + epsilon := by
            rw [add_assoc, ENNReal.add_halves]

    have exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable
        (mu : Measure ℝ) [WeaklyRegular mu] [SigmaFinite mu]
        (f : ℝ → NNReal) (hf : AEMeasurable f mu) {epsilon : ENNReal}
        (hepsilon : epsilon ≠ 0) :
        ∃ g : ℝ → ENNReal, (∀ x, (f x : ENNReal) < g x) ∧
          LowerSemicontinuous g ∧
          (∫⁻ x, g x ∂mu) ≤ (∫⁻ x, f x ∂mu) + epsilon := by
      have hhalf : epsilon / 2 ≠ 0 := (ENNReal.half_pos hepsilon).ne'
      rcases exists_lt_lowerSemicontinuous_lintegral_ge mu (hf.mk f)
          hf.measurable_mk hhalf with ⟨g0, hfg0, hg0cont, hg0int⟩
      rcases exists_measurable_superset_of_null hf.ae_eq_mk with
        ⟨s, hs, hsmeas, hmus⟩
      rcases exists_le_lowerSemicontinuous_lintegral_ge mu
          (s.indicator fun _ ↦ (⊤ : ENNReal))
          (measurable_const.indicator hsmeas) hhalf with
        ⟨g1, hle1, hg1cont, hg1int⟩
      refine ⟨fun x ↦ g0 x + g1 x, fun x ↦ ?_, hg0cont.add hg1cont, ?_⟩
      · by_cases hx : x ∈ s
        · have h := hle1 x
          rw [Set.indicator_of_mem hx] at h
          have htop : g1 x = ⊤ := top_unique h
          change (f x : ENNReal) < g0 x + g1 x
          rw [htop]
          calc
            (f x : ENNReal) < ⊤ := ENNReal.coe_lt_top
            _ = g0 x + ⊤ := (add_top _).symm
        · have hfx : f x = hf.mk f x := by
            rw [Set.compl_subset_comm] at hs
            exact hs hx
          rw [hfx]
          exact (hfg0 x).trans_le le_self_add
      · calc
          ∫⁻ x, g0 x + g1 x ∂mu = (∫⁻ x, g0 x ∂mu) + ∫⁻ x, g1 x ∂mu :=
            lintegral_add_left hg0cont.measurable _
          _ ≤ (∫⁻ x, f x ∂mu) + epsilon / 2 + (0 + epsilon / 2) := by
            refine add_le_add ?_ ?_
            · have hmkAE :
                  (fun x ↦ ((hf.mk f x : NNReal) : ENNReal)) =ᵐ[mu]
                    fun x ↦ (f x : ENNReal) :=
                (hf.ae_eq_mk.fun_comp fun y : NNReal ↦ (y : ENNReal)).symm
              have hmk :
                  (∫⁻ x, ((AEMeasurable.mk f hf x : NNReal) : ENNReal) ∂mu) =
                    ∫⁻ x, (f x : ENNReal) ∂mu :=
                lintegral_congr_ae hmkAE
              rw [hmk] at hg0int
              exact hg0int
            · have htopIntegral :
                  (∫⁻ x, s.indicator (fun _ ↦ (⊤ : ENNReal)) x ∂mu) = 0 := by
                rw [lintegral_indicator_const hsmeas, hmus]
                exact mul_zero ⊤
              rw [htopIntegral] at hg1int
              exact hg1int
          _ = (∫⁻ x, f x ∂mu) + epsilon := by
            rw [zero_add, add_assoc, ENNReal.add_halves]

    have exists_lt_lowerSemicontinuous_integral_gt_nnreal
        (mu : Measure ℝ) [WeaklyRegular mu] [SigmaFinite mu]
        (f : ℝ → NNReal) (hf : Integrable (fun x ↦ (f x : ℝ)) mu)
        {epsilon : ℝ} (hepsilon : 0 < epsilon) :
        ∃ g : ℝ → ENNReal, (∀ x, (f x : ENNReal) < g x) ∧
          LowerSemicontinuous g ∧ (∀ᵐ x ∂mu, g x < ⊤) ∧
          Integrable (fun x ↦ (g x).toReal) mu ∧
          (∫ x, (g x).toReal ∂mu) < (∫ x, (f x : ℝ) ∂mu) + epsilon := by
      have hfmeas : AEMeasurable f mu := by
        refine hf.aestronglyMeasurable.real_toNNReal.aemeasurable.congr
          (Filter.Eventually.of_forall fun x ↦ ?_)
        exact Real.toNNReal_coe
      lift epsilon to NNReal using hepsilon.le
      obtain ⟨delta, hdelta_pos, hdelta_epsilon⟩ :
          ∃ delta : NNReal, 0 < delta ∧ delta < epsilon := exists_between hepsilon
      have hf_ne_top : (∫⁻ x, f x ∂mu) ≠ ⊤ :=
        (hasFiniteIntegral_iff_ofNNReal.1 hf.hasFiniteIntegral).ne
      rcases exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable mu f hfmeas
          (ENNReal.coe_ne_zero.2 hdelta_pos.ne') with
        ⟨g, hfg, hgcont, hgint⟩
      have hg_ne_top : (∫⁻ x, g x ∂mu) ≠ ⊤ :=
        ne_top_of_le_ne_top
          (ENNReal.add_ne_top.2 ⟨hf_ne_top, ENNReal.coe_ne_top⟩) hgint
      have hg_lt_top : ∀ᵐ x ∂mu, g x < ⊤ := ae_lt_top hgcont.measurable hg_ne_top
      have hIg : (∫⁻ x, ENNReal.ofReal (g x).toReal ∂mu) = ∫⁻ x, g x ∂mu := by
        apply lintegral_congr_ae
        filter_upwards [hg_lt_top] with x hx
        simp only [hx.ne, ENNReal.ofReal_toReal, Ne, not_false_eq_true]
      refine ⟨g, hfg, hgcont, hg_lt_top, ?_, ?_⟩
      · refine ⟨hgcont.measurable.ennreal_toReal.aemeasurable.aestronglyMeasurable, ?_⟩
        refine (hasFiniteIntegral_iff_ofReal
          (Filter.Eventually.of_forall fun x ↦ ENNReal.toReal_nonneg)).2 ?_
        rw [hIg]
        exact hg_ne_top.lt_top
      · rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
        · calc
            ENNReal.toReal (∫⁻ x, ENNReal.ofReal (g x).toReal ∂mu) =
                ENNReal.toReal (∫⁻ x, g x ∂mu) := by rw [hIg]
            _ ≤ ENNReal.toReal ((∫⁻ x, f x ∂mu) + delta) := by
              apply ENNReal.toReal_mono _ hgint
              simpa using hf_ne_top
            _ = ENNReal.toReal (∫⁻ x, f x ∂mu) + delta := by
              rw [ENNReal.toReal_add hf_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal]
            _ < ENNReal.toReal (∫⁻ x, f x ∂mu) + epsilon := by gcongr
            _ = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (f x : ℝ) ∂mu) + epsilon := by
              simp
        · exact Filter.Eventually.of_forall fun x ↦ by simp
        · exact hfmeas.coe_nnreal_real.aestronglyMeasurable
        · exact Filter.Eventually.of_forall fun x ↦ by simp
        · exact hgcont.measurable.ennreal_toReal.aemeasurable.aestronglyMeasurable

    have simple_exists_upperSemicontinuous_le_lintegral_le
        (mu : Measure ℝ) [WeaklyRegular mu]
        (f : SimpleFunc ℝ NNReal) (hf_ne_top : (∫⁻ x, f x ∂mu) ≠ ⊤)
        {epsilon : ENNReal} (hepsilon : epsilon ≠ 0) :
        ∃ g : ℝ → NNReal, (∀ x, g x ≤ f x) ∧ UpperSemicontinuous g ∧
          (∫⁻ x, f x ∂mu) ≤ (∫⁻ x, g x ∂mu) + epsilon := by
      induction f using MeasureTheory.SimpleFunc.induction generalizing epsilon with
      | @const d s hs =>
        classical
        by_cases hd : d = 0
        · subst d
          refine ⟨fun _ ↦ 0, ?_, upperSemicontinuous_const, ?_⟩
          · intro x
            exact bot_le
          · have hfzero :
                (fun x ↦ ((SimpleFunc.piecewise s hs
                  (SimpleFunc.const ℝ (0 : NNReal))
                  (SimpleFunc.const ℝ 0)) x : ENNReal)) =
                    fun _ : ℝ ↦ (0 : ENNReal) := by
              funext x
              change ((if x ∈ s then (0 : NNReal) else 0 : NNReal) : ENNReal) = 0
              by_cases hx : x ∈ s
              · rw [if_pos hx]
                exact ENNReal.coe_zero
              · rw [if_neg hx]
                exact ENNReal.coe_zero
            rw [hfzero, lintegral_zero]
            exact zero_le
        let f := SimpleFunc.piecewise s hs
          (SimpleFunc.const ℝ d) (SimpleFunc.const ℝ 0)
        change (∫⁻ x, f x ∂mu) ≠ ⊤ at hf_ne_top
        have hfunction : (fun x ↦ (f x : ENNReal)) =
            Set.indicator s (fun _ ↦ (d : ENNReal)) := by
          funext x
          dsimp [f]
          by_cases hx : x ∈ s
          · rw [Set.indicator_of_mem hx]
            change ((if x ∈ s then d else 0 : NNReal) : ENNReal) = (d : ENNReal)
            rw [if_pos hx]
          · rw [Set.indicator_of_notMem hx]
            change ((if x ∈ s then d else 0 : NNReal) : ENNReal) = 0
            rw [if_neg hx]
            exact ENNReal.coe_zero
        have hintegral : (∫⁻ x, f x ∂mu) = (d : ENNReal) * mu s := by
          rw [hfunction]
          exact lintegral_indicator_const hs (d : ENNReal)
        have hmus : mu s < ⊤ := by
          apply lt_top_iff_ne_top.2
          intro hmus
          apply hf_ne_top
          rw [hintegral, hmus]
          exact ENNReal.mul_top (ENNReal.coe_ne_zero.2 hd)
        have hpos : (0 : ENNReal) < epsilon / d :=
          ENNReal.div_pos_iff.2 ⟨hepsilon, ENNReal.coe_ne_top⟩
        obtain ⟨F, hFs, hFclosed, hmuF⟩ :
            ∃ F : Set ℝ, F ⊆ s ∧ IsClosed F ∧ mu s < mu F + epsilon / d :=
          hs.exists_isClosed_lt_add hmus.ne hpos.ne'
        refine ⟨Set.indicator F (fun _ ↦ d), fun x ↦ ?_,
          hFclosed.upperSemicontinuous_indicator zero_le, ?_⟩
        · dsimp [f]
          change (if x ∈ F then d else 0) ≤ (if x ∈ s then d else 0)
          by_cases hx : x ∈ F
          · rw [if_pos hx, if_pos (hFs hx)]
          · rw [if_neg hx]
            exact bot_le
        · suffices (d : ENNReal) * mu s ≤ d * mu F + epsilon by
            have hFFunction :
                (fun x ↦ ((Set.indicator F (fun _ ↦ d)) x : ENNReal)) =
                  Set.indicator F (fun _ ↦ (d : ENNReal)) := by
              funext x
              by_cases hx : x ∈ F
              · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
              · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
                exact ENNReal.coe_zero
            have hFIntegral :
                (∫⁻ x, ((Set.indicator F (fun _ ↦ d)) x : ENNReal) ∂mu) =
                  (d : ENNReal) * mu F := by
              rw [hFFunction]
              exact lintegral_indicator_const hFclosed.measurableSet (d : ENNReal)
            rw [hintegral, hFIntegral]
            exact this
          calc
            (d : ENNReal) * mu s ≤ d * (mu F + epsilon / d) := by grw [hmuF]
            _ = d * mu F + epsilon := by
              simp_rw [mul_add]
              rw [ENNReal.mul_div_cancel _ ENNReal.coe_ne_top]
              exact ENNReal.coe_ne_zero.2 hd
      | @add f1 f2 _ h1 h2 =>
        have hsum_ne_top :
            ((∫⁻ x, f1 x ∂mu) + ∫⁻ x, f2 x ∂mu) ≠ ⊤ := by
          rwa [← lintegral_add_left f1.measurable.coe_nnreal_ennreal]
        rcases h1 (ENNReal.add_ne_top.1 hsum_ne_top).1
            (ENNReal.half_pos hepsilon).ne' with ⟨g1, hg1, hg1cont, hg1int⟩
        rcases h2 (ENNReal.add_ne_top.1 hsum_ne_top).2
            (ENNReal.half_pos hepsilon).ne' with ⟨g2, hg2, hg2cont, hg2int⟩
        refine ⟨fun x ↦ g1 x + g2 x, fun x ↦ add_le_add (hg1 x) (hg2 x),
          hg1cont.add hg2cont, ?_⟩
        simp only [SimpleFunc.coe_add, ENNReal.coe_add, Pi.add_apply]
        rw [lintegral_add_left f1.measurable.coe_nnreal_ennreal,
          lintegral_add_left hg1cont.measurable.coe_nnreal_ennreal]
        convert! add_le_add hg1int hg2int using 1
        conv_lhs => rw [← ENNReal.add_halves epsilon]
        ac_rfl

    have exists_upperSemicontinuous_le_lintegral_le
        (mu : Measure ℝ) [WeaklyRegular mu]
        (f : ℝ → NNReal) (hf_ne_top : (∫⁻ x, f x ∂mu) ≠ ⊤)
        {epsilon : ENNReal} (hepsilon : epsilon ≠ 0) :
        ∃ g : ℝ → NNReal, (∀ x, g x ≤ f x) ∧ UpperSemicontinuous g ∧
          (∫⁻ x, f x ∂mu) ≤ (∫⁻ x, g x ∂mu) + epsilon := by
      obtain ⟨fs, hfs, hfsint⟩ : ∃ fs : SimpleFunc ℝ NNReal,
          (∀ x, fs x ≤ f x) ∧
          (∫⁻ x, f x ∂mu) ≤ (∫⁻ x, fs x ∂mu) + epsilon / 2 := by
        have hlt := ENNReal.lt_add_right hf_ne_top (ENNReal.half_pos hepsilon).ne'
        conv_rhs at hlt => rw [lintegral_eq_nnreal (fun x ↦ (f x : ENNReal)) mu]
        rw [ENNReal.biSup_add'] at hlt
        · rcases lt_iSup_iff.mp hlt with ⟨fs, hlt⟩
          rcases lt_iSup_iff.mp hlt with ⟨hfs, hfsint⟩
          refine ⟨fs, fun x ↦ ENNReal.coe_le_coe.mp (hfs x), ?_⟩
          convert! hfsint.le
          rw [← SimpleFunc.lintegral_eq_lintegral]
          simp only [SimpleFunc.coe_map, Function.comp_apply]
        · exact ⟨0, fun _ ↦ bot_le⟩
      have hfs_ne_top : (∫⁻ x, fs x ∂mu) ≠ ⊤ := by
        refine ne_top_of_le_ne_top hf_ne_top (lintegral_mono fun x ↦ ?_)
        exact ENNReal.coe_le_coe.mpr (hfs x)
      obtain ⟨g, hgfs, hgcont, hgint⟩ :=
        simple_exists_upperSemicontinuous_le_lintegral_le mu fs hfs_ne_top
          (ENNReal.half_pos hepsilon).ne'
      refine ⟨g, fun x ↦ (hgfs x).trans (hfs x), hgcont, ?_⟩
      calc
        (∫⁻ x, f x ∂mu) ≤ (∫⁻ x, fs x ∂mu) + epsilon / 2 := hfsint
        _ ≤ (∫⁻ x, g x ∂mu) + epsilon / 2 + epsilon / 2 :=
          add_le_add hgint le_rfl
        _ = (∫⁻ x, g x ∂mu) + epsilon := by rw [add_assoc, ENNReal.add_halves]

    have exists_upperSemicontinuous_le_integral_le
        (mu : Measure ℝ) [WeaklyRegular mu]
        (f : ℝ → NNReal) (hf : Integrable (fun x ↦ (f x : ℝ)) mu)
        {epsilon : ℝ} (hepsilon : 0 < epsilon) :
        ∃ g : ℝ → NNReal, (∀ x, g x ≤ f x) ∧ UpperSemicontinuous g ∧
          Integrable (fun x ↦ (g x : ℝ)) mu ∧
          (∫ x, (f x : ℝ) ∂mu) - epsilon ≤ ∫ x, (g x : ℝ) ∂mu := by
      lift epsilon to NNReal using hepsilon.le
      rw [NNReal.coe_pos, ← ENNReal.coe_pos] at hepsilon
      have hIf : (∫⁻ x, f x ∂mu) < ⊤ :=
        hasFiniteIntegral_iff_ofNNReal.1 hf.hasFiniteIntegral
      rcases exists_upperSemicontinuous_le_lintegral_le mu f hIf.ne hepsilon.ne' with
        ⟨g, hgf, hgcont, hgint⟩
      have hIg : (∫⁻ x, g x ∂mu) < ⊤ := by
        refine lt_of_le_of_lt (lintegral_mono fun x ↦ ?_) hIf
        simpa using hgf x
      refine ⟨g, hgf, hgcont, ?_, ?_⟩
      · refine Integrable.mono hf hgcont.measurable.coe_nnreal_real.aemeasurable.aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall fun x ↦ by simp [hgf x]
      · rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
        · rw [sub_le_iff_le_add]
          convert! ENNReal.toReal_mono _ hgint
          · simp
          · rw [ENNReal.toReal_add hIg.ne ENNReal.coe_ne_top]
            simp
          · simpa using hIg.ne
        · exact Filter.Eventually.of_forall fun x ↦ by simp
        · exact hgcont.measurable.coe_nnreal_real.aemeasurable.aestronglyMeasurable
        · exact Filter.Eventually.of_forall fun x ↦ by simp
        · exact hf.aestronglyMeasurable

    have exists_lt_lowerSemicontinuous_integral_lt
        (mu : Measure ℝ) [WeaklyRegular mu] [SigmaFinite mu]
        (f : ℝ → ℝ) (hf : Integrable f mu) {epsilon : ℝ}
        (hepsilon : 0 < epsilon) :
        ∃ g : ℝ → EReal, (∀ x, (f x : EReal) < g x) ∧
          LowerSemicontinuous g ∧ Integrable (fun x ↦ EReal.toReal (g x)) mu ∧
          (∀ᵐ x ∂mu, g x < ⊤) ∧
          (∫ x, EReal.toReal (g x) ∂mu) < (∫ x, f x ∂mu) + epsilon := by
      let delta : NNReal := ⟨epsilon / 2, (half_pos hepsilon).le⟩
      have hdelta_pos : 0 < delta := half_pos hepsilon
      let fp : ℝ → NNReal := fun x ↦ Real.toNNReal (f x)
      have hfpint : Integrable (fun x ↦ (fp x : ℝ)) mu := hf.real_toNNReal
      rcases exists_lt_lowerSemicontinuous_integral_gt_nnreal mu fp hfpint hdelta_pos with
        ⟨gp, hfp_gp, hgpcont, hgp_top, hgpint, hgp_bound⟩
      let fm : ℝ → NNReal := fun x ↦ Real.toNNReal (-f x)
      have hfmint : Integrable (fun x ↦ (fm x : ℝ)) mu := hf.neg.real_toNNReal
      rcases exists_upperSemicontinuous_le_integral_le mu fm hfmint hdelta_pos with
        ⟨gm, hgm_fm, hgmcont, hgmint, hgm_bound⟩
      let g : ℝ → EReal := fun x ↦ (gp x : EReal) - gm x
      have hgreal : ∀ᵐ x ∂mu,
          (g x).toReal = (gp x : EReal).toReal - (gm x : EReal).toReal := by
        filter_upwards [hgp_top] with x hx
        rw [EReal.toReal_sub] <;> simp [hx.ne]
      refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
      · intro x
        rw [EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (f x)]
        refine EReal.sub_lt_sub_of_lt_of_le ?_ ?_ ?_ ?_
        · exact EReal.coe_ennreal_lt_coe_ennreal_iff.2 (hfp_gp x)
        · exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (ENNReal.coe_le_coe.2 (hgm_fm x))
        · simp
        · simp
      · apply LowerSemicontinuous.add'
        · exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hgpcont
            (fun _ _ hxy ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy)
        · apply continuous_neg.comp_upperSemicontinuous_antitone _
            (fun _ _ hxy ↦ EReal.neg_le_neg_iff.2 hxy)
          apply continuous_coe_ennreal_ereal.comp_upperSemicontinuous _
              (fun _ _ hxy ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy)
          exact ENNReal.continuous_coe.comp_upperSemicontinuous hgmcont
            (fun _ _ hxy ↦ ENNReal.coe_le_coe.2 hxy)
        · intro x
          exact EReal.continuousAt_add (by simp) (by simp)
      · rw [integrable_congr hgreal]
        refine (hgpint.sub hgmint).congr (Filter.Eventually.of_forall fun x ↦ ?_)
        simp only [Pi.sub_apply, EReal.toReal_coe_ennreal, ENNReal.coe_toReal]
      · filter_upwards [hgp_top] with x hx
        change (gp x : EReal) + -(gm x : EReal) < ⊤
        apply EReal.add_lt_top
        · intro htop
          exact hx.ne (EReal.coe_ennreal_eq_top_iff.mp htop)
        · intro htop
          exact EReal.coe_ennreal_ne_bot _ (EReal.neg_eq_top_iff.mp htop)
      · calc
          (∫ x, (g x).toReal ∂mu) =
              ∫ x, EReal.toReal (gp x) - EReal.toReal (gm x) ∂mu :=
            integral_congr_ae hgreal
          _ = (∫ x, EReal.toReal (gp x) ∂mu) - ∫ x, (gm x : ℝ) ∂mu := by
            simp only [EReal.toReal_coe_ennreal, ENNReal.coe_toReal]
            exact integral_sub hgpint hgmint
          _ < (∫ x, (fp x : ℝ) ∂mu) + delta - ∫ x, (gm x : ℝ) ∂mu := by
            apply sub_lt_sub_right
            convert! hgp_bound
            simp only [EReal.toReal_coe_ennreal]
          _ ≤ (∫ x, (fp x : ℝ) ∂mu) + delta -
                ((∫ x, (fm x : ℝ) ∂mu) - delta) :=
            sub_le_sub_left hgm_bound _
          _ = (∫ x, f x ∂mu) + 2 * delta := by
            simp_rw [integral_eq_integral_pos_part_sub_integral_neg_part hf]
            ring
          _ = (∫ x, f x ∂mu) + epsilon := by
            congr 1
            change 2 * (epsilon / 2) = epsilon
            ring

    have continuous_primitive_integrable
        (f : ℝ → ℝ) (hf : Integrable f volume) (a : ℝ) :
        Continuous (fun b ↦ ∫ x in a..b, f x) := by
      rw [continuous_iff_continuousAt]
      intro b
      have hmeasure : Filter.Tendsto (fun x ↦ volume (uIoc b x))
          (nhds b) (nhds 0) := by
        simp only [Real.volume_uIoc]
        have hsub : Continuous (fun x : ℝ ↦ x - b) :=
          continuous_id.sub continuous_const
        have hreal : Filter.Tendsto (fun x : ℝ ↦ |x - b|)
            (nhds b) (nhds 0) := by
          have hc : ContinuousAt (fun x : ℝ ↦ |x - b|) b :=
            (continuous_abs.comp hsub).continuousAt
          change Filter.Tendsto (fun x : ℝ ↦ |x - b|) (nhds b)
            (nhds |b - b|) at hc
          simpa using hc
        have hcomp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
        change Filter.Tendsto (fun x : ℝ ↦ ENNReal.ofReal |x - b|)
          (nhds b) (nhds (ENNReal.ofReal 0)) at hcomp
        simpa using hcomp
      have hset : Filter.Tendsto (fun x ↦ ∫ t in uIoc b x, f t)
          (nhds b) (nhds 0) := hf.tendsto_setIntegral_nhds_zero hmeasure
      have hsmall : Filter.Tendsto (fun x ↦ ∫ t in b..x, f t)
          (nhds b) (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hnorm := hset.norm
        simpa only [norm_zero, intervalIntegral.norm_intervalIntegral_eq] using hnorm
      have hadd : ∀ x, ∫ t in a..x, f t =
          (∫ t in a..b, f t) + ∫ t in b..x, f t := by
        intro x
        exact (intervalIntegral.integral_add_adjacent_intervals
          hf.intervalIntegrable hf.intervalIntegrable).symm
      have hconst : Filter.Tendsto (fun _ : ℝ ↦ ∫ t in a..b, f t)
          (nhds b) (nhds (∫ t in a..b, f t)) := tendsto_const_nhds
      have ht : Filter.Tendsto
          (fun x : ℝ ↦ (∫ t in a..b, f t) + ∫ t in b..x, f t)
          (nhds b) (nhds (∫ t in a..b, f t)) := by
        simpa using hconst.add hsmall
      change Filter.Tendsto (fun x ↦ ∫ t in a..x, f t) (nhds b)
        (nhds (∫ t in a..b, f t))
      exact ht.congr' (Filter.Eventually.of_forall fun x ↦ (hadd x).symm)

    have continuousOn_primitive_Icc
        (f : ℝ → ℝ) (hf : IntegrableOn f (Icc (0 : ℝ) 1) volume) :
        ContinuousOn (fun x ↦ ∫ t in (0 : ℝ)..x, f t) (Icc 0 1) := by
      let f0 : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator f
      have hf0 : Integrable f0 volume := hf.integrable_indicator measurableSet_Icc
      have hc : ContinuousOn (fun x ↦ ∫ t in (0 : ℝ)..x, f0 t) (Icc 0 1) :=
        (continuous_primitive_integrable f0 hf0 0).continuousOn
      apply hc.congr
      intro x hx
      apply intervalIntegral.integral_congr
      intro y hy
      have hyIcc : y ∈ Icc (0 : ℝ) 1 := by
        rw [uIcc_of_le hx.1] at hy
        exact ⟨hy.1, hy.2.trans hx.2⟩
      simp only [f0, Set.indicator_of_mem hyIcc]

    have sub_le_integral_of_hasDerivWithinAt
        (g g' : ℝ → ℝ)
        (hgcont : ContinuousOn g (Icc (0 : ℝ) 1))
        (hgderiv : ∀ x ∈ Ico (0 : ℝ) 1,
          HasDerivWithinAt g (g' x) (Ioi x) x)
        (hgint : IntegrableOn g' (Icc (0 : ℝ) 1) volume) :
        g 1 - g 0 ≤ ∫ y in (0 : ℝ)..1, g' y := by
      refine le_of_forall_pos_le_add fun epsilon hepsilon ↦ ?_
      rcases exists_lt_lowerSemicontinuous_integral_lt
          (volume.restrict (Icc (0 : ℝ) 1)) g' hgint.integrable hepsilon with
        ⟨G, hgG, hGcont, hGint, hGtop, hGbound⟩
      let s := {t | g t - g 0 ≤ ∫ u in (0 : ℝ)..t, (G u).toReal} ∩ Icc (0 : ℝ) 1
      have hsclosed : IsClosed s := by
        have hpcont : ContinuousOn
            (fun t ↦ (g t - g 0, ∫ u in (0 : ℝ)..t, (G u).toReal)) (Icc 0 1) :=
          (hgcont.sub continuousOn_const).prodMk
            (continuousOn_primitive_Icc (fun u ↦ (G u).toReal) hGint)
        simp only [s, inter_comm]
        exact hpcont.preimage_isClosed_of_isClosed isClosed_Icc
          OrderClosedTopology.isClosed_le'
      have hmain : Icc (0 : ℝ) 1 ⊆
          {t | g t - g 0 ≤ ∫ u in (0 : ℝ)..t, (G u).toReal} := by
        refine hsclosed.Icc_subset_of_forall_exists_gt
          (by
            change g 0 - g 0 ≤ ∫ _u in (0 : ℝ)..0, (G _u).toReal
            rw [sub_self, intervalIntegral.integral_same])
          (fun t ht v htv ↦ ?_)
        obtain ⟨y, hgty, hyG⟩ : ∃ y : ℝ, (g' t : EReal) < y ∧ (y : EReal) < G t :=
          EReal.lt_iff_exists_real_btwn.1
            ((EReal.coe_le_coe_iff.2 le_rfl).trans_lt (hgG t))
        have hI1 : ∀ᶠ u in nhdsWithin t (Ioi t),
            (u - t) * y ≤ ∫ w in t..u, (G w).toReal := by
          have hnear : ∀ᶠ u in nhds t, (y : EReal) < G u :=
            hGcont.lowerSemicontinuousAt _ _ hyG
          rcases mem_nhds_iff_exists_Ioo_subset.1 hnear with
            ⟨m, M, ⟨hm, hM⟩, hsub⟩
          have hnbd : Ioo t (min M 1) ∈ nhdsWithin t (Ioi t) :=
            Ioo_mem_nhdsGT (lt_min hM ht.2.2)
          filter_upwards [hnbd] with u hu
          have hI : Icc t u ⊆ Icc (0 : ℝ) 1 :=
            Icc_subset_Icc ht.2.1 (hu.2.le.trans (min_le_right _ _))
          calc
            (u - t) * y = ∫ _ in Icc t u, y := by
              rw [MeasureTheory.integral_const,
                measureReal_restrict_apply MeasurableSet.univ, univ_inter,
                Real.volume_real_Icc_of_le hu.1.le, smul_eq_mul]
            _ ≤ ∫ w in t..u, (G w).toReal := by
              rw [intervalIntegral.integral_of_le hu.1.le, ← integral_Icc_eq_integral_Ioc]
              apply setIntegral_mono_ae_restrict
              · simp
              · exact IntegrableOn.mono_set hGint hI
              · have htop : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), G x < ⊤ :=
                  ae_mono (Measure.restrict_mono hI le_rfl) hGtop
                have hmem : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), x ∈ Icc t u :=
                  ae_restrict_mem measurableSet_Icc
                filter_upwards [htop, hmem] with x hGx hx
                apply EReal.coe_le_coe_iff.1
                have hxopen : x ∈ Ioo m M := by
                  exact ⟨hm.trans_le hx.1,
                    (hx.2.trans_lt hu.2).trans_le (min_le_left M 1)⟩
                refine (hsub hxopen).out.le.trans_eq ?_
                exact (EReal.coe_toReal hGx.ne (hgG x).ne_bot).symm
        have hI2 : ∀ᶠ u in nhdsWithin t (Ioi t),
            g u - g t ≤ (u - t) * y := by
          have hgty' : g' t < y := EReal.coe_lt_coe_iff.1 hgty
          have hrem :=
            (hasDerivWithinAt_iff_isLittleO.1 (hgderiv t ⟨ht.2.1, ht.2.2⟩)).bound
              (sub_pos.2 hgty')
          filter_upwards [hrem, self_mem_nhdsWithin] with u hu htu
          have htu_pos : 0 < u - t := sub_pos.2 htu
          have habs :
              |g u - g t - (u - t) * g' t| ≤ (y - g' t) * (u - t) := by
            simpa only [Real.norm_eq_abs, abs_of_pos htu_pos, smul_eq_mul] using hu
          have hres_le : g u - g t - (u - t) * g' t ≤
              (y - g' t) * (u - t) := (le_abs_self _).trans habs
          nlinarith
        have hI3 : ∀ᶠ u in nhdsWithin t (Ioi t),
            g u - g t ≤ ∫ w in t..u, (G w).toReal := by
          filter_upwards [hI1, hI2] with u hu1 hu2 using hu2.trans hu1
        have hI4 : ∀ᶠ u in nhdsWithin t (Ioi t), u ∈ Ioc t (min v 1) :=
          Ioc_mem_nhdsGT (lt_min htv ht.2.2)
        rcases (hI3.and hI4).exists with ⟨x, hx, hxin⟩
        refine ⟨x, ?_, Ioc_subset_Ioc le_rfl (min_le_left _ _) hxin⟩
        calc
          g x - g 0 = g t - g 0 + (g x - g t) := by ring
          _ ≤ (∫ w in (0 : ℝ)..t, (G w).toReal) + ∫ w in t..x, (G w).toReal :=
            add_le_add ht.1 hx
          _ = ∫ w in (0 : ℝ)..x, (G w).toReal := by
            apply intervalIntegral.integral_add_adjacent_intervals
            · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2.1]
              exact IntegrableOn.mono_set hGint
                (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2.2.le))
            · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxin.1.le]
              apply IntegrableOn.mono_set hGint
              exact Ioc_subset_Icc_self.trans
                (Icc_subset_Icc ht.2.1 (hxin.2.trans (min_le_right _ _)))
      calc
        g 1 - g 0 ≤ ∫ y in (0 : ℝ)..1, (G y).toReal :=
          hmain (right_mem_Icc.2 zero_le_one)
        _ ≤ (∫ y in (0 : ℝ)..1, g' y) + epsilon := by
          convert! hGbound.le <;>
            · rw [intervalIntegral.integral_of_le zero_le_one]
              simp only [integral_Icc_eq_integral_Ioc]

    have hasDerivAt_square (f : ℝ → ℝ) (f' x : ℝ)
        (hf : HasDerivAt f f' x) :
        HasDerivAt (fun y ↦ f y ^ 2) (2 * f x * f') x := by
      have hfrem := hf
      rw [hasDerivAt_iff_isLittleO] at hfrem ⊢
      let dx : ℝ → ℝ := fun y ↦ y - x
      let df : ℝ → ℝ := fun y ↦ f y - f x
      have hlin : (fun y ↦ dx y * f') =O[nhds x] dx := by
        refine ((Asymptotics.isBigO_refl dx (nhds x)).const_mul_left f').congr
          ?_ (fun _ ↦ rfl)
        intro y
        dsimp [dx]
        ring
      have hdf_big : df =O[nhds x] dx := by
        refine (hfrem.isBigO.add hlin).congr ?_ (fun _ ↦ rfl)
        intro y
        dsimp [df, dx]
        ring
      have hdf_zero : df =o[nhds x] (fun _ ↦ (1 : ℝ)) := by
        rw [Asymptotics.isLittleO_one_iff]
        have hc := hf.continuousAt.sub
          (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ f x) x)
        change Filter.Tendsto (fun y ↦ f y - f x) (nhds x)
          (nhds (f x - f x)) at hc
        simpa only [df, sub_self] using hc
      have hdf_sq : (fun y ↦ df y * df y) =o[nhds x] dx := by
        refine (hdf_big.mul_isLittleO hdf_zero).congr (fun _ ↦ rfl) ?_
        intro y
        simp only [dx, mul_one]
      have hrem :
          (fun y ↦ 2 * f x * (f y - f x - (y - x) * f')) =o[nhds x]
            (fun y ↦ y - x) := by
        exact hfrem.const_mul_left (2 * f x)
      refine (hdf_sq.add hrem).congr ?_ (fun _ ↦ rfl)
      intro y
      dsimp [df, dx]
      ring

    let F : ℝ → ℝ := fun x ↦ -(c / 2) * H x ^ 2
    have hFderivAt (x : ℝ) :
        HasDerivAt F (-c * H x * deriv H x) x := by
      have hsquare := hasDerivAt_square H (deriv H x) x (hH x).hasDerivAt
      have hmul := hasDerivAt_const_mul (-(c / 2)) (fun y ↦ H y ^ 2)
        (2 * H x * deriv H x) x hsquare
      change HasDerivAt (fun y ↦ -(c / 2) * H y ^ 2)
        (-c * H x * deriv H x) x
      exact hmul.congr_deriv (by ring)
    have hFdiff : Differentiable ℝ F := fun x ↦ (hFderivAt x).differentiableAt
    have hFderiv (x : ℝ) : deriv F x = -c * H x * deriv H x :=
      (hFderivAt x).deriv
    have hFint : IntervalIntegrable (deriv F) volume 0 1 := by
      apply hqint.congr_uIoo
      intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) 1 := by
        simpa [uIoo_of_le zero_le_one] using hx
      exact (hq x hx').trans (hFderiv x).symm
    have hFintOn : IntegrableOn (deriv F) (Icc (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one
        (enorm_ne_top : ‖deriv F 0‖ₑ ≠ ⊤)).1 hFint
    have hupper : F 1 - F 0 ≤ ∫ x in (0 : ℝ)..1, deriv F x :=
      sub_le_integral_of_hasDerivWithinAt F (deriv F) hFdiff.continuous.continuousOn
        (fun x _ ↦ by
          rw [hFderiv x]
          exact (hFderivAt x).hasDerivWithinAt) hFintOn
    have hnegDeriv (x : ℝ) :
        HasDerivAt (fun y ↦ -F y) (-deriv F x) x := by
      have hmul := hasDerivAt_const_mul (-1) F (deriv F x) x
        (hFdiff x).hasDerivAt
      refine (hmul.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ ?_)).congr_deriv ?_
      · ring
      · ring
    have hnegInt : IntegrableOn (fun x ↦ -deriv F x) (Icc (0 : ℝ) 1) volume := by
      exact hFintOn.neg
    have hlower : (-F 1) - (-F 0) ≤ ∫ x in (0 : ℝ)..1, -deriv F x :=
      sub_le_integral_of_hasDerivWithinAt (fun x ↦ -F x) (fun x ↦ -deriv F x)
        hFdiff.continuous.fun_neg.continuousOn
        (fun x _ ↦ (hnegDeriv x).hasDerivWithinAt) hnegInt
    rw [intervalIntegral.integral_neg] at hlower
    have hFTC : (∫ x in (0 : ℝ)..1, deriv F x) = F 1 - F 0 := by
      linarith
    calc
      (∫ x in (0 : ℝ)..1, q x) = ∫ x in (0 : ℝ)..1, deriv F x :=
        intervalIntegral.integral_congr_ae (by
          have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
            rw [ae_iff]
            change volume {x : ℝ | ¬ x ≠ 1} = 0
            rw [show {x : ℝ | ¬ x ≠ 1} = ({1} : Set ℝ) by
              ext x
              exact not_ne_iff]
            exact measure_singleton 1
          filter_upwards [hne] with x hxne
          intro hx
          rw [uIoc_of_le zero_le_one] at hx
          have hxIoo : x ∈ Ioo (0 : ℝ) 1 :=
            ⟨hx.1, lt_of_le_of_ne hx.2 hxne⟩
          exact (hq x hxIoo).trans (hFderiv x).symm)
      _ = F 1 - F 0 := hFTC
      _ = -(c / 2) * (H 1 ^ 2 - H 0 ^ 2) := by
        dsimp [F]
        ring

  let workCoefficient : ℝ :=
    data.permeability.val * data.volume.val * susceptibility
  have heatIntegral_eq (p : TorusProcess)
      (hp : IsFixedTemperatureProcess data temperature H_i H_f p) :
      (∫ tau in (0 : ℝ)..1, (p.heatEntering tau).val) =
        -(workCoefficient / 2) * (H_f.val ^ 2 - H_i.val ^ 2) := by
    rcases hp with ⟨_, hregular, hfield_i, hfield_f, htemperature_fixed,
      hvolume_fixed, _, hequation, hinternal, hwork, hfirst⟩
    let H : ℝ → ℝ := fun x ↦ (p.state x).fieldStrength.val
    let M : ℝ → ℝ := fun x ↦ (p.state x).magnetization.val
    let T : ℝ → ℝ := fun x ↦ (p.state x).temperature.val
    have hM_eq (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
        M x = susceptibility * H x := by
      have heq := hequation x hx
      unfold SatisfiesEquationOfState at heq
      have hTx := congrArg WithDim.val (htemperature_fixed x hx)
      have hVx := congrArg WithDim.val (hvolume_fixed x hx)
      dsimp [T, M, H] at hTx hVx ⊢
      rw [hTx, hVx] at heq
      dsimp [susceptibility]
      have hden : temperature.val * data.volume.val ≠ 0 :=
        mul_ne_zero htemperature.ne' hvolume.ne'
      calc
        (p.state x).magnetization.val =
            (data.amount.val * data.curieParameter.val * H x) /
              (temperature.val * data.volume.val) := by
          apply (eq_div_iff hden).2
          calc
            (p.state x).magnetization.val *
                  (temperature.val * data.volume.val) =
                temperature.val * (p.state x).magnetization.val *
                  data.volume.val := by ring
            _ = data.amount.val * data.curieParameter.val * H x := heq
        _ = data.amount.val * data.curieParameter.val /
              (temperature.val * data.volume.val) * H x :=
          (div_mul_eq_mul_div
            (data.amount.val * data.curieParameter.val)
            (temperature.val * data.volume.val) (H x)).symm
    have hheat_rate (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
        (p.heatEntering x).val =
          -workCoefficient * H x * deriv H x := by
      have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
      have hMlocal : M =ᶠ[nhds x] fun y ↦ susceptibility * H y := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
        exact hM_eq y ⟨hy.1.le, hy.2.le⟩
      have hMderiv : deriv M x = susceptibility * deriv H x := by
        calc
          deriv M x = deriv (fun y ↦ susceptibility * H y) x := hMlocal.deriv_eq
          _ = susceptibility * deriv H x :=
            (hasDerivAt_const_mul susceptibility H (deriv H x) x
              (hregular.2.1 x).hasDerivAt).deriv
      have hTlocal : T =ᶠ[nhds x] fun _ ↦ temperature.val := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
        exact congrArg WithDim.val
          (htemperature_fixed y ⟨hy.1.le, hy.2.le⟩)
      have hTderiv : deriv T x = 0 := by
        calc
          deriv T x = deriv (fun _ : ℝ ↦ temperature.val) x := hTlocal.deriv_eq
          _ = 0 := deriv_const x temperature.val
      have hint := hinternal x hxIcc
      have hwrk := hwork x hxIcc
      have hfst := hfirst x hxIcc
      have hVx := congrArg WithDim.val (hvolume_fixed x hxIcc)
      change deriv (fun y ↦ (p.state y).internalEnergy.val) x =
        (heatCapacityAtConstantMagnetization data (p.state x).temperature).val *
          deriv T x at hint
      rw [hTderiv, mul_zero] at hint
      change (p.workEntering x).val =
        data.permeability.val * (p.state x).volume.val * H x * deriv M x at hwrk
      rw [hVx, hMderiv] at hwrk
      change deriv (fun y ↦ (p.state y).internalEnergy.val) x =
        (p.heatEntering x).val + (p.workEntering x).val at hfst
      dsimp [workCoefficient]
      nlinarith [hint, hwrk, hfst]
    have hHdiff : Differentiable ℝ H := hregular.2.1
    have hqint : IntervalIntegrable
        (fun x ↦ (p.heatEntering x).val) MeasureTheory.volume 0 1 :=
      hregular.2.2.2.2.2.2
    rw [newtonLeibniz_mul_deriv H (fun x ↦ (p.heatEntering x).val)
      workCoefficient hHdiff hqint hheat_rate]
    have hHi := congrArg WithDim.val hfield_i
    have hHf := congrArg WithDim.val hfield_f
    dsimp [H] at hHi hHf ⊢
    rw [hHi, hHf]

  have hpath_independent :
      ∀ p₁ p₂ : TorusProcess,
        IsFixedTemperatureProcess data temperature H_i H_f p₁ →
        IsFixedTemperatureProcess data temperature H_i H_f p₂ →
        (∫ tau in (0 : ℝ)..1, (p₁.heatEntering tau).val) =
          ∫ tau in (0 : ℝ)..1, (p₂.heatEntering tau).val := by
    intro p₁ p₂ hp₁ hp₂
    exact (heatIntegral_eq p₁ hp₁).trans (heatIntegral_eq p₂ hp₂).symm

  obtain ⟨p₀, hp₀⟩ := hprocess_exists
  let Q₀ : Energy := ⟨∫ tau in (0 : ℝ)..1, (p₀.heatEntering tau).val⟩
  refine ⟨Q₀, ?_, ?_⟩
  · constructor
    · exact ⟨p₀, hp₀⟩
    · intro p hp
      unfold HasNetHeatEntering
      dsimp [Q₀]
      exact hpath_independent p₀ p hp₀ hp
  · intro Q hQ
    apply WithDim.ext
    exact (hQ.2 p₀ hp₀).trans (hpath_independent p₀ p₀ hp₀ hp₀).symm

end Ipho2026Gpt56solBlind.Problem3B1
