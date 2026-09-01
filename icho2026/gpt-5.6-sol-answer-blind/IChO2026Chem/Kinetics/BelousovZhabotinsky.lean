import IChO2026Chem.Core

/-!
# Shared Belousov--Zhabotinsky kinetics

The numerical conventions in this module are those printed in IChO 2026,
Theory Problem 2.  Concentrations and elementary rates are represented by
their real numerical readouts in the corresponding source units.
-/

namespace IChO2026Chem.Kinetics.BelousovZhabotinsky

/-! ## Project-local Mathlib supplement — Belousov--Zhabotinsky kinetics -/

/-- A molar concentration is its numerical readout in the source's `M` scale. -/
abbrev MolarConcentration := ℝ

/-- A second-order constant is its numerical readout in `M⁻¹ s⁻¹`. -/
abbrev SecondOrderRateConstant := ℝ

/-- A third-order constant is its numerical readout in `M⁻² s⁻¹`. -/
abbrev ThirdOrderRateConstant := ℝ

/-- A fourth-order constant is its numerical readout in `M⁻³ s⁻¹`. -/
abbrev FourthOrderRateConstant := ℝ

/-- The BZ species needed by the shared elementary-step mass-action laws. -/
inductive Species where
  | hbro2
  | bromate
  | bromide
  | proton
  | bro2Radical
  | hbro
  | ceIII
  | ceIV
  | bma
  | malonicAcid
  deriving DecidableEq, Repr

deriving instance Fintype for Species

/-- A BZ state assigns each shared species its molar concentration. -/
abbrev State := Species → MolarConcentration

/-- The source-given kinetic constants, separated by elementary-step order. -/
structure KineticParameters where
  k1 : ThirdOrderRateConstant
  k2 : ThirdOrderRateConstant
  k3 : SecondOrderRateConstant
  k4 : ThirdOrderRateConstant
  k5 : FourthOrderRateConstant
  k6 : SecondOrderRateConstant
  k7 : SecondOrderRateConstant

/-- The mass-action rate of `HBrO₂ + BrO₃⁻ + H⁺ → 2 BrO₂• + H₂O`. -/
def rate1 (parameters : KineticParameters) (state : State) : ℝ :=
  parameters.k1 * state .hbro2 * state .bromate * state .proton

/-- The mass-action rate of `BrO₂• + Ce(III) + H⁺ → HBrO₂ + Ce(IV)`. -/
def rate2 (parameters : KineticParameters) (state : State) : ℝ :=
  parameters.k2 * state .bro2Radical * state .ceIII * state .proton

/-- The mass-action rate of `2 HBrO₂ → BrO₃⁻ + HBrO + H⁺`. -/
def rate3 (parameters : KineticParameters) (state : State) : ℝ :=
  parameters.k3 * state .hbro2 ^ 2

/-- The mass-action rate of `HBrO₂ + Br⁻ + H⁺ → 2 HBrO`. -/
def rate4 (parameters : KineticParameters) (state : State) : ℝ :=
  parameters.k4 * state .hbro2 * state .bromide * state .proton

/-- The mass-action rate of `BrO₃⁻ + Br⁻ + 2 H⁺ → HBrO + HBrO₂`. -/
def rate5 (parameters : KineticParameters) (state : State) : ℝ :=
  parameters.k5 * state .bromate * state .bromide * state .proton ^ 2

/-- The mass-action rate of `HBrO + malonic acid → products`. -/
def rate6 (parameters : KineticParameters) (state : State) : ℝ :=
  parameters.k6 * state .hbro * state .malonicAcid

/-- The mass-action rate of `Ce(IV) + BMA → Ce(III) + Br⁻ + products`. -/
def rate7 (parameters : KineticParameters) (state : State) : ℝ :=
  parameters.k7 * state .ceIV * state .bma

/-- Positive common HBrO₂ and H⁺ factors can be cancelled from equal rates 1 and 4. -/
theorem rate1_eq_rate4_of_positive
    (parameters : KineticParameters) (state : State)
    (hhbro2 : 0 < state .hbro2) (hproton : 0 < state .proton)
    (h : rate1 parameters state = rate4 parameters state) :
    parameters.k1 * state .bromate = parameters.k4 * state .bromide := by
  apply mul_left_cancel₀ (mul_ne_zero (ne_of_gt hhbro2) (ne_of_gt hproton))
  calc
    (state .hbro2 * state .proton) * (parameters.k1 * state .bromate) =
        parameters.k1 * state .hbro2 * state .bromate * state .proton := by ring
    _ = parameters.k4 * state .hbro2 * state .bromide * state .proton := h
    _ = (state .hbro2 * state .proton) * (parameters.k4 * state .bromide) := by ring

/-- Updating a state only at bromide specializes the step-(4) mass-action law. -/
theorem rate4_update_bromide (parameters : KineticParameters) (state : State)
    (bromide : MolarConcentration) :
    rate4 parameters (Function.update state .bromide bromide) =
      parameters.k4 * state .hbro2 * bromide * state .proton := by
  simp [rate4]

/-- Updating a state only at bromide specializes the step-(5) mass-action law. -/
theorem rate5_update_bromide (parameters : KineticParameters) (state : State)
    (bromide : MolarConcentration) :
    rate5 parameters (Function.update state .bromide bromide) =
      parameters.k5 * state .bromate * bromide * state .proton ^ 2 := by
  simp [rate5]

end IChO2026Chem.Kinetics.BelousovZhabotinsky
