import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits

/-!
# Temperature adapters

Thin, assumption-preserving adapters between ChemistryLib and Physlib's absolute-temperature
and temperature-unit interfaces.

Grounding sources:

* `grounding:Physlib.Thermodynamics.Temperature.Basic` at revision
  `1706ae68b63996f1d97717e672e50c9e3933d933`
* `grounding:Physlib.Thermodynamics.Temperature.TemperatureUnits` at revision
  `1706ae68b63996f1d97717e672e50c9e3933d933`
-/

namespace ChemistryLib.Thermodynamics

/-- The absolute temperature is strictly positive. -/
def PositiveAbsoluteTemperature (T : Temperature) : Prop :=
  0 < T.val

/-- Explicit semantics for interpreting a real-valued reading in a given temperature unit. -/
structure TemperatureReadingSemantics (_unit : TemperatureUnit) where
  /-- Convert a reading in the indexed unit to an absolute temperature. -/
  toTemperature : ℝ → Temperature

/-- Inverse absolute temperature, exposed as a real number. -/
noncomputable def inverseTemperature
    (T : Temperature) (_hT : PositiveAbsoluteTemperature T) : ℝ :=
  (T.β : ℝ)

/-- The ChemistryLib adapter is definitionally Physlib's inverse temperature. -/
theorem inverseTemperature_eq_beta_toReal
    (T : Temperature) (hT : PositiveAbsoluteTemperature T) :
    inverseTemperature T hT = (T.β : ℝ) := by
  rfl

/-- Physlib's closed form for inverse temperature. -/
theorem inverseTemperature_eq_one_div_kB_mul_temperature
    (T : Temperature) (hT : PositiveAbsoluteTemperature T) :
    inverseTemperature T hT = 1 / (Constants.kB * T.val) := by
  simpa only [inverseTemperature, Temperature.toReal] using T.β_toReal

/-- Inverse temperature is positive when absolute temperature is positive. -/
theorem inverseTemperature_pos
    (T : Temperature) (hT : PositiveAbsoluteTemperature T) :
    0 < inverseTemperature T hT := by
  exact T.beta_pos hT

/-- Interpret a real-valued reading using the supplied unit-specific semantics. -/
def temperatureOfReading
    (unit : TemperatureUnit) (semantics : TemperatureReadingSemantics unit) :
    ℝ → Temperature :=
  semantics.toTemperature

end ChemistryLib.Thermodynamics
