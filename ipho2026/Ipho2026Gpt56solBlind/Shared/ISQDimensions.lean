import Mathlib.Tactic
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic

/-!
# Shared ISQ dimensions and coherent-SI coordinates

This module fixes the answer-independent dimensional vocabulary used by the
problem formalizations.  Dimensions use Physlib's seven-element ISQ basis, and
dimensioned quantities retain that basis index through `WithDim`.  Conversion
to coherent SI is an explicit boundary because Physlib's `HasDim` machinery is
for its LTMCT basis rather than the ISQ basis.
-/

namespace Ipho2026Gpt56solBlind.Shared.ISQDimensions

/-! ## Base dimensions -/

/-- The ISQ length base dimension. -/
def lengthDimension : Dimension ISQDimensionBase :=
  Dimension.single .length

/-- The ISQ time base dimension. -/
def timeDimension : Dimension ISQDimensionBase :=
  Dimension.single .time

/-- The ISQ mass base dimension. -/
def massDimension : Dimension ISQDimensionBase :=
  Dimension.single .mass

/-- The ISQ electric-current base dimension. -/
def currentDimension : Dimension ISQDimensionBase :=
  Dimension.single .current

/-- The ISQ thermodynamic-temperature base dimension. -/
def temperatureDimension : Dimension ISQDimensionBase :=
  Dimension.single .temperature

/-- The ISQ amount-of-substance base dimension. -/
def amountDimension : Dimension ISQDimensionBase :=
  Dimension.single .amount

/-! ## Derived dimensions -/

/-- Area has length-squared dimension. -/
def areaDimension : Dimension ISQDimensionBase :=
  lengthDimension ^ (2 : ℕ)

/-- Volume has length-cubed dimension. -/
def volumeDimension : Dimension ISQDimensionBase :=
  lengthDimension ^ (3 : ℕ)

/-- Mechanical energy has mass times area per time-squared dimension. -/
def energyDimension : Dimension ISQDimensionBase :=
  massDimension * areaDimension * (timeDimension ^ (2 : ℕ))⁻¹

/-- A signed energy rate has energy per time dimension. -/
def heatRateDimension : Dimension ISQDimensionBase :=
  energyDimension * timeDimension⁻¹

/-- Pressure has energy per volume dimension. -/
def pressureDimension : Dimension ISQDimensionBase :=
  energyDimension * volumeDimension⁻¹

/-- Mass density has mass per volume dimension. -/
def massDensityDimension : Dimension ISQDimensionBase :=
  massDimension * volumeDimension⁻¹

/-- Molar mass has mass per amount-of-substance dimension. -/
def molarMassDimension : Dimension ISQDimensionBase :=
  massDimension * amountDimension⁻¹

/-- A molar gas constant has energy per amount per temperature dimension. -/
def molarGasConstantDimension : Dimension ISQDimensionBase :=
  energyDimension * amountDimension⁻¹ * temperatureDimension⁻¹

/-- An amount-to-count conversion factor has inverse-amount dimension. -/
def inverseAmountDimension : Dimension ISQDimensionBase :=
  amountDimension⁻¹

/-- Heat capacity has energy per temperature dimension. -/
def heatCapacityDimension : Dimension ISQDimensionBase :=
  energyDimension * temperatureDimension⁻¹

/-- A spatial temperature gradient has temperature per length dimension. -/
def temperatureGradientDimension : Dimension ISQDimensionBase :=
  temperatureDimension * lengthDimension⁻¹

/-- Thermal resistance has temperature difference per heat rate dimension. -/
def thermalResistanceDimension : Dimension ISQDimensionBase :=
  temperatureDimension * heatRateDimension⁻¹

/-- Thermal conductivity has heat rate per area per temperature gradient dimension. -/
def thermalConductivityDimension : Dimension ISQDimensionBase :=
  heatRateDimension * areaDimension⁻¹ * temperatureGradientDimension⁻¹

/-- Magnetic field strength and magnetization have current per length dimension. -/
def magneticFieldStrengthDimension : Dimension ISQDimensionBase :=
  currentDimension * lengthDimension⁻¹

/-- Magnetic flux density has mass per current per time-squared dimension. -/
def magneticFluxDensityDimension : Dimension ISQDimensionBase :=
  massDimension * currentDimension⁻¹ * (timeDimension ^ (2 : ℕ))⁻¹

/-- Permeability has magnetic-flux-density per field-strength dimension. -/
def permeabilityDimension : Dimension ISQDimensionBase :=
  magneticFluxDensityDimension * magneticFieldStrengthDimension⁻¹

/-- The Curie parameter has temperature times volume per amount dimension. -/
def curieParameterDimension : Dimension ISQDimensionBase :=
  temperatureDimension * volumeDimension * amountDimension⁻¹

/-- The coefficient in `C = n λ / T²` has energy-temperature per amount dimension. -/
def heatCapacityCoefficientDimension : Dimension ISQDimensionBase :=
  energyDimension * temperatureDimension * amountDimension⁻¹

/-! ## Dimensioned real quantities -/

/-- A real coordinate carrying a fixed ISQ dimension. -/
abbrev Quantity (d : Dimension ISQDimensionBase) := WithDim d ℝ

/-- Length quantities. -/
abbrev Length := Quantity lengthDimension

/-- Time quantities. -/
abbrev Time := Quantity timeDimension

/-- Mass quantities. -/
abbrev Mass := Quantity massDimension

/-- Electric-current quantities. -/
abbrev ElectricCurrent := Quantity currentDimension

/-- Absolute-temperature quantities; positivity is imposed separately. -/
abbrev Temperature := Quantity temperatureDimension

/-- Signed temperature-difference quantities. -/
abbrev TemperatureDifference := Quantity temperatureDimension

/-- Amount-of-substance quantities. -/
abbrev AmountOfSubstance := Quantity amountDimension

/-- Area quantities. -/
abbrev Area := Quantity areaDimension

/-- Volume quantities. -/
abbrev Volume := Quantity volumeDimension

/-- Signed energy quantities. -/
abbrev Energy := Quantity energyDimension

/-- Signed heat-rate quantities. -/
abbrev HeatRate := Quantity heatRateDimension

/-- Pressure quantities. -/
abbrev Pressure := Quantity pressureDimension

/-- Mass-density quantities. -/
abbrev MassDensity := Quantity massDensityDimension

/-- Molar-mass quantities. -/
abbrev MolarMass := Quantity molarMassDimension

/-- Molar-gas-constant quantities. -/
abbrev MolarGasConstant := Quantity molarGasConstantDimension

/-- Inverse-amount quantities. -/
abbrev InverseAmount := Quantity inverseAmountDimension

/-- Heat-capacity quantities. -/
abbrev HeatCapacity := Quantity heatCapacityDimension

/-- Temperature-gradient quantities. -/
abbrev TemperatureGradient := Quantity temperatureGradientDimension

/-- Thermal-resistance quantities. -/
abbrev ThermalResistance := Quantity thermalResistanceDimension

/-- Thermal-conductivity quantities. -/
abbrev ThermalConductivity := Quantity thermalConductivityDimension

/-- Magnetic-field-strength quantities. -/
abbrev MagneticFieldStrength := Quantity magneticFieldStrengthDimension

/-- Magnetization quantities, dimensionally equal to magnetic field strength. -/
abbrev Magnetization := Quantity magneticFieldStrengthDimension

/-- Magnetic-flux-density quantities. -/
abbrev MagneticFluxDensity := Quantity magneticFluxDensityDimension

/-- Permeability quantities. -/
abbrev Permeability := Quantity permeabilityDimension

/-- Curie-parameter quantities. -/
abbrev CurieParameter := Quantity curieParameterDimension

/-- Heat-capacity-coefficient quantities. -/
abbrev HeatCapacityCoefficient := Quantity heatCapacityCoefficientDimension

/-! ## Canonical conversion to coherent SI -/

/-- The real coordinate of a dimensioned quantity after conversion from the
source unit choice to coherent SI. -/
noncomputable def coordinateInSI (sourceUnits : SIUnitChoices)
    {d : Dimension ISQDimensionBase} (x : Quantity d) : ℝ :=
  ↑(SIUnitChoices.dimScale sourceUnits SIUnitChoices.SI d) * x.val

/-- Conversion from a source unit choice to coherent SI, retaining the exact
dimension index. -/
noncomputable def quantityInSI (sourceUnits : SIUnitChoices)
    {d : Dimension ISQDimensionBase} (x : Quantity d) : Quantity d :=
  ⟨coordinateInSI sourceUnits x⟩

/-- Every source-to-coherent-SI dimensional scale is strictly positive. -/
lemma dimScaleToSI_pos (sourceUnits : SIUnitChoices)
    (d : Dimension ISQDimensionBase) :
    0 < SIUnitChoices.dimScale sourceUnits SIUnitChoices.SI d := by
  simp only [SIUnitChoices.dimScale, UnitScale.dimScale, MonoidHom.coe_mk,
    OneHom.coe_mk]
  refine Finset.prod_pos fun b _ ↦ NNReal.rpow_pos ?_
  exact div_pos (sourceUnits.toScale.scale_pos b)
    (SIUnitChoices.SI.toScale.scale_pos b)

/-- Conversion of an already coherent-SI coordinate is the identity. -/
@[simp]
lemma coordinateInSI_self {d : Dimension ISQDimensionBase} (x : Quantity d) :
    coordinateInSI SIUnitChoices.SI x = x.val := by
  simp [coordinateInSI, SIUnitChoices.dimScale_self]

/-- Conversion of an already coherent-SI quantity is the identity. -/
@[simp]
lemma quantityInSI_self {d : Dimension ISQDimensionBase} (x : Quantity d) :
    quantityInSI SIUnitChoices.SI x = x := by
  apply WithDim.ext
  simp [quantityInSI]

/-- Coherent-SI coordinates characterize equality within each fixed dimension. -/
lemma coordinateInSI_eq_iff (sourceUnits : SIUnitChoices)
    {d : Dimension ISQDimensionBase} (x y : Quantity d) :
    coordinateInSI sourceUnits x = coordinateInSI sourceUnits y ↔ x = y := by
  constructor
  · intro h
    apply WithDim.ext
    apply mul_left_cancel₀
      (NNReal.coe_ne_zero.mpr (ne_of_gt (dimScaleToSI_pos sourceUnits d)))
    simpa only [coordinateInSI] using h
  · rintro rfl
    rfl

/-- Dimension-preserving coherent-SI conversion is injective at each dimension. -/
lemma quantityInSI_eq_iff (sourceUnits : SIUnitChoices)
    {d : Dimension ISQDimensionBase} (x y : Quantity d) :
    quantityInSI sourceUnits x = quantityInSI sourceUnits y ↔ x = y := by
  constructor
  · intro h
    apply (coordinateInSI_eq_iff sourceUnits x y).mp
    simpa only [quantityInSI] using congrArg WithDim.val h
  · rintro rfl
    rfl

/-! ## Dimensional identities for physical laws -/

/-- Expanded mechanical energy dimension. -/
lemma energyDimension_eq :
    energyDimension =
      massDimension * lengthDimension ^ (2 : ℕ) * (timeDimension ^ (2 : ℕ))⁻¹ := by
  rfl

/-- Pressure times volume has energy dimension. -/
lemma pressure_mul_volume_dimension :
    pressureDimension * volumeDimension = energyDimension := by
  ext b
  simp [pressureDimension]

/-- Amount times the molar gas constant times temperature has energy dimension. -/
lemma amount_mul_molarGasConstant_mul_temperature_dimension :
    amountDimension * molarGasConstantDimension * temperatureDimension = energyDimension := by
  ext b
  simp [molarGasConstantDimension]
  ring

/-- The two products in the ideal-gas equation have the same dimension. -/
lemma idealGas_products_dimension :
    pressureDimension * volumeDimension =
      amountDimension * molarGasConstantDimension * temperatureDimension := by
  rw [pressure_mul_volume_dimension,
    amount_mul_molarGasConstant_mul_temperature_dimension]

/-- Permeability times field strength has magnetic-flux-density dimension. -/
lemma permeability_mul_magneticFieldStrength_dimension :
    permeabilityDimension * magneticFieldStrengthDimension =
      magneticFluxDensityDimension := by
  ext b
  simp [permeabilityDimension]

/-- The two products in the magnetic equation of state have equal dimension. -/
lemma magneticEquationOfState_products_dimension :
    temperatureDimension * magneticFieldStrengthDimension * volumeDimension =
      amountDimension * curieParameterDimension * magneticFieldStrengthDimension := by
  ext b
  simp [curieParameterDimension]
  ring

/-- Permeability times volume times two field-strength factors has energy dimension. -/
lemma magneticWork_product_dimension :
    permeabilityDimension * volumeDimension * magneticFieldStrengthDimension *
        magneticFieldStrengthDimension = energyDimension := by
  ext b
  simp [permeabilityDimension, magneticFluxDensityDimension,
    magneticFieldStrengthDimension, volumeDimension, energyDimension, areaDimension]
  ring

/-- Heat capacity times temperature has energy dimension. -/
lemma heatCapacity_mul_temperature_dimension :
    heatCapacityDimension * temperatureDimension = energyDimension := by
  ext b
  simp [heatCapacityDimension]

/-- The product in `C = n λ / T²` has heat-capacity dimension. -/
lemma heatCapacityCoefficient_law_dimension :
    amountDimension * heatCapacityCoefficientDimension *
        (temperatureDimension ^ (2 : ℕ))⁻¹ = heatCapacityDimension := by
  ext b
  simp [heatCapacityCoefficientDimension, heatCapacityDimension]
  ring

/-- Heat rate times thermal resistance has temperature-difference dimension. -/
lemma heatRate_mul_thermalResistance_dimension :
    heatRateDimension * thermalResistanceDimension = temperatureDimension := by
  ext b
  simp [thermalResistanceDimension]

/-- Thermal conductivity times area times temperature gradient has heat-rate dimension. -/
lemma fourier_product_dimension :
    thermalConductivityDimension * areaDimension * temperatureGradientDimension =
      heatRateDimension := by
  ext b
  simp [thermalConductivityDimension]
  ring

end Ipho2026Gpt56solBlind.Shared.ISQDimensions
