import Mathlib
import Ipho2026Gpt56solBlind.Shared.ISQDimensions
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic

/-!
# Shared paramagnetic thermodynamics

This file gives an answer-independent model of a thin paramagnetic torus and
one regular quasistatic process leg.  Dimensioned data remain indexed by the
seven-base ISQ dimension group.  Differentiation, integration, logarithms,
and products are taken only after every quantity has been converted from the
single apparatus unit choice to a coherent-SI real coordinate.

The winding direction, Ampere-loop direction, and positive flux normal are
fixed together.  Thus positive current produces positive field strength,
Faraday's law carries its explicit minus sign, and source balance supplies
the second sign reversal.  Work entering the material is obtained only after
subtracting the vacuum-field contribution.
-/

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics

open Ipho2026Gpt56solBlind.Shared.ISQDimensions

/-! ## Coherent coordinates, dimensions, and transfer signs -/

/-- The coherent-SI real coordinate used by every physical law in this file. -/
def coherentCoordinate (sourceUnits : SIUnitChoices)
    {d : Dimension ISQDimensionBase} (x : Quantity d) : ℝ :=
  coordinateInSI sourceUnits x

/-- Construct the unique quantity with a prescribed coherent-SI coordinate. -/
def quantityFromCoherentCoordinate (sourceUnits : SIUnitChoices)
    (d : Dimension ISQDimensionBase) (x : ℝ) : Quantity d :=
  ⟨x / (SIUnitChoices.dimScale sourceUnits SIUnitChoices.SI d : ℝ)⟩

/-- Reconstruction has the prescribed coherent-SI coordinate. -/
lemma coherentCoordinate_quantityFromCoherentCoordinate (sourceUnits : SIUnitChoices)
    (d : Dimension ISQDimensionBase) (x : ℝ) :
    coherentCoordinate sourceUnits
      (quantityFromCoherentCoordinate sourceUnits d x) = x := by
  have hscale :
      (SIUnitChoices.dimScale sourceUnits SIUnitChoices.SI d : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (ne_of_gt (dimScaleToSI_pos sourceUnits d))
  simp only [coherentCoordinate, quantityFromCoherentCoordinate, coordinateInSI]
  field_simp

/-- A fixed coherent-SI coordinate reconstructs a unique quantity at each dimension. -/
lemma quantityFromCoherentCoordinate_unique (sourceUnits : SIUnitChoices)
    (d : Dimension ISQDimensionBase) (x : ℝ) (q : Quantity d)
    (hq : coherentCoordinate sourceUnits q = x) :
    q = quantityFromCoherentCoordinate sourceUnits d x := by
  apply (coordinateInSI_eq_iff sourceUnits q
    (quantityFromCoherentCoordinate sourceUnits d x)).mp
  change coherentCoordinate sourceUnits q =
    coherentCoordinate sourceUnits
      (quantityFromCoherentCoordinate sourceUnits d x)
  rw [hq, coherentCoordinate_quantityFromCoherentCoordinate]

/-- Magnetic flux is magnetic-flux density times area. -/
def magneticFluxDimension : Dimension ISQDimensionBase :=
  magneticFluxDensityDimension * areaDimension

/-- Dimensioned magnetic flux, also used for an emf increment per unit
dimensionless process parameter. -/
abbrev MagneticFlux := Quantity magneticFluxDimension

/-- Current times a linked-flux increment has energy dimension. -/
lemma current_mul_magneticFlux_dimension :
    currentDimension * magneticFluxDimension = energyDimension := by
  ext b
  simp [magneticFluxDimension, magneticFluxDensityDimension, areaDimension,
    energyDimension]
  ring

/-- In the common sign convention, a signed transfer is entering precisely
when its coherent-SI energy coordinate is positive. -/
def EnteringPositive (sourceUnits : SIUnitChoices) (transfer : Energy) : Prop :=
  0 < coherentCoordinate sourceUnits transfer

/-! ## Positive torus and material data -/

/-- Thin-torus geometry and an oriented winding.  The winding, mean loop, and
flux normal use the common positive orientation described in the module
header. -/
structure TorusData where
  unitSystem : SIUnitChoices
  meanRadius : Length
  innerRadius : Length
  crossSectionArea : Area
  volume : Volume
  meanLoopLength : Length
  thinnessBound : ℝ
  turns : ℕ

/-- Positivity and the exact thin-torus idealization. -/
def TorusData.IsPhysical (G : TorusData) : Prop :=
  0 < coherentCoordinate G.unitSystem G.meanRadius ∧
  0 < coherentCoordinate G.unitSystem G.innerRadius ∧
  0 < coherentCoordinate G.unitSystem G.crossSectionArea ∧
  0 < coherentCoordinate G.unitSystem G.volume ∧
  0 < coherentCoordinate G.unitSystem G.meanLoopLength ∧
  0 < G.thinnessBound ∧ G.thinnessBound < 1 ∧
  0 < G.turns ∧
  coherentCoordinate G.unitSystem G.innerRadius ≤
    G.thinnessBound * coherentCoordinate G.unitSystem G.meanRadius ∧
  coherentCoordinate G.unitSystem G.meanLoopLength =
    2 * Real.pi * coherentCoordinate G.unitSystem G.meanRadius ∧
  coherentCoordinate G.unitSystem G.volume =
    coherentCoordinate G.unitSystem G.crossSectionArea *
      coherentCoordinate G.unitSystem G.meanLoopLength

/-- Homogeneous isotropic paramagnetic material constants. -/
structure MaterialData where
  vacuumPermeability : Permeability
  amount : AmountOfSubstance
  curieParameter : CurieParameter
  heatCapacityCoefficient : HeatCapacityCoefficient

/-- Strict positivity of all material constants in the torus unit system. -/
def MaterialData.IsPhysical (sourceUnits : SIUnitChoices)
    (D : MaterialData) : Prop :=
  0 < coherentCoordinate sourceUnits D.vacuumPermeability ∧
  0 < coherentCoordinate sourceUnits D.amount ∧
  0 < coherentCoordinate sourceUnits D.curieParameter ∧
  0 < coherentCoordinate sourceUnits D.heatCapacityCoefficient

/-- One oriented torus paired with one paramagnetic material. -/
structure ParamagneticData where
  torus : TorusData
  material : MaterialData

/-- Physicality of the apparatus, using the torus's unit system for every
material coordinate. -/
def ParamagneticData.IsPhysical (D : ParamagneticData) : Prop :=
  D.torus.IsPhysical ∧ D.material.IsPhysical D.torus.unitSystem

/-! ## Equilibrium states and constitutive data -/

/-- A positive-field equilibrium state before its physicality conditions are
imposed. -/
structure EquilibriumState where
  temperature : Temperature
  fieldStrength : MagneticFieldStrength
  magnetization : Magnetization

/-- The positive-temperature, positive-field domain of the model. -/
def EquilibriumState.IsPhysical (sourceUnits : SIUnitChoices)
    (s : EquilibriumState) : Prop :=
  0 < coherentCoordinate sourceUnits s.temperature ∧
  0 < coherentCoordinate sourceUnits s.fieldStrength ∧
  0 < coherentCoordinate sourceUnits s.magnetization

/-- Curie's equation of state in coherent-SI coordinates. -/
def SatisfiesEquationOfState (D : ParamagneticData)
    (s : EquilibriumState) : Prop :=
  coherentCoordinate D.torus.unitSystem s.temperature *
      coherentCoordinate D.torus.unitSystem s.magnetization *
      coherentCoordinate D.torus.unitSystem D.torus.volume =
    coherentCoordinate D.torus.unitSystem D.material.amount *
      coherentCoordinate D.torus.unitSystem D.material.curieParameter *
      coherentCoordinate D.torus.unitSystem s.fieldStrength

/-- The constitutive law `B = μ₀ (H + M)`, returned as a dimensioned
flux-density quantity. -/
def magneticFluxDensity (D : ParamagneticData)
    (s : EquilibriumState) : MagneticFluxDensity :=
  quantityFromCoherentCoordinate D.torus.unitSystem
    magneticFluxDensityDimension
    (coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
      (coherentCoordinate D.torus.unitSystem s.fieldStrength +
        coherentCoordinate D.torus.unitSystem s.magnetization))

/-- Heat capacity at constant magnetization, governed by
`C_M = n λ / T²` on the positive-temperature domain. -/
def heatCapacityAtConstantMagnetization (D : ParamagneticData)
    (T : Temperature) : HeatCapacity :=
  quantityFromCoherentCoordinate D.torus.unitSystem heatCapacityDimension
    (coherentCoordinate D.torus.unitSystem D.material.amount *
      coherentCoordinate D.torus.unitSystem D.material.heatCapacityCoefficient /
      coherentCoordinate D.torus.unitSystem T ^ 2)

/-- Both sides of the equation of state have the same ISQ dimension. -/
lemma equationOfState_dimension :
    temperatureDimension * magneticFieldStrengthDimension * volumeDimension =
      amountDimension * curieParameterDimension *
        magneticFieldStrengthDimension := by
  exact magneticEquationOfState_products_dimension

/-! ## Regular quasistatic processes and endpoints -/

/-- A process parameter is dimensionless.  Its emf fields are linked-flux
increments per unit parameter, and its work and heat fields are signed energy
increments per unit parameter.  Only `[a,b]` is physically meaningful. -/
structure QuasistaticProcess where
  a : ℝ
  b : ℝ
  state : ℝ → EquilibriumState
  windingCurrent : ℝ → ElectricCurrent
  internalEnergy : ℝ → Energy
  inducedEmfIncrement : ℝ → MagneticFlux
  sourceEmfIncrement : ℝ → MagneticFlux
  sourceWorkIncrement : ℝ → Energy
  heatIncrement : ℝ → Energy

/-- A nondegenerate physical quasistatic path with `C¹` state, current, and
internal-energy coordinates on an open neighborhood of its compact physical
interval, and integrable transfer increments on that interval. -/
def QuasistaticProcess.IsRegular (D : ParamagneticData)
    (p : QuasistaticProcess) : Prop :=
  D.IsPhysical ∧
  p.a < p.b ∧
  (∃ neighborhood : Set ℝ,
    IsOpen neighborhood ∧
    Set.Icc p.a p.b ⊆ neighborhood ∧
    ContDiffOn ℝ 1
      (fun τ ↦ coherentCoordinate D.torus.unitSystem
        (p.state τ).temperature) neighborhood ∧
    ContDiffOn ℝ 1
      (fun τ ↦ coherentCoordinate D.torus.unitSystem
        (p.state τ).fieldStrength) neighborhood ∧
    ContDiffOn ℝ 1
      (fun τ ↦ coherentCoordinate D.torus.unitSystem
        (p.state τ).magnetization) neighborhood ∧
    ContDiffOn ℝ 1
      (fun τ ↦ coherentCoordinate D.torus.unitSystem
        (p.windingCurrent τ)) neighborhood ∧
    ContDiffOn ℝ 1
      (fun τ ↦ coherentCoordinate D.torus.unitSystem
        (p.internalEnergy τ)) neighborhood) ∧
  IntervalIntegrable
      (fun τ ↦ coherentCoordinate D.torus.unitSystem
        (p.inducedEmfIncrement τ)) MeasureTheory.volume p.a p.b ∧
  IntervalIntegrable
      (fun τ ↦ coherentCoordinate D.torus.unitSystem
        (p.sourceEmfIncrement τ)) MeasureTheory.volume p.a p.b ∧
  IntervalIntegrable
      (fun τ ↦ coherentCoordinate D.torus.unitSystem
        (p.sourceWorkIncrement τ)) MeasureTheory.volume p.a p.b ∧
  IntervalIntegrable
      (fun τ ↦ coherentCoordinate D.torus.unitSystem
        (p.heatIncrement τ)) MeasureTheory.volume p.a p.b ∧
  ∀ τ ∈ Set.Icc p.a p.b,
    (p.state τ).IsPhysical D.torus.unitSystem ∧
      SatisfiesEquationOfState D (p.state τ)

/-- The process begins at the prescribed equilibrium state. -/
def StartsAt (p : QuasistaticProcess) (initial : EquilibriumState) : Prop :=
  p.state p.a = initial

/-- The process ends at the prescribed equilibrium state. -/
def FinishesAt (p : QuasistaticProcess) (final : EquilibriumState) : Prop :=
  p.state p.b = final

/-- Both full equilibrium endpoints are prescribed. -/
def HasEndpoints (p : QuasistaticProcess) (initial final : EquilibriumState) : Prop :=
  StartsAt p initial ∧ FinishesAt p final

/-- Prescribe only temperature and applied-field endpoints; magnetization is
left to equilibrium and the equation of state. -/
def HasTemperatureFieldEndpoints (p : QuasistaticProcess)
    (Tᵢ : Temperature) (Hᵢ : MagneticFieldStrength)
    (T_f : Temperature) (H_f : MagneticFieldStrength) : Prop :=
  (p.state p.a).temperature = Tᵢ ∧
  (p.state p.a).fieldStrength = Hᵢ ∧
  (p.state p.b).temperature = T_f ∧
  (p.state p.b).fieldStrength = H_f

/-! ## Linked flux, Faraday law, and magnetic work -/

/-- Flux through every positively linked winding turn. -/
def linkedFlux (D : ParamagneticData) (s : EquilibriumState) : MagneticFlux :=
  quantityFromCoherentCoordinate D.torus.unitSystem magneticFluxDimension
    ((D.torus.turns : ℝ) *
      coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
      coherentCoordinate D.torus.unitSystem (magneticFluxDensity D s))

/-- Linked flux of the same geometry, winding, current orientation, and field
strength after replacing the material core by vacuum. -/
def vacuumLinkedFlux (D : ParamagneticData)
    (s : EquilibriumState) : MagneticFlux :=
  quantityFromCoherentCoordinate D.torus.unitSystem magneticFluxDimension
    ((D.torus.turns : ℝ) *
      coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
      coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
      coherentCoordinate D.torus.unitSystem s.fieldStrength)

/-- Oriented uniform-field Ampere law along the physical interval. -/
def SatisfiesAmpereLaw (D : ParamagneticData)
    (p : QuasistaticProcess) : Prop :=
  ∀ τ ∈ Set.Icc p.a p.b,
    coherentCoordinate D.torus.unitSystem D.torus.meanLoopLength *
        coherentCoordinate D.torus.unitSystem (p.state τ).fieldStrength =
      (D.torus.turns : ℝ) *
        coherentCoordinate D.torus.unitSystem (p.windingCurrent τ)

/-- Faraday's law with Lenz's-law opposition shown explicitly. -/
def SatisfiesFaradayLaw (D : ParamagneticData)
    (p : QuasistaticProcess) : Prop :=
  ∀ τ ∈ Set.Icc p.a p.b,
    coherentCoordinate D.torus.unitSystem (p.inducedEmfIncrement τ) =
      -deriv
        (fun t ↦ coherentCoordinate D.torus.unitSystem
          (linkedFlux D (p.state t))) τ

/-- The lossless source balances the induced back emf. -/
def SatisfiesSourceBalance (D : ParamagneticData)
    (p : QuasistaticProcess) : Prop :=
  ∀ τ ∈ Set.Icc p.a p.b,
    coherentCoordinate D.torus.unitSystem (p.sourceEmfIncrement τ) =
      -coherentCoordinate D.torus.unitSystem (p.inducedEmfIncrement τ)

/-- Source work is current times source-emf increment, with positive values
entering the combined vacuum field and material. -/
def SatisfiesSourceWorkLaw (D : ParamagneticData)
    (p : QuasistaticProcess) : Prop :=
  ∀ τ ∈ Set.Icc p.a p.b,
    coherentCoordinate D.torus.unitSystem (p.sourceWorkIncrement τ) =
      coherentCoordinate D.torus.unitSystem (p.windingCurrent τ) *
        coherentCoordinate D.torus.unitSystem (p.sourceEmfIncrement τ)

/-- Work needed to establish the corresponding vacuum-core flux. -/
def vacuumWorkIncrement (D : ParamagneticData) (p : QuasistaticProcess)
    (τ : ℝ) : Energy :=
  quantityFromCoherentCoordinate D.torus.unitSystem energyDimension
    (coherentCoordinate D.torus.unitSystem (p.windingCurrent τ) *
      deriv
        (fun t ↦ coherentCoordinate D.torus.unitSystem
          (vacuumLinkedFlux D (p.state t))) τ)

/-- Work entering the material after subtraction of vacuum-field work. -/
def materialWorkIncrement (D : ParamagneticData) (p : QuasistaticProcess)
    (τ : ℝ) : Energy :=
  p.sourceWorkIncrement τ - vacuumWorkIncrement D p τ

/-- Source-work increment derived from the oriented electromagnetic laws. -/
lemma sourceWork_characterization (D : ParamagneticData)
    (p : QuasistaticProcess) (hregular : p.IsRegular D)
    (hAmpere : SatisfiesAmpereLaw D p)
    (hFaraday : SatisfiesFaradayLaw D p)
    (hsourceBalance : SatisfiesSourceBalance D p)
    (hsourceWork : SatisfiesSourceWorkLaw D p)
    (τ : ℝ) (hτ : τ ∈ Set.Icc p.a p.b) :
    coherentCoordinate D.torus.unitSystem (p.sourceWorkIncrement τ) =
      coherentCoordinate D.torus.unitSystem D.torus.volume *
        coherentCoordinate D.torus.unitSystem (p.state τ).fieldStrength *
        deriv
          (fun t ↦ coherentCoordinate D.torus.unitSystem
            (magneticFluxDensity D (p.state t))) τ := by
  rcases hregular.1.1 with
    ⟨_, _, _, _, _, _, _, _, _, _, hvolume⟩
  calc
    coherentCoordinate D.torus.unitSystem (p.sourceWorkIncrement τ) =
        coherentCoordinate D.torus.unitSystem (p.windingCurrent τ) *
          coherentCoordinate D.torus.unitSystem (p.sourceEmfIncrement τ) :=
      hsourceWork τ hτ
    _ = coherentCoordinate D.torus.unitSystem (p.windingCurrent τ) *
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (linkedFlux D (p.state t))) τ := by
      rw [hsourceBalance τ hτ, hFaraday τ hτ]
      ring
    _ = coherentCoordinate D.torus.unitSystem (p.windingCurrent τ) *
          ((D.torus.turns : ℝ) *
            coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (magneticFluxDensity D (p.state t))) τ) := by
      congr 1
      simp only [linkedFlux,
        coherentCoordinate_quantityFromCoherentCoordinate]
      rw [deriv_const_mul_field]
    _ = coherentCoordinate D.torus.unitSystem D.torus.volume *
          coherentCoordinate D.torus.unitSystem (p.state τ).fieldStrength *
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (magneticFluxDensity D (p.state t))) τ := by
      rw [hvolume]
      calc
        coherentCoordinate D.torus.unitSystem (p.windingCurrent τ) *
              ((D.torus.turns : ℝ) *
                coherentCoordinate D.torus.unitSystem
                  D.torus.crossSectionArea *
                deriv
                  (fun t ↦ coherentCoordinate D.torus.unitSystem
                    (magneticFluxDensity D (p.state t))) τ) =
            coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
              ((D.torus.turns : ℝ) *
                coherentCoordinate D.torus.unitSystem (p.windingCurrent τ)) *
              deriv
                (fun t ↦ coherentCoordinate D.torus.unitSystem
                  (magneticFluxDensity D (p.state t))) τ := by ring
        _ = coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
              (coherentCoordinate D.torus.unitSystem D.torus.meanLoopLength *
                coherentCoordinate D.torus.unitSystem
                  (p.state τ).fieldStrength) *
              deriv
                (fun t ↦ coherentCoordinate D.torus.unitSystem
                  (magneticFluxDensity D (p.state t))) τ := by
          rw [hAmpere τ hτ]
        _ = _ := by ring

/-- Vacuum-core work derived from Ampere's law and vacuum flux linkage. -/
lemma vacuumWork_characterization (D : ParamagneticData)
    (p : QuasistaticProcess) (hregular : p.IsRegular D)
    (hAmpere : SatisfiesAmpereLaw D p)
    (τ : ℝ) (hτ : τ ∈ Set.Icc p.a p.b) :
    coherentCoordinate D.torus.unitSystem (vacuumWorkIncrement D p τ) =
      coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
        coherentCoordinate D.torus.unitSystem D.torus.volume *
        coherentCoordinate D.torus.unitSystem (p.state τ).fieldStrength *
        deriv
          (fun t ↦ coherentCoordinate D.torus.unitSystem
            (p.state t).fieldStrength) τ := by
  rcases hregular.1.1 with
    ⟨_, _, _, _, _, _, _, _, _, _, hvolume⟩
  calc
    coherentCoordinate D.torus.unitSystem (vacuumWorkIncrement D p τ) =
        coherentCoordinate D.torus.unitSystem (p.windingCurrent τ) *
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (vacuumLinkedFlux D (p.state t))) τ := by
      simp only [vacuumWorkIncrement,
        coherentCoordinate_quantityFromCoherentCoordinate]
    _ = coherentCoordinate D.torus.unitSystem (p.windingCurrent τ) *
          ((D.torus.turns : ℝ) *
            coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
            coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).fieldStrength) τ) := by
      congr 1
      simp only [vacuumLinkedFlux,
        coherentCoordinate_quantityFromCoherentCoordinate]
      rw [deriv_const_mul_field]
    _ = coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
          coherentCoordinate D.torus.unitSystem D.torus.volume *
          coherentCoordinate D.torus.unitSystem (p.state τ).fieldStrength *
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).fieldStrength) τ := by
      rw [hvolume]
      calc
        coherentCoordinate D.torus.unitSystem (p.windingCurrent τ) *
              ((D.torus.turns : ℝ) *
                coherentCoordinate D.torus.unitSystem
                  D.torus.crossSectionArea *
                coherentCoordinate D.torus.unitSystem
                  D.material.vacuumPermeability *
                deriv
                  (fun t ↦ coherentCoordinate D.torus.unitSystem
                    (p.state t).fieldStrength) τ) =
            coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
              coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
              ((D.torus.turns : ℝ) *
                coherentCoordinate D.torus.unitSystem (p.windingCurrent τ)) *
              deriv
                (fun t ↦ coherentCoordinate D.torus.unitSystem
                  (p.state t).fieldStrength) τ := by ring
        _ = coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
              coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
              (coherentCoordinate D.torus.unitSystem D.torus.meanLoopLength *
                coherentCoordinate D.torus.unitSystem
                  (p.state τ).fieldStrength) *
              deriv
                (fun t ↦ coherentCoordinate D.torus.unitSystem
                  (p.state t).fieldStrength) τ := by
          rw [hAmpere τ hτ]
        _ = _ := by ring

/-- Source work decomposes into vacuum-field and material work, and the latter
obeys the derived material-work coordinate law. -/
theorem source_vacuum_material_work_decomposition (D : ParamagneticData)
    (p : QuasistaticProcess) (hregular : p.IsRegular D)
    (hAmpere : SatisfiesAmpereLaw D p)
    (hFaraday : SatisfiesFaradayLaw D p)
    (hsourceBalance : SatisfiesSourceBalance D p)
    (hsourceWork : SatisfiesSourceWorkLaw D p)
    (τ : ℝ) (hτ : τ ∈ Set.Icc p.a p.b) :
    p.sourceWorkIncrement τ =
        vacuumWorkIncrement D p τ + materialWorkIncrement D p τ ∧
      coherentCoordinate D.torus.unitSystem (materialWorkIncrement D p τ) =
        coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
          coherentCoordinate D.torus.unitSystem D.torus.volume *
          coherentCoordinate D.torus.unitSystem (p.state τ).fieldStrength *
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).magnetization) τ := by
  constructor
  · unfold materialWorkIncrement
    abel
  · rcases hregular.2.2.1 with
      ⟨neighborhood, hopen, hIcc, _, hH, hM, _, _⟩
    have hτn : τ ∈ neighborhood := hIcc hτ
    have hHdiff : DifferentiableAt ℝ
        (fun t ↦ coherentCoordinate D.torus.unitSystem
          (p.state t).fieldStrength) τ :=
      (hH.differentiableOn_one τ hτn).differentiableAt
        (hopen.mem_nhds hτn)
    have hMdiff : DifferentiableAt ℝ
        (fun t ↦ coherentCoordinate D.torus.unitSystem
          (p.state t).magnetization) τ :=
      (hM.differentiableOn_one τ hτn).differentiableAt
        (hopen.mem_nhds hτn)
    have hderivB :
        deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (magneticFluxDensity D (p.state t))) τ =
          coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            (deriv
                (fun t ↦ coherentCoordinate D.torus.unitSystem
                  (p.state t).fieldStrength) τ +
              deriv
                (fun t ↦ coherentCoordinate D.torus.unitSystem
                  (p.state t).magnetization) τ) := by
      simp only [magneticFluxDensity,
        coherentCoordinate_quantityFromCoherentCoordinate]
      rw [deriv_const_mul_field, deriv_fun_add hHdiff hMdiff]
    calc
      coherentCoordinate D.torus.unitSystem
          (materialWorkIncrement D p τ) =
        coherentCoordinate D.torus.unitSystem (p.sourceWorkIncrement τ) -
          coherentCoordinate D.torus.unitSystem (vacuumWorkIncrement D p τ) := by
        simp only [materialWorkIncrement, coherentCoordinate, coordinateInSI,
          WithDim.val_sub]
        ring
      _ = coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
          coherentCoordinate D.torus.unitSystem D.torus.volume *
          coherentCoordinate D.torus.unitSystem (p.state τ).fieldStrength *
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).magnetization) τ := by
        rw [sourceWork_characterization D p hregular hAmpere hFaraday
          hsourceBalance hsourceWork τ hτ,
          vacuumWork_characterization D p hregular hAmpere τ hτ,
          hderivB]
        ring

/-! ## Internal energy, the first law, and reversible legs -/

/-- Coherent-SI coordinate of the supplied internal-energy differential
`C_M dT` per unit dimensionless process parameter. -/
def internalEnergyDifferential (D : ParamagneticData)
    (p : QuasistaticProcess) (τ : ℝ) : ℝ :=
  coherentCoordinate D.torus.unitSystem
      (heatCapacityAtConstantMagnetization D (p.state τ).temperature) *
    deriv
      (fun t ↦ coherentCoordinate D.torus.unitSystem
        (p.state t).temperature) τ

/-- The internal-energy path obeys the supplied differential law. -/
def SatisfiesInternalEnergyLaw (D : ParamagneticData)
    (p : QuasistaticProcess) : Prop :=
  ∀ τ ∈ Set.Icc p.a p.b,
    deriv
        (fun t ↦ coherentCoordinate D.torus.unitSystem
          (p.internalEnergy t)) τ =
      internalEnergyDifferential D p τ

/-- First law with both heat and vacuum-subtracted material work positive when
they enter the material. -/
def SatisfiesFirstLaw (D : ParamagneticData)
    (p : QuasistaticProcess) : Prop :=
  ∀ τ ∈ Set.Icc p.a p.b,
    deriv
        (fun t ↦ coherentCoordinate D.torus.unitSystem
          (p.internalEnergy t)) τ =
      coherentCoordinate D.torus.unitSystem (p.heatIncrement τ) +
        coherentCoordinate D.torus.unitSystem (materialWorkIncrement D p τ)

/-- Constant positive absolute temperature on the whole physical interval. -/
def IsIsothermal (D : ParamagneticData) (p : QuasistaticProcess)
    (T₀ : Temperature) : Prop :=
  0 < coherentCoordinate D.torus.unitSystem T₀ ∧
  ∀ τ ∈ Set.Icc p.a p.b, (p.state τ).temperature = T₀

/-- Pointwise-zero heat increment, rather than merely zero net heat. -/
def IsAdiabatic (D : ParamagneticData) (p : QuasistaticProcess) : Prop :=
  ∀ τ ∈ Set.Icc p.a p.b,
    coherentCoordinate D.torus.unitSystem (p.heatIncrement τ) = 0

/-- A reversible ideal leg obeys every local equilibrium, electromagnetic,
and thermodynamic law and contains no dissipative term. -/
def IsReversibleLeg (D : ParamagneticData) (p : QuasistaticProcess) : Prop :=
  p.IsRegular D ∧
  SatisfiesAmpereLaw D p ∧
  SatisfiesFaradayLaw D p ∧
  SatisfiesSourceBalance D p ∧
  SatisfiesSourceWorkLaw D p ∧
  SatisfiesInternalEnergyLaw D p ∧
  SatisfiesFirstLaw D p

/-! ## Isothermal heat and its answer-free endpoint predicate -/

/-- An admissible reversible isothermal leg with prescribed positive
temperature and field endpoints.  No heat formula or field monotonicity is
included. -/
def IsReversibleIsothermalEndpointLeg (D : ParamagneticData)
    (T₀ : Temperature) (Hᵢ H_f : MagneticFieldStrength)
    (p : QuasistaticProcess) : Prop :=
  0 < coherentCoordinate D.torus.unitSystem T₀ ∧
  0 < coherentCoordinate D.torus.unitSystem Hᵢ ∧
  0 < coherentCoordinate D.torus.unitSystem H_f ∧
  IsReversibleLeg D p ∧
  IsIsothermal D p T₀ ∧
  HasTemperatureFieldEndpoints p T₀ Hᵢ T₀ H_f

/-- A dimensioned energy is the net signed heat entering along the process. -/
def HasNetHeatEntering (D : ParamagneticData) (p : QuasistaticProcess)
    (Q : Energy) : Prop :=
  coherentCoordinate D.torus.unitSystem Q =
    ∫ τ in p.a..p.b,
      coherentCoordinate D.torus.unitSystem (p.heatIncrement τ)

/-- Answer-free endpoint heat predicate: at least one admissible path exists,
and every admissible path has the same proposed signed heat. -/
def IsEndpointHeatSolution (D : ParamagneticData)
    (T₀ : Temperature) (Hᵢ H_f : MagneticFieldStrength)
    (Q : Energy) : Prop :=
  (∃ p : QuasistaticProcess,
    IsReversibleIsothermalEndpointLeg D T₀ Hᵢ H_f p) ∧
  ∀ p : QuasistaticProcess,
    IsReversibleIsothermalEndpointLeg D T₀ Hᵢ H_f p →
      HasNetHeatEntering D p Q

/-- Pointwise and path-integral characterization of heat along a reversible
isothermal endpoint leg.  The integral is intentionally not evaluated. -/
theorem isothermalHeat_characterization (D : ParamagneticData)
    (T₀ : Temperature) (Hᵢ H_f : MagneticFieldStrength)
    (p : QuasistaticProcess)
    (hleg : IsReversibleIsothermalEndpointLeg D T₀ Hᵢ H_f p) :
    (∀ τ ∈ Set.Icc p.a p.b,
      coherentCoordinate D.torus.unitSystem (p.heatIncrement τ) =
          -(coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            coherentCoordinate D.torus.unitSystem D.torus.volume *
            coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).magnetization) τ) ∧
        coherentCoordinate D.torus.unitSystem (p.heatIncrement τ) =
          -(coherentCoordinate D.torus.unitSystem
                D.material.vacuumPermeability *
              coherentCoordinate D.torus.unitSystem D.material.amount *
              coherentCoordinate D.torus.unitSystem D.material.curieParameter /
              coherentCoordinate D.torus.unitSystem T₀) *
            coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).fieldStrength) τ) ∧
    ∀ Q : Energy,
      HasNetHeatEntering D p Q ↔
        coherentCoordinate D.torus.unitSystem Q =
          ∫ τ in p.a..p.b,
            -(coherentCoordinate D.torus.unitSystem
                  D.material.vacuumPermeability *
                coherentCoordinate D.torus.unitSystem D.material.amount *
                coherentCoordinate D.torus.unitSystem D.material.curieParameter /
                coherentCoordinate D.torus.unitSystem T₀) *
              coherentCoordinate D.torus.unitSystem
                (p.state τ).fieldStrength *
              deriv
                (fun t ↦ coherentCoordinate D.torus.unitSystem
                  (p.state t).fieldStrength) τ := by
  rcases hleg with
    ⟨hT₀, _, _, hrev, hisothermal, _⟩
  rcases hrev with
    ⟨hregular, hAmpere, hFaraday, hsourceBalance, hsourceWork,
      hinternalEnergy, hfirstLaw⟩
  have hregular' := hregular
  rcases hregular with
    ⟨_, hab, ⟨neighborhood, hopen, hIcc, hT, hH, hM, _, _⟩,
      _, _, _, _, hstate⟩
  have hpoint : ∀ τ ∈ Set.Icc p.a p.b,
      coherentCoordinate D.torus.unitSystem (p.heatIncrement τ) =
          -(coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            coherentCoordinate D.torus.unitSystem D.torus.volume *
            coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).magnetization) τ) ∧
        coherentCoordinate D.torus.unitSystem (p.heatIncrement τ) =
          -(coherentCoordinate D.torus.unitSystem
                D.material.vacuumPermeability *
              coherentCoordinate D.torus.unitSystem D.material.amount *
              coherentCoordinate D.torus.unitSystem D.material.curieParameter /
              coherentCoordinate D.torus.unitSystem T₀) *
            coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).fieldStrength) τ := by
    intro τ hτ
    have hτn : τ ∈ neighborhood := hIcc hτ
    have hunique : UniqueDiffWithinAt ℝ (Set.Icc p.a p.b) τ :=
      (uniqueDiffOn_Icc hab) τ hτ
    have hTdiff : DifferentiableAt ℝ
        (fun t ↦ coherentCoordinate D.torus.unitSystem
          (p.state t).temperature) τ :=
      (hT.differentiableOn_one τ hτn).differentiableAt
        (hopen.mem_nhds hτn)
    have hHdiff : DifferentiableAt ℝ
        (fun t ↦ coherentCoordinate D.torus.unitSystem
          (p.state t).fieldStrength) τ :=
      (hH.differentiableOn_one τ hτn).differentiableAt
        (hopen.mem_nhds hτn)
    have hMdiff : DifferentiableAt ℝ
        (fun t ↦ coherentCoordinate D.torus.unitSystem
          (p.state t).magnetization) τ :=
      (hM.differentiableOn_one τ hτn).differentiableAt
        (hopen.mem_nhds hτn)
    have htemperatureOn : Set.EqOn
        (fun t ↦ coherentCoordinate D.torus.unitSystem
          (p.state t).temperature)
        (fun _ ↦ coherentCoordinate D.torus.unitSystem T₀)
        (Set.Icc p.a p.b) := by
      intro t ht
      exact congrArg (coherentCoordinate D.torus.unitSystem)
        (hisothermal.2 t ht)
    have hTderiv :
        deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).temperature) τ = 0 := by
      calc
        deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).temperature) τ =
            derivWithin
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).temperature) (Set.Icc p.a p.b) τ :=
          (hTdiff.derivWithin hunique).symm
        _ = derivWithin
              (fun _ ↦ coherentCoordinate D.torus.unitSystem T₀)
              (Set.Icc p.a p.b) τ :=
          derivWithin_congr htemperatureOn (htemperatureOn hτ)
        _ = 0 := by simp
    have hinternalEnergyZero :
        deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.internalEnergy t)) τ = 0 := by
      rw [hinternalEnergy τ hτ]
      simp [internalEnergyDifferential, hTderiv]
    have hmaterial :=
      (source_vacuum_material_work_decomposition D p hregular'
        hAmpere hFaraday hsourceBalance hsourceWork τ hτ).2
    have hheatMaterial := hfirstLaw τ hτ
    rw [hinternalEnergyZero, hmaterial] at hheatMaterial
    have hheatFirst :
        coherentCoordinate D.torus.unitSystem (p.heatIncrement τ) =
          -(coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            coherentCoordinate D.torus.unitSystem D.torus.volume *
            coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).magnetization) τ) := by
      linarith
    have hequationOn : Set.EqOn
        (fun t ↦ coherentCoordinate D.torus.unitSystem T₀ *
          coherentCoordinate D.torus.unitSystem (p.state t).magnetization *
          coherentCoordinate D.torus.unitSystem D.torus.volume)
        (fun t ↦ coherentCoordinate D.torus.unitSystem D.material.amount *
          coherentCoordinate D.torus.unitSystem D.material.curieParameter *
          coherentCoordinate D.torus.unitSystem (p.state t).fieldStrength)
        (Set.Icc p.a p.b) := by
      intro t ht
      have hequation := (hstate t ht).2
      change
        coherentCoordinate D.torus.unitSystem (p.state t).temperature *
              coherentCoordinate D.torus.unitSystem (p.state t).magnetization *
              coherentCoordinate D.torus.unitSystem D.torus.volume =
          coherentCoordinate D.torus.unitSystem D.material.amount *
              coherentCoordinate D.torus.unitSystem D.material.curieParameter *
              coherentCoordinate D.torus.unitSystem (p.state t).fieldStrength
        at hequation
      rw [hisothermal.2 t ht] at hequation
      exact hequation
    have hleftDiff : DifferentiableAt ℝ
        (fun t ↦ coherentCoordinate D.torus.unitSystem T₀ *
          coherentCoordinate D.torus.unitSystem (p.state t).magnetization *
          coherentCoordinate D.torus.unitSystem D.torus.volume) τ :=
      (hMdiff.const_mul _).mul_const _
    have hrightDiff : DifferentiableAt ℝ
        (fun t ↦ coherentCoordinate D.torus.unitSystem D.material.amount *
          coherentCoordinate D.torus.unitSystem D.material.curieParameter *
          coherentCoordinate D.torus.unitSystem (p.state t).fieldStrength) τ :=
      hHdiff.const_mul _
    have hequationDeriv :
        deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem T₀ *
              coherentCoordinate D.torus.unitSystem (p.state t).magnetization *
              coherentCoordinate D.torus.unitSystem D.torus.volume) τ =
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem D.material.amount *
              coherentCoordinate D.torus.unitSystem D.material.curieParameter *
              coherentCoordinate D.torus.unitSystem
                (p.state t).fieldStrength) τ := by
      calc
        _ = derivWithin
              (fun t ↦ coherentCoordinate D.torus.unitSystem T₀ *
                coherentCoordinate D.torus.unitSystem
                  (p.state t).magnetization *
                coherentCoordinate D.torus.unitSystem D.torus.volume)
              (Set.Icc p.a p.b) τ :=
          (hleftDiff.derivWithin hunique).symm
        _ = derivWithin
              (fun t ↦ coherentCoordinate D.torus.unitSystem D.material.amount *
                coherentCoordinate D.torus.unitSystem
                  D.material.curieParameter *
                coherentCoordinate D.torus.unitSystem
                  (p.state t).fieldStrength)
              (Set.Icc p.a p.b) τ :=
          derivWithin_congr hequationOn (hequationOn hτ)
        _ = _ := hrightDiff.derivWithin hunique
    have hequationDeriv' :
        coherentCoordinate D.torus.unitSystem T₀ *
              deriv
                (fun t ↦ coherentCoordinate D.torus.unitSystem
                  (p.state t).magnetization) τ *
              coherentCoordinate D.torus.unitSystem D.torus.volume =
          coherentCoordinate D.torus.unitSystem D.material.amount *
            coherentCoordinate D.torus.unitSystem D.material.curieParameter *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).fieldStrength) τ := by
      simpa only [deriv_mul_const_field, deriv_const_mul_field] using
        hequationDeriv
    have hT₀ne : coherentCoordinate D.torus.unitSystem T₀ ≠ 0 :=
      ne_of_gt hT₀
    have hvolumeMagnetizationDeriv :
        coherentCoordinate D.torus.unitSystem D.torus.volume *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).magnetization) τ =
          (coherentCoordinate D.torus.unitSystem D.material.amount *
              coherentCoordinate D.torus.unitSystem D.material.curieParameter /
              coherentCoordinate D.torus.unitSystem T₀) *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).fieldStrength) τ := by
      field_simp [hT₀ne]
      nlinarith [hequationDeriv']
    refine ⟨hheatFirst, ?_⟩
    calc
      coherentCoordinate D.torus.unitSystem (p.heatIncrement τ) =
          -(coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            coherentCoordinate D.torus.unitSystem D.torus.volume *
            coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).magnetization) τ) := hheatFirst
      _ = -(coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength *
            (coherentCoordinate D.torus.unitSystem D.torus.volume *
              deriv
                (fun t ↦ coherentCoordinate D.torus.unitSystem
                  (p.state t).magnetization) τ)) := by ring
      _ = -(coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength *
            ((coherentCoordinate D.torus.unitSystem D.material.amount *
                coherentCoordinate D.torus.unitSystem
                  D.material.curieParameter /
                coherentCoordinate D.torus.unitSystem T₀) *
              deriv
                (fun t ↦ coherentCoordinate D.torus.unitSystem
                  (p.state t).fieldStrength) τ)) := by
        rw [hvolumeMagnetizationDeriv]
      _ = _ := by ring
  refine ⟨hpoint, ?_⟩
  have hintegral :
      (∫ τ in p.a..p.b,
        coherentCoordinate D.torus.unitSystem (p.heatIncrement τ)) =
        ∫ τ in p.a..p.b,
          -(coherentCoordinate D.torus.unitSystem
                D.material.vacuumPermeability *
              coherentCoordinate D.torus.unitSystem D.material.amount *
              coherentCoordinate D.torus.unitSystem D.material.curieParameter /
              coherentCoordinate D.torus.unitSystem T₀) *
            coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).fieldStrength) τ := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    exact (hpoint τ (by simpa only [Set.uIcc_of_le hab.le] using hτ)).2
  intro Q
  unfold HasNetHeatEntering
  rw [hintegral]

/-- Governing path-integral characterization of the endpoint heat solution,
without selecting or evaluating a closed endpoint expression. -/
theorem endpointHeatSolution_characterization (D : ParamagneticData)
    (T₀ : Temperature) (Hᵢ H_f : MagneticFieldStrength) (Q : Energy)
    (hD : D.IsPhysical)
    (hT₀ : 0 < coherentCoordinate D.torus.unitSystem T₀)
    (hHᵢ : 0 < coherentCoordinate D.torus.unitSystem Hᵢ)
    (hH_f : 0 < coherentCoordinate D.torus.unitSystem H_f) :
    IsEndpointHeatSolution D T₀ Hᵢ H_f Q ↔
      (∃ p : QuasistaticProcess,
        IsReversibleIsothermalEndpointLeg D T₀ Hᵢ H_f p) ∧
      ∀ p : QuasistaticProcess,
        IsReversibleIsothermalEndpointLeg D T₀ Hᵢ H_f p →
          coherentCoordinate D.torus.unitSystem Q =
            ∫ τ in p.a..p.b,
              -(coherentCoordinate D.torus.unitSystem
                    D.material.vacuumPermeability *
                  coherentCoordinate D.torus.unitSystem D.material.amount *
                  coherentCoordinate D.torus.unitSystem
                    D.material.curieParameter /
                  coherentCoordinate D.torus.unitSystem T₀) *
                coherentCoordinate D.torus.unitSystem
                  (p.state τ).fieldStrength *
                deriv
                  (fun t ↦ coherentCoordinate D.torus.unitSystem
                    (p.state t).fieldStrength) τ := by
  constructor
  · rintro ⟨hexists, hall⟩
    refine ⟨hexists, ?_⟩
    intro p hp
    exact ((isothermalHeat_characterization D T₀ Hᵢ H_f p hp).2 Q).mp
      (hall p hp)
  · rintro ⟨hexists, hall⟩
    refine ⟨hexists, ?_⟩
    intro p hp
    exact ((isothermalHeat_characterization D T₀ Hᵢ H_f p hp).2 Q).mpr
      (hall p hp)

/-! ## Adiabatic endpoint relation and temperature-change predicate -/

/-- An admissible reversible adiabatic leg with four positive prescribed
endpoint coordinates.  No endpoint relation is assumed here. -/
def IsReversibleAdiabaticEndpointLeg (D : ParamagneticData)
    (Tᵢ : Temperature) (Hᵢ : MagneticFieldStrength)
    (T_f : Temperature) (H_f : MagneticFieldStrength)
    (p : QuasistaticProcess) : Prop :=
  0 < coherentCoordinate D.torus.unitSystem Tᵢ ∧
  0 < coherentCoordinate D.torus.unitSystem Hᵢ ∧
  0 < coherentCoordinate D.torus.unitSystem T_f ∧
  0 < coherentCoordinate D.torus.unitSystem H_f ∧
  IsReversibleLeg D p ∧
  IsAdiabatic D p ∧
  HasTemperatureFieldEndpoints p Tᵢ Hᵢ T_f H_f

/-- Coefficient in the local logarithmic adiabatic field law, expressed as a
function of a coherent-SI field coordinate. -/
def adiabaticFieldCoefficient (D : ParamagneticData) (h : ℝ) : ℝ :=
  coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
      coherentCoordinate D.torus.unitSystem D.material.curieParameter * h /
    (coherentCoordinate D.torus.unitSystem
        D.material.heatCapacityCoefficient +
      coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
        coherentCoordinate D.torus.unitSystem D.material.curieParameter * h ^ 2)

/-- Unevaluated dimensionless potential obtained by integrating the local
adiabatic field coefficient. -/
def adiabaticPotential (D : ParamagneticData) (h : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..h, adiabaticFieldCoefficient D x

/-- Substantive integrated endpoint relation derived from the local adiabatic
law.  It includes apparatus and endpoint positivity but no proposed endpoint
temperature. -/
def AdiabaticEndpointRelation (D : ParamagneticData)
    (Tᵢ : Temperature) (Hᵢ : MagneticFieldStrength)
    (T_f : Temperature) (H_f : MagneticFieldStrength) : Prop :=
  D.IsPhysical ∧
  0 < coherentCoordinate D.torus.unitSystem Tᵢ ∧
  0 < coherentCoordinate D.torus.unitSystem Hᵢ ∧
  0 < coherentCoordinate D.torus.unitSystem T_f ∧
  0 < coherentCoordinate D.torus.unitSystem H_f ∧
  Real.log (coherentCoordinate D.torus.unitSystem T_f) -
      Real.log (coherentCoordinate D.torus.unitSystem Tᵢ) =
    adiabaticPotential D
        (coherentCoordinate D.torus.unitSystem H_f) -
      adiabaticPotential D
        (coherentCoordinate D.torus.unitSystem Hᵢ)

/-- Answer-free signed temperature-change solution predicate. -/
def IsEndpointTemperatureChangeSolution (D : ParamagneticData)
    (Tᵢ : Temperature) (Hᵢ H_f : MagneticFieldStrength)
    (ΔT : TemperatureDifference) : Prop :=
  AdiabaticEndpointRelation D Tᵢ Hᵢ (Tᵢ + ΔT) H_f

/-- Under physical material data, the adiabatic coefficient denominator is
everywhere positive; consequently the coefficient is globally `C¹`,
continuous, and interval-integrable. -/
lemma adiabaticFieldCoefficient_denominator_pos (D : ParamagneticData)
    (hD : D.IsPhysical) :
    (∀ h : ℝ,
      0 < coherentCoordinate D.torus.unitSystem
            D.material.heatCapacityCoefficient +
          coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            coherentCoordinate D.torus.unitSystem D.material.curieParameter *
            h ^ 2) ∧
    ContDiff ℝ 1 (adiabaticFieldCoefficient D) ∧
    Continuous (adiabaticFieldCoefficient D) ∧
    ∀ a b : ℝ,
      IntervalIntegrable (adiabaticFieldCoefficient D)
        MeasureTheory.volume a b := by
  have hμ : 0 < coherentCoordinate D.torus.unitSystem
      D.material.vacuumPermeability := hD.2.1
  have hK : 0 < coherentCoordinate D.torus.unitSystem
      D.material.curieParameter := hD.2.2.2.1
  have hlambda : 0 < coherentCoordinate D.torus.unitSystem
      D.material.heatCapacityCoefficient := hD.2.2.2.2
  have hdenominator : ∀ h : ℝ,
      0 < coherentCoordinate D.torus.unitSystem
            D.material.heatCapacityCoefficient +
          coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            coherentCoordinate D.torus.unitSystem D.material.curieParameter *
            h ^ 2 := by
    intro h
    have hnonneg : 0 ≤
        coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
          coherentCoordinate D.torus.unitSystem D.material.curieParameter *
          h ^ 2 :=
      mul_nonneg (mul_pos hμ hK).le (sq_nonneg h)
    linarith [hlambda]
  have hsmooth : ContDiff ℝ 1 (adiabaticFieldCoefficient D) := by
    unfold adiabaticFieldCoefficient
    apply ContDiff.div
    · fun_prop
    · fun_prop
    · intro h
      exact ne_of_gt (hdenominator h)
  exact ⟨hdenominator, hsmooth, hsmooth.continuous,
    fun a b ↦ hsmooth.continuous.intervalIntegrable a b⟩

/-- Local reversible adiabatic law, both before and after division by the
strictly positive temperature and coefficient denominator. -/
lemma adiabatic_differential_relation (D : ParamagneticData)
    (p : QuasistaticProcess) (hleg : IsReversibleLeg D p)
    (hadiabatic : IsAdiabatic D p) (τ : ℝ)
    (hτ : τ ∈ Set.Icc p.a p.b) :
    (coherentCoordinate D.torus.unitSystem
          D.material.heatCapacityCoefficient +
        coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
          coherentCoordinate D.torus.unitSystem D.material.curieParameter *
          coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength ^ 2) *
        deriv
          (fun t ↦ coherentCoordinate D.torus.unitSystem
            (p.state t).temperature) τ =
      coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
        coherentCoordinate D.torus.unitSystem D.material.curieParameter *
        coherentCoordinate D.torus.unitSystem
          (p.state τ).fieldStrength *
        coherentCoordinate D.torus.unitSystem (p.state τ).temperature *
        deriv
          (fun t ↦ coherentCoordinate D.torus.unitSystem
            (p.state t).fieldStrength) τ ∧
    deriv
          (fun t ↦ coherentCoordinate D.torus.unitSystem
            (p.state t).temperature) τ /
        coherentCoordinate D.torus.unitSystem (p.state τ).temperature =
      adiabaticFieldCoefficient D
          (coherentCoordinate D.torus.unitSystem
            (p.state τ).fieldStrength) *
        deriv
          (fun t ↦ coherentCoordinate D.torus.unitSystem
            (p.state t).fieldStrength) τ := by
  rcases hleg with
    ⟨hregular, hAmpere, hFaraday, hsourceBalance, hsourceWork,
      hinternalEnergy, hfirstLaw⟩
  have hregular' := hregular
  rcases hregular with
    ⟨hD, hab, ⟨neighborhood, hopen, hIcc, hT, hH, hM, _, _⟩,
      _, _, _, _, hstate⟩
  have hτn : τ ∈ neighborhood := hIcc hτ
  have hunique : UniqueDiffWithinAt ℝ (Set.Icc p.a p.b) τ :=
    (uniqueDiffOn_Icc hab) τ hτ
  have hTdiff : DifferentiableAt ℝ
      (fun t ↦ coherentCoordinate D.torus.unitSystem
        (p.state t).temperature) τ :=
    (hT.differentiableOn_one τ hτn).differentiableAt
      (hopen.mem_nhds hτn)
  have hHdiff : DifferentiableAt ℝ
      (fun t ↦ coherentCoordinate D.torus.unitSystem
        (p.state t).fieldStrength) τ :=
    (hH.differentiableOn_one τ hτn).differentiableAt
      (hopen.mem_nhds hτn)
  have hMdiff : DifferentiableAt ℝ
      (fun t ↦ coherentCoordinate D.torus.unitSystem
        (p.state t).magnetization) τ :=
    (hM.differentiableOn_one τ hτn).differentiableAt
      (hopen.mem_nhds hτn)
  have hequationOn : Set.EqOn
      (fun t ↦ coherentCoordinate D.torus.unitSystem
          (p.state t).temperature *
        coherentCoordinate D.torus.unitSystem (p.state t).magnetization *
        coherentCoordinate D.torus.unitSystem D.torus.volume)
      (fun t ↦ coherentCoordinate D.torus.unitSystem D.material.amount *
        coherentCoordinate D.torus.unitSystem D.material.curieParameter *
        coherentCoordinate D.torus.unitSystem (p.state t).fieldStrength)
      (Set.Icc p.a p.b) := by
    intro t ht
    exact (hstate t ht).2
  have hleftDiff : DifferentiableAt ℝ
      (fun t ↦ coherentCoordinate D.torus.unitSystem
          (p.state t).temperature *
        coherentCoordinate D.torus.unitSystem (p.state t).magnetization *
        coherentCoordinate D.torus.unitSystem D.torus.volume) τ :=
    (hTdiff.mul hMdiff).mul_const _
  have hrightDiff : DifferentiableAt ℝ
      (fun t ↦ coherentCoordinate D.torus.unitSystem D.material.amount *
        coherentCoordinate D.torus.unitSystem D.material.curieParameter *
        coherentCoordinate D.torus.unitSystem (p.state t).fieldStrength) τ :=
    hHdiff.const_mul _
  have hequationDerivRaw :
      deriv
          (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).temperature *
            coherentCoordinate D.torus.unitSystem
              (p.state t).magnetization *
            coherentCoordinate D.torus.unitSystem D.torus.volume) τ =
        deriv
          (fun t ↦ coherentCoordinate D.torus.unitSystem D.material.amount *
            coherentCoordinate D.torus.unitSystem D.material.curieParameter *
            coherentCoordinate D.torus.unitSystem
              (p.state t).fieldStrength) τ := by
    calc
      _ = derivWithin
            (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).temperature *
              coherentCoordinate D.torus.unitSystem
                (p.state t).magnetization *
              coherentCoordinate D.torus.unitSystem D.torus.volume)
            (Set.Icc p.a p.b) τ :=
        (hleftDiff.derivWithin hunique).symm
      _ = derivWithin
            (fun t ↦ coherentCoordinate D.torus.unitSystem D.material.amount *
              coherentCoordinate D.torus.unitSystem D.material.curieParameter *
              coherentCoordinate D.torus.unitSystem
                (p.state t).fieldStrength)
            (Set.Icc p.a p.b) τ :=
        derivWithin_congr hequationOn (hequationOn hτ)
      _ = _ := hrightDiff.derivWithin hunique
  have hequationDeriv :
      (deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).temperature) τ *
          coherentCoordinate D.torus.unitSystem (p.state τ).magnetization +
        coherentCoordinate D.torus.unitSystem (p.state τ).temperature *
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).magnetization) τ) *
          coherentCoordinate D.torus.unitSystem D.torus.volume =
        coherentCoordinate D.torus.unitSystem D.material.amount *
          coherentCoordinate D.torus.unitSystem D.material.curieParameter *
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).fieldStrength) τ := by
    simpa only [deriv_mul_const_field, deriv_fun_mul hTdiff hMdiff,
      deriv_const_mul_field] using hequationDerivRaw
  have hequation := (hstate τ hτ).2
  change
    coherentCoordinate D.torus.unitSystem (p.state τ).temperature *
          coherentCoordinate D.torus.unitSystem (p.state τ).magnetization *
          coherentCoordinate D.torus.unitSystem D.torus.volume =
      coherentCoordinate D.torus.unitSystem D.material.amount *
          coherentCoordinate D.torus.unitSystem D.material.curieParameter *
          coherentCoordinate D.torus.unitSystem (p.state τ).fieldStrength
    at hequation
  have hmaterial :=
    (source_vacuum_material_work_decomposition D p hregular'
      hAmpere hFaraday hsourceBalance hsourceWork τ hτ).2
  have hinternalFormula :
      internalEnergyDifferential D p τ =
        (coherentCoordinate D.torus.unitSystem D.material.amount *
            coherentCoordinate D.torus.unitSystem
              D.material.heatCapacityCoefficient /
            coherentCoordinate D.torus.unitSystem
              (p.state τ).temperature ^ 2) *
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).temperature) τ := by
    simp only [internalEnergyDifferential,
      heatCapacityAtConstantMagnetization,
      coherentCoordinate_quantityFromCoherentCoordinate]
  have henergy :
      (coherentCoordinate D.torus.unitSystem D.material.amount *
            coherentCoordinate D.torus.unitSystem
              D.material.heatCapacityCoefficient /
            coherentCoordinate D.torus.unitSystem
              (p.state τ).temperature ^ 2) *
          deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.state t).temperature) τ =
        coherentCoordinate D.torus.unitSystem
              D.material.vacuumPermeability *
            coherentCoordinate D.torus.unitSystem D.torus.volume *
            coherentCoordinate D.torus.unitSystem
              (p.state τ).fieldStrength *
            deriv
              (fun t ↦ coherentCoordinate D.torus.unitSystem
                (p.state t).magnetization) τ := by
    calc
      _ = internalEnergyDifferential D p τ := hinternalFormula.symm
      _ = deriv
            (fun t ↦ coherentCoordinate D.torus.unitSystem
              (p.internalEnergy t)) τ := (hinternalEnergy τ hτ).symm
      _ = coherentCoordinate D.torus.unitSystem (p.heatIncrement τ) +
            coherentCoordinate D.torus.unitSystem
              (materialWorkIncrement D p τ) := hfirstLaw τ hτ
      _ = _ := by
        rw [hadiabatic τ hτ, hmaterial]
        ring
  let temperature := coherentCoordinate D.torus.unitSystem
    (p.state τ).temperature
  let field := coherentCoordinate D.torus.unitSystem
    (p.state τ).fieldStrength
  let magnetization := coherentCoordinate D.torus.unitSystem
    (p.state τ).magnetization
  let amount := coherentCoordinate D.torus.unitSystem D.material.amount
  let curie := coherentCoordinate D.torus.unitSystem D.material.curieParameter
  let lambda := coherentCoordinate D.torus.unitSystem
    D.material.heatCapacityCoefficient
  let permeability := coherentCoordinate D.torus.unitSystem
    D.material.vacuumPermeability
  let volumeCoordinate := coherentCoordinate D.torus.unitSystem D.torus.volume
  let temperatureDeriv := deriv
    (fun t ↦ coherentCoordinate D.torus.unitSystem
      (p.state t).temperature) τ
  let fieldDeriv := deriv
    (fun t ↦ coherentCoordinate D.torus.unitSystem
      (p.state t).fieldStrength) τ
  let magnetizationDeriv := deriv
    (fun t ↦ coherentCoordinate D.torus.unitSystem
      (p.state t).magnetization) τ
  have htemperature : 0 < temperature := (hstate τ hτ).1.1
  have hamount : 0 < amount := hD.2.2.1
  have hequation' :
      temperature * magnetization * volumeCoordinate =
        amount * curie * field := by
    simpa [temperature, magnetization, volumeCoordinate, amount, curie,
      field] using hequation
  have hequationDeriv' :
      (temperatureDeriv * magnetization +
          temperature * magnetizationDeriv) * volumeCoordinate =
        amount * curie * fieldDeriv := by
    simpa [temperature, temperatureDeriv, magnetization,
      magnetizationDeriv, volumeCoordinate, amount, curie, fieldDeriv]
      using hequationDeriv
  have henergy' :
      (amount * lambda / temperature ^ 2) * temperatureDeriv =
        permeability * volumeCoordinate * field * magnetizationDeriv := by
    simpa [amount, lambda, temperature, temperatureDeriv, permeability,
      volumeCoordinate, field, magnetizationDeriv] using henergy
  have hmagnetizationDeriv :
      temperature ^ 2 * volumeCoordinate * magnetizationDeriv =
        amount * curie *
          (temperature * fieldDeriv - field * temperatureDeriv) := by
    calc
      temperature ^ 2 * volumeCoordinate * magnetizationDeriv =
          temperature *
              ((temperatureDeriv * magnetization +
                  temperature * magnetizationDeriv) * volumeCoordinate) -
            temperatureDeriv *
              (temperature * magnetization * volumeCoordinate) := by ring
      _ = temperature * (amount * curie * fieldDeriv) -
            temperatureDeriv * (amount * curie * field) := by
        rw [hequationDeriv', hequation']
      _ = _ := by ring
  have henergyPolynomial :
      amount * lambda * temperatureDeriv =
        permeability * field *
          (temperature ^ 2 * volumeCoordinate * magnetizationDeriv) := by
    calc
      amount * lambda * temperatureDeriv =
          ((amount * lambda / temperature ^ 2) * temperatureDeriv) *
            temperature ^ 2 := by
        field_simp [ne_of_gt htemperature]
      _ = (permeability * volumeCoordinate * field * magnetizationDeriv) *
            temperature ^ 2 := by rw [henergy']
      _ = _ := by ring
  rw [hmagnetizationDeriv] at henergyPolynomial
  have hfactor :
      amount * (lambda * temperatureDeriv) =
        amount * (permeability * curie * field *
          (temperature * fieldDeriv - field * temperatureDeriv)) := by
    calc
      amount * (lambda * temperatureDeriv) =
          amount * lambda * temperatureDeriv := by ring
      _ = permeability * field *
          (amount * curie *
            (temperature * fieldDeriv - field * temperatureDeriv)) :=
        henergyPolynomial
      _ = _ := by ring
  have hcancelled :
      lambda * temperatureDeriv =
        permeability * curie * field *
          (temperature * fieldDeriv - field * temperatureDeriv) := by
    exact mul_left_cancel₀ (ne_of_gt hamount) hfactor
  have hpolynomial :
      (lambda + permeability * curie * field ^ 2) * temperatureDeriv =
        permeability * curie * field * temperature * fieldDeriv := by
    calc
      (lambda + permeability * curie * field ^ 2) * temperatureDeriv =
          lambda * temperatureDeriv +
            permeability * curie * field ^ 2 * temperatureDeriv := by ring
      _ = permeability * curie * field *
            (temperature * fieldDeriv - field * temperatureDeriv) +
          permeability * curie * field ^ 2 * temperatureDeriv := by
        rw [hcancelled]
      _ = _ := by ring
  have hdenominator :
      0 < lambda + permeability * curie * field ^ 2 := by
    simpa [lambda, permeability, curie] using
      (adiabaticFieldCoefficient_denominator_pos D hD).1 field
  change
    (lambda + permeability * curie * field ^ 2) * temperatureDeriv =
          permeability * curie * field * temperature * fieldDeriv ∧
      temperatureDeriv / temperature =
        (permeability * curie * field /
          (lambda + permeability * curie * field ^ 2)) * fieldDeriv
  refine ⟨hpolynomial, ?_⟩
  field_simp [ne_of_gt htemperature, ne_of_gt hdenominator]
  nlinarith only [hpolynomial]

/-- Every admissible reversible adiabatic endpoint leg satisfies the
integrated endpoint relation; that relation is not an input to the leg. -/
theorem adiabatic_endpoint_relation_of_leg (D : ParamagneticData)
    (Tᵢ : Temperature) (Hᵢ : MagneticFieldStrength)
    (T_f : Temperature) (H_f : MagneticFieldStrength)
    (p : QuasistaticProcess)
    (hleg : IsReversibleAdiabaticEndpointLeg D Tᵢ Hᵢ T_f H_f p) :
    AdiabaticEndpointRelation D Tᵢ Hᵢ T_f H_f := by
  rcases hleg with
    ⟨hTᵢ, hHᵢ, hT_f, hH_f, hrev, hadiabatic, hendpoints⟩
  have hrev' := hrev
  rcases hrev with
    ⟨hregular, _, _, _, _, _, _⟩
  rcases hregular with
    ⟨hD, hab, ⟨neighborhood, hopen, hIcc, hT, hH, _, _, _⟩,
      _, _, _, _, hstate⟩
  rcases adiabaticFieldCoefficient_denominator_pos D hD with
    ⟨_, _, hcoefficientContinuous, hcoefficientIntegrable⟩
  have hpotentialHasDerivAt : ∀ x : ℝ,
      HasDerivAt (adiabaticPotential D) (adiabaticFieldCoefficient D x) x := by
    intro x
    unfold adiabaticPotential
    exact intervalIntegral.integral_hasDerivAt_right
      (hcoefficientIntegrable 0 x)
      hcoefficientContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcoefficientContinuous.continuousAt
  have hpotentialDifferentiable : Differentiable ℝ (adiabaticPotential D) :=
    fun x ↦ (hpotentialHasDerivAt x).differentiableAt
  have hpotentialDerivative :
      deriv (adiabaticPotential D) = adiabaticFieldCoefficient D := by
    funext x
    exact (hpotentialHasDerivAt x).deriv
  have hpotentialContDiff : ContDiff ℝ 1 (adiabaticPotential D) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨hpotentialDifferentiable, ?_⟩
    rw [hpotentialDerivative]
    exact hcoefficientContinuous
  have hlogContDiff : ContDiffOn ℝ 1
      (fun t ↦ Real.log (coherentCoordinate D.torus.unitSystem
        (p.state t).temperature)) (Set.Icc p.a p.b) := by
    apply (hT.mono hIcc).log
    intro t ht
    exact ne_of_gt (hstate t ht).1.1
  have hpotentialAlongContDiff : ContDiffOn ℝ 1
      (fun t ↦ adiabaticPotential D
        (coherentCoordinate D.torus.unitSystem (p.state t).fieldStrength))
      (Set.Icc p.a p.b) := by
    simpa only [Function.comp_def] using
      hpotentialContDiff.comp_contDiffOn (hH.mono hIcc)
  have hderivativesEqual : ∀ t ∈ Set.Icc p.a p.b,
      deriv
          (fun x ↦ Real.log (coherentCoordinate D.torus.unitSystem
            (p.state x).temperature)) t =
        deriv
          (fun x ↦ adiabaticPotential D
            (coherentCoordinate D.torus.unitSystem
              (p.state x).fieldStrength)) t := by
    intro t ht
    have htn : t ∈ neighborhood := hIcc ht
    have hTdiff : DifferentiableAt ℝ
        (fun x ↦ coherentCoordinate D.torus.unitSystem
          (p.state x).temperature) t :=
      (hT.differentiableOn_one t htn).differentiableAt
        (hopen.mem_nhds htn)
    have hHdiff : DifferentiableAt ℝ
        (fun x ↦ coherentCoordinate D.torus.unitSystem
          (p.state x).fieldStrength) t :=
      (hH.differentiableOn_one t htn).differentiableAt
        (hopen.mem_nhds htn)
    have htemperatureNe : coherentCoordinate D.torus.unitSystem
        (p.state t).temperature ≠ 0 := ne_of_gt (hstate t ht).1.1
    have hlogDerivative :
        deriv
            (fun x ↦ Real.log (coherentCoordinate D.torus.unitSystem
              (p.state x).temperature)) t =
          deriv
              (fun x ↦ coherentCoordinate D.torus.unitSystem
                (p.state x).temperature) t /
            coherentCoordinate D.torus.unitSystem
              (p.state t).temperature := by
      have hcomp := ((Real.hasDerivAt_log htemperatureNe).comp t
        hTdiff.hasDerivAt).deriv
      simpa only [Function.comp_def, div_eq_mul_inv, mul_comm] using hcomp
    have hpotentialAlongDerivative :
        deriv
            (fun x ↦ adiabaticPotential D
              (coherentCoordinate D.torus.unitSystem
                (p.state x).fieldStrength)) t =
          adiabaticFieldCoefficient D
              (coherentCoordinate D.torus.unitSystem
                (p.state t).fieldStrength) *
            deriv
              (fun x ↦ coherentCoordinate D.torus.unitSystem
                (p.state x).fieldStrength) t := by
      have hcomp := (hpotentialHasDerivAt
          (coherentCoordinate D.torus.unitSystem
            (p.state t).fieldStrength)).comp t hHdiff.hasDerivAt
      simpa only [Function.comp_def] using hcomp.deriv
    calc
      deriv
          (fun x ↦ Real.log (coherentCoordinate D.torus.unitSystem
            (p.state x).temperature)) t =
        deriv
              (fun x ↦ coherentCoordinate D.torus.unitSystem
                (p.state x).temperature) t /
            coherentCoordinate D.torus.unitSystem
              (p.state t).temperature := hlogDerivative
      _ = adiabaticFieldCoefficient D
              (coherentCoordinate D.torus.unitSystem
                (p.state t).fieldStrength) *
            deriv
              (fun x ↦ coherentCoordinate D.torus.unitSystem
                (p.state x).fieldStrength) t :=
        (adiabatic_differential_relation D p hrev' hadiabatic t ht).2
      _ = deriv
          (fun x ↦ adiabaticPotential D
            (coherentCoordinate D.torus.unitSystem
              (p.state x).fieldStrength)) t := hpotentialAlongDerivative.symm
  have hlogIntegral :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc hlogContDiff hab.le
  have hpotentialIntegral :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc
      hpotentialAlongContDiff hab.le
  have hintegralsEqual :
      (∫ t in p.a..p.b,
        deriv
          (fun x ↦ Real.log (coherentCoordinate D.torus.unitSystem
            (p.state x).temperature)) t) =
      ∫ t in p.a..p.b,
        deriv
          (fun x ↦ adiabaticPotential D
            (coherentCoordinate D.torus.unitSystem
              (p.state x).fieldStrength)) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hderivativesEqual t
      (by simpa only [Set.uIcc_of_le hab.le] using ht)
  have hpathEndpoint :
      Real.log (coherentCoordinate D.torus.unitSystem
          (p.state p.b).temperature) -
          Real.log (coherentCoordinate D.torus.unitSystem
            (p.state p.a).temperature) =
        adiabaticPotential D
            (coherentCoordinate D.torus.unitSystem
              (p.state p.b).fieldStrength) -
          adiabaticPotential D
            (coherentCoordinate D.torus.unitSystem
              (p.state p.a).fieldStrength) := by
    calc
      _ = ∫ t in p.a..p.b,
          deriv
            (fun x ↦ Real.log (coherentCoordinate D.torus.unitSystem
              (p.state x).temperature)) t := hlogIntegral.symm
      _ = ∫ t in p.a..p.b,
          deriv
            (fun x ↦ adiabaticPotential D
              (coherentCoordinate D.torus.unitSystem
                (p.state x).fieldStrength)) t := hintegralsEqual
      _ = _ := hpotentialIntegral
  refine ⟨hD, hTᵢ, hHᵢ, hT_f, hH_f, ?_⟩
  simpa only [hendpoints.1, hendpoints.2.1, hendpoints.2.2.1,
    hendpoints.2.2.2] using hpathEndpoint

/-- For physical apparatus and positive prescribed initial temperature and
fields, the substantive integral endpoint relation selects exactly one final
absolute temperature. -/
theorem adiabatic_endpoint_relation_existsUnique (D : ParamagneticData)
    (Tᵢ : Temperature) (Hᵢ H_f : MagneticFieldStrength)
    (hD : D.IsPhysical)
    (hTᵢ : 0 < coherentCoordinate D.torus.unitSystem Tᵢ)
    (hHᵢ : 0 < coherentCoordinate D.torus.unitSystem Hᵢ)
    (hH_f : 0 < coherentCoordinate D.torus.unitSystem H_f) :
    ∃! T_f : Temperature,
      AdiabaticEndpointRelation D Tᵢ Hᵢ T_f H_f := by
  let endpointLogCoordinate : ℝ :=
    Real.log (coherentCoordinate D.torus.unitSystem Tᵢ) +
      adiabaticPotential D
        (coherentCoordinate D.torus.unitSystem H_f) -
      adiabaticPotential D
        (coherentCoordinate D.torus.unitSystem Hᵢ)
  let T_f : Temperature :=
    quantityFromCoherentCoordinate D.torus.unitSystem
      temperatureDimension (Real.exp endpointLogCoordinate)
  refine ⟨T_f, ?_, ?_⟩
  · unfold AdiabaticEndpointRelation
    refine ⟨hD, hTᵢ, hHᵢ, ?_, hH_f, ?_⟩
    · rw [show coherentCoordinate D.torus.unitSystem T_f =
          Real.exp endpointLogCoordinate by
        exact coherentCoordinate_quantityFromCoherentCoordinate
          D.torus.unitSystem temperatureDimension
            (Real.exp endpointLogCoordinate)]
      exact Real.exp_pos endpointLogCoordinate
    · rw [show coherentCoordinate D.torus.unitSystem T_f =
          Real.exp endpointLogCoordinate by
        exact coherentCoordinate_quantityFromCoherentCoordinate
          D.torus.unitSystem temperatureDimension
            (Real.exp endpointLogCoordinate), Real.log_exp]
      dsimp only [endpointLogCoordinate]
      ring
  · intro other hother
    apply (coordinateInSI_eq_iff D.torus.unitSystem other T_f).mp
    change coherentCoordinate D.torus.unitSystem other =
      coherentCoordinate D.torus.unitSystem T_f
    have hotherPositive :
        0 < coherentCoordinate D.torus.unitSystem other :=
      hother.2.2.2.1
    have hotherEquation := hother.2.2.2.2.2
    have hotherLog :
        Real.log (coherentCoordinate D.torus.unitSystem other) =
          endpointLogCoordinate := by
      dsimp only [endpointLogCoordinate]
      linarith
    calc
      coherentCoordinate D.torus.unitSystem other =
          Real.exp (Real.log
            (coherentCoordinate D.torus.unitSystem other)) :=
        (Real.exp_log hotherPositive).symm
      _ = Real.exp endpointLogCoordinate := by rw [hotherLog]
      _ = coherentCoordinate D.torus.unitSystem T_f := by
        exact (coherentCoordinate_quantityFromCoherentCoordinate
          D.torus.unitSystem temperatureDimension
            (Real.exp endpointLogCoordinate)).symm

/-- The corresponding signed endpoint temperature change exists uniquely,
without assuming its sign or placing its value in the theorem signature. -/
theorem endpointTemperatureChange_existsUnique (D : ParamagneticData)
    (Tᵢ : Temperature) (Hᵢ H_f : MagneticFieldStrength)
    (hD : D.IsPhysical)
    (hTᵢ : 0 < coherentCoordinate D.torus.unitSystem Tᵢ)
    (hHᵢ : 0 < coherentCoordinate D.torus.unitSystem Hᵢ)
    (hH_f : 0 < coherentCoordinate D.torus.unitSystem H_f) :
    ∃! ΔT : TemperatureDifference,
      IsEndpointTemperatureChangeSolution D Tᵢ Hᵢ H_f ΔT := by
  rcases adiabatic_endpoint_relation_existsUnique D Tᵢ Hᵢ H_f
      hD hTᵢ hHᵢ hH_f with
    ⟨T_f, hT_f, hT_f_unique⟩
  refine ⟨T_f - Tᵢ, ?_, ?_⟩
  · change AdiabaticEndpointRelation D Tᵢ Hᵢ
      (Tᵢ + (T_f - Tᵢ)) H_f
    have hsum : Tᵢ + (T_f - Tᵢ) = T_f := by abel
    rw [hsum]
    exact hT_f
  · intro other hother
    have hsum : Tᵢ + other = T_f :=
      hT_f_unique (Tᵢ + other) hother
    calc
      other = (Tᵢ + other) - Tᵢ := by abel
      _ = T_f - Tᵢ := by rw [hsum]

end Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics
