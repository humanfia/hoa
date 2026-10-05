import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Physlib.Units.SIUnitChoices
import Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
import Ipho2026Gpt56solBlind.Shared.FiniteDataAndAffineFit

/-!
# Radial heat flow through the Figure 17 acrylic wall

This file separates an analytic cylindrical-conduction core from the empirical
Part-C adapter.  Dimensioned quantities retain their ISQ dimension; scalar
calculus and finite fitting are performed only after taking coherent-SI
coordinates.  The requested resistance and conductivity remain unknowns of
governing-law predicates.
-/

namespace Ipho2026Gpt56solBlind.Shared

open scoped BigOperators

noncomputable section

namespace RadialConductionCore

open Ipho2026Gpt56solBlind.Shared.ISQDimensions

/-! ## Coherent-SI coordinates and cylindrical geometry -/

/-- The coherent-SI real coordinate of a dimensioned quantity. -/
def siValue {d : Dimension ISQDimensionBase} (x : Quantity d) : ℝ :=
  coordinateInSI SIUnitChoices.SI x

/-- A cylindrical wall with strictly ordered radii and positive wetted length. -/
@[ext]
structure CylindricalWall where
  innerRadius : Length
  outerRadius : Length
  wettedLength : Length
  innerRadius_pos : 0 < siValue innerRadius
  innerRadius_lt_outerRadius : siValue innerRadius < siValue outerRadius
  wettedLength_pos : 0 < siValue wettedLength

/-- Membership in the closed radial wall interval. -/
def InClosedWall (wall : CylindricalWall) (radius : ℝ) : Prop :=
  siValue wall.innerRadius ≤ radius ∧ radius ≤ siValue wall.outerRadius

/-- Membership in the open radial wall interval. -/
def InOpenWall (wall : CylindricalWall) (radius : ℝ) : Prop :=
  siValue wall.innerRadius < radius ∧ radius < siValue wall.outerRadius

/-- `outerRadius` is farther from the common axis than `innerRadius`. -/
def RadiallyOutwardOf (wall : CylindricalWall) (innerRadius outerRadius : ℝ) : Prop :=
  InClosedWall wall innerRadius ∧ InClosedWall wall outerRadius ∧
    innerRadius < outerRadius

/-- Wetted lateral area `2 π r ℓ`, not annular cross-sectional area. -/
def lateralArea (wall : CylindricalWall) (radius : ℝ) : Area :=
  ⟨2 * Real.pi * radius * siValue wall.wettedLength⟩

/-- Every lateral area at a closed-wall radius is positive. -/
lemma lateralArea_pos (wall : CylindricalWall) (radius : ℝ)
    (hRadius : InClosedWall wall radius) :
    0 < siValue (lateralArea wall radius) := by
  have hRadiusPos : 0 < radius :=
    lt_of_lt_of_le wall.innerRadius_pos hRadius.1
  have hProductPos :
      0 < 2 * Real.pi * radius * siValue wall.wettedLength := by
    exact
      mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hRadiusPos)
        wall.wettedLength_pos
  simpa only [siValue, lateralArea, coordinateInSI_self] using hProductPos

/-! ## Regular profiles and the signed outward Fourier law -/

/-- An absolute-temperature profile parameterized by outward-increasing radius. -/
abbrev RadialTemperatureProfile := ℝ → Temperature

/-- A temperature-gradient field directed toward increasing radius. -/
abbrev OutwardTemperatureDerivative := ℝ → TemperatureGradient

/-- A single signed, radius-independent outward heat rate. -/
abbrev ConstantOutwardHeatRate := HeatRate

/-- Material, boundary, profile, derivative, and signed-rate data at one snapshot. -/
structure RadialThermalSnapshot where
  conductivity : ThermalConductivity
  conductivity_pos : 0 < siValue conductivity
  innerBulkTemperature : Temperature
  outerBulkTemperature : Temperature
  innerBulkTemperature_pos : 0 < siValue innerBulkTemperature
  outerBulkTemperature_pos : 0 < siValue outerBulkTemperature
  profile : RadialTemperatureProfile
  outwardDerivative : OutwardTemperatureDerivative
  outwardHeatRate : ConstantOutwardHeatRate

/-- Closed-wall continuity and positivity, open-wall derivative data, and
integrability of the scalar derivative. -/
def RegularRadialProfile (wall : CylindricalWall)
    (profile : RadialTemperatureProfile)
    (outwardDerivative : OutwardTemperatureDerivative) : Prop :=
  ContinuousOn (fun radius ↦ siValue (profile radius))
      (Set.Icc (siValue wall.innerRadius) (siValue wall.outerRadius)) ∧
    (∀ radius, InClosedWall wall radius → 0 < siValue (profile radius)) ∧
    (∀ radius, InOpenWall wall radius →
      HasDerivAt (fun radialCoordinate ↦ siValue (profile radialCoordinate))
        (siValue (outwardDerivative radius)) radius) ∧
    IntervalIntegrable
      (deriv (fun radialCoordinate ↦ siValue (profile radialCoordinate)))
      MeasureTheory.volume (siValue wall.innerRadius) (siValue wall.outerRadius)

/-- The profile faces equal the named inner- and outer-bulk temperatures. -/
def HasBoundaryTemperatures (wall : CylindricalWall)
    (snapshot : RadialThermalSnapshot) : Prop :=
  snapshot.profile (siValue wall.innerRadius) = snapshot.innerBulkTemperature ∧
    snapshot.profile (siValue wall.outerRadius) = snapshot.outerBulkTemperature

/-- Signed Fourier conduction in the outward-increasing radial coordinate. -/
def SatisfiesOutwardFourierLaw (wall : CylindricalWall)
    (snapshot : RadialThermalSnapshot) : Prop :=
  ∀ radius, InOpenWall wall radius →
    siValue snapshot.outwardHeatRate =
      -siValue snapshot.conductivity * siValue (lateralArea wall radius) *
        siValue (snapshot.outwardDerivative radius)

/-- A regular boundary-matched snapshot satisfying the signed Fourier law. -/
def IsSteadyRadialConduction (wall : CylindricalWall)
    (snapshot : RadialThermalSnapshot) : Prop :=
  RegularRadialProfile wall snapshot.profile snapshot.outwardDerivative ∧
    HasBoundaryTemperatures wall snapshot ∧
    SatisfiesOutwardFourierLaw wall snapshot

/-- Integration of the steady radial Fourier law across the acrylic wall. -/
lemma integratedFourierLaw (wall : CylindricalWall)
    (snapshot : RadialThermalSnapshot)
    (hSteady : IsSteadyRadialConduction wall snapshot) :
    siValue snapshot.outerBulkTemperature - siValue snapshot.innerBulkTemperature =
      -(siValue snapshot.outwardHeatRate /
          (2 * Real.pi * siValue snapshot.conductivity * siValue wall.wettedLength)) *
        Real.log (siValue wall.outerRadius / siValue wall.innerRadius) := by
  rcases hSteady with ⟨hRegular, hBoundary, hFourier⟩
  rcases hRegular with
    ⟨hContinuous, _hPositive, hDerivative, hIntegrable⟩
  let f : ℝ → ℝ := fun radius ↦ siValue (snapshot.profile radius)
  change ContinuousOn f
    (Set.Icc (siValue wall.innerRadius) (siValue wall.outerRadius)) at hContinuous
  change ∀ radius, InOpenWall wall radius →
    HasDerivAt f (siValue (snapshot.outwardDerivative radius)) radius at hDerivative
  change IntervalIntegrable (deriv f) MeasureTheory.volume
    (siValue wall.innerRadius) (siValue wall.outerRadius) at hIntegrable
  have hFundamentalTheorem :
      (∫ radius in siValue wall.innerRadius..siValue wall.outerRadius,
          deriv f radius) =
        f (siValue wall.outerRadius) - f (siValue wall.innerRadius) := by
    apply intervalIntegral.integral_deriv_eq_sub_uIoo
    · simpa only [Set.uIcc_of_le wall.innerRadius_lt_outerRadius.le] using
        hContinuous
    · intro radius hRadius
      rw [Set.uIoo_of_le wall.innerRadius_lt_outerRadius.le] at hRadius
      exact (hDerivative radius hRadius).differentiableAt
    · exact hIntegrable
  have hDerivativeFormula :
      Set.EqOn (deriv f)
        (fun radius ↦
          -(siValue snapshot.outwardHeatRate /
              (2 * Real.pi * siValue snapshot.conductivity *
                siValue wall.wettedLength)) * radius⁻¹)
        (Set.uIoo (siValue wall.innerRadius) (siValue wall.outerRadius)) := by
    intro radius hRadius
    rw [Set.uIoo_of_le wall.innerRadius_lt_outerRadius.le] at hRadius
    have hRadiusPos : 0 < radius :=
      lt_trans wall.innerRadius_pos hRadius.1
    have hFourierAt := hFourier radius hRadius
    have hFourierAt' :
        siValue snapshot.outwardHeatRate =
          -siValue snapshot.conductivity *
              (2 * Real.pi * radius * siValue wall.wettedLength) *
            siValue (snapshot.outwardDerivative radius) := by
      simpa only [siValue, lateralArea, coordinateInSI_self] using hFourierAt
    have hCoefficientNe :
        -siValue snapshot.conductivity *
            (2 * Real.pi * radius * siValue wall.wettedLength) ≠ 0 := by
      apply mul_ne_zero
      · exact neg_ne_zero.mpr (ne_of_gt snapshot.conductivity_pos)
      · exact
          mul_ne_zero
            (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
              (ne_of_gt hRadiusPos))
            (ne_of_gt wall.wettedLength_pos)
    have hGradientSolved :
        siValue (snapshot.outwardDerivative radius) =
          siValue snapshot.outwardHeatRate /
            (-siValue snapshot.conductivity *
              (2 * Real.pi * radius * siValue wall.wettedLength)) := by
      apply (eq_div_iff hCoefficientNe).2
      calc
        siValue (snapshot.outwardDerivative radius) *
              (-siValue snapshot.conductivity *
                (2 * Real.pi * radius * siValue wall.wettedLength)) =
            (-siValue snapshot.conductivity *
                (2 * Real.pi * radius * siValue wall.wettedLength)) *
              siValue (snapshot.outwardDerivative radius) := by ring
        _ = siValue snapshot.outwardHeatRate := hFourierAt'.symm
    calc
      deriv f radius = siValue (snapshot.outwardDerivative radius) :=
        (hDerivative radius hRadius).deriv
      _ = siValue snapshot.outwardHeatRate /
          (-siValue snapshot.conductivity *
            (2 * Real.pi * radius * siValue wall.wettedLength)) :=
        hGradientSolved
      _ = -(siValue snapshot.outwardHeatRate /
            (2 * Real.pi * siValue snapshot.conductivity *
              siValue wall.wettedLength)) * radius⁻¹ := by
        field_simp [ne_of_gt snapshot.conductivity_pos,
          ne_of_gt wall.wettedLength_pos, ne_of_gt hRadiusPos,
          ne_of_gt Real.pi_pos]
  have hInnerBoundary := congrArg (fun temperature ↦ siValue temperature) hBoundary.1
  have hOuterBoundary := congrArg (fun temperature ↦ siValue temperature) hBoundary.2
  have hOuterRadiusPos : 0 < siValue wall.outerRadius :=
    lt_trans wall.innerRadius_pos wall.innerRadius_lt_outerRadius
  calc
    siValue snapshot.outerBulkTemperature -
          siValue snapshot.innerBulkTemperature =
        f (siValue wall.outerRadius) - f (siValue wall.innerRadius) := by
          change siValue snapshot.outerBulkTemperature -
              siValue snapshot.innerBulkTemperature =
            siValue (snapshot.profile (siValue wall.outerRadius)) -
              siValue (snapshot.profile (siValue wall.innerRadius))
          rw [hOuterBoundary, hInnerBoundary]
    _ = ∫ radius in siValue wall.innerRadius..siValue wall.outerRadius,
          deriv f radius := hFundamentalTheorem.symm
    _ = ∫ radius in siValue wall.innerRadius..siValue wall.outerRadius,
          -(siValue snapshot.outwardHeatRate /
              (2 * Real.pi * siValue snapshot.conductivity *
                siValue wall.wettedLength)) * radius⁻¹ :=
      intervalIntegral.integral_congr_uIoo hDerivativeFormula
    _ = -(siValue snapshot.outwardHeatRate /
            (2 * Real.pi * siValue snapshot.conductivity *
              siValue wall.wettedLength)) *
          (∫ radius in siValue wall.innerRadius..siValue wall.outerRadius,
            radius⁻¹) := by
      rw [intervalIntegral.integral_const_mul]
    _ = -(siValue snapshot.outwardHeatRate /
            (2 * Real.pi * siValue snapshot.conductivity *
              siValue wall.wettedLength)) *
          Real.log (siValue wall.outerRadius / siValue wall.innerRadius) := by
      rw [integral_inv_of_pos wall.innerRadius_pos hOuterRadiusPos]

/-! ## Heat received by the inner water and capacity scope -/

/-- Positive absolute bulk-temperature histories for elapsed times. -/
structure BulkTemperatureHistory where
  innerTemperature : ℝ → Temperature
  outerTemperature : ℝ → Temperature
  innerTemperature_pos : ∀ t, 0 ≤ t → 0 < siValue (innerTemperature t)
  outerTemperature_pos : ∀ t, 0 ≤ t → 0 < siValue (outerTemperature t)

/-- Cumulative inner-received heat and the two oppositely oriented rates. -/
structure InnerWaterHeatHistory where
  heatIntoInner : ℝ → Energy
  heatRateIntoInner : ℝ → HeatRate
  outwardHeatRate : ℝ → HeatRate

/-- Cumulative heat starts at zero and differentiates to the inner-received
rate, including a right derivative at elapsed time zero. -/
def HeatIntoInnerIsDerivative (history : InnerWaterHeatHistory) : Prop :=
  siValue (history.heatIntoInner 0) = 0 ∧
    (∀ t, 0 < t →
      HasDerivAt (fun elapsed ↦ siValue (history.heatIntoInner elapsed))
        (siValue (history.heatRateIntoInner t)) t) ∧
    HasDerivWithinAt (fun elapsed ↦ siValue (history.heatIntoInner elapsed))
      (siValue (history.heatRateIntoInner 0)) (Set.Ici 0) 0

/-- At one time, heat received by the inner water is opposite to outward wall heat. -/
def PointwiseHeatRateSignBridge (heatRateIntoInner outwardHeatRate : HeatRate) : Prop :=
  heatRateIntoInner = -outwardHeatRate

/-- The orientation bridge holds for every nonnegative elapsed time. -/
def HasHeatRateSignBridge (history : InnerWaterHeatHistory) : Prop :=
  ∀ t, 0 ≤ t →
    PointwiseHeatRateSignBridge (history.heatRateIntoInner t)
      (history.outwardHeatRate t)

/-- Mass-specific heat capacity, with SI coordinate in J kg⁻¹ K⁻¹. -/
abbrev SpecificHeatCapacity :=
  Quantity (energyDimension * massDimension⁻¹ * temperatureDimension⁻¹)

/-- Inner-water source geometry and positive material inputs. -/
@[ext]
structure InnerWaterGeometry where
  wall : CylindricalWall
  innerWaterHeight : Length
  waterMassDensity : MassDensity
  waterSpecificHeatCapacity : SpecificHeatCapacity
  innerWaterHeight_pos : 0 < siValue innerWaterHeight
  waterMassDensity_pos : 0 < siValue waterMassDensity
  waterSpecificHeatCapacity_pos : 0 < siValue waterSpecificHeatCapacity
  wettedLength_le_innerWaterHeight :
    siValue wall.wettedLength ≤ siValue innerWaterHeight

/-- Cylindrical inner-water volume. -/
def innerWaterVolume (geometry : InnerWaterGeometry) : Volume :=
  ⟨Real.pi * siValue geometry.wall.innerRadius ^ 2 *
    siValue geometry.innerWaterHeight⟩

/-- Water mass obtained from density and the cylindrical volume. -/
def innerWaterMass (geometry : InnerWaterGeometry) : Mass :=
  ⟨siValue geometry.waterMassDensity * siValue (innerWaterVolume geometry)⟩

/-- Lumped heat capacity of the inner water. -/
def innerWaterHeatCapacity (geometry : InnerWaterGeometry) : HeatCapacity :=
  ⟨siValue (innerWaterMass geometry) *
    siValue geometry.waterSpecificHeatCapacity⟩

/-- The derived inner-water volume, mass, and heat capacity are positive. -/
lemma innerWaterHeatCapacity_pos (geometry : InnerWaterGeometry) :
    0 < siValue (innerWaterVolume geometry) ∧
      0 < siValue (innerWaterMass geometry) ∧
      0 < siValue (innerWaterHeatCapacity geometry) := by
  have hVolume : 0 < siValue (innerWaterVolume geometry) := by
    have hProductPos :
        0 < Real.pi * siValue geometry.wall.innerRadius ^ 2 *
          siValue geometry.innerWaterHeight := by
      exact
        mul_pos
          (mul_pos Real.pi_pos (pow_pos geometry.wall.innerRadius_pos 2))
          geometry.innerWaterHeight_pos
    simpa only [siValue, innerWaterVolume, coordinateInSI_self] using hProductPos
  have hMass : 0 < siValue (innerWaterMass geometry) := by
    have hProductPos := mul_pos geometry.waterMassDensity_pos hVolume
    simpa only [siValue, innerWaterMass, coordinateInSI_self] using hProductPos
  refine ⟨hVolume, hMass, ?_⟩
  have hProductPos := mul_pos hMass geometry.waterSpecificHeatCapacity_pos
  simpa only [siValue, innerWaterHeatCapacity, coordinateInSI_self] using hProductPos

/-- A signed absolute-temperature rate, with SI coordinate in K s⁻¹. -/
abbrev TemperatureRate := Quantity (temperatureDimension * timeDimension⁻¹)

/-- Lumped inner-water heat balance `q = C v`. -/
def SatisfiesInnerWaterHeatBalance (geometry : InnerWaterGeometry)
    (innerTemperatureRate : TemperatureRate) (heatRateIntoInner : HeatRate) : Prop :=
  siValue heatRateIntoInner =
    siValue (innerWaterHeatCapacity geometry) * siValue innerTemperatureRate

/-- Pointwise effective-resistance law for the heat received by the inner water. -/
def PointwiseThermalResistanceLaw (resistance : ThermalResistance)
    (innerTemperature outerTemperature : Temperature)
    (heatRateIntoInner : HeatRate) : Prop :=
  siValue resistance ≠ 0 ∧
    siValue heatRateIntoInner =
      (siValue outerTemperature - siValue innerTemperature) / siValue resistance

/-- The pointwise resistance law along a pair of temperature and heat histories. -/
def SatisfiesThermalResistanceLaw (temperatures : BulkTemperatureHistory)
    (heat : InnerWaterHeatHistory) (resistance : ThermalResistance) : Prop :=
  ∀ t, 0 ≤ t →
    PointwiseThermalResistanceLaw resistance (temperatures.innerTemperature t)
      (temperatures.outerTemperature t) (heat.heatRateIntoInner t)

/-- Separate physical and C.3/C.4-modeled apparatus capacity accounting. -/
structure CapacityContext where
  innerWaterGeometry : InnerWaterGeometry
  outerWaterHeatCapacity : HeatCapacity
  physicalApparatusHeatCapacity : HeatCapacity
  c3c4ModeledApparatusHeatCapacity : HeatCapacity
  outerWaterHeatCapacity_pos : 0 < siValue outerWaterHeatCapacity
  physicalApparatusHeatCapacity_nonneg :
    0 ≤ siValue physicalApparatusHeatCapacity

/-- Only the apparatus contribution used in the C.3/C.4 model is set to zero. -/
def C3C4ApparatusCapacityIdealization (context : CapacityContext) : Prop :=
  siValue context.c3c4ModeledApparatusHeatCapacity = 0

/-- The scoped C.3/C.4 idealization leaves both water capacities and the
physical apparatus capacity intact. -/
lemma c3c4Idealization_capacity_scope (context : CapacityContext)
    (hIdealization : C3C4ApparatusCapacityIdealization context) :
    0 < siValue (innerWaterHeatCapacity context.innerWaterGeometry) ∧
      0 < siValue context.outerWaterHeatCapacity ∧
      0 ≤ siValue context.physicalApparatusHeatCapacity ∧
      siValue context.c3c4ModeledApparatusHeatCapacity = 0 := by
  exact
    ⟨(innerWaterHeatCapacity_pos context.innerWaterGeometry).2.2,
      context.outerWaterHeatCapacity_pos,
      context.physicalApparatusHeatCapacity_nonneg, hIdealization⟩

/-! ## Conductivity characterized by the integrated laws -/

/-- The logarithmic radius ratio of a positive cylindrical wall is positive. -/
lemma log_radiusRatio_pos (wall : CylindricalWall) :
    0 < Real.log (siValue wall.outerRadius / siValue wall.innerRadius) := by
  apply Real.log_pos
  apply (lt_div_iff₀ wall.innerRadius_pos).2
  simpa using wall.innerRadius_lt_outerRadius

/-- Positive resistance and conductivity related by integrated cylindrical conduction. -/
def ConductivityCharacterization (wall : CylindricalWall)
    (resistance : ThermalResistance) (conductivity : ThermalConductivity) : Prop :=
  0 < siValue resistance ∧
    0 < siValue conductivity ∧
    2 * Real.pi * siValue wall.wettedLength * siValue conductivity *
        siValue resistance =
      Real.log (siValue wall.outerRadius / siValue wall.innerRadius)

/-- The steady Fourier law, sign bridge, and resistance law imply the
conductivity characterization when the boundary difference is nonzero. -/
theorem steadyLaws_imply_conductivityCharacterization
    (wall : CylindricalWall) (snapshot : RadialThermalSnapshot)
    (heatRateIntoInner : HeatRate) (resistance : ThermalResistance)
    (hSteady : IsSteadyRadialConduction wall snapshot)
    (hSignBridge :
      PointwiseHeatRateSignBridge heatRateIntoInner snapshot.outwardHeatRate)
    (hResistanceLaw :
      PointwiseThermalResistanceLaw resistance snapshot.innerBulkTemperature
        snapshot.outerBulkTemperature heatRateIntoInner)
    (hResistancePos : 0 < siValue resistance)
    (hTemperatureDifference :
      siValue snapshot.outerBulkTemperature -
          siValue snapshot.innerBulkTemperature ≠ 0) :
    ConductivityCharacterization wall resistance snapshot.conductivity := by
  rcases hResistanceLaw with ⟨hResistanceNe, hResistanceEquation⟩
  change heatRateIntoInner = -snapshot.outwardHeatRate at hSignBridge
  have hSignCoordinate :
      siValue heatRateIntoInner = -siValue snapshot.outwardHeatRate := by
    simpa only [siValue, coordinateInSI_self, WithDim.val_neg] using
      congrArg (fun heatRate ↦ siValue heatRate) hSignBridge
  have hIntegrated := integratedFourierLaw wall snapshot hSteady
  have hFourierDenominatorNe :
      2 * Real.pi * siValue snapshot.conductivity *
          siValue wall.wettedLength ≠ 0 := by
    exact
      mul_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
          (ne_of_gt snapshot.conductivity_pos))
        (ne_of_gt wall.wettedLength_pos)
  have hIntegratedCleared :
      (siValue snapshot.outerBulkTemperature -
          siValue snapshot.innerBulkTemperature) *
          (2 * Real.pi * siValue snapshot.conductivity *
            siValue wall.wettedLength) =
        siValue heatRateIntoInner *
          Real.log (siValue wall.outerRadius / siValue wall.innerRadius) := by
    calc
      (siValue snapshot.outerBulkTemperature -
            siValue snapshot.innerBulkTemperature) *
            (2 * Real.pi * siValue snapshot.conductivity *
              siValue wall.wettedLength) =
          (-(siValue snapshot.outwardHeatRate /
                (2 * Real.pi * siValue snapshot.conductivity *
                  siValue wall.wettedLength)) *
              Real.log (siValue wall.outerRadius / siValue wall.innerRadius)) *
            (2 * Real.pi * siValue snapshot.conductivity *
              siValue wall.wettedLength) := by rw [hIntegrated]
      _ = (-siValue snapshot.outwardHeatRate) *
            Real.log (siValue wall.outerRadius / siValue wall.innerRadius) := by
          field_simp [hFourierDenominatorNe,
            ne_of_gt snapshot.conductivity_pos,
            ne_of_gt wall.wettedLength_pos]
      _ = siValue heatRateIntoInner *
            Real.log (siValue wall.outerRadius / siValue wall.innerRadius) := by
          rw [hSignCoordinate]
  have hResistanceCleared :
      siValue heatRateIntoInner * siValue resistance =
        siValue snapshot.outerBulkTemperature -
          siValue snapshot.innerBulkTemperature := by
    rw [hResistanceEquation]
    exact div_mul_cancel₀ _ hResistanceNe
  refine ⟨hResistancePos, snapshot.conductivity_pos, ?_⟩
  apply mul_left_cancel₀ hTemperatureDifference
  calc
    (siValue snapshot.outerBulkTemperature -
          siValue snapshot.innerBulkTemperature) *
        (2 * Real.pi * siValue wall.wettedLength *
          siValue snapshot.conductivity * siValue resistance) =
      ((siValue snapshot.outerBulkTemperature -
            siValue snapshot.innerBulkTemperature) *
          (2 * Real.pi * siValue snapshot.conductivity *
            siValue wall.wettedLength)) * siValue resistance := by ring
    _ = (siValue heatRateIntoInner *
          Real.log (siValue wall.outerRadius / siValue wall.innerRadius)) *
        siValue resistance := by rw [hIntegratedCleared]
    _ = (siValue heatRateIntoInner * siValue resistance) *
          Real.log (siValue wall.outerRadius / siValue wall.innerRadius) := by ring
    _ = (siValue snapshot.outerBulkTemperature -
          siValue snapshot.innerBulkTemperature) *
        Real.log (siValue wall.outerRadius / siValue wall.innerRadius) := by
      rw [hResistanceCleared]

/-- A positive resistance and positive cylindrical wall determine exactly one
conductivity through the governing logarithmic relation. -/
theorem existsUnique_conductivityCharacterization (wall : CylindricalWall)
    (resistance : ThermalResistance) (hResistancePos : 0 < siValue resistance) :
    ∃! conductivity : ThermalConductivity,
      ConductivityCharacterization wall resistance conductivity := by
  let conductivity : ThermalConductivity :=
    ⟨Real.log (siValue wall.outerRadius / siValue wall.innerRadius) /
      (2 * Real.pi * siValue wall.wettedLength * siValue resistance)⟩
  have hLogPos := log_radiusRatio_pos wall
  have hCoefficientPos :
      0 < 2 * Real.pi * siValue wall.wettedLength * siValue resistance := by
    exact
      mul_pos
        (mul_pos (mul_pos (by norm_num) Real.pi_pos) wall.wettedLength_pos)
        hResistancePos
  have hConductivityPos : 0 < siValue conductivity := by
    simpa only [conductivity, siValue, coordinateInSI_self] using
      div_pos hLogPos hCoefficientPos
  have hCharacterization :
      ConductivityCharacterization wall resistance conductivity := by
    refine ⟨hResistancePos, hConductivityPos, ?_⟩
    have hLengthValNe : wall.wettedLength.val ≠ 0 := by
      simpa only [siValue, coordinateInSI_self] using
        ne_of_gt wall.wettedLength_pos
    have hResistanceValNe : resistance.val ≠ 0 := by
      simpa only [siValue, coordinateInSI_self] using
        ne_of_gt hResistancePos
    simp only [conductivity, siValue, coordinateInSI_self]
    field_simp [hLengthValNe, hResistanceValNe]
  refine ⟨conductivity, hCharacterization, ?_⟩
  intro other hOther
  apply
    (coordinateInSI_eq_iff SIUnitChoices.SI other conductivity).mp
  change siValue other = siValue conductivity
  apply mul_left_cancel₀ (ne_of_gt hCoefficientPos)
  calc
    (2 * Real.pi * siValue wall.wettedLength * siValue resistance) *
          siValue other =
        2 * Real.pi * siValue wall.wettedLength * siValue other *
          siValue resistance := by ring
    _ = Real.log (siValue wall.outerRadius / siValue wall.innerRadius) :=
      hOther.2.2
    _ = 2 * Real.pi * siValue wall.wettedLength * siValue conductivity *
          siValue resistance := hCharacterization.2.2.symm
    _ = (2 * Real.pi * siValue wall.wettedLength * siValue resistance) *
          siValue conductivity := by ring

end RadialConductionCore

namespace RadialHeatFlow

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
open Ipho2026Gpt56solBlind.Shared.FiniteObservations
open Ipho2026Gpt56solBlind.Shared.ExactGraph
open Ipho2026Gpt56solBlind.Shared.AffineFit
open Ipho2026Gpt56solBlind.Shared.RadialConductionCore

/-! ## Prepared Part-C observations and the Figure 17 geometry bridge -/

/-- One externally observed time, inner temperature, and outer temperature. -/
structure TemperatureSample where
  elapsedTime : Time
  innerTemperature : Temperature
  outerTemperature : Temperature
  elapsedTime_nonneg : 0 ≤ siValue elapsedTime
  innerTemperature_pos : 0 < siValue innerTemperature
  outerTemperature_pos : 0 < siValue outerTemperature

/-- Figure 17 measurements, water columns and material data used in Part C. -/
structure Figure17PartCApparatusData where
  measurements : Figure17Measurements
  outerWaterHeight : Length
  innerWaterHeight : Length
  waterMassDensity : MassDensity
  waterSpecificHeatCapacity : SpecificHeatCapacity
  outerWaterTargetTemperature : Temperature

/-- Ordered procedure facts preceding the externally supplied record. -/
structure Figure17PartCProcedureState where
  outerLevelSetBeforeHeating : Bool
  outerWaterHeatedToTargetAfterLevelSet : Bool
  pumpHomogenizedAfterHeating : Bool
  innerLevelSetAfterOuterHomogenization : Bool
  stopwatchStartedAfterInnerLevelSet : Bool

/-- Source geometry, material positivity, declared heights and target, and the
ordered Part-C preparation procedure. -/
def PreparedFigure17PartCApparatus (apparatus : Figure17PartCApparatusData)
    (procedure : Figure17PartCProcedureState) : Prop :=
  SatisfiesFigure17Geometry apparatus.measurements ∧
    0 < siValue apparatus.waterMassDensity ∧
    0 < siValue apparatus.waterSpecificHeatCapacity ∧
    apparatus.outerWaterHeight = lengthInCentimetres 15 ∧
    apparatus.outerWaterTargetTemperature = temperatureInKelvin (273.15 + 65) ∧
    procedure.outerLevelSetBeforeHeating = true ∧
    procedure.outerWaterHeatedToTargetAfterLevelSet = true ∧
    procedure.pumpHomogenizedAfterHeating = true ∧
    apparatus.innerWaterHeight = lengthInCentimetres 10 ∧
    procedure.innerLevelSetAfterOuterHomogenization = true ∧
    procedure.stopwatchStartedAfterInnerLevelSet = true

/-- A named Part-C run with one fixed apparatus, procedure, and indexed
external temperature record. -/
structure Figure17PartCRadialRun (q : ℕ) where
  apparatus : Figure17PartCApparatusData
  procedure : Figure17PartCProcedureState
  externalRecord : Fin q → TemperatureSample

/-- Preparedness constrains the fixed setup, not any observed record value. -/
def PreparedFigure17PartCRadialRun {q : ℕ}
    (run : Figure17PartCRadialRun q) : Prop :=
  PreparedFigure17PartCApparatus run.apparatus run.procedure

/-- The unique analytic wall and inner-water geometry tied to Figure 17 data. -/
def Figure17PartCGeometryBridge (apparatus : Figure17PartCApparatusData)
    (wall : CylindricalWall) (geometry : InnerWaterGeometry) : Prop :=
  siValue wall.innerRadius =
      siValue apparatus.measurements.innerCylinderInsideDiameter / 2 ∧
    siValue wall.outerRadius =
      siValue wall.innerRadius +
        siValue apparatus.measurements.innerCylinderWallThickness ∧
    siValue wall.wettedLength =
      min (siValue apparatus.innerWaterHeight)
        (siValue apparatus.outerWaterHeight) ∧
    siValue wall.outerRadius <
      siValue apparatus.measurements.outerCylinderOutsideDiameter / 2 -
        siValue apparatus.measurements.outerCylinderWallThickness ∧
    geometry.wall = wall ∧
    geometry.innerWaterHeight = apparatus.innerWaterHeight ∧
    geometry.waterMassDensity = apparatus.waterMassDensity ∧
    geometry.waterSpecificHeatCapacity = apparatus.waterSpecificHeatCapacity ∧
    siValue (innerClearCrossSectionArea apparatus.measurements) =
      Real.pi * siValue wall.innerRadius ^ 2 ∧
    siValue (innerWaterVolume geometry) =
      siValue (innerClearCrossSectionArea apparatus.measurements) *
        siValue apparatus.innerWaterHeight

/-- A prepared Part-C apparatus determines exactly one wall/source-geometry pair. -/
theorem existsUnique_figure17PartCGeometryBridge
    (apparatus : Figure17PartCApparatusData)
    (procedure : Figure17PartCProcedureState)
    (hPrepared : PreparedFigure17PartCApparatus apparatus procedure) :
    ∃! pair : CylindricalWall × InnerWaterGeometry,
      Figure17PartCGeometryBridge apparatus pair.1 pair.2 := by
  rcases hPrepared with
    ⟨hFigureGeometry, hDensityPos, hSpecificHeatPos, hOuterHeight,
      _hTarget, _hOuterLevel, _hOuterHeating, _hPump, hInnerHeight,
      _hInnerLevel, _hStopwatch⟩
  rcases hFigureGeometry with
    ⟨_hOuterTolerance, _hInnerTolerance, _hInnerWallTolerance,
      _hOuterWallTolerance, hInnerDiameterPos, _hOuterDiameterPos,
      hInnerWallPos, _hOuterWallPos, hNesting⟩
  have hInnerHeightPos : 0 < siValue apparatus.innerWaterHeight := by
    rw [hInnerHeight]
    norm_num [siValue, lengthInCentimetres]
  have hOuterHeightPos : 0 < siValue apparatus.outerWaterHeight := by
    rw [hOuterHeight]
    norm_num [siValue, lengthInCentimetres]
  let wall : CylindricalWall :=
    { innerRadius :=
        ⟨siValue apparatus.measurements.innerCylinderInsideDiameter / 2⟩
      outerRadius :=
        ⟨siValue apparatus.measurements.innerCylinderInsideDiameter / 2 +
          siValue apparatus.measurements.innerCylinderWallThickness⟩
      wettedLength :=
        ⟨min (siValue apparatus.innerWaterHeight)
          (siValue apparatus.outerWaterHeight)⟩
      innerRadius_pos := by
        simpa only [siValue, coordinateInSI_self] using
          div_pos hInnerDiameterPos (by norm_num)
      innerRadius_lt_outerRadius := by
        simp only [siValue, coordinateInSI_self]
        have hInnerWallPos' :
            0 < apparatus.measurements.innerCylinderWallThickness.val := by
          simpa only [siValue, coordinateInSI_self] using hInnerWallPos
        linarith
      wettedLength_pos := by
        simpa only [siValue, coordinateInSI_self] using
          lt_min hInnerHeightPos hOuterHeightPos }
  let geometry : InnerWaterGeometry :=
    { wall := wall
      innerWaterHeight := apparatus.innerWaterHeight
      waterMassDensity := apparatus.waterMassDensity
      waterSpecificHeatCapacity := apparatus.waterSpecificHeatCapacity
      innerWaterHeight_pos := hInnerHeightPos
      waterMassDensity_pos := hDensityPos
      waterSpecificHeatCapacity_pos := hSpecificHeatPos
      wettedLength_le_innerWaterHeight := by
        simp only [wall, siValue, coordinateInSI_self]
        exact min_le_left _ _ }
  have hBridge : Figure17PartCGeometryBridge apparatus wall geometry := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [wall, siValue, coordinateInSI_self]
    · simp only [wall, siValue, coordinateInSI_self]
    · simp only [wall, siValue, coordinateInSI_self]
    · simpa only [wall, siValue, coordinateInSI_self] using hNesting
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [innerClearCrossSectionArea, wall, siValue,
        coordinateInSI_self]
    · simp only [innerWaterVolume, innerClearCrossSectionArea, geometry,
        wall, siValue, coordinateInSI_self]
  refine ⟨(wall, geometry), hBridge, ?_⟩
  intro other hOther
  rcases hBridge with
    ⟨hInnerRadius, hOuterRadius, hWettedLength, _hWallNesting,
      hGeometryWall, hGeometryHeight, hGeometryDensity, hGeometrySpecificHeat,
      _hClearArea, _hVolume⟩
  rcases hOther with
    ⟨hOtherInnerRadius, hOtherOuterRadius, hOtherWettedLength,
      _hOtherWallNesting, hOtherGeometryWall, hOtherGeometryHeight,
      hOtherGeometryDensity, hOtherGeometrySpecificHeat,
      _hOtherClearArea, _hOtherVolume⟩
  have hInnerCoordinate :
      siValue other.1.innerRadius = siValue wall.innerRadius :=
    hOtherInnerRadius.trans hInnerRadius.symm
  have hWall : other.1 = wall := by
    apply CylindricalWall.ext
    · apply
        (coordinateInSI_eq_iff SIUnitChoices.SI other.1.innerRadius
          wall.innerRadius).mp
      exact hInnerCoordinate
    · apply
        (coordinateInSI_eq_iff SIUnitChoices.SI other.1.outerRadius
          wall.outerRadius).mp
      calc
        siValue other.1.outerRadius =
            siValue other.1.innerRadius +
              siValue apparatus.measurements.innerCylinderWallThickness :=
          hOtherOuterRadius
        _ = siValue wall.innerRadius +
              siValue apparatus.measurements.innerCylinderWallThickness := by
          rw [hInnerCoordinate]
        _ = siValue wall.outerRadius := hOuterRadius.symm
    · apply
        (coordinateInSI_eq_iff SIUnitChoices.SI other.1.wettedLength
          wall.wettedLength).mp
      exact hOtherWettedLength.trans hWettedLength.symm
  have hGeometry : other.2 = geometry := by
    apply InnerWaterGeometry.ext
    · exact hOtherGeometryWall.trans (hWall.trans hGeometryWall.symm)
    · exact hOtherGeometryHeight.trans hGeometryHeight.symm
    · exact hOtherGeometryDensity.trans hGeometryDensity.symm
    · exact hOtherGeometrySpecificHeat.trans hGeometrySpecificHeat.symm
  exact Prod.ext hWall hGeometry

/-- Index-sensitive identity with one entry of a prepared named run. -/
def Figure17PartCObservationProvenance {q : ℕ}
    (run : Figure17PartCRadialRun q) (index : Fin q)
    (sample : TemperatureSample) : Prop :=
  PreparedFigure17PartCRadialRun run ∧ sample = run.externalRecord index

/-- A nonempty, ordered, multiplicity-preserving series from one named run. -/
abbrev RadialObservationSeries (q : ℕ) :=
  ObservationSeries q (Figure17PartCRadialRun q) TemperatureSample
    (fun run index sample ↦ Figure17PartCObservationProvenance run index sample)

/-! ## Exact adjacent observations -/

/-- Strictly increasing adjacent elapsed times and at least one interval. -/
def ValidRadialSuccessiveTimeGaps {m : ℕ}
    (observations : RadialObservationSeries (m + 1)) : Prop :=
  ValidSuccessiveTimeGaps observations (fun sample ↦ siValue sample.elapsedTime)

/-- Average outer-minus-inner temperature difference over one adjacent interval. -/
def adjacentAverageTemperatureDifference {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (_valid : ValidRadialSuccessiveTimeGaps observations) (index : Fin m) :
    TemperatureDifference :=
  ⟨((siValue (observations.samples (Fin.castSucc index)).outerTemperature -
          siValue (observations.samples (Fin.castSucc index)).innerTemperature) +
      (siValue (observations.samples (Fin.succ index)).outerTemperature -
          siValue (observations.samples (Fin.succ index)).innerTemperature)) / 2⟩

/-- Inner-temperature forward difference over one adjacent interval. -/
def adjacentInnerTemperatureRate {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (_valid : ValidRadialSuccessiveTimeGaps observations) (index : Fin m) :
    TemperatureRate :=
  ⟨(siValue (observations.samples (Fin.succ index)).innerTemperature -
        siValue (observations.samples (Fin.castSucc index)).innerTemperature) /
      (siValue (observations.samples (Fin.succ index)).elapsedTime -
        siValue (observations.samples (Fin.castSucc index)).elapsedTime)⟩

/-- Adjacent heat rate obtained by retaining the full positive water capacity. -/
def adjacentHeatRateObservation {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (geometry : InnerWaterGeometry) (index : Fin m) : HeatRate :=
  ⟨siValue (innerWaterHeatCapacity geometry) *
    siValue (adjacentInnerTemperatureRate observations valid index)⟩

/-- Ordered coherent-SI predictor/heat-rate points from common adjacent intervals. -/
def heatRateFitGraph {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (geometry : InnerWaterGeometry) : Fin m → ℝ × ℝ :=
  fun index ↦
    (siValue (adjacentAverageTemperatureDifference observations valid index),
      siValue (adjacentHeatRateObservation observations valid geometry index))

/-- The nonempty affine data containing every point of the exact adjacent graph. -/
def heatRateAffineData {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (geometry : InnerWaterGeometry) : AffineData m :=
  AffineData.ofGraph valid.1 (heatRateFitGraph observations valid geometry)

/-- Fixed prepared provenance, gaps, and source geometry determine exactly the
displayed affine coordinate families. -/
theorem existsUnique_heatRateAffineData {m : ℕ}
    (run : Figure17PartCRadialRun (m + 1))
    (observations : RadialObservationSeries (m + 1))
    (hPrepared : PreparedFigure17PartCRadialRun run)
    (hRun : observations.run = run)
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (geometry : InnerWaterGeometry) :
    ∃! data : AffineData m,
      (∀ index,
        data.predictor index = (heatRateFitGraph observations valid geometry index).1) ∧
      ∀ index,
        data.response index = (heatRateFitGraph observations valid geometry index).2 := by
  let canonical := heatRateAffineData observations valid geometry
  refine ⟨canonical, ?_, ?_⟩
  · constructor <;> intro index <;>
      rfl
  · intro data hData
    apply AffineData.ext_coordinates
    · intro index
      exact hData.1 index
    · intro index
      exact hData.2 index

/-- Exact discrete coupling of adjacent observations to a nonzero resistance. -/
def SatisfiesAdjacentResistanceLaw {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (geometry : InnerWaterGeometry) (resistance : ThermalResistance) : Prop :=
  siValue resistance ≠ 0 ∧
    ∀ index,
      siValue (adjacentHeatRateObservation observations valid geometry index) =
        siValue (adjacentAverageTemperatureDifference observations valid index) /
          siValue resistance

/-! ## Supplied coefficient-fit protocols -/

/-- A data-only protocol with an explicit objective and finite equation family. -/
structure HeatRateFitProtocol (m : ℕ) where
  equationCount : AffineData m → ℕ
  objective : AffineData m → ℝ → ℝ → ℝ
  equationResidual :
    (data : AffineData m) → Fin (equationCount data) → ℝ → ℝ → ℝ

/-- The coefficients satisfy every declared equation and globally minimize the
declared objective on exactly the supplied data. -/
def ProtocolAccepts {m : ℕ} (protocol : HeatRateFitProtocol m)
    (data : AffineData m) (intercept slope : ℝ) : Prop :=
  (∀ equation,
    protocol.equationResidual data equation intercept slope = 0) ∧
    ∀ intercept' slope',
      protocol.objective data intercept slope ≤
        protocol.objective data intercept' slope'

/-- The supplied protocol accepts exactly one coefficient pair on the data. -/
def WellPosedHeatRateFitProtocol {m : ℕ} (protocol : HeatRateFitProtocol m)
    (data : AffineData m) : Prop :=
  ∃! pair : ℝ × ℝ, ProtocolAccepts protocol data pair.1 pair.2

/-- Accepted, unique protocol coefficients with a physically positive slope. -/
def PositiveSlopeProtocolFitCertificate {m : ℕ}
    (protocol : HeatRateFitProtocol m) (data : AffineData m)
    (intercept slope : ℝ) : Prop :=
  WellPosedHeatRateFitProtocol protocol data ∧
    ProtocolAccepts protocol data intercept slope ∧
    0 < slope ∧ slope ≠ 0

/-- An exactly affine graph is accepted with its exact coefficients. -/
def ExactAffineFaithful {m : ℕ} (protocol : HeatRateFitProtocol m)
    (data : AffineData m) : Prop :=
  ∀ intercept slope,
    (∀ index, data.response index = intercept + slope * data.predictor index) →
      ProtocolAccepts protocol data intercept slope

/-! ## Physical adapter for fit coefficients -/

/-- A positive resistance whose coherent-SI coordinate is reciprocal to the
unique accepted positive slope. -/
def ResistanceCharacterization {m : ℕ} (data : AffineData m)
    (protocol : HeatRateFitProtocol m) (resistance : ThermalResistance) : Prop :=
  0 < siValue resistance ∧
    siValue resistance ≠ 0 ∧
    ∃ intercept slope,
      PositiveSlopeProtocolFitCertificate protocol data intercept slope ∧
        slope * siValue resistance = 1

/-- An exact adjacent law is compatible with any well-posed exact-affine
faithful protocol on the canonical data. -/
lemma adjacentLaw_implies_resistanceCharacterization {m : ℕ}
    (observations : RadialObservationSeries (m + 1))
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (geometry : InnerWaterGeometry) (protocol : HeatRateFitProtocol m)
    (resistance : ThermalResistance)
    (hResistancePos : 0 < siValue resistance)
    (hAdjacentLaw :
      SatisfiesAdjacentResistanceLaw observations valid geometry resistance)
    (hNondegenerate :
      NondegeneratePredictor (heatRateAffineData observations valid geometry))
    (hWellPosed :
      WellPosedHeatRateFitProtocol protocol
        (heatRateAffineData observations valid geometry))
    (hFaithful :
      ExactAffineFaithful protocol
        (heatRateAffineData observations valid geometry)) :
    ResistanceCharacterization (heatRateAffineData observations valid geometry)
      protocol resistance := by
  rcases hAdjacentLaw with ⟨hResistanceNe, hAdjacentLaw⟩
  let data := heatRateAffineData observations valid geometry
  have hExactAffine :
      ∀ index, data.response index =
        0 + (1 / siValue resistance) * data.predictor index := by
    intro index
    simpa only [data, heatRateAffineData, AffineData.ofGraph,
      heatRateFitGraph, one_div, zero_add, div_eq_mul_inv, one_mul, mul_comm] using
      hAdjacentLaw index
  have hAccepted :
      ProtocolAccepts protocol data 0 (1 / siValue resistance) :=
    hFaithful 0 (1 / siValue resistance) hExactAffine
  have hSlopePos : 0 < 1 / siValue resistance := one_div_pos.mpr hResistancePos
  have hSlopeNe : 1 / siValue resistance ≠ 0 := ne_of_gt hSlopePos
  refine ⟨hResistancePos, hResistanceNe, 0, 1 / siValue resistance, ?_, ?_⟩
  · exact ⟨hWellPosed, hAccepted, hSlopePos, hSlopeNe⟩
  · exact one_div_mul_cancel hResistanceNe

/-- A certified positive fit slope determines exactly one thermal resistance. -/
theorem existsUnique_resistanceCharacterization {m : ℕ}
    (data : AffineData m) (protocol : HeatRateFitProtocol m)
    (hCertificate :
      ∃ intercept slope,
        PositiveSlopeProtocolFitCertificate protocol data intercept slope) :
    ∃! resistance : ThermalResistance,
      ResistanceCharacterization data protocol resistance := by
  rcases hCertificate with ⟨intercept₀, slope₀, hCertificate₀⟩
  rcases hCertificate₀ with
    ⟨hWellPosed₀, hAccepted₀, hSlopePos₀, hSlopeNe₀⟩
  let resistance : ThermalResistance := ⟨1 / slope₀⟩
  have hResistancePos : 0 < siValue resistance := by
    simpa only [resistance, siValue, coordinateInSI_self] using
      one_div_pos.mpr hSlopePos₀
  have hResistanceNe : siValue resistance ≠ 0 := ne_of_gt hResistancePos
  have hProduct : slope₀ * siValue resistance = 1 := by
    simp only [resistance, siValue, coordinateInSI_self, one_div]
    exact mul_inv_cancel₀ hSlopeNe₀
  have hCharacterization :
      ResistanceCharacterization data protocol resistance := by
    exact
      ⟨hResistancePos, hResistanceNe, intercept₀, slope₀,
        ⟨hWellPosed₀, hAccepted₀, hSlopePos₀, hSlopeNe₀⟩,
        hProduct⟩
  refine ⟨resistance, hCharacterization, ?_⟩
  intro other hOther
  rcases hOther with
    ⟨_hOtherPos, _hOtherNe, intercept, slope, hOtherCertificate,
      hOtherProduct⟩
  have hOtherAccepted := hOtherCertificate.2.1
  rcases hWellPosed₀ with ⟨acceptedPair, hAcceptedPair, hUniqueAccepted⟩
  have hCoefficientPair :
      (intercept, slope) = (intercept₀, slope₀) :=
    (hUniqueAccepted (intercept, slope) hOtherAccepted).trans
      (hUniqueAccepted (intercept₀, slope₀) hAccepted₀).symm
  have hSlope : slope = slope₀ := congrArg Prod.snd hCoefficientPair
  apply
    (coordinateInSI_eq_iff SIUnitChoices.SI other resistance).mp
  change siValue other = siValue resistance
  apply mul_left_cancel₀ hSlopeNe₀
  calc
    slope₀ * siValue other = slope * siValue other := by rw [hSlope]
    _ = 1 := hOtherProduct
    _ = slope₀ * siValue resistance := hProduct.symm

/-- Coupled fit-to-resistance and radial-resistance-to-conductivity laws. -/
def ProtocolResistanceConductivityCharacterization {m : ℕ}
    (wall : CylindricalWall) (data : AffineData m)
    (protocol : HeatRateFitProtocol m) (resistance : ThermalResistance)
    (conductivity : ThermalConductivity) : Prop :=
  ResistanceCharacterization data protocol resistance ∧
    ConductivityCharacterization wall resistance conductivity

/-- A certified supplied fit and fixed wall determine one resistance/conductivity pair. -/
theorem existsUnique_protocolResistanceConductivityCharacterization {m : ℕ}
    (wall : CylindricalWall) (data : AffineData m)
    (protocol : HeatRateFitProtocol m)
    (hCertificate :
      ∃ intercept slope,
        PositiveSlopeProtocolFitCertificate protocol data intercept slope) :
    ∃! pair : ThermalResistance × ThermalConductivity,
      ProtocolResistanceConductivityCharacterization wall data protocol
        pair.1 pair.2 := by
  rcases existsUnique_resistanceCharacterization data protocol hCertificate with
    ⟨resistance, hResistance, hResistanceUnique⟩
  rcases existsUnique_conductivityCharacterization wall resistance hResistance.1 with
    ⟨conductivity, hConductivity, hConductivityUnique⟩
  refine ⟨(resistance, conductivity), ⟨hResistance, hConductivity⟩, ?_⟩
  rintro ⟨otherResistance, otherConductivity⟩ hOther
  have hOtherResistance : otherResistance = resistance :=
    hResistanceUnique otherResistance hOther.1
  subst otherResistance
  have hOtherConductivity : otherConductivity = conductivity :=
    hConductivityUnique otherConductivity hOther.2
  subst otherConductivity
  rfl

/-! ## Joint prepared-run characterization -/

/-- Prepared provenance, valid adjacent construction, the unique Figure 17
geometry bridge, and the two physical governing characterizations. -/
def ResistanceConductivityCharacterization {m : ℕ}
    (run : Figure17PartCRadialRun (m + 1))
    (observations : RadialObservationSeries (m + 1))
    (protocol : HeatRateFitProtocol m) (resistance : ThermalResistance)
    (conductivity : ThermalConductivity) : Prop :=
  PreparedFigure17PartCRadialRun run ∧
    observations.run = run ∧
    ∃ valid : ValidRadialSuccessiveTimeGaps observations,
      ∃ wall : CylindricalWall, ∃ geometry : InnerWaterGeometry,
        Figure17PartCGeometryBridge run.apparatus wall geometry ∧
          ProtocolResistanceConductivityCharacterization wall
            (heatRateAffineData observations valid geometry) protocol
            resistance conductivity

/-- A prepared named run, exact adjacent data, and certified protocol determine
exactly one resistance/conductivity pair. -/
theorem existsUnique_resistanceConductivityCharacterization {m : ℕ}
    (run : Figure17PartCRadialRun (m + 1))
    (observations : RadialObservationSeries (m + 1))
    (protocol : HeatRateFitProtocol m)
    (hPrepared : PreparedFigure17PartCRadialRun run)
    (hRun : observations.run = run)
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (wall : CylindricalWall) (geometry : InnerWaterGeometry)
    (hBridge : Figure17PartCGeometryBridge run.apparatus wall geometry)
    (hCertificate :
      ∃ intercept slope,
        PositiveSlopeProtocolFitCertificate protocol
          (heatRateAffineData observations valid geometry) intercept slope) :
    ∃! pair : ThermalResistance × ThermalConductivity,
      ResistanceConductivityCharacterization run observations protocol
        pair.1 pair.2 := by
  rcases
      existsUnique_protocolResistanceConductivityCharacterization wall
        (heatRateAffineData observations valid geometry) protocol hCertificate with
    ⟨pair, hPair, hPairUnique⟩
  refine ⟨pair, ?_, ?_⟩
  · exact ⟨hPrepared, hRun, valid, wall, geometry, hBridge, hPair⟩
  · intro other hOther
    rcases hOther with
      ⟨_hOtherPrepared, _hOtherRun, otherValid, otherWall, otherGeometry,
        hOtherBridge, hOtherPair⟩
    have hPreparedApparatus :
        PreparedFigure17PartCApparatus run.apparatus run.procedure := hPrepared
    rcases
        existsUnique_figure17PartCGeometryBridge run.apparatus run.procedure
          hPreparedApparatus with
      ⟨bridgePair, hBridgePair, hBridgeUnique⟩
    have hBridgeEquality :
        (otherWall, otherGeometry) = (wall, geometry) :=
      (hBridgeUnique (otherWall, otherGeometry) hOtherBridge).trans
        (hBridgeUnique (wall, geometry) hBridge).symm
    have hWallEquality : otherWall = wall :=
      congrArg Prod.fst hBridgeEquality
    have hGeometryEquality : otherGeometry = geometry :=
      congrArg Prod.snd hBridgeEquality
    subst otherWall
    subst otherGeometry
    have hValidEquality : otherValid = valid := Subsingleton.elim _ _
    subst otherValid
    exact hPairUnique other hOtherPair

/-! ## Explicit ordinary-least-squares specialization -/

/-- The two normal equations together with the residual-sum-of-squares objective. -/
def ordinaryLeastSquaresHeatRateProtocol (m : ℕ) : HeatRateFitProtocol m where
  equationCount := fun _data ↦ 2
  objective := fun data intercept slope ↦
    residualSumSquares data intercept slope
  equationResidual := fun data equation intercept slope ↦
    if equation = (0 : Fin 2) then
      ∑ index : Fin m, residual data intercept slope index
    else
      ∑ index : Fin m,
        data.predictor index * residual data intercept slope index

/-- On nondegenerate data, acceptance by the explicit OLS protocol is exactly
the affine normal-equation fit relation. -/
theorem olsProtocolAccepts_iff_isAffineFit {m : ℕ} (data : AffineData m)
    (hNondegenerate : NondegeneratePredictor data) (intercept slope : ℝ) :
    ProtocolAccepts (ordinaryLeastSquaresHeatRateProtocol m) data intercept slope ↔
      IsAffineFit data intercept slope := by
  constructor
  · rintro ⟨hEquations, _hMinimal⟩
    change AffineNormalEquations data intercept slope
    constructor
    · simpa [ordinaryLeastSquaresHeatRateProtocol] using
        hEquations (0 : Fin 2)
    · simpa [ordinaryLeastSquaresHeatRateProtocol] using
        hEquations (1 : Fin 2)
  · intro hFit
    refine ⟨?_, ?_⟩
    · intro equation
      change Fin 2 at equation
      have hCases : equation = (0 : Fin 2) ∨ equation = (1 : Fin 2) := by
        omega
      rcases hCases with hEquation | hEquation <;>
        subst equation
      · simpa [ordinaryLeastSquaresHeatRateProtocol] using hFit.1
      · simpa [ordinaryLeastSquaresHeatRateProtocol] using hFit.2
    · exact
        (isAffineFit_iff_isLeastResidual data hNondegenerate intercept slope).1
          hFit

/-- The explicit OLS heat-rate protocol is well posed on nondegenerate data. -/
theorem olsProtocol_wellPosed {m : ℕ} (data : AffineData m)
    (hNondegenerate : NondegeneratePredictor data) :
    WellPosedHeatRateFitProtocol (ordinaryLeastSquaresHeatRateProtocol m) data := by
  rcases existsUnique_isAffineFit data hNondegenerate with
    ⟨pair, hPair, hUnique⟩
  refine ⟨pair, ?_, ?_⟩
  · exact
      (olsProtocolAccepts_iff_isAffineFit data hNondegenerate pair.1 pair.2).2
        hPair
  · intro other hOther
    exact hUnique other
      ((olsProtocolAccepts_iff_isAffineFit data hNondegenerate
        other.1 other.2).1 hOther)

/-- Explicit OLS selection with a positive fitted slope gives unique physical
resistance and conductivity unknowns. -/
theorem existsUnique_resistanceConductivityCharacterization_ols {m : ℕ}
    (run : Figure17PartCRadialRun (m + 1))
    (observations : RadialObservationSeries (m + 1))
    (hPrepared : PreparedFigure17PartCRadialRun run)
    (hRun : observations.run = run)
    (valid : ValidRadialSuccessiveTimeGaps observations)
    (wall : CylindricalWall) (geometry : InnerWaterGeometry)
    (hBridge : Figure17PartCGeometryBridge run.apparatus wall geometry)
    (hNondegenerate :
      NondegeneratePredictor (heatRateAffineData observations valid geometry))
    (hPositiveFit :
      ∃ intercept slope,
        IsAffineFit (heatRateAffineData observations valid geometry) intercept slope ∧
          0 < slope ∧ slope ≠ 0) :
    ∃! pair : ThermalResistance × ThermalConductivity,
      ResistanceConductivityCharacterization run observations
        (ordinaryLeastSquaresHeatRateProtocol m) pair.1 pair.2 := by
  rcases hPositiveFit with
    ⟨intercept, slope, hFit, hSlopePos, hSlopeNe⟩
  have hAccepted :
      ProtocolAccepts (ordinaryLeastSquaresHeatRateProtocol m)
        (heatRateAffineData observations valid geometry) intercept slope :=
    (olsProtocolAccepts_iff_isAffineFit
      (heatRateAffineData observations valid geometry) hNondegenerate
      intercept slope).2 hFit
  have hWellPosed :
      WellPosedHeatRateFitProtocol (ordinaryLeastSquaresHeatRateProtocol m)
        (heatRateAffineData observations valid geometry) :=
    olsProtocol_wellPosed
      (heatRateAffineData observations valid geometry) hNondegenerate
  apply
    existsUnique_resistanceConductivityCharacterization run observations
      (ordinaryLeastSquaresHeatRateProtocol m) hPrepared hRun valid wall geometry
      hBridge
  exact
    ⟨intercept, slope,
      ⟨hWellPosed, hAccepted, hSlopePos, hSlopeNe⟩⟩

end RadialHeatFlow

end

end Ipho2026Gpt56solBlind.Shared
