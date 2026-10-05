import Ipho2026Gpt56solBlind.Shared.RefrigeratorCycle

/-!
# IPhO 2026 Problem 3, part C.3

Answer-blind specification of one refrigeration cycle applied to the printed
potassium-chromate and liquid-helium data.  The requested final temperature is
characterized by the governing one-cycle energy update; no derived numerical
temperature is built into the statement.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_3_C_3

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics
open Ipho2026Gpt56solBlind.Shared.RefrigeratorCycle

/-! ## Dimensioned numerical source data -/

/-- Specific heat capacity has energy per mass per temperature dimension. -/
def specificHeatCapacityDimension : Dimension ISQDimensionBase :=
  energyDimension * massDimension⁻¹ * temperatureDimension⁻¹

/-- Dimensioned specific heat capacity. -/
abbrev SpecificHeatCapacity := Quantity specificHeatCapacityDimension

/-- Density times volume times specific heat capacity has heat-capacity dimension. -/
lemma massDensity_mul_volume_mul_specificHeatCapacity_dimension :
    massDensityDimension * volumeDimension * specificHeatCapacityDimension =
      heatCapacityDimension := by
  change
    (massDimension * volumeDimension⁻¹) * volumeDimension *
        (energyDimension * massDimension⁻¹ * temperatureDimension⁻¹) =
      energyDimension * temperatureDimension⁻¹
  calc
    (massDimension * volumeDimension⁻¹) * volumeDimension *
          (energyDimension * massDimension⁻¹ * temperatureDimension⁻¹) =
        (volumeDimension⁻¹ * volumeDimension) *
          (massDimension * massDimension⁻¹) *
            (energyDimension * temperatureDimension⁻¹) := by
      ac_rfl
    _ = 1 * 1 * (energyDimension * temperatureDimension⁻¹) := by
      rw [inv_mul_cancel, mul_inv_cancel]
    _ = energyDimension * temperatureDimension⁻¹ := by
      rw [one_mul, one_mul]

/-- The potassium-chromate quantities printed in the question, before
positivity and numerical matching are imposed. -/
structure PotassiumChromateSourceData where
  amount : AmountOfSubstance
  curieParameter : CurieParameter
  massDensity : MassDensity
  molarMass : MolarMass
  field1 : MagneticFieldStrength
  field2 : MagneticFieldStrength
  field3 : MagneticFieldStrength
  field4 : MagneticFieldStrength

/-- The liquid-helium quantities printed in the question, before positivity
and numerical matching are imposed. -/
structure LiquidHeliumSourceData where
  volume : Volume
  initialTemperature : Temperature
  specificHeatCapacity : SpecificHeatCapacity
  massDensity : MassDensity

/-- One fixed source/problem context.  Its permeability is a common apparatus
constant, not an additional printed sample measurement. -/
structure OneCycleSourceData where
  unitSystem : SIUnitChoices
  vacuumPermeability : Permeability
  potassiumChromate : PotassiumChromateSourceData
  liquidHelium : LiquidHeliumSourceData

namespace OneCycleSourceData

/-- Exact coherent-SI transcription of every numerical datum printed in C.3.
The litre is converted to `10⁻³ m³`; no coordinate is prescribed for
vacuum permeability. -/
def MatchesStatement (S : OneCycleSourceData) : Prop :=
  let P := S.potassiumChromate
  let L := S.liquidHelium
  coordinateInSI S.unitSystem P.amount = 2.0 ∧
  coordinateInSI S.unitSystem P.curieParameter = (187 : ℝ) / 100000000 ∧
  coordinateInSI S.unitSystem P.massDensity = 2730 ∧
  coordinateInSI S.unitSystem P.molarMass = (19 : ℝ) / 100 ∧
  coordinateInSI S.unitSystem P.field1 = 411624 ∧
  coordinateInSI S.unitSystem P.field2 = 311306 ∧
  coordinateInSI S.unitSystem P.field3 = 204618 ∧
  coordinateInSI S.unitSystem P.field4 = 240446 ∧
  coordinateInSI S.unitSystem L.volume = (1 : ℝ) / 1000 ∧
  coordinateInSI S.unitSystem L.initialTemperature = 1.00 ∧
  coordinateInSI S.unitSystem L.specificHeatCapacity = 100 ∧
  coordinateInSI S.unitSystem L.massDensity = 130

/-- Positivity of the common permeability and all printed source quantities. -/
def IsPhysical (S : OneCycleSourceData) : Prop :=
  let P := S.potassiumChromate
  let L := S.liquidHelium
  0 < coherentCoordinate S.unitSystem S.vacuumPermeability ∧
  0 < coherentCoordinate S.unitSystem P.amount ∧
  0 < coherentCoordinate S.unitSystem P.curieParameter ∧
  0 < coherentCoordinate S.unitSystem P.massDensity ∧
  0 < coherentCoordinate S.unitSystem P.molarMass ∧
  0 < coherentCoordinate S.unitSystem P.field1 ∧
  0 < coherentCoordinate S.unitSystem P.field2 ∧
  0 < coherentCoordinate S.unitSystem P.field3 ∧
  0 < coherentCoordinate S.unitSystem P.field4 ∧
  0 < coherentCoordinate S.unitSystem L.volume ∧
  0 < coherentCoordinate S.unitSystem L.initialTemperature ∧
  0 < coherentCoordinate S.unitSystem L.specificHeatCapacity ∧
  0 < coherentCoordinate S.unitSystem L.massDensity

end OneCycleSourceData

/-! ## A source-matched cycle and constant-capacity helium body -/

/-- A possible apparatus and composed cycle realizing one source context.
The lower endpoint is auxiliary model-domain data, not the requested answer. -/
structure OneCycleRealization where
  source : OneCycleSourceData
  apparatus : ParamagneticData
  cycle : ComposedFourLegCycle apparatus
  minTemperature : Temperature

namespace OneCycleRealization

/-- Source positivity together with a positive, nondegenerate helium
temperature domain.  Apparatus and cycle-state physicality are carried by the
composed-cycle structure. -/
def IsPhysical (R : OneCycleRealization) : Prop :=
  R.source.IsPhysical ∧
  0 < coherentCoordinate R.source.unitSystem R.minTemperature ∧
  coherentCoordinate R.source.unitSystem R.minTemperature <
    coherentCoordinate R.source.unitSystem
      R.source.liquidHelium.initialTemperature

/-- The apparatus and every source quantity use the same unit choice. -/
def IsUnitCompatible (R : OneCycleRealization) : Prop :=
  R.apparatus.torus.unitSystem = R.source.unitSystem

/-- Governing identification of the apparatus and directed cycle with the
fixed source record. -/
def IsSourceMatched (R : OneCycleRealization) : Prop :=
  let S := R.source
  let P := S.potassiumChromate
  let L := S.liquidHelium
  R.apparatus.material.vacuumPermeability = S.vacuumPermeability ∧
  R.apparatus.material.amount = P.amount ∧
  R.apparatus.material.curieParameter = P.curieParameter ∧
  coherentCoordinate S.unitSystem R.apparatus.torus.volume *
      coherentCoordinate S.unitSystem P.massDensity =
    coherentCoordinate S.unitSystem P.amount *
      coherentCoordinate S.unitSystem P.molarMass ∧
  R.cycle.coldTemperature = L.initialTemperature ∧
  (R.cycle.state .v0).fieldStrength = P.field1 ∧
  (R.cycle.state .v1).fieldStrength = P.field2 ∧
  (R.cycle.state .v2).fieldStrength = P.field3 ∧
  (R.cycle.state .v3).fieldStrength = P.field4

end OneCycleRealization

/-- The printed field ordering and the reversible-cycle laws identify the
source legs: `e1` is cold-isothermal, `e3` hot-isothermal, and the other two
legs are adiabatic. -/
lemma sourceMatchedCycle_roles (R : OneCycleRealization)
    (hmatch : R.source.MatchesStatement)
    (hphysical : R.IsPhysical)
    (hunit : R.IsUnitCompatible)
    (hsource : R.IsSourceMatched) :
    IsColdIsothermalLeg R.cycle .e1 ∧
      IsHotIsothermalLeg R.cycle .e3 ∧
      IsAdiabaticCycleLeg R.cycle .e0 ∧
      IsAdiabaticCycleLeg R.cycle .e2 := by
  classical
  have hunitEq :
      R.apparatus.torus.unitSystem = R.source.unitSystem := hunit
  rcases hmatch with
    ⟨_, _, _, _, hfield1Coordinate, hfield2Coordinate,
      hfield3Coordinate, hfield4Coordinate, _, _, _, _⟩
  rcases hsource with
    ⟨_, _, _, _, _, hfield1, hfield2, hfield3, hfield4⟩
  have hv0 :
      coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.state .v0).fieldStrength = 411624 := by
    simpa only [coherentCoordinate, hfield1, hunitEq] using hfield1Coordinate
  have hv1 :
      coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.state .v1).fieldStrength = 311306 := by
    simpa only [coherentCoordinate, hfield2, hunitEq] using hfield2Coordinate
  have hv2 :
      coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.state .v2).fieldStrength = 204618 := by
    simpa only [coherentCoordinate, hfield3, hunitEq] using hfield3Coordinate
  have hv3 :
      coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.state .v3).fieldStrength = 240446 := by
    simpa only [coherentCoordinate, hfield4, hunitEq] using hfield4Coordinate
  have isothermalLegHeat (e : CycleLeg)
      (hiso : IsColdIsothermalLeg R.cycle e) :
      coherentCoordinate R.apparatus.torus.unitSystem (R.cycle.leg e).heat =
        (coherentCoordinate R.apparatus.torus.unitSystem
              R.apparatus.material.vacuumPermeability *
            coherentCoordinate R.apparatus.torus.unitSystem
              R.apparatus.material.amount *
            coherentCoordinate R.apparatus.torus.unitSystem
              R.apparatus.material.curieParameter /
            (2 * coherentCoordinate R.apparatus.torus.unitSystem
              R.cycle.coldTemperature)) *
          (coherentCoordinate R.apparatus.torus.unitSystem
                (R.cycle.state e.startVertex).fieldStrength ^ 2 -
            coherentCoordinate R.apparatus.torus.unitSystem
                (R.cycle.state e.finishVertex).fieldStrength ^ 2) := by
    let p := (R.cycle.leg e).process
    let field : ℝ → ℝ := fun t ↦
      coherentCoordinate R.apparatus.torus.unitSystem
        (p.state t).fieldStrength
    let coefficient : ℝ :=
      coherentCoordinate R.apparatus.torus.unitSystem
            R.apparatus.material.vacuumPermeability *
          coherentCoordinate R.apparatus.torus.unitSystem
            R.apparatus.material.amount *
          coherentCoordinate R.apparatus.torus.unitSystem
            R.apparatus.material.curieParameter /
          coherentCoordinate R.apparatus.torus.unitSystem
            R.cycle.coldTemperature
    have hab : p.a < p.b := (R.cycle.leg e).isReversible.1.2.1
    have hstart := R.cycle.legStarts e
    have hfinish := R.cycle.legFinishes e
    change p.state p.a = R.cycle.state e.startVertex at hstart
    change p.state p.b = R.cycle.state e.finishVertex at hfinish
    have htemperatureStart := hiso.2 p.a ⟨le_rfl, hab.le⟩
    have htemperatureFinish := hiso.2 p.b ⟨hab.le, le_rfl⟩
    rw [hstart] at htemperatureStart
    rw [hfinish] at htemperatureFinish
    have hleg : IsReversibleIsothermalEndpointLeg R.apparatus
        R.cycle.coldTemperature
        (R.cycle.state e.startVertex).fieldStrength
        (R.cycle.state e.finishVertex).fieldStrength p := by
      refine ⟨R.cycle.temperatureOrder.1,
        (R.cycle.statePhysical e.startVertex).2.1,
        (R.cycle.statePhysical e.finishVertex).2.1,
        (R.cycle.leg e).isReversible, hiso, ?_⟩
      unfold HasTemperatureFieldEndpoints
      rw [hstart, hfinish]
      exact ⟨htemperatureStart, rfl, htemperatureFinish, rfl⟩
    have hnet : HasNetHeatEntering R.apparatus p (R.cycle.leg e).heat := by
      unfold HasNetHeatEntering ReversibleLeg.heat
      rw [coherentCoordinate_quantityFromCoherentCoordinate]
    have hcharacterization :=
      ((isothermalHeat_characterization R.apparatus
        R.cycle.coldTemperature
        (R.cycle.state e.startVertex).fieldStrength
        (R.cycle.state e.finishVertex).fieldStrength p hleg).2
          (R.cycle.leg e).heat).mp hnet
    change
      coherentCoordinate R.apparatus.torus.unitSystem (R.cycle.leg e).heat =
        ∫ t in p.a..p.b,
          -coefficient * field t * deriv field t at hcharacterization
    rcases (R.cycle.leg e).isReversible.1 with
      ⟨_, _, ⟨neighborhood, hopen, hIcc, _, hfieldSmooth, _, _, _⟩,
        _, _, _, _, _⟩
    have hfieldSmoothIcc :
        ContDiffOn ℝ 1 field (Set.Icc p.a p.b) :=
      hfieldSmooth.mono hIcc
    have hsquareSmooth :
        ContDiffOn ℝ 1 (fun t ↦ field t ^ 2 / 2) (Set.Icc p.a p.b) :=
      (hfieldSmoothIcc.pow 2).div_const 2
    have hderivative (t : ℝ) (ht : t ∈ Set.Icc p.a p.b) :
        deriv (fun x ↦ field x ^ 2 / 2) t =
          field t * deriv field t := by
      have hfieldDifferentiable : DifferentiableAt ℝ field t :=
        (hfieldSmooth.differentiableOn_one t (hIcc ht)).differentiableAt
          (hopen.mem_nhds (hIcc ht))
      have hderiv :=
        ((hfieldDifferentiable.hasDerivAt.pow 2).div_const 2).deriv
      calc
        deriv (fun x ↦ field x ^ 2 / 2) t =
            2 * field t * deriv field t / 2 := by
          simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
            using hderiv
        _ = field t * deriv field t := by ring
    have hintegral :
        (∫ t in p.a..p.b, field t * deriv field t) =
          (field p.b ^ 2 - field p.a ^ 2) / 2 := by
      calc
        (∫ t in p.a..p.b, field t * deriv field t) =
            ∫ t in p.a..p.b, deriv (fun x ↦ field x ^ 2 / 2) t := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hab.le] at ht
          exact (hderivative t ht).symm
        _ = field p.b ^ 2 / 2 - field p.a ^ 2 / 2 :=
          intervalIntegral.integral_deriv_of_contDiffOn_Icc
            hsquareSmooth hab.le
        _ = (field p.b ^ 2 - field p.a ^ 2) / 2 := by ring
    have hheat :
        coherentCoordinate R.apparatus.torus.unitSystem (R.cycle.leg e).heat =
          -coefficient * ((field p.b ^ 2 - field p.a ^ 2) / 2) := by
      calc
        coherentCoordinate R.apparatus.torus.unitSystem (R.cycle.leg e).heat =
            ∫ t in p.a..p.b,
              -coefficient * field t * deriv field t := hcharacterization
        _ = ∫ t in p.a..p.b,
              (-coefficient) * (field t * deriv field t) := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
        _ = (-coefficient) *
              ∫ t in p.a..p.b, field t * deriv field t :=
          intervalIntegral.integral_const_mul _ _
        _ = -coefficient * ((field p.b ^ 2 - field p.a ^ 2) / 2) := by
          rw [hintegral]
    have hfieldStart :
        field p.a = coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.state e.startVertex).fieldStrength := by
      simp [field, hstart]
    have hfieldFinish :
        field p.b = coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.state e.finishVertex).fieldStrength := by
      simp [field, hfinish]
    rw [hfieldStart, hfieldFinish] at hheat
    dsimp [coefficient] at hheat
    calc
      coherentCoordinate R.apparatus.torus.unitSystem (R.cycle.leg e).heat =
          -(coherentCoordinate R.apparatus.torus.unitSystem
                R.apparatus.material.vacuumPermeability *
              coherentCoordinate R.apparatus.torus.unitSystem
                R.apparatus.material.amount *
              coherentCoordinate R.apparatus.torus.unitSystem
                R.apparatus.material.curieParameter /
              coherentCoordinate R.apparatus.torus.unitSystem
                R.cycle.coldTemperature) *
            ((coherentCoordinate R.apparatus.torus.unitSystem
                    (R.cycle.state e.finishVertex).fieldStrength ^ 2 -
                coherentCoordinate R.apparatus.torus.unitSystem
                    (R.cycle.state e.startVertex).fieldStrength ^ 2) / 2) :=
        hheat
      _ = _ := by ring
  have coldLegFieldDecreases (e : CycleLeg)
      (hcold : IsColdIsothermalLeg R.cycle e) :
      coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.state e.finishVertex).fieldStrength <
        coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.state e.startVertex).fieldStrength := by
    have hheat := isothermalLegHeat e hcold
    have hheatPositive := (transferMagnitudes_pos R.cycle).1
    have hcoldEq' (other : CycleLeg) :
        IsColdIsothermalLeg R.cycle other ↔ other = e := by
      constructor
      · intro hother
        rcases R.cycle.coldLegUnique with ⟨w, hw, hunique⟩
        exact (hunique other hother).trans (hunique e hcold).symm
      · rintro rfl
        exact hcold
    have hcoldFilter' :
        Finset.univ.filter (IsColdIsothermalLeg R.cycle) = {e} := by
      ext other
      simp [hcoldEq' other]
    have hlegHeatPositive :
        0 < coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.leg e).heat := by
      simpa [coldHeatMagnitude, hcoldFilter'] using hheatPositive
    have hmaterial := R.cycle.apparatusPhysical.2
    have hcoefficientPositive :
        0 < coherentCoordinate R.apparatus.torus.unitSystem
              R.apparatus.material.vacuumPermeability *
              coherentCoordinate R.apparatus.torus.unitSystem
                R.apparatus.material.amount *
              coherentCoordinate R.apparatus.torus.unitSystem
                R.apparatus.material.curieParameter /
              (2 * coherentCoordinate R.apparatus.torus.unitSystem
                R.cycle.coldTemperature) :=
      div_pos (mul_pos (mul_pos hmaterial.1 hmaterial.2.1)
        hmaterial.2.2.1) (mul_pos (by norm_num) R.cycle.temperatureOrder.1)
    have hproductPositive :
        0 < (coherentCoordinate R.apparatus.torus.unitSystem
              R.apparatus.material.vacuumPermeability *
              coherentCoordinate R.apparatus.torus.unitSystem
                R.apparatus.material.amount *
              coherentCoordinate R.apparatus.torus.unitSystem
                R.apparatus.material.curieParameter /
              (2 * coherentCoordinate R.apparatus.torus.unitSystem
                R.cycle.coldTemperature)) *
            (coherentCoordinate R.apparatus.torus.unitSystem
                  (R.cycle.state e.startVertex).fieldStrength ^ 2 -
              coherentCoordinate R.apparatus.torus.unitSystem
                  (R.cycle.state e.finishVertex).fieldStrength ^ 2) := by
      rw [← hheat]
      exact hlegHeatPositive
    have hsquares :
        coherentCoordinate R.apparatus.torus.unitSystem
              (R.cycle.state e.finishVertex).fieldStrength ^ 2 <
          coherentCoordinate R.apparatus.torus.unitSystem
              (R.cycle.state e.startVertex).fieldStrength ^ 2 := by
      have hdifference :=
        pos_of_mul_pos_right hproductPositive hcoefficientPositive.le
      linarith
    exact (sq_lt_sq₀
      (R.cycle.statePhysical e.finishVertex).2.1.le
      (R.cycle.statePhysical e.startVertex).2.1.le).mp hsquares
  rcases R.cycle.coldLegUnique with
    ⟨coldLeg, hcold, hcoldUnique⟩
  have hcoldDecreases := coldLegFieldDecreases coldLeg hcold
  have hcoldCases : coldLeg = .e0 ∨ coldLeg = .e1 := by
    cases coldLeg with
    | e0 => exact Or.inl rfl
    | e1 => exact Or.inr rfl
    | e2 =>
        dsimp [CycleLeg.startVertex, CycleLeg.finishVertex] at hcoldDecreases
        rw [hv2, hv3] at hcoldDecreases
        norm_num at hcoldDecreases
    | e3 =>
        dsimp [CycleLeg.startVertex, CycleLeg.finishVertex] at hcoldDecreases
        rw [hv3, hv0] at hcoldDecreases
        norm_num at hcoldDecreases
  have endpointTemperatures (e : CycleLeg) (T : Temperature)
      (hiso : IsIsothermal R.apparatus (R.cycle.leg e).process T) :
      (R.cycle.state e.startVertex).temperature = T ∧
        (R.cycle.state e.finishVertex).temperature = T := by
    have hab : (R.cycle.leg e).process.a < (R.cycle.leg e).process.b :=
      (R.cycle.leg e).isReversible.1.2.1
    have hstart := hiso.2 (R.cycle.leg e).process.a ⟨le_rfl, hab.le⟩
    have hfinish := hiso.2 (R.cycle.leg e).process.b ⟨hab.le, le_rfl⟩
    have hs := R.cycle.legStarts e
    have hf := R.cycle.legFinishes e
    unfold StartsAt at hs
    unfold FinishesAt at hf
    rw [hs] at hstart
    rw [hf] at hfinish
    exact ⟨hstart, hfinish⟩
  have hnotColdE0 : ¬ IsColdIsothermalLeg R.cycle .e0 := by
    intro hcoldE0
    rcases R.cycle.hotLegUnique with ⟨hotLeg, hhot, hhotUnique⟩
    have hinter :=
      (thermalRole_partition R.cycle).2.2.2.2 hotLeg .e0 hhot hcoldE0 |>.1
    have hhotLeg : hotLeg = .e2 := by
      cases hotLeg <;>
        simp [CycleLeg.startVertex, CycleLeg.finishVertex] at hinter ⊢
    subst hotLeg
    have hnotHotE1 : ¬ IsHotIsothermalLeg R.cycle .e1 := by
      intro h
      have heq := (hhotUnique .e1 h).trans (hhotUnique .e2 hhot).symm
      cases heq
    have hnotColdE1 : ¬ IsColdIsothermalLeg R.cycle .e1 := by
      intro h
      rcases R.cycle.coldLegUnique with ⟨w, hw, hunique⟩
      have heq := (hunique .e1 h).trans (hunique .e0 hcoldE0).symm
      cases heq
    have hadiE1 : IsAdiabaticCycleLeg R.cycle .e1 :=
      ((R.cycle.roleExactlyOne .e1).1.resolve_left hnotHotE1).resolve_left
        hnotColdE1
    have hcoldTemperatures := endpointTemperatures .e0
      R.cycle.coldTemperature hcoldE0
    have hhotTemperatures := endpointTemperatures .e2
      R.cycle.hotTemperature hhot
    have hadiEndpoint : IsReversibleAdiabaticEndpointLeg R.apparatus
        R.cycle.coldTemperature (R.cycle.state .v1).fieldStrength
        R.cycle.hotTemperature (R.cycle.state .v2).fieldStrength
        (R.cycle.leg .e1).process := by
      refine ⟨R.cycle.temperatureOrder.1,
        (R.cycle.statePhysical .v1).2.1,
        lt_trans R.cycle.temperatureOrder.1 R.cycle.temperatureOrder.2,
        (R.cycle.statePhysical .v2).2.1,
        (R.cycle.leg .e1).isReversible, hadiE1, ?_⟩
      have hs := R.cycle.legStarts .e1
      have hf := R.cycle.legFinishes .e1
      unfold StartsAt at hs
      unfold FinishesAt at hf
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hs]
        exact hcoldTemperatures.2
      · rw [hs]
        rfl
      · rw [hf]
        exact hhotTemperatures.1
      · rw [hf]
        rfl
    rcases adiabatic_endpoint_relation_of_leg R.apparatus
      R.cycle.coldTemperature (R.cycle.state .v1).fieldStrength
      R.cycle.hotTemperature (R.cycle.state .v2).fieldStrength
      (R.cycle.leg .e1).process hadiEndpoint with
      ⟨hD, _, _, _, _, hrelation⟩
    let Hᵢ := coherentCoordinate R.apparatus.torus.unitSystem
      (R.cycle.state .v1).fieldStrength
    let H_f := coherentCoordinate R.apparatus.torus.unitSystem
      (R.cycle.state .v2).fieldStrength
    have hHᵢPositive : 0 < Hᵢ := (R.cycle.statePhysical .v1).2.1
    have hHfPositive : 0 < H_f := (R.cycle.statePhysical .v2).2.1
    have hHfLt : H_f < Hᵢ := by
      dsimp [Hᵢ, H_f]
      rw [hv1, hv2]
      norm_num
    rcases adiabaticFieldCoefficient_denominator_pos R.apparatus hD with
      ⟨hdenominator, _, hcontinuous, hintegrable⟩
    have hcoefficientPositive (x : ℝ) (hx : 0 < x) :
        0 < adiabaticFieldCoefficient R.apparatus x := by
      unfold adiabaticFieldCoefficient
      exact div_pos
        (mul_pos (mul_pos hD.2.1 hD.2.2.2.1) hx)
        (hdenominator x)
    have hintegralPositive :
        0 < ∫ x in H_f..Hᵢ, adiabaticFieldCoefficient R.apparatus x := by
      apply intervalIntegral.integral_pos hHfLt hcontinuous.continuousOn
      · intro x hx
        exact (hcoefficientPositive x (hHfPositive.trans hx.1)).le
      · exact ⟨H_f, ⟨le_rfl, hHfLt.le⟩,
          hcoefficientPositive H_f hHfPositive⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hintegrable 0 H_f) (hintegrable H_f Hᵢ)
    change adiabaticPotential R.apparatus H_f +
        (∫ x in H_f..Hᵢ, adiabaticFieldCoefficient R.apparatus x) =
      adiabaticPotential R.apparatus Hᵢ at hadd
    have hpotentialLt :
        adiabaticPotential R.apparatus H_f <
          adiabaticPotential R.apparatus Hᵢ := by
      linarith
    have hhotPositive :
        0 < coherentCoordinate R.apparatus.torus.unitSystem
          R.cycle.hotTemperature :=
      lt_trans R.cycle.temperatureOrder.1 R.cycle.temperatureOrder.2
    have hlogLt := Real.strictMonoOn_log R.cycle.temperatureOrder.1
      hhotPositive R.cycle.temperatureOrder.2
    change
      Real.log (coherentCoordinate R.apparatus.torus.unitSystem
          R.cycle.hotTemperature) -
          Real.log (coherentCoordinate R.apparatus.torus.unitSystem
            R.cycle.coldTemperature) =
        adiabaticPotential R.apparatus H_f -
          adiabaticPotential R.apparatus Hᵢ at hrelation
    linarith
  have hcoldE1 : IsColdIsothermalLeg R.cycle .e1 := by
    rcases hcoldCases with hcoldE0 | hcoldE1
    · subst coldLeg
      exact False.elim (hnotColdE0 hcold)
    · subst coldLeg
      exact hcold
  rcases R.cycle.hotLegUnique with ⟨hotLeg, hhot, hhotUnique⟩
  have hinter :=
    (thermalRole_partition R.cycle).2.2.2.2 hotLeg .e1 hhot hcoldE1 |>.1
  have hhotLeg : hotLeg = .e3 := by
    cases hotLeg <;>
      simp [CycleLeg.startVertex, CycleLeg.finishVertex] at hinter ⊢
  subst hotLeg
  have remainingAdiabatic (e : CycleLeg)
      (hneHot : e ≠ .e3) (hneCold : e ≠ .e1) :
      IsAdiabaticCycleLeg R.cycle e := by
    have hnotHot : ¬ IsHotIsothermalLeg R.cycle e := by
      intro he
      exact hneHot ((hhotUnique e he).trans (hhotUnique .e3 hhot).symm)
    have hnotCold : ¬ IsColdIsothermalLeg R.cycle e := by
      intro he
      rcases R.cycle.coldLegUnique with ⟨w, hw, hunique⟩
      exact hneCold ((hunique e he).trans (hunique .e1 hcoldE1).symm)
    exact ((R.cycle.roleExactlyOne e).1.resolve_left hnotHot).resolve_left
      hnotCold
  exact ⟨hcoldE1, hhot,
    remainingAdiabatic .e0 (by decide) (by decide),
    remainingAdiabatic .e2 (by decide) (by decide)⟩

/-- Total constant heat capacity of the helium body, reconstructed from the
coherent coordinate `ρ V c`. -/
def liquidHeliumHeatCapacity (S : OneCycleSourceData) : HeatCapacity :=
  quantityFromCoherentCoordinate S.unitSystem heatCapacityDimension
    (coherentCoordinate S.unitSystem S.liquidHelium.massDensity *
      coherentCoordinate S.unitSystem S.liquidHelium.volume *
      coherentCoordinate S.unitSystem S.liquidHelium.specificHeatCapacity)

/-- Coherent coordinate of the reconstructed total helium heat capacity. -/
lemma liquidHeliumHeatCapacity_coordinate (S : OneCycleSourceData) :
    coherentCoordinate S.unitSystem (liquidHeliumHeatCapacity S) =
      coherentCoordinate S.unitSystem S.liquidHelium.massDensity *
      coherentCoordinate S.unitSystem S.liquidHelium.volume *
        coherentCoordinate S.unitSystem
          S.liquidHelium.specificHeatCapacity := by
  change coherentCoordinate S.unitSystem
      (quantityFromCoherentCoordinate S.unitSystem heatCapacityDimension
        (coherentCoordinate S.unitSystem S.liquidHelium.massDensity *
          coherentCoordinate S.unitSystem S.liquidHelium.volume *
            coherentCoordinate S.unitSystem
              S.liquidHelium.specificHeatCapacity)) =
    coherentCoordinate S.unitSystem S.liquidHelium.massDensity *
      coherentCoordinate S.unitSystem S.liquidHelium.volume *
        coherentCoordinate S.unitSystem S.liquidHelium.specificHeatCapacity
  rw [coherentCoordinate_quantityFromCoherentCoordinate]

/-- Constant-capacity helium body over the realization's admissible
temperature interval. -/
def heliumColdBodyModel (R : OneCycleRealization) : ColdBodyModel :=
  { unitSystem := R.source.unitSystem
    minTemperature := R.minTemperature
    maxTemperature := R.source.liquidHelium.initialTemperature
    internalEnergyCoordinate := fun t ↦
      coherentCoordinate R.source.unitSystem
          (liquidHeliumHeatCapacity R.source) * t
    heatCapacityCoordinate := fun _ ↦
      coherentCoordinate R.source.unitSystem
        (liquidHeliumHeatCapacity R.source) }

/-- Reservoir state before the cycle: the helium begins at its printed
temperature, while the hot reservoir is the cycle's hot reservoir. -/
def initialBodyReservoirState (R : OneCycleRealization) : BodyReservoirState :=
  { coldTemperature := R.source.liquidHelium.initialTemperature
    hotTemperature := R.cycle.hotTemperature }

/-- The source realization induces a physical constant-capacity body, a
physical initial state, a shared unit system, and matching cycle reservoirs. -/
theorem sourceModel_bridge (R : OneCycleRealization)
    (hphysical : R.IsPhysical)
    (hunit : R.IsUnitCompatible)
    (hsource : R.IsSourceMatched) :
    (heliumColdBodyModel R).IsPhysical ∧
      HasConstantHeatCapacity (heliumColdBodyModel R)
        (liquidHeliumHeatCapacity R.source) ∧
      (initialBodyReservoirState R).IsPhysical (heliumColdBodyModel R) ∧
      SharesUnitSystem (heliumColdBodyModel R) R.apparatus ∧
      CycleMatchesReservoirState R.cycle (initialBodyReservoirState R) := by
  rcases hphysical with ⟨hsourcePhysical, hminPositive, hminLt⟩
  rcases hsourcePhysical with
    ⟨_, _, _, _, _, _, _, _, _, hvolumePositive, hinitialPositive,
      hspecificPositive, hdensityPositive⟩
  rcases hsource with
    ⟨_, _, _, _, hcold, _, _, _, _⟩
  have hcapacityPositive :
      0 < coherentCoordinate R.source.unitSystem
        (liquidHeliumHeatCapacity R.source) := by
    rw [liquidHeliumHeatCapacity_coordinate]
    exact mul_pos (mul_pos hdensityPositive hvolumePositive) hspecificPositive
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change
      0 < coherentCoordinate R.source.unitSystem R.minTemperature ∧
      coherentCoordinate R.source.unitSystem R.minTemperature <
          coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature ∧
      ContinuousOn
          (fun t : ℝ ↦
            coherentCoordinate R.source.unitSystem
                (liquidHeliumHeatCapacity R.source) * t)
          (Set.Icc
            (coherentCoordinate R.source.unitSystem R.minTemperature)
            (coherentCoordinate R.source.unitSystem
              R.source.liquidHelium.initialTemperature)) ∧
      DifferentiableOn ℝ
          (fun t : ℝ ↦
            coherentCoordinate R.source.unitSystem
                (liquidHeliumHeatCapacity R.source) * t)
          (Set.Ioo
            (coherentCoordinate R.source.unitSystem R.minTemperature)
            (coherentCoordinate R.source.unitSystem
              R.source.liquidHelium.initialTemperature)) ∧
      ContinuousOn
          (fun _ : ℝ ↦ coherentCoordinate R.source.unitSystem
            (liquidHeliumHeatCapacity R.source))
          (Set.Icc
            (coherentCoordinate R.source.unitSystem R.minTemperature)
            (coherentCoordinate R.source.unitSystem
              R.source.liquidHelium.initialTemperature)) ∧
      (∀ t ∈ Set.Icc
          (coherentCoordinate R.source.unitSystem R.minTemperature)
          (coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature),
        0 < coherentCoordinate R.source.unitSystem
          (liquidHeliumHeatCapacity R.source)) ∧
      ∀ t ∈ Set.Ioo
          (coherentCoordinate R.source.unitSystem R.minTemperature)
          (coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature),
        deriv
            (fun x : ℝ ↦ coherentCoordinate R.source.unitSystem
              (liquidHeliumHeatCapacity R.source) * x) t =
          coherentCoordinate R.source.unitSystem
            (liquidHeliumHeatCapacity R.source)
    refine ⟨hminPositive, hminLt, ?_, ?_, ?_, ?_, ?_⟩
    · fun_prop
    · fun_prop
    · fun_prop
    · intro _ _
      exact hcapacityPositive
    · intro _ _
      simp
  · exact ⟨hcapacityPositive, by intro _ _; rfl⟩
  · change
      coherentCoordinate R.source.unitSystem R.minTemperature ≤
          coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature ∧
      coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature ≤
          coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature ∧
      0 < coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature ∧
      coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature <
          coherentCoordinate R.source.unitSystem R.cycle.hotTemperature
    refine ⟨hminLt.le, le_rfl, hinitialPositive, ?_⟩
    have htemperatureOrder := R.cycle.temperatureOrder.2
    rw [hcold, hunit] at htemperatureOrder
    exact htemperatureOrder
  · exact hunit.symm
  · exact ⟨hcold, rfl⟩

/-- The unique cold leg gives the source-field expression for heat extracted
in one cycle.  The context permeability remains symbolic and fixed. -/
theorem sourceCycleColdHeat_coordinate (R : OneCycleRealization)
    (hmatch : R.source.MatchesStatement)
    (hphysical : R.IsPhysical)
    (hunit : R.IsUnitCompatible)
    (hsource : R.IsSourceMatched) :
    coherentCoordinate R.source.unitSystem (coldHeatMagnitude R.cycle) =
      (coherentCoordinate R.source.unitSystem R.source.vacuumPermeability *
          coherentCoordinate R.source.unitSystem
            R.source.potassiumChromate.amount *
          coherentCoordinate R.source.unitSystem
            R.source.potassiumChromate.curieParameter /
          (2 * coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature)) *
        (coherentCoordinate R.source.unitSystem
              R.source.potassiumChromate.field2 ^ 2 -
          coherentCoordinate R.source.unitSystem
              R.source.potassiumChromate.field3 ^ 2) := by
  classical
  have hroles := sourceMatchedCycle_roles R hmatch hphysical hunit hsource
  have hcoldEq (e : CycleLeg) :
      IsColdIsothermalLeg R.cycle e ↔ e = .e1 := by
    constructor
    · intro he
      rcases R.cycle.coldLegUnique with ⟨w, hw, hunique⟩
      exact (hunique e he).trans (hunique .e1 hroles.1).symm
    · rintro rfl
      exact hroles.1
  have hcoldFilter :
      Finset.univ.filter (IsColdIsothermalLeg R.cycle) = {.e1} := by
    ext e
    simp [hcoldEq e]
  have hcoldMagnitude :
      coldHeatMagnitude R.cycle = (R.cycle.leg .e1).heat := by
    simp [coldHeatMagnitude, hcoldFilter]
  have hheatApparatus :
      coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.leg .e1).heat =
        (coherentCoordinate R.apparatus.torus.unitSystem
              R.apparatus.material.vacuumPermeability *
            coherentCoordinate R.apparatus.torus.unitSystem
              R.apparatus.material.amount *
            coherentCoordinate R.apparatus.torus.unitSystem
              R.apparatus.material.curieParameter /
            (2 * coherentCoordinate R.apparatus.torus.unitSystem
              R.cycle.coldTemperature)) *
          (coherentCoordinate R.apparatus.torus.unitSystem
                (R.cycle.state .v1).fieldStrength ^ 2 -
            coherentCoordinate R.apparatus.torus.unitSystem
                (R.cycle.state .v2).fieldStrength ^ 2) := by
    let p := (R.cycle.leg .e1).process
    let field : ℝ → ℝ := fun t ↦
      coherentCoordinate R.apparatus.torus.unitSystem
        (p.state t).fieldStrength
    let coefficient : ℝ :=
      coherentCoordinate R.apparatus.torus.unitSystem
            R.apparatus.material.vacuumPermeability *
          coherentCoordinate R.apparatus.torus.unitSystem
            R.apparatus.material.amount *
          coherentCoordinate R.apparatus.torus.unitSystem
            R.apparatus.material.curieParameter /
          coherentCoordinate R.apparatus.torus.unitSystem
            R.cycle.coldTemperature
    have hab : p.a < p.b := (R.cycle.leg .e1).isReversible.1.2.1
    have hstart := R.cycle.legStarts .e1
    have hfinish := R.cycle.legFinishes .e1
    change p.state p.a = R.cycle.state .v1 at hstart
    change p.state p.b = R.cycle.state .v2 at hfinish
    have hcoldIsothermal :
        IsIsothermal R.apparatus p R.cycle.coldTemperature := hroles.1
    have htemperatureStart :=
      hcoldIsothermal.2 p.a ⟨le_rfl, hab.le⟩
    have htemperatureFinish :=
      hcoldIsothermal.2 p.b ⟨hab.le, le_rfl⟩
    rw [hstart] at htemperatureStart
    rw [hfinish] at htemperatureFinish
    have hleg : IsReversibleIsothermalEndpointLeg R.apparatus
        R.cycle.coldTemperature
        (R.cycle.state .v1).fieldStrength
        (R.cycle.state .v2).fieldStrength p := by
      refine ⟨R.cycle.temperatureOrder.1,
        (R.cycle.statePhysical .v1).2.1,
        (R.cycle.statePhysical .v2).2.1,
        (R.cycle.leg .e1).isReversible, hcoldIsothermal, ?_⟩
      unfold HasTemperatureFieldEndpoints
      rw [hstart, hfinish]
      exact ⟨htemperatureStart, rfl, htemperatureFinish, rfl⟩
    have hnet :
        HasNetHeatEntering R.apparatus p (R.cycle.leg .e1).heat := by
      unfold HasNetHeatEntering ReversibleLeg.heat
      rw [coherentCoordinate_quantityFromCoherentCoordinate]
    have hcharacterization :=
      ((isothermalHeat_characterization R.apparatus
        R.cycle.coldTemperature
        (R.cycle.state .v1).fieldStrength
        (R.cycle.state .v2).fieldStrength p hleg).2
          (R.cycle.leg .e1).heat).mp hnet
    change
      coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.leg .e1).heat =
        ∫ t in p.a..p.b,
          -coefficient * field t * deriv field t at hcharacterization
    rcases (R.cycle.leg .e1).isReversible.1 with
      ⟨_, _, ⟨neighborhood, hopen, hIcc, _, hfieldSmooth, _, _, _⟩,
        _, _, _, _, _⟩
    have hfieldSmoothIcc :
        ContDiffOn ℝ 1 field (Set.Icc p.a p.b) :=
      hfieldSmooth.mono hIcc
    have hsquareSmooth :
        ContDiffOn ℝ 1 (fun t ↦ field t ^ 2 / 2) (Set.Icc p.a p.b) :=
      (hfieldSmoothIcc.pow 2).div_const 2
    have hderivative (t : ℝ) (ht : t ∈ Set.Icc p.a p.b) :
        deriv (fun x ↦ field x ^ 2 / 2) t =
          field t * deriv field t := by
      have hfieldDifferentiable : DifferentiableAt ℝ field t :=
        (hfieldSmooth.differentiableOn_one t (hIcc ht)).differentiableAt
          (hopen.mem_nhds (hIcc ht))
      have hderiv :=
        ((hfieldDifferentiable.hasDerivAt.pow 2).div_const 2).deriv
      calc
        deriv (fun x ↦ field x ^ 2 / 2) t =
            2 * field t * deriv field t / 2 := by
          simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
            using hderiv
        _ = field t * deriv field t := by ring
    have hintegral :
        (∫ t in p.a..p.b, field t * deriv field t) =
          (field p.b ^ 2 - field p.a ^ 2) / 2 := by
      calc
        (∫ t in p.a..p.b, field t * deriv field t) =
            ∫ t in p.a..p.b, deriv (fun x ↦ field x ^ 2 / 2) t := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hab.le] at ht
          exact (hderivative t ht).symm
        _ = field p.b ^ 2 / 2 - field p.a ^ 2 / 2 :=
          intervalIntegral.integral_deriv_of_contDiffOn_Icc
            hsquareSmooth hab.le
        _ = (field p.b ^ 2 - field p.a ^ 2) / 2 := by ring
    have hheat :
        coherentCoordinate R.apparatus.torus.unitSystem
            (R.cycle.leg .e1).heat =
          -coefficient * ((field p.b ^ 2 - field p.a ^ 2) / 2) := by
      calc
        coherentCoordinate R.apparatus.torus.unitSystem
            (R.cycle.leg .e1).heat =
            ∫ t in p.a..p.b,
              -coefficient * field t * deriv field t := hcharacterization
        _ = ∫ t in p.a..p.b,
              (-coefficient) * (field t * deriv field t) := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
        _ = (-coefficient) *
              ∫ t in p.a..p.b, field t * deriv field t :=
          intervalIntegral.integral_const_mul _ _
        _ = -coefficient * ((field p.b ^ 2 - field p.a ^ 2) / 2) := by
          rw [hintegral]
    have hfieldStart :
        field p.a = coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.state .v1).fieldStrength := by
      simp [field, hstart]
    have hfieldFinish :
        field p.b = coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.state .v2).fieldStrength := by
      simp [field, hfinish]
    rw [hfieldStart, hfieldFinish] at hheat
    dsimp [coefficient] at hheat
    calc
      coherentCoordinate R.apparatus.torus.unitSystem
          (R.cycle.leg .e1).heat =
          -(coherentCoordinate R.apparatus.torus.unitSystem
                R.apparatus.material.vacuumPermeability *
              coherentCoordinate R.apparatus.torus.unitSystem
                R.apparatus.material.amount *
              coherentCoordinate R.apparatus.torus.unitSystem
                R.apparatus.material.curieParameter /
              coherentCoordinate R.apparatus.torus.unitSystem
                R.cycle.coldTemperature) *
            ((coherentCoordinate R.apparatus.torus.unitSystem
                    (R.cycle.state .v2).fieldStrength ^ 2 -
                coherentCoordinate R.apparatus.torus.unitSystem
                    (R.cycle.state .v1).fieldStrength ^ 2) / 2) := hheat
      _ = _ := by ring
  have hunitEq :
      R.apparatus.torus.unitSystem = R.source.unitSystem := hunit
  rcases hsource with
    ⟨hpermeability, hamount, hcurie, _, hcold,
      _, hfield2, hfield3, _⟩
  rw [← hunitEq, hcoldMagnitude, hheatApparatus,
    hpermeability, hamount, hcurie, hcold, hfield2, hfield3]

namespace OneCycleRealization

/-- The one-cycle source heat fits above the chosen lower endpoint of the
helium model. -/
def HasAvailableEnergy (R : OneCycleRealization) : Prop :=
  (coherentCoordinate R.source.unitSystem R.source.vacuumPermeability *
        coherentCoordinate R.source.unitSystem
          R.source.potassiumChromate.amount *
        coherentCoordinate R.source.unitSystem
          R.source.potassiumChromate.curieParameter /
        (2 * coherentCoordinate R.source.unitSystem
          R.source.liquidHelium.initialTemperature)) *
      (coherentCoordinate R.source.unitSystem
            R.source.potassiumChromate.field2 ^ 2 -
        coherentCoordinate R.source.unitSystem
            R.source.potassiumChromate.field3 ^ 2) ≤
    coherentCoordinate R.source.unitSystem
        (liquidHeliumHeatCapacity R.source) *
      (coherentCoordinate R.source.unitSystem
          R.source.liquidHelium.initialTemperature -
        coherentCoordinate R.source.unitSystem R.minTemperature)

end OneCycleRealization

/-- The explicit source inequality supplies the energy-domain premise for the
abstract one-cycle body update. -/
theorem sourceAvailableEnergy_bridge (R : OneCycleRealization)
    (hmatch : R.source.MatchesStatement)
    (hphysical : R.IsPhysical)
    (hunit : R.IsUnitCompatible)
    (hsource : R.IsSourceMatched)
    (havailable : R.HasAvailableEnergy) :
    coherentCoordinate R.source.unitSystem (coldHeatMagnitude R.cycle) ≤
      (heliumColdBodyModel R).internalEnergyCoordinate
          (coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature) -
        (heliumColdBodyModel R).internalEnergyCoordinate
          (coherentCoordinate R.source.unitSystem R.minTemperature) := by
  rw [sourceCycleColdHeat_coordinate R hmatch hphysical hunit hsource]
  change
    (coherentCoordinate R.source.unitSystem R.source.vacuumPermeability *
          coherentCoordinate R.source.unitSystem
            R.source.potassiumChromate.amount *
          coherentCoordinate R.source.unitSystem
            R.source.potassiumChromate.curieParameter /
          (2 * coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature)) *
        (coherentCoordinate R.source.unitSystem
              R.source.potassiumChromate.field2 ^ 2 -
          coherentCoordinate R.source.unitSystem
              R.source.potassiumChromate.field3 ^ 2) ≤
      coherentCoordinate R.source.unitSystem
          (liquidHeliumHeatCapacity R.source) *
        (coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature -
          coherentCoordinate R.source.unitSystem R.minTemperature) at havailable
  change
    (coherentCoordinate R.source.unitSystem R.source.vacuumPermeability *
          coherentCoordinate R.source.unitSystem
            R.source.potassiumChromate.amount *
          coherentCoordinate R.source.unitSystem
            R.source.potassiumChromate.curieParameter /
          (2 * coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature)) *
        (coherentCoordinate R.source.unitSystem
              R.source.potassiumChromate.field2 ^ 2 -
          coherentCoordinate R.source.unitSystem
              R.source.potassiumChromate.field3 ^ 2) ≤
      coherentCoordinate R.source.unitSystem
            (liquidHeliumHeatCapacity R.source) *
          coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature -
        coherentCoordinate R.source.unitSystem
            (liquidHeliumHeatCapacity R.source) *
          coherentCoordinate R.source.unitSystem R.minTemperature
  nlinarith [havailable]

namespace OneCycleRealization

/-- All source transcription, physicality, compatibility, matching, and
energy-domain conditions required of a realization. -/
def IsAdmissible (R : OneCycleRealization) : Prop :=
  R.source.MatchesStatement ∧
  R.IsPhysical ∧
  R.IsUnitCompatible ∧
  R.IsSourceMatched ∧
  R.HasAvailableEnergy

end OneCycleRealization

/-! ## Post-cycle helium temperature -/

/-- A candidate temperature is requested exactly when it is the cold
component of a state related to the initial state by the governing completed
cycle update. -/
def IsRequestedFinalTemperature (R : OneCycleRealization)
    (T : Temperature) : Prop :=
  ∃ σ' : BodyReservoirState,
    σ'.coldTemperature = T ∧
      OneCycleStateUpdate (heliumColdBodyModel R) R.cycle
        (initialBodyReservoirState R) σ'

/-- Every state-update candidate is strictly colder than the initial helium. -/
lemma requestedFinalTemperature_cold_lt (R : OneCycleRealization)
    (T : Temperature) (hT : IsRequestedFinalTemperature R T) :
    coherentCoordinate R.source.unitSystem T <
      coherentCoordinate R.source.unitSystem
        R.source.liquidHelium.initialTemperature := by
  rcases hT with ⟨finalState, hfinalTemperature, hupdate⟩
  have hlt := oneCycleStateUpdate_cold_lt
    (heliumColdBodyModel R) R.cycle
    (initialBodyReservoirState R) finalState hupdate
  change coherentCoordinate R.source.unitSystem finalState.coldTemperature <
    coherentCoordinate R.source.unitSystem
      R.source.liquidHelium.initialTemperature at hlt
  rw [hfinalTemperature] at hlt
  exact hlt

/-- Within each fixed admissible realization, the governing update determines
exactly one final helium temperature. -/
theorem realizationFinalTemperature_existsUnique (R : OneCycleRealization)
    (hR : R.IsAdmissible) :
    ∃! T : Temperature, IsRequestedFinalTemperature R T := by
  rcases hR with ⟨hmatch, hphysical, hunit, hsource, havailable⟩
  rcases sourceModel_bridge R hphysical hunit hsource with
    ⟨hbody, _, hinitial, hunits, hmatches⟩
  have hcapacity := sourceAvailableEnergy_bridge R hmatch hphysical hunit
    hsource havailable
  have hunitEq :
      R.apparatus.torus.unitSystem = R.source.unitSystem := hunit
  have hcapacity' :
      coherentCoordinate R.apparatus.torus.unitSystem
          (coldHeatMagnitude R.cycle) ≤
        (heliumColdBodyModel R).internalEnergyCoordinate
            (coherentCoordinate (heliumColdBodyModel R).unitSystem
              (initialBodyReservoirState R).coldTemperature) -
          (heliumColdBodyModel R).internalEnergyCoordinate
            (coherentCoordinate (heliumColdBodyModel R).unitSystem
              (heliumColdBodyModel R).minTemperature) := by
    change coherentCoordinate R.apparatus.torus.unitSystem
          (coldHeatMagnitude R.cycle) ≤
        (heliumColdBodyModel R).internalEnergyCoordinate
            (coherentCoordinate R.source.unitSystem
              R.source.liquidHelium.initialTemperature) -
          (heliumColdBodyModel R).internalEnergyCoordinate
            (coherentCoordinate R.source.unitSystem R.minTemperature)
    calc
      coherentCoordinate R.apparatus.torus.unitSystem
          (coldHeatMagnitude R.cycle) =
          coherentCoordinate R.source.unitSystem
            (coldHeatMagnitude R.cycle) := by
        rw [hunitEq]
      _ ≤ _ := hcapacity
  rcases oneCycleNextState_existsUnique
      (heliumColdBodyModel R) R.cycle (initialBodyReservoirState R)
      hbody hinitial hunits hmatches hcapacity' with
    ⟨finalState, hupdate, hupdateUnique⟩
  refine ⟨finalState.coldTemperature, ⟨finalState, rfl, hupdate⟩, ?_⟩
  intro T hT
  rcases hT with ⟨otherState, hotherTemperature, hotherUpdate⟩
  have hstate : otherState = finalState :=
    hupdateUnique otherState hotherUpdate
  calc
    T = otherState.coldTemperature := hotherTemperature.symm
    _ = finalState.coldTemperature := congrArg BodyReservoirState.coldTemperature hstate

/-- A source-level candidate is produced by some admissible apparatus and
cycle realizing exactly the same fixed source/problem context. -/
def IsSourceRequestedFinalTemperature (S : OneCycleSourceData)
    (T : Temperature) : Prop :=
  ∃ R : OneCycleRealization,
    R.source = S ∧
      R.IsAdmissible ∧
      IsRequestedFinalTemperature R T

/-- Every source-level candidate obeys the same source-only energy balance. -/
theorem sourceRequestedFinalTemperature_energyBalance
    (S : OneCycleSourceData) (T : Temperature)
    (hT : IsSourceRequestedFinalTemperature S T) :
    coherentCoordinate S.unitSystem (liquidHeliumHeatCapacity S) *
        (coherentCoordinate S.unitSystem S.liquidHelium.initialTemperature -
          coherentCoordinate S.unitSystem T) =
      (coherentCoordinate S.unitSystem S.vacuumPermeability *
          coherentCoordinate S.unitSystem S.potassiumChromate.amount *
          coherentCoordinate S.unitSystem S.potassiumChromate.curieParameter /
          (2 * coherentCoordinate S.unitSystem
            S.liquidHelium.initialTemperature)) *
        (coherentCoordinate S.unitSystem S.potassiumChromate.field2 ^ 2 -
          coherentCoordinate S.unitSystem
            S.potassiumChromate.field3 ^ 2) := by
  rcases hT with ⟨R, hRsource, hadmissible, finalState,
    hfinalTemperature, hupdate⟩
  subst S
  rcases hadmissible with
    ⟨hmatch, hphysical, hunit, hsource, _⟩
  have hheat := sourceCycleColdHeat_coordinate R hmatch hphysical hunit hsource
  have hunitEq :
      R.apparatus.torus.unitSystem = R.source.unitSystem := hunit
  rcases hupdate with ⟨_, _, _, _, _, _, henergy⟩
  change
    coherentCoordinate R.source.unitSystem
          (liquidHeliumHeatCapacity R.source) *
        coherentCoordinate R.source.unitSystem finalState.coldTemperature =
      coherentCoordinate R.source.unitSystem
          (liquidHeliumHeatCapacity R.source) *
          coherentCoordinate R.source.unitSystem
            R.source.liquidHelium.initialTemperature -
        coherentCoordinate R.apparatus.torus.unitSystem
          (coldHeatMagnitude R.cycle) at henergy
  rw [hfinalTemperature, hunitEq] at henergy
  nlinarith [henergy, hheat]

/-- Two admissible realizations of the same fixed context cannot produce
different requested temperatures. -/
theorem requestedFinalTemperature_realizationInvariant
    (S : OneCycleSourceData)
    (R₁ R₂ : OneCycleRealization) (T₁ T₂ : Temperature)
    (hsource₁ : R₁.source = S) (hsource₂ : R₂.source = S)
    (hadmissible₁ : R₁.IsAdmissible)
    (hadmissible₂ : R₂.IsAdmissible)
    (hT₁ : IsRequestedFinalTemperature R₁ T₁)
    (hT₂ : IsRequestedFinalTemperature R₂ T₂) :
    T₁ = T₂ := by
  have hsourceT₁ : IsSourceRequestedFinalTemperature S T₁ :=
    ⟨R₁, hsource₁, hadmissible₁, hT₁⟩
  have hsourceT₂ : IsSourceRequestedFinalTemperature S T₂ :=
    ⟨R₂, hsource₂, hadmissible₂, hT₂⟩
  have hbalance₁ :=
    sourceRequestedFinalTemperature_energyBalance S T₁ hsourceT₁
  have hbalance₂ :=
    sourceRequestedFinalTemperature_energyBalance S T₂ hsourceT₂
  have hR₁Physical : R₁.IsPhysical := hadmissible₁.2.1
  have hSPhysical : S.IsPhysical := by
    have hSourcePhysical : R₁.source.IsPhysical := hR₁Physical.1
    rw [hsource₁] at hSourcePhysical
    exact hSourcePhysical
  rcases hSPhysical with
    ⟨_, _, _, _, _, _, _, _, _, hvolumePositive, _, hspecificPositive,
      hdensityPositive⟩
  have hcapacityPositive :
      0 < coherentCoordinate S.unitSystem (liquidHeliumHeatCapacity S) := by
    rw [liquidHeliumHeatCapacity_coordinate]
    exact mul_pos (mul_pos hdensityPositive hvolumePositive) hspecificPositive
  apply (coordinateInSI_eq_iff S.unitSystem T₁ T₂).mp
  change coherentCoordinate S.unitSystem T₁ =
    coherentCoordinate S.unitSystem T₂
  nlinarith [hbalance₁, hbalance₂, hcapacityPositive]

/-- For a physical, statement-matched context admitting at least one
governing apparatus/cycle realization, there is exactly one source-level
post-cycle helium temperature.  No value for that temperature occurs in the
signature. -/
theorem requestedFinalTemperature_existsUnique
    (S : OneCycleSourceData)
    (hmatch : S.MatchesStatement)
    (hphysical : S.IsPhysical)
    (hexists : ∃ R₀ : OneCycleRealization,
      R₀.source = S ∧
      0 < coherentCoordinate S.unitSystem R₀.minTemperature ∧
      coherentCoordinate S.unitSystem R₀.minTemperature <
        coherentCoordinate S.unitSystem S.liquidHelium.initialTemperature ∧
      R₀.IsUnitCompatible ∧
      R₀.IsSourceMatched ∧
      R₀.HasAvailableEnergy) :
    ∃! T : Temperature, IsSourceRequestedFinalTemperature S T := by
  rcases hexists with
    ⟨R₀, hR₀Source, hminPositive, hminLt, hunit, hsource, havailable⟩
  subst S
  have hR₀Physical : R₀.IsPhysical :=
    ⟨hphysical, hminPositive, hminLt⟩
  have hR₀Admissible : R₀.IsAdmissible :=
    ⟨hmatch, hR₀Physical, hunit, hsource, havailable⟩
  rcases realizationFinalTemperature_existsUnique R₀ hR₀Admissible with
    ⟨T₀, hT₀, _⟩
  refine ⟨T₀, ⟨R₀, rfl, hR₀Admissible, hT₀⟩, ?_⟩
  intro T hT
  rcases hT with ⟨R, hRSource, hRAdmissible, hRT⟩
  exact requestedFinalTemperature_realizationInvariant R₀.source
    R R₀ T T₀ hRSource rfl hRAdmissible hR₀Admissible hRT hT₀

end Ipho2026Gpt56solBlind.ProblemIPhO2026_3_C_3
