import Mathlib
import Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics

/-!
# Reversible refrigerator cycles and cooling histories

This module builds a closed, directed four-leg refrigerator from the shared
paramagnetic-process model.  Heat and material work use the system-positive
sign convention.  The concrete cycle legs acquire their hot, cold, and
adiabatic roles from process predicates rather than from their names.

The later body-update and continuous-history predicates are answer-free: they
state energy balances, Carnot relations, regularity, and endpoint conditions,
without storing a requested temperature, elapsed time, or performance value.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Interval

namespace Ipho2026Gpt56solBlind.Shared.RefrigeratorCycle

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics

/-! ## Entropy quantities and the directed four-cycle -/

/-- Entropy has energy-per-temperature dimension. -/
def entropyDimension : Dimension ISQDimensionBase :=
  energyDimension * temperatureDimension⁻¹

/-- Entropy quantities.  Only differences are used below. -/
abbrev Entropy := Quantity entropyDimension

/-- Four abstract vertices, named only by cyclic order. -/
inductive CycleVertex
  | v0 | v1 | v2 | v3
  deriving DecidableEq, Fintype

/-- The four directed edges of the abstract cycle. -/
inductive CycleLeg
  | e0 | e1 | e2 | e3
  deriving DecidableEq, Fintype

namespace CycleLeg

/-- Initial vertex of a directed leg. -/
def startVertex : CycleLeg → CycleVertex
  | .e0 => .v0
  | .e1 => .v1
  | .e2 => .v2
  | .e3 => .v3

/-- Final vertex of a directed leg. -/
def finishVertex : CycleLeg → CycleVertex
  | .e0 => .v1
  | .e1 => .v2
  | .e2 => .v3
  | .e3 => .v0

end CycleLeg

/-- The four directed legs are nonloops, compose in cyclic order, close, and
give bijections from legs to both their start and finish vertices. -/
lemma cycleLegs_compose :
    (∀ e : CycleLeg, e.startVertex ≠ e.finishVertex) ∧
      CycleLeg.e0.finishVertex = CycleLeg.e1.startVertex ∧
      CycleLeg.e1.finishVertex = CycleLeg.e2.startVertex ∧
      CycleLeg.e2.finishVertex = CycleLeg.e3.startVertex ∧
      CycleLeg.e3.finishVertex = CycleLeg.e0.startVertex ∧
      Function.Bijective CycleLeg.startVertex ∧
      Function.Bijective CycleLeg.finishVertex := by
  decide

/-- A shared quasistatic process together with all reversible-leg laws. -/
structure ReversibleLeg (D : ParamagneticData) where
  process : QuasistaticProcess
  isReversible : IsReversibleLeg D process

namespace ReversibleLeg

/-- Net signed heat entering the material during a leg. -/
def heat {D : ParamagneticData} (L : ReversibleLeg D) : Energy :=
  quantityFromCoherentCoordinate D.torus.unitSystem energyDimension
    (∫ τ in L.process.a..L.process.b,
      coherentCoordinate D.torus.unitSystem (L.process.heatIncrement τ))

/-- Net signed vacuum-subtracted material work entering during a leg. -/
def work {D : ParamagneticData} (L : ReversibleLeg D) : Energy :=
  quantityFromCoherentCoordinate D.torus.unitSystem energyDimension
    (∫ τ in L.process.a..L.process.b,
      coherentCoordinate D.torus.unitSystem
        (materialWorkIncrement D L.process τ))

/-- Internal-energy change from the process's directed endpoints. -/
def internalEnergyChange {D : ParamagneticData}
    (L : ReversibleLeg D) : Energy :=
  quantityFromCoherentCoordinate D.torus.unitSystem energyDimension
    (coherentCoordinate D.torus.unitSystem
        (L.process.internalEnergy L.process.b) -
      coherentCoordinate D.torus.unitSystem
        (L.process.internalEnergy L.process.a))

end ReversibleLeg

/-- Integrated first law with both transfers system-positive. -/
lemma reversibleLeg_firstLaw {D : ParamagneticData}
    (L : ReversibleLeg D) :
    L.internalEnergyChange = L.heat + L.work := by
  rcases L.isReversible with
    ⟨hregular, _, _, _, _, _, hfirstLaw⟩
  rcases hregular with
    ⟨_, hab, ⟨neighborhood, hopen, hIcc, _, _, _, _, henergySmooth⟩,
      _, _, _, hheatIntegrable, _⟩
  let u : ℝ → ℝ := fun t =>
    coherentCoordinate D.torus.unitSystem (L.process.internalEnergy t)
  let q : ℝ → ℝ := fun t =>
    coherentCoordinate D.torus.unitSystem (L.process.heatIncrement t)
  let w : ℝ → ℝ := fun t =>
    coherentCoordinate D.torus.unitSystem
      (materialWorkIncrement D L.process t)
  have huSmooth : ContDiffOn ℝ 1 u (Set.Icc L.process.a L.process.b) :=
    henergySmooth.mono hIcc
  have hduIntegrable : IntervalIntegrable (deriv u) MeasureTheory.volume
      L.process.a L.process.b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab.le
    exact (henergySmooth.continuousOn_deriv_of_isOpen hopen (by norm_num)).mono hIcc
  have hwIntegrable : IntervalIntegrable w MeasureTheory.volume
      L.process.a L.process.b := by
    apply IntervalIntegrable.congr _ (hduIntegrable.sub hheatIntegrable)
    intro t ht
    rw [Set.uIoc_of_le hab.le] at ht
    have ht' : t ∈ Set.Icc L.process.a L.process.b := ⟨ht.1.le, ht.2⟩
    dsimp [u, q, w]
    linarith [hfirstLaw t ht']
  have hfundamental :
      (∫ t in L.process.a..L.process.b, deriv u t) =
        u L.process.b - u L.process.a :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc huSmooth hab.le
  have hbalance :
      u L.process.b - u L.process.a =
        (∫ t in L.process.a..L.process.b, q t) +
          ∫ t in L.process.a..L.process.b, w t := by
    rw [← hfundamental]
    calc
      (∫ t in L.process.a..L.process.b, deriv u t) =
          ∫ t in L.process.a..L.process.b, q t + w t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hab.le] at ht
        simpa [u, q, w] using hfirstLaw t ht
      _ = (∫ t in L.process.a..L.process.b, q t) +
          ∫ t in L.process.a..L.process.b, w t :=
        intervalIntegral.integral_add hheatIntegrable hwIntegrable
  apply (coordinateInSI_eq_iff D.torus.unitSystem _ _).mp
  change coherentCoordinate D.torus.unitSystem L.internalEnergyChange =
    coherentCoordinate D.torus.unitSystem (L.heat + L.work)
  have hcoordinateAdd (x y : Energy) :
      coherentCoordinate D.torus.unitSystem (x + y) =
        coherentCoordinate D.torus.unitSystem x +
          coherentCoordinate D.torus.unitSystem y := by
    simp [coherentCoordinate, coordinateInSI]
    ring
  rw [hcoordinateAdd]
  simp only [ReversibleLeg.internalEnergyChange, ReversibleLeg.heat,
    ReversibleLeg.work, coherentCoordinate_quantityFromCoherentCoordinate]
  simpa [u, q, w] using hbalance

/-- Thermodynamic roles, independent of concrete edge names. -/
inductive ThermalRole
  | hotIsothermal
  | coldIsothermal
  | adiabatic
  deriving DecidableEq

/-- A closed reversible four-leg refrigerator whose leg roles are certified
by path predicates rather than stored as an annotation. -/
structure ComposedFourLegCycle (D : ParamagneticData) where
  state : CycleVertex → EquilibriumState
  internalEnergy : CycleVertex → Energy
  entropy : CycleVertex → Entropy
  leg : CycleLeg → ReversibleLeg D
  hotTemperature : Temperature
  coldTemperature : Temperature
  apparatusPhysical : D.IsPhysical
  statePhysical : ∀ v, (state v).IsPhysical D.torus.unitSystem
  stateEquation : ∀ v, SatisfiesEquationOfState D (state v)
  temperatureOrder :
    0 < coherentCoordinate D.torus.unitSystem coldTemperature ∧
      coherentCoordinate D.torus.unitSystem coldTemperature <
        coherentCoordinate D.torus.unitSystem hotTemperature
  legStarts : ∀ e,
    StartsAt (leg e).process (state e.startVertex)
  legFinishes : ∀ e,
    FinishesAt (leg e).process (state e.finishVertex)
  legInitialEnergy : ∀ e,
    (leg e).process.internalEnergy (leg e).process.a =
      internalEnergy e.startVertex
  legFinalEnergy : ∀ e,
    (leg e).process.internalEnergy (leg e).process.b =
      internalEnergy e.finishVertex
  roleExactlyOne : ∀ e,
    (IsIsothermal D (leg e).process hotTemperature ∨
      IsIsothermal D (leg e).process coldTemperature ∨
      IsAdiabatic D (leg e).process) ∧
    ¬ (IsIsothermal D (leg e).process hotTemperature ∧
      IsIsothermal D (leg e).process coldTemperature) ∧
    ¬ (IsIsothermal D (leg e).process hotTemperature ∧
      IsAdiabatic D (leg e).process) ∧
    ¬ (IsIsothermal D (leg e).process coldTemperature ∧
      IsAdiabatic D (leg e).process)
  hotLegUnique : ∃! e : CycleLeg,
    IsIsothermal D (leg e).process hotTemperature
  coldLegUnique : ∃! e : CycleLeg,
    IsIsothermal D (leg e).process coldTemperature
  adiabaticLegsExactlyTwo : ∃ e₁ e₂ : CycleLeg,
    e₁ ≠ e₂ ∧
      ∀ e, IsAdiabatic D (leg e).process ↔ e = e₁ ∨ e = e₂
  hotEntropyHeatLaw : ∀ e,
    IsIsothermal D (leg e).process hotTemperature →
      coherentCoordinate D.torus.unitSystem (leg e).heat =
        coherentCoordinate D.torus.unitSystem hotTemperature *
          (coherentCoordinate D.torus.unitSystem
              (entropy e.finishVertex) -
            coherentCoordinate D.torus.unitSystem
              (entropy e.startVertex))
  coldEntropyHeatLaw : ∀ e,
    IsIsothermal D (leg e).process coldTemperature →
      coherentCoordinate D.torus.unitSystem (leg e).heat =
        coherentCoordinate D.torus.unitSystem coldTemperature *
          (coherentCoordinate D.torus.unitSystem
              (entropy e.finishVertex) -
            coherentCoordinate D.torus.unitSystem
              (entropy e.startVertex))
  adiabaticEntropyLaw : ∀ e,
    IsAdiabatic D (leg e).process →
      entropy e.finishVertex = entropy e.startVertex
  coldEntropyIncreases : ∀ e,
    IsIsothermal D (leg e).process coldTemperature →
      coherentCoordinate D.torus.unitSystem (entropy e.startVertex) <
        coherentCoordinate D.torus.unitSystem (entropy e.finishVertex)

/-- Entropy change along a directed cycle leg. -/
def legEntropyChange {D : ParamagneticData}
    (C : ComposedFourLegCycle D) (e : CycleLeg) : Entropy :=
  C.entropy e.finishVertex - C.entropy e.startVertex

/-- A leg is hot-isothermal exactly when its process is isothermal at the
cycle's hot-reservoir temperature. -/
def IsHotIsothermalLeg {D : ParamagneticData}
    (C : ComposedFourLegCycle D) (e : CycleLeg) : Prop :=
  IsIsothermal D (C.leg e).process C.hotTemperature

/-- Cold-isothermal role predicate. -/
def IsColdIsothermalLeg {D : ParamagneticData}
    (C : ComposedFourLegCycle D) (e : CycleLeg) : Prop :=
  IsIsothermal D (C.leg e).process C.coldTemperature

/-- Pointwise-adiabatic role predicate. -/
def IsAdiabaticCycleLeg {D : ParamagneticData}
    (C : ComposedFourLegCycle D) (e : CycleLeg) : Prop :=
  IsAdiabatic D (C.leg e).process

/-- The role determined by the mutually exclusive process predicates. -/
noncomputable def thermalRoleOf {D : ParamagneticData}
    (C : ComposedFourLegCycle D) (e : CycleLeg) : ThermalRole := by
  classical
  exact if IsHotIsothermalLeg C e then .hotIsothermal
    else if IsColdIsothermalLeg C e then .coldIsothermal
    else .adiabatic

/-- The derived role predicates form the required one-hot, one-cold,
two-adiabatic partition; the two isothermal endpoint pairs are disjoint and
exhaust all vertices. -/
lemma thermalRole_partition {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    (∀ e,
      (thermalRoleOf C e = .hotIsothermal ↔ IsHotIsothermalLeg C e) ∧
      (thermalRoleOf C e = .coldIsothermal ↔ IsColdIsothermalLeg C e) ∧
      (thermalRoleOf C e = .adiabatic ↔ IsAdiabaticCycleLeg C e)) ∧
    (∃! e : CycleLeg, IsHotIsothermalLeg C e) ∧
    (∃! e : CycleLeg, IsColdIsothermalLeg C e) ∧
    (∃ e₁ e₂ : CycleLeg, e₁ ≠ e₂ ∧
      ∀ e, IsAdiabaticCycleLeg C e ↔ e = e₁ ∨ e = e₂) ∧
    ∀ eₕ e_c,
      IsHotIsothermalLeg C eₕ → IsColdIsothermalLeg C e_c →
        ({eₕ.startVertex, eₕ.finishVertex} : Finset CycleVertex) ∩
              {e_c.startVertex, e_c.finishVertex} = ∅ ∧
          ({eₕ.startVertex, eₕ.finishVertex} : Finset CycleVertex) ∪
              {e_c.startVertex, e_c.finishVertex} = Finset.univ := by
  classical
  have endpointTemperatures (e : CycleLeg) (T : Temperature)
      (hiso : IsIsothermal D (C.leg e).process T) :
      (C.state e.startVertex).temperature = T ∧
        (C.state e.finishVertex).temperature = T := by
    have hab : (C.leg e).process.a < (C.leg e).process.b :=
      (C.leg e).isReversible.1.2.1
    have hstart := hiso.2 (C.leg e).process.a ⟨le_rfl, hab.le⟩
    have hfinish := hiso.2 (C.leg e).process.b ⟨hab.le, le_rfl⟩
    have hs := C.legStarts e
    have hf := C.legFinishes e
    unfold StartsAt at hs
    unfold FinishesAt at hf
    rw [hs] at hstart
    rw [hf] at hfinish
    exact ⟨hstart, hfinish⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e
    rcases C.roleExactlyOne e with ⟨hrole, hhotCold, hhotAdiabatic,
      hcoldAdiabatic⟩
    by_cases hhot : IsHotIsothermalLeg C e
    · have hcold : ¬ IsColdIsothermalLeg C e :=
        fun h => hhotCold ⟨hhot, h⟩
      have hadi : ¬ IsAdiabaticCycleLeg C e :=
        fun h => hhotAdiabatic ⟨hhot, h⟩
      simp [thermalRoleOf, hhot, hcold, hadi]
    · by_cases hcold : IsColdIsothermalLeg C e
      · have hadi : ¬ IsAdiabaticCycleLeg C e :=
          fun h => hcoldAdiabatic ⟨hcold, h⟩
        simp [thermalRoleOf, hhot, hcold, hadi]
      · have hadi : IsAdiabaticCycleLeg C e :=
          (hrole.resolve_left hhot).resolve_left hcold
        simp [thermalRoleOf, hhot, hcold, hadi]
  · simpa [IsHotIsothermalLeg] using C.hotLegUnique
  · simpa [IsColdIsothermalLeg] using C.coldLegUnique
  · simpa [IsAdiabaticCycleLeg] using C.adiabaticLegsExactlyTwo
  · intro eₕ e_c hhot hcold
    have hhotEndpoints := endpointTemperatures eₕ C.hotTemperature hhot
    have hcoldEndpoints := endpointTemperatures e_c C.coldTemperature hcold
    have htemperatureNe : C.hotTemperature ≠ C.coldTemperature := by
      intro h
      have hlt := C.temperatureOrder.2
      rw [h] at hlt
      exact (lt_irrefl _ hlt)
    have hdisjoint :
        Disjoint ({eₕ.startVertex, eₕ.finishVertex} : Finset CycleVertex)
          {e_c.startVertex, e_c.finishVertex} := by
      rw [Finset.disjoint_left]
      intro v hvhot hvcold
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvhot hvcold
      have hvHot : (C.state v).temperature = C.hotTemperature := by
        rcases hvhot with hv | hv
        · simpa [hv] using hhotEndpoints.1
        · simpa [hv] using hhotEndpoints.2
      have hvCold : (C.state v).temperature = C.coldTemperature := by
        rcases hvcold with hv | hv
        · simpa [hv] using hcoldEndpoints.1
        · simpa [hv] using hcoldEndpoints.2
      exact htemperatureNe (hvHot.symm.trans hvCold)
    refine ⟨Finset.disjoint_iff_inter_eq_empty.mp hdisjoint, ?_⟩
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisjoint]
    have hhotCard :
        ({eₕ.startVertex, eₕ.finishVertex} : Finset CycleVertex).card = 2 := by
      cases eₕ <;> decide
    have hcoldCard :
        ({e_c.startVertex, e_c.finishVertex} : Finset CycleVertex).card = 2 := by
      cases e_c <;> decide
    rw [hhotCard, hcoldCard]
    decide

/-! ## Per-cycle heat, work, and Carnot balance -/

/-- Net signed heat entering the material over the whole cycle. -/
def cycleSignedHeat {D : ParamagneticData}
    (C : ComposedFourLegCycle D) : Energy :=
  ∑ e : CycleLeg, (C.leg e).heat

/-- Net signed material work entering the refrigerator over the cycle. -/
def cycleWorkInput {D : ParamagneticData}
    (C : ComposedFourLegCycle D) : Energy :=
  ∑ e : CycleLeg, (C.leg e).work

/-- Positive-magnitude candidate for heat delivered to the hot reservoir,
defined without naming its unique leg. -/
noncomputable def hotHeatMagnitude {D : ParamagneticData}
    (C : ComposedFourLegCycle D) : Energy := by
  classical
  exact -(Finset.univ.filter (IsHotIsothermalLeg C)).sum
    (fun e => (C.leg e).heat)

/-- Positive-magnitude candidate for heat absorbed from the cold body. -/
noncomputable def coldHeatMagnitude {D : ParamagneticData}
    (C : ComposedFourLegCycle D) : Energy := by
  classical
  exact (Finset.univ.filter (IsColdIsothermalLeg C)).sum
    (fun e => (C.leg e).heat)

/-- Directed endpoint internal-energy changes telescope around the cycle. -/
lemma cycleInternalEnergy_sum_eq_zero {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    (∑ e : CycleLeg, (C.leg e).internalEnergyChange) = 0 := by
  classical
  have hcoordinateSub (x y : Energy) :
      coherentCoordinate D.torus.unitSystem (x - y) =
        coherentCoordinate D.torus.unitSystem x -
          coherentCoordinate D.torus.unitSystem y := by
    simp [coherentCoordinate, coordinateInSI]
    ring
  have hchange (e : CycleLeg) :
      (C.leg e).internalEnergyChange =
        C.internalEnergy e.finishVertex - C.internalEnergy e.startVertex := by
    apply (coordinateInSI_eq_iff D.torus.unitSystem _ _).mp
    change
      coherentCoordinate D.torus.unitSystem (C.leg e).internalEnergyChange =
        coherentCoordinate D.torus.unitSystem
          (C.internalEnergy e.finishVertex - C.internalEnergy e.startVertex)
    rw [hcoordinateSub]
    simp only [ReversibleLeg.internalEnergyChange,
      coherentCoordinate_quantityFromCoherentCoordinate]
    rw [C.legFinalEnergy e, C.legInitialEnergy e]
  let startEquiv : CycleLeg ≃ CycleVertex :=
    Equiv.ofBijective CycleLeg.startVertex cycleLegs_compose.2.2.2.2.2.1
  let finishEquiv : CycleLeg ≃ CycleVertex :=
    Equiv.ofBijective CycleLeg.finishVertex cycleLegs_compose.2.2.2.2.2.2
  have hstartSum :
      (∑ e : CycleLeg, C.internalEnergy e.startVertex) =
        ∑ v : CycleVertex, C.internalEnergy v := by
    exact startEquiv.sum_comp C.internalEnergy
  have hfinishSum :
      (∑ e : CycleLeg, C.internalEnergy e.finishVertex) =
        ∑ v : CycleVertex, C.internalEnergy v := by
    exact finishEquiv.sum_comp C.internalEnergy
  calc
    (∑ e : CycleLeg, (C.leg e).internalEnergyChange) =
        ∑ e : CycleLeg,
          (C.internalEnergy e.finishVertex - C.internalEnergy e.startVertex) := by
      apply Finset.sum_congr rfl
      intro e _
      exact hchange e
    _ = (∑ e : CycleLeg, C.internalEnergy e.finishVertex) -
        ∑ e : CycleLeg, C.internalEnergy e.startVertex := by
      simp only [Finset.sum_sub_distrib]
    _ = 0 := by rw [hfinishSum, hstartSum, sub_self]

/-- Closed-cycle first law in the system-positive sign convention. -/
theorem cycle_heat_work_balance {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    cycleSignedHeat C + cycleWorkInput C = 0 := by
  rw [← cycleInternalEnergy_sum_eq_zero C]
  simp only [cycleSignedHeat, cycleWorkInput, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  exact (reversibleLeg_firstLaw (C.leg e)).symm

/-- Entropy changes telescope, and the hot and cold filtered changes are
opposites because the two adiabatic changes vanish. -/
lemma cycleEntropy_sum_eq_zero {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    (∑ e : CycleLeg, legEntropyChange C e) = 0 ∧
      ∀ eₕ e_c,
        IsHotIsothermalLeg C eₕ → IsColdIsothermalLeg C e_c →
          legEntropyChange C eₕ = -legEntropyChange C e_c := by
  classical
  let startEquiv : CycleLeg ≃ CycleVertex :=
    Equiv.ofBijective CycleLeg.startVertex cycleLegs_compose.2.2.2.2.2.1
  let finishEquiv : CycleLeg ≃ CycleVertex :=
    Equiv.ofBijective CycleLeg.finishVertex cycleLegs_compose.2.2.2.2.2.2
  have hstartSum :
      (∑ e : CycleLeg, C.entropy e.startVertex) =
        ∑ v : CycleVertex, C.entropy v := by
    exact startEquiv.sum_comp C.entropy
  have hfinishSum :
      (∑ e : CycleLeg, C.entropy e.finishVertex) =
        ∑ v : CycleVertex, C.entropy v := by
    exact finishEquiv.sum_comp C.entropy
  have htotal : (∑ e : CycleLeg, legEntropyChange C e) = 0 := by
    simp only [legEntropyChange, Finset.sum_sub_distrib]
    rw [hfinishSum, hstartSum, sub_self]
  refine ⟨htotal, ?_⟩
  intro eₕ e_c hhot hcold
  have hhotEq : ∀ e, IsHotIsothermalLeg C e → e = eₕ := by
    intro e he
    rcases C.hotLegUnique with ⟨w, hw, huw⟩
    exact (huw e he).trans (huw eₕ hhot).symm
  have hcoldEq : ∀ e, IsColdIsothermalLeg C e → e = e_c := by
    intro e he
    rcases C.coldLegUnique with ⟨w, hw, huw⟩
    exact (huw e he).trans (huw e_c hcold).symm
  have hne : eₕ ≠ e_c := by
    intro heq
    subst e_c
    exact (C.roleExactlyOne eₕ).2.1 ⟨hhot, hcold⟩
  have hzero (e : CycleLeg) (hehot : e ≠ eₕ) (hecold : e ≠ e_c) :
      legEntropyChange C e = 0 := by
    have hadi : IsAdiabaticCycleLeg C e := by
      rcases (C.roleExactlyOne e).1 with he | he | he
      · exact False.elim (hehot (hhotEq e he))
      · exact False.elim (hecold (hcoldEq e he))
      · exact he
    have hentropy := C.adiabaticEntropyLaw e hadi
    simp [legEntropyChange, hentropy]
  have hecMem : e_c ∈ (Finset.univ.erase eₕ : Finset CycleLeg) :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  have hremaining :
      (∑ e ∈ (Finset.univ.erase eₕ).erase e_c,
        legEntropyChange C e) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hecNe : e ≠ e_c := (Finset.mem_erase.mp he).1
    have hehotNe : e ≠ eₕ :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1
    exact hzero e hehotNe hecNe
  have hpairSum :
      (∑ e : CycleLeg, legEntropyChange C e) =
        legEntropyChange C eₕ + legEntropyChange C e_c := by
    calc
      (∑ e : CycleLeg, legEntropyChange C e) =
          legEntropyChange C eₕ +
            ∑ e ∈ Finset.univ.erase eₕ, legEntropyChange C e :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ eₕ)).symm
      _ = legEntropyChange C eₕ +
          (legEntropyChange C e_c +
            ∑ e ∈ (Finset.univ.erase eₕ).erase e_c,
              legEntropyChange C e) := by
        congr 1
        exact (Finset.add_sum_erase (Finset.univ.erase eₕ) _ hecMem).symm
      _ = legEntropyChange C eₕ + legEntropyChange C e_c := by
        rw [hremaining, add_zero]
  rw [hpairSum] at htotal
  exact eq_neg_of_add_eq_zero_left htotal

/-- Cross-multiplied reversible Carnot heat relation. -/
theorem reversibleCarnot_heat_relation {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    coherentCoordinate D.torus.unitSystem C.hotTemperature *
        coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) =
      coherentCoordinate D.torus.unitSystem C.coldTemperature *
        coherentCoordinate D.torus.unitSystem (hotHeatMagnitude C) := by
  classical
  rcases C.hotLegUnique with ⟨eₕ, hhot, hhotUnique⟩
  rcases C.coldLegUnique with ⟨e_c, hcold, hcoldUnique⟩
  have hhotEq : ∀ e, IsHotIsothermalLeg C e ↔ e = eₕ := by
    intro e
    constructor
    · exact hhotUnique e
    · rintro rfl
      exact hhot
  have hcoldEq : ∀ e, IsColdIsothermalLeg C e ↔ e = e_c := by
    intro e
    constructor
    · exact hcoldUnique e
    · rintro rfl
      exact hcold
  have hhotFilter :
      Finset.univ.filter (IsHotIsothermalLeg C) = {eₕ} := by
    ext e
    simp [hhotEq e]
  have hcoldFilter :
      Finset.univ.filter (IsColdIsothermalLeg C) = {e_c} := by
    ext e
    simp [hcoldEq e]
  have hhotMagnitude : hotHeatMagnitude C = -(C.leg eₕ).heat := by
    simp [hotHeatMagnitude, hhotFilter]
  have hcoldMagnitude : coldHeatMagnitude C = (C.leg e_c).heat := by
    simp [coldHeatMagnitude, hcoldFilter]
  have hcoordinateSub (x y : Entropy) :
      coherentCoordinate D.torus.unitSystem (x - y) =
        coherentCoordinate D.torus.unitSystem x -
          coherentCoordinate D.torus.unitSystem y := by
    simp [coherentCoordinate, coordinateInSI]
    ring
  have hcoordinateNeg {d : Dimension ISQDimensionBase} (x : Quantity d) :
      coherentCoordinate D.torus.unitSystem (-x) =
        -coherentCoordinate D.torus.unitSystem x := by
    simp [coherentCoordinate, coordinateInSI]
  have hhotDelta :
      coherentCoordinate D.torus.unitSystem (legEntropyChange C eₕ) =
        coherentCoordinate D.torus.unitSystem (C.entropy eₕ.finishVertex) -
          coherentCoordinate D.torus.unitSystem (C.entropy eₕ.startVertex) := by
    exact hcoordinateSub _ _
  have hcoldDelta :
      coherentCoordinate D.torus.unitSystem (legEntropyChange C e_c) =
        coherentCoordinate D.torus.unitSystem (C.entropy e_c.finishVertex) -
          coherentCoordinate D.torus.unitSystem (C.entropy e_c.startVertex) := by
    exact hcoordinateSub _ _
  have hhotLaw := C.hotEntropyHeatLaw eₕ hhot
  have hcoldLaw := C.coldEntropyHeatLaw e_c hcold
  rw [← hhotDelta] at hhotLaw
  rw [← hcoldDelta] at hcoldLaw
  have hentropy := (cycleEntropy_sum_eq_zero C).2 eₕ e_c hhot hcold
  have hentropyCoordinate :=
    congrArg (coherentCoordinate D.torus.unitSystem) hentropy
  rw [hcoordinateNeg] at hentropyCoordinate
  rw [hhotMagnitude, hcoldMagnitude, hcoordinateNeg, hcoldLaw, hhotLaw,
    hentropyCoordinate]
  ring

/-- Signed cycle heat is cold heat absorbed minus hot heat rejected. -/
lemma cycleSignedHeat_eq_cold_sub_hot {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    cycleSignedHeat C = coldHeatMagnitude C - hotHeatMagnitude C := by
  classical
  rcases C.hotLegUnique with ⟨eₕ, hhot, hhotUnique⟩
  rcases C.coldLegUnique with ⟨e_c, hcold, hcoldUnique⟩
  have hhotEq : ∀ e, IsHotIsothermalLeg C e → e = eₕ := hhotUnique
  have hcoldEq : ∀ e, IsColdIsothermalLeg C e → e = e_c := hcoldUnique
  have hne : eₕ ≠ e_c := by
    intro heq
    subst e_c
    exact (C.roleExactlyOne eₕ).2.1 ⟨hhot, hcold⟩
  have hadiHeatZero (e : CycleLeg) (hadi : IsAdiabaticCycleLeg C e) :
      (C.leg e).heat = 0 := by
    apply (coordinateInSI_eq_iff D.torus.unitSystem _ _).mp
    change coherentCoordinate D.torus.unitSystem (C.leg e).heat =
      coherentCoordinate D.torus.unitSystem (0 : Energy)
    simp only [ReversibleLeg.heat,
      coherentCoordinate_quantityFromCoherentCoordinate]
    have hab : (C.leg e).process.a < (C.leg e).process.b :=
      (C.leg e).isReversible.1.2.1
    have hintegral :
        (∫ t in (C.leg e).process.a..(C.leg e).process.b,
          coherentCoordinate D.torus.unitSystem
            ((C.leg e).process.heatIncrement t)) = 0 := by
      calc
        (∫ t in (C.leg e).process.a..(C.leg e).process.b,
            coherentCoordinate D.torus.unitSystem
              ((C.leg e).process.heatIncrement t)) =
            ∫ _t in (C.leg e).process.a..(C.leg e).process.b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hab.le] at ht
          exact hadi t ht
        _ = 0 := by simp
    simpa [coherentCoordinate, coordinateInSI] using hintegral
  have hzero (e : CycleLeg) (hehot : e ≠ eₕ) (hecold : e ≠ e_c) :
      (C.leg e).heat = 0 := by
    have hadi : IsAdiabaticCycleLeg C e := by
      rcases (C.roleExactlyOne e).1 with he | he | he
      · exact False.elim (hehot (hhotEq e he))
      · exact False.elim (hecold (hcoldEq e he))
      · exact he
    exact hadiHeatZero e hadi
  have hecMem : e_c ∈ (Finset.univ.erase eₕ : Finset CycleLeg) :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  have hremaining :
      (∑ e ∈ (Finset.univ.erase eₕ).erase e_c, (C.leg e).heat) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hecNe : e ≠ e_c := (Finset.mem_erase.mp he).1
    have hehotNe : e ≠ eₕ :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1
    exact hzero e hehotNe hecNe
  have hcycle : cycleSignedHeat C = (C.leg eₕ).heat + (C.leg e_c).heat := by
    unfold cycleSignedHeat
    calc
      (∑ e : CycleLeg, (C.leg e).heat) =
          (C.leg eₕ).heat + ∑ e ∈ Finset.univ.erase eₕ, (C.leg e).heat :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ eₕ)).symm
      _ = (C.leg eₕ).heat +
          ((C.leg e_c).heat +
            ∑ e ∈ (Finset.univ.erase eₕ).erase e_c, (C.leg e).heat) := by
        congr 1
        exact (Finset.add_sum_erase (Finset.univ.erase eₕ) _ hecMem).symm
      _ = (C.leg eₕ).heat + (C.leg e_c).heat := by
        rw [hremaining, add_zero]
  have hhotFilter :
      Finset.univ.filter (IsHotIsothermalLeg C) = {eₕ} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · exact hhotEq e
    · rintro rfl
      exact hhot
  have hcoldFilter :
      Finset.univ.filter (IsColdIsothermalLeg C) = {e_c} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · exact hcoldEq e
    · rintro rfl
      exact hcold
  rw [hcycle]
  simp [hotHeatMagnitude, coldHeatMagnitude, hhotFilter, hcoldFilter]
  abel

/-- Cold heat, rejected hot heat, and net input work are positive magnitudes. -/
theorem transferMagnitudes_pos {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    0 < coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) ∧
      0 < coherentCoordinate D.torus.unitSystem (hotHeatMagnitude C) ∧
      0 < coherentCoordinate D.torus.unitSystem (cycleWorkInput C) := by
  classical
  rcases C.coldLegUnique with ⟨e_c, hcold, hcoldUnique⟩
  have hcoldEq : ∀ e, IsColdIsothermalLeg C e ↔ e = e_c := by
    intro e
    constructor
    · exact hcoldUnique e
    · rintro rfl
      exact hcold
  have hcoldFilter :
      Finset.univ.filter (IsColdIsothermalLeg C) = {e_c} := by
    ext e
    simp [hcoldEq e]
  have hcoldMagnitude : coldHeatMagnitude C = (C.leg e_c).heat := by
    simp [coldHeatMagnitude, hcoldFilter]
  have hcoldLaw := C.coldEntropyHeatLaw e_c hcold
  have hcoldEntropy := C.coldEntropyIncreases e_c hcold
  have hcoldPositive :
      0 < coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) := by
    rw [hcoldMagnitude, hcoldLaw]
    exact mul_pos C.temperatureOrder.1 (sub_pos.mpr hcoldEntropy)
  have hhotTemperaturePositive :
      0 < coherentCoordinate D.torus.unitSystem C.hotTemperature :=
    lt_trans C.temperatureOrder.1 C.temperatureOrder.2
  have hcarnot := reversibleCarnot_heat_relation C
  have hhotPositive :
      0 < coherentCoordinate D.torus.unitSystem (hotHeatMagnitude C) := by
    have hleftPositive :
        0 < coherentCoordinate D.torus.unitSystem C.hotTemperature *
          coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) :=
      mul_pos hhotTemperaturePositive hcoldPositive
    have hrightPositive :
        0 < coherentCoordinate D.torus.unitSystem C.coldTemperature *
          coherentCoordinate D.torus.unitSystem (hotHeatMagnitude C) := by
      rwa [← hcarnot]
    rcases mul_pos_iff.mp hrightPositive with hpositive | hnegative
    · exact hpositive.2
    · exact False.elim ((not_lt_of_ge C.temperatureOrder.1.le) hnegative.1)
  have hhotGreater :
      coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) <
        coherentCoordinate D.torus.unitSystem (hotHeatMagnitude C) := by
    have hmul :
        coherentCoordinate D.torus.unitSystem C.coldTemperature *
          coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) <
        coherentCoordinate D.torus.unitSystem C.hotTemperature *
          coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) :=
      mul_lt_mul_of_pos_right C.temperatureOrder.2 hcoldPositive
    have hmul' :
        coherentCoordinate D.torus.unitSystem C.coldTemperature *
            coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) <
          coherentCoordinate D.torus.unitSystem C.coldTemperature *
            coherentCoordinate D.torus.unitSystem (hotHeatMagnitude C) := by
      calc
        _ < coherentCoordinate D.torus.unitSystem C.hotTemperature *
            coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) := hmul
        _ = _ := hcarnot
    exact lt_of_mul_lt_mul_left hmul' C.temperatureOrder.1.le
  have hcoordinateAdd (x y : Energy) :
      coherentCoordinate D.torus.unitSystem (x + y) =
        coherentCoordinate D.torus.unitSystem x +
          coherentCoordinate D.torus.unitSystem y := by
    simp [coherentCoordinate, coordinateInSI]
    ring
  have hcoordinateSub (x y : Energy) :
      coherentCoordinate D.torus.unitSystem (x - y) =
        coherentCoordinate D.torus.unitSystem x -
          coherentCoordinate D.torus.unitSystem y := by
    simp [coherentCoordinate, coordinateInSI]
    ring
  have hcoordinateZero :
      coherentCoordinate D.torus.unitSystem (0 : Energy) = 0 := by
    simp [coherentCoordinate, coordinateInSI]
  have hbalance := cycle_heat_work_balance C
  rw [cycleSignedHeat_eq_cold_sub_hot C] at hbalance
  have hbalanceCoordinate :=
    congrArg (coherentCoordinate D.torus.unitSystem) hbalance
  rw [hcoordinateAdd, hcoordinateSub, hcoordinateZero] at hbalanceCoordinate
  have hworkPositive :
      0 < coherentCoordinate D.torus.unitSystem (cycleWorkInput C) := by
    linarith
  exact ⟨hcoldPositive, hhotPositive, hworkPositive⟩

/-- Positive-magnitude first-law balance. -/
theorem cycle_magnitude_balance {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    hotHeatMagnitude C = coldHeatMagnitude C + cycleWorkInput C := by
  have hbalance := cycle_heat_work_balance C
  rw [cycleSignedHeat_eq_cold_sub_hot C] at hbalance
  calc
    hotHeatMagnitude C = hotHeatMagnitude C + 0 := (add_zero _).symm
    _ = hotHeatMagnitude C +
        (coldHeatMagnitude C - hotHeatMagnitude C + cycleWorkInput C) := by
      rw [hbalance]
    _ = coldHeatMagnitude C + cycleWorkInput C := by abel

/-- Cross-multiplied relation between input work and cold heat. -/
theorem work_cold_Carnot_relation {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    (coherentCoordinate D.torus.unitSystem C.hotTemperature -
        coherentCoordinate D.torus.unitSystem C.coldTemperature) *
          coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) =
      coherentCoordinate D.torus.unitSystem C.coldTemperature *
        coherentCoordinate D.torus.unitSystem (cycleWorkInput C) := by
  have hcoordinateAdd (x y : Energy) :
      coherentCoordinate D.torus.unitSystem (x + y) =
        coherentCoordinate D.torus.unitSystem x +
          coherentCoordinate D.torus.unitSystem y := by
    simp [coherentCoordinate, coordinateInSI]
    ring
  have hmagnitude := congrArg (coherentCoordinate D.torus.unitSystem)
    (cycle_magnitude_balance C)
  rw [hcoordinateAdd] at hmagnitude
  have hcarnot := reversibleCarnot_heat_relation C
  rw [hmagnitude] at hcarnot
  nlinarith

/-! ## Answer-free diagram annotations -/

/-- An unordered two-vertex diagram column. -/
def DiagramColumn :=
  {vertices : Finset CycleVertex // vertices.card = 2}

/-- The unordered endpoint column of a leg. -/
def legColumn (e : CycleLeg) : DiagramColumn :=
  ⟨{e.startVertex, e.finishVertex}, by cases e <;> decide⟩

/-- Candidate labels for both reservoir columns and both heat-transfer legs. -/
structure DiagramAnnotation where
  hotColumn : DiagramColumn
  coldColumn : DiagramColumn
  hotDeliveryLeg : CycleLeg
  coldAbsorptionLeg : CycleLeg

/-- Correctness of a complete candidate annotation. -/
def IsCompleteDiagramAnnotation {D : ParamagneticData}
    (C : ComposedFourLegCycle D) (A : DiagramAnnotation) : Prop :=
  IsHotIsothermalLeg C A.hotDeliveryLeg ∧
  IsColdIsothermalLeg C A.coldAbsorptionLeg ∧
  A.hotColumn = legColumn A.hotDeliveryLeg ∧
  A.coldColumn = legColumn A.coldAbsorptionLeg ∧
  (∀ v ∈ A.hotColumn.1,
    (C.state v).temperature = C.hotTemperature) ∧
  (∀ v ∈ A.coldColumn.1,
    (C.state v).temperature = C.coldTemperature) ∧
  A.hotDeliveryLeg ≠ A.coldAbsorptionLeg ∧
  A.hotColumn.1 ∩ A.coldColumn.1 = ∅ ∧
  A.hotColumn.1 ∪ A.coldColumn.1 = Finset.univ ∧
  (∀ e,
    (IsHotIsothermalLeg C e ∨ IsColdIsothermalLeg C e ↔
      e = A.hotDeliveryLeg ∨ e = A.coldAbsorptionLeg) ∧
    (IsAdiabaticCycleLeg C e ↔
      e ≠ A.hotDeliveryLeg ∧ e ≠ A.coldAbsorptionLeg)) ∧
  (∀ e,
    (coherentCoordinate D.torus.unitSystem (C.leg e).heat ≠ 0 ↔
      e = A.hotDeliveryLeg ∨ e = A.coldAbsorptionLeg)) ∧
  coherentCoordinate D.torus.unitSystem
      (C.leg A.hotDeliveryLeg).heat < 0 ∧
  0 < coherentCoordinate D.torus.unitSystem
      (C.leg A.coldAbsorptionLeg).heat

/-- A complete correct annotation exists uniquely, without selecting a fixed
enumerated edge or a left/right column in the theorem statement. -/
theorem completeDiagramAnnotation_existsUnique {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    ∃! A : DiagramAnnotation, IsCompleteDiagramAnnotation C A := by
  classical
  rcases C.hotLegUnique with ⟨eₕ, hhot, hhotUnique⟩
  rcases C.coldLegUnique with ⟨e_c, hcold, hcoldUnique⟩
  have hhotEq : ∀ e, IsHotIsothermalLeg C e → e = eₕ := hhotUnique
  have hcoldEq : ∀ e, IsColdIsothermalLeg C e → e = e_c := hcoldUnique
  have hne : eₕ ≠ e_c := by
    intro heq
    subst e_c
    exact (C.roleExactlyOne eₕ).2.1 ⟨hhot, hcold⟩
  have endpointTemperatures (e : CycleLeg) (T : Temperature)
      (hiso : IsIsothermal D (C.leg e).process T) :
      (C.state e.startVertex).temperature = T ∧
        (C.state e.finishVertex).temperature = T := by
    have hab : (C.leg e).process.a < (C.leg e).process.b :=
      (C.leg e).isReversible.1.2.1
    have hstart := hiso.2 (C.leg e).process.a ⟨le_rfl, hab.le⟩
    have hfinish := hiso.2 (C.leg e).process.b ⟨hab.le, le_rfl⟩
    have hs := C.legStarts e
    have hf := C.legFinishes e
    unfold StartsAt at hs
    unfold FinishesAt at hf
    rw [hs] at hstart
    rw [hf] at hfinish
    exact ⟨hstart, hfinish⟩
  have hhotEndpoints := endpointTemperatures eₕ C.hotTemperature hhot
  have hcoldEndpoints := endpointTemperatures e_c C.coldTemperature hcold
  have hcolumns :=
    (thermalRole_partition C).2.2.2.2 eₕ e_c hhot hcold
  have hhotVertices : ∀ v ∈ (legColumn eₕ).1,
      (C.state v).temperature = C.hotTemperature := by
    intro v hv
    simp only [legColumn, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hhotEndpoints.1
    · exact hhotEndpoints.2
  have hcoldVertices : ∀ v ∈ (legColumn e_c).1,
      (C.state v).temperature = C.coldTemperature := by
    intro v hv
    simp only [legColumn, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hcoldEndpoints.1
    · exact hcoldEndpoints.2
  have hroles : ∀ e,
      (IsHotIsothermalLeg C e ∨ IsColdIsothermalLeg C e ↔
          e = eₕ ∨ e = e_c) ∧
        (IsAdiabaticCycleLeg C e ↔ e ≠ eₕ ∧ e ≠ e_c) := by
    intro e
    constructor
    · constructor
      · rintro (he | he)
        · exact Or.inl (hhotEq e he)
        · exact Or.inr (hcoldEq e he)
      · rintro (rfl | rfl)
        · exact Or.inl hhot
        · exact Or.inr hcold
    · constructor
      · intro hadi
        constructor
        · intro he
          subst e
          exact (C.roleExactlyOne eₕ).2.2.1 ⟨hhot, hadi⟩
        · intro he
          subst e
          exact (C.roleExactlyOne e_c).2.2.2 ⟨hcold, hadi⟩
      · rintro ⟨hehot, hecold⟩
        rcases (C.roleExactlyOne e).1 with he | he | he
        · exact False.elim (hehot (hhotEq e he))
        · exact False.elim (hecold (hcoldEq e he))
        · exact he
  have hadiHeatZero (e : CycleLeg) (hadi : IsAdiabaticCycleLeg C e) :
      (C.leg e).heat = 0 := by
    apply (coordinateInSI_eq_iff D.torus.unitSystem _ _).mp
    change coherentCoordinate D.torus.unitSystem (C.leg e).heat =
      coherentCoordinate D.torus.unitSystem (0 : Energy)
    simp only [ReversibleLeg.heat,
      coherentCoordinate_quantityFromCoherentCoordinate]
    have hab : (C.leg e).process.a < (C.leg e).process.b :=
      (C.leg e).isReversible.1.2.1
    have hintegral :
        (∫ t in (C.leg e).process.a..(C.leg e).process.b,
          coherentCoordinate D.torus.unitSystem
            ((C.leg e).process.heatIncrement t)) = 0 := by
      calc
        (∫ t in (C.leg e).process.a..(C.leg e).process.b,
            coherentCoordinate D.torus.unitSystem
              ((C.leg e).process.heatIncrement t)) =
            ∫ _t in (C.leg e).process.a..(C.leg e).process.b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hab.le] at ht
          exact hadi t ht
        _ = 0 := by simp
    simpa [coherentCoordinate, coordinateInSI] using hintegral
  have hhotFilter :
      Finset.univ.filter (IsHotIsothermalLeg C) = {eₕ} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · exact hhotEq e
    · rintro rfl
      exact hhot
  have hcoldFilter :
      Finset.univ.filter (IsColdIsothermalLeg C) = {e_c} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · exact hcoldEq e
    · rintro rfl
      exact hcold
  have hhotMagnitude : hotHeatMagnitude C = -(C.leg eₕ).heat := by
    simp [hotHeatMagnitude, hhotFilter]
  have hcoldMagnitude : coldHeatMagnitude C = (C.leg e_c).heat := by
    simp [coldHeatMagnitude, hcoldFilter]
  have hcoordinateNeg (x : Energy) :
      coherentCoordinate D.torus.unitSystem (-x) =
        -coherentCoordinate D.torus.unitSystem x := by
    simp [coherentCoordinate, coordinateInSI]
  have htransfers := transferMagnitudes_pos C
  have hhotNegative :
      coherentCoordinate D.torus.unitSystem (C.leg eₕ).heat < 0 := by
    have hh := htransfers.2.1
    rw [hhotMagnitude, hcoordinateNeg] at hh
    linarith
  have hcoldPositive :
      0 < coherentCoordinate D.torus.unitSystem (C.leg e_c).heat := by
    simpa [hcoldMagnitude] using htransfers.1
  have hheatIff : ∀ e,
      (coherentCoordinate D.torus.unitSystem (C.leg e).heat ≠ 0 ↔
        e = eₕ ∨ e = e_c) := by
    intro e
    constructor
    · intro hnonzero
      rcases (C.roleExactlyOne e).1 with he | he | he
      · exact Or.inl (hhotEq e he)
      · exact Or.inr (hcoldEq e he)
      · exfalso
        apply hnonzero
        rw [hadiHeatZero e he]
        simp [coherentCoordinate, coordinateInSI]
    · rintro (rfl | rfl)
      · exact ne_of_lt hhotNegative
      · exact ne_of_gt hcoldPositive
  let A : DiagramAnnotation :=
    { hotColumn := legColumn eₕ
      coldColumn := legColumn e_c
      hotDeliveryLeg := eₕ
      coldAbsorptionLeg := e_c }
  refine ⟨A, ?_, ?_⟩
  · exact ⟨hhot, hcold, rfl, rfl, hhotVertices, hcoldVertices, hne,
      hcolumns.1, hcolumns.2, hroles, hheatIff, hhotNegative, hcoldPositive⟩
  · intro A' hA'
    have hhotLeg : A'.hotDeliveryLeg = eₕ := hhotEq _ hA'.1
    have hcoldLeg : A'.coldAbsorptionLeg = e_c := hcoldEq _ hA'.2.1
    rcases A' with ⟨hotColumn, coldColumn, hotLeg, coldLeg⟩
    dsimp at hhotLeg hcoldLeg hA' ⊢
    subst hotLeg
    subst coldLeg
    rcases hA' with ⟨_, _, hhotColumn, hcoldColumn, _⟩
    change hotColumn = legColumn eₕ at hhotColumn
    change coldColumn = legColumn e_c at hcoldColumn
    subst hotColumn
    subst coldColumn
    rfl

/-! ## Adiabatic invariant and four-state magnetization composition -/

/-- Coherent-coordinate adiabatic invariant candidate in temperature and
magnetization.  No endpoint magnetization is selected by this definition. -/
def adiabaticInvariantCoordinate (D : ParamagneticData)
    (T : Temperature) (M : Magnetization) : ℝ :=
  1 / coherentCoordinate D.torus.unitSystem T ^ 2 +
    (coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
          coherentCoordinate D.torus.unitSystem D.torus.volume ^ 2 /
        (coherentCoordinate D.torus.unitSystem D.material.amount ^ 2 *
          coherentCoordinate D.torus.unitSystem D.material.curieParameter *
          coherentCoordinate D.torus.unitSystem
            D.material.heatCapacityCoefficient)) *
      coherentCoordinate D.torus.unitSystem M ^ 2

/-- The invariant has zero derivative along every reversible adiabatic leg. -/
lemma adiabaticInvariant_deriv_eq_zero (D : ParamagneticData)
    (L : ReversibleLeg D) (hadiabatic : IsAdiabatic D L.process) :
    ∀ τ ∈ Set.Icc L.process.a L.process.b,
      deriv
        (fun t => adiabaticInvariantCoordinate D
          (L.process.state t).temperature
          (L.process.state t).magnetization) τ = 0 := by
  intro τ hτ
  rcases L.isReversible with
    ⟨hregular, hAmpere, hFaraday, hsourceBalance, hsourceWork,
      hinternalEnergy, hfirstLaw⟩
  have hregular' := hregular
  rcases hregular with
    ⟨hD, _, ⟨neighborhood, hopen, hIcc, hT, _, hM, _, _⟩,
      _, _, _, _, hstate⟩
  have hτn : τ ∈ neighborhood := hIcc hτ
  let temperature : ℝ → ℝ := fun t =>
    coherentCoordinate D.torus.unitSystem (L.process.state t).temperature
  let magnetization : ℝ → ℝ := fun t =>
    coherentCoordinate D.torus.unitSystem (L.process.state t).magnetization
  let field : ℝ := coherentCoordinate D.torus.unitSystem
    (L.process.state τ).fieldStrength
  let amount : ℝ := coherentCoordinate D.torus.unitSystem D.material.amount
  let curie : ℝ := coherentCoordinate D.torus.unitSystem D.material.curieParameter
  let lambda : ℝ := coherentCoordinate D.torus.unitSystem
    D.material.heatCapacityCoefficient
  let permeability : ℝ := coherentCoordinate D.torus.unitSystem
    D.material.vacuumPermeability
  let volumeCoordinate : ℝ := coherentCoordinate D.torus.unitSystem D.torus.volume
  let coefficient : ℝ := permeability * volumeCoordinate ^ 2 /
    (amount ^ 2 * curie * lambda)
  have htemperature : 0 < temperature τ := by
    exact (hstate τ hτ).1.1
  have hamount : 0 < amount := hD.2.2.1
  have hcurie : 0 < curie := hD.2.2.2.1
  have hlambda : 0 < lambda := hD.2.2.2.2
  have hpermeability : 0 < permeability := hD.2.1
  have hvolume : 0 < volumeCoordinate := hD.1.2.2.2.1
  have htemperatureDiff : DifferentiableAt ℝ temperature τ :=
    (hT.differentiableOn_one τ hτn).differentiableAt (hopen.mem_nhds hτn)
  have hmagnetizationDiff : DifferentiableAt ℝ magnetization τ :=
    (hM.differentiableOn_one τ hτn).differentiableAt (hopen.mem_nhds hτn)
  have hmaterial :=
    (source_vacuum_material_work_decomposition D L.process hregular'
      hAmpere hFaraday hsourceBalance hsourceWork τ hτ).2
  have henergy :
      (amount * lambda / temperature τ ^ 2) * deriv temperature τ =
        permeability * volumeCoordinate * field * deriv magnetization τ := by
    calc
      (amount * lambda / temperature τ ^ 2) * deriv temperature τ =
          internalEnergyDifferential D L.process τ := by
        simp only [internalEnergyDifferential,
          heatCapacityAtConstantMagnetization,
          coherentCoordinate_quantityFromCoherentCoordinate]
        rfl
      _ = deriv
          (fun t => coherentCoordinate D.torus.unitSystem
            (L.process.internalEnergy t)) τ := (hinternalEnergy τ hτ).symm
      _ = coherentCoordinate D.torus.unitSystem (L.process.heatIncrement τ) +
          coherentCoordinate D.torus.unitSystem
            (materialWorkIncrement D L.process τ) := hfirstLaw τ hτ
      _ = permeability * volumeCoordinate * field *
          deriv magnetization τ := by
        rw [hadiabatic τ hτ, hmaterial]
        simp only [zero_add]
        rfl
  have hequation :
      temperature τ * magnetization τ * volumeCoordinate =
        amount * curie * field := by
    exact (hstate τ hτ).2
  have henergyPolynomial :
      amount * lambda * deriv temperature τ =
        permeability * volumeCoordinate * field *
          deriv magnetization τ * temperature τ ^ 2 := by
    calc
      amount * lambda * deriv temperature τ =
          ((amount * lambda / temperature τ ^ 2) *
            deriv temperature τ) * temperature τ ^ 2 := by
        field_simp [ne_of_gt htemperature]
      _ = (permeability * volumeCoordinate * field *
          deriv magnetization τ) * temperature τ ^ 2 := by rw [henergy]
  have hcombined :
      amount ^ 2 * curie * lambda * deriv temperature τ =
        permeability * volumeCoordinate ^ 2 * magnetization τ *
          deriv magnetization τ * temperature τ ^ 3 := by
    calc
      amount ^ 2 * curie * lambda * deriv temperature τ =
          (amount * lambda * deriv temperature τ) * (amount * curie) := by ring
      _ = (permeability * volumeCoordinate * field *
          deriv magnetization τ * temperature τ ^ 2) *
            (amount * curie) := by rw [henergyPolynomial]
      _ = permeability * volumeCoordinate *
          (amount * curie * field) * deriv magnetization τ *
            temperature τ ^ 2 := by ring
      _ = permeability * volumeCoordinate *
          (temperature τ * magnetization τ * volumeCoordinate) *
            deriv magnetization τ * temperature τ ^ 2 := by rw [← hequation]
      _ = permeability * volumeCoordinate ^ 2 * magnetization τ *
          deriv magnetization τ * temperature τ ^ 3 := by ring
  have hlocal :
      deriv temperature τ / temperature τ ^ 3 =
        coefficient * magnetization τ * deriv magnetization τ := by
    dsimp [coefficient]
    field_simp [ne_of_gt htemperature, ne_of_gt hamount, ne_of_gt hcurie,
      ne_of_gt hlambda]
    nlinarith only [hcombined]
  have htemperatureTerm :
      HasDerivAt (fun t => 1 / temperature t ^ 2)
        (-2 * deriv temperature τ / temperature τ ^ 3) τ := by
    have hpower : HasDerivAt (temperature ^ 2)
        (2 * temperature τ * deriv temperature τ) τ := by
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
        htemperatureDiff.hasDerivAt.pow 2
    have hinverse := hpower.inv (pow_ne_zero 2 (ne_of_gt htemperature))
    have hinversePointwise :
        HasDerivAt (fun t => 1 / temperature t ^ 2)
          (-(2 * temperature τ * deriv temperature τ) /
            (temperature τ ^ 2) ^ 2) τ := by
      apply hinverse.congr_of_eventuallyEq
      filter_upwards [] with t
      simp only [Pi.inv_apply, Pi.pow_apply, one_div]
    apply hinversePointwise.congr_deriv
    field_simp [ne_of_gt htemperature]
  have hmagnetizationTerm :
      HasDerivAt (fun t => coefficient * magnetization t ^ 2)
        (coefficient * (2 * magnetization τ * deriv magnetization τ)) τ := by
    have hpower : HasDerivAt (magnetization ^ 2)
        (2 * magnetization τ * deriv magnetization τ) τ := by
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
        hmagnetizationDiff.hasDerivAt.pow 2
    have hscaled := hpower.const_mul coefficient
    apply hscaled.congr_of_eventuallyEq
    filter_upwards [] with t
    simp only [Pi.pow_apply]
  have hinvariant : HasDerivAt
      (fun t => 1 / temperature t ^ 2 + coefficient * magnetization t ^ 2)
      (-2 * deriv temperature τ / temperature τ ^ 3 +
        coefficient * (2 * magnetization τ * deriv magnetization τ)) τ := by
    have hsum := htemperatureTerm.add hmagnetizationTerm
    apply hsum.congr_of_eventuallyEq
    filter_upwards [] with t
    rfl
  change deriv
    (fun t => 1 / temperature t ^ 2 + coefficient * magnetization t ^ 2) τ = 0
  rw [hinvariant.deriv]
  calc
    -2 * deriv temperature τ / temperature τ ^ 3 +
          coefficient * (2 * magnetization τ * deriv magnetization τ) =
        -2 * (deriv temperature τ / temperature τ ^ 3) +
          2 * (coefficient * magnetization τ * deriv magnetization τ) := by ring
    _ = 0 := by rw [hlocal]; ring

/-- Endpoint form of the adiabatic invariant for prescribed full states. -/
theorem adiabaticInvariant_endpoint (D : ParamagneticData)
    (L : ReversibleLeg D) (initial final : EquilibriumState)
    (hendpoints : HasEndpoints L.process initial final)
    (hadiabatic : IsAdiabatic D L.process) :
    adiabaticInvariantCoordinate D initial.temperature initial.magnetization =
      adiabaticInvariantCoordinate D final.temperature final.magnetization := by
  rcases L.isReversible.1 with
    ⟨_, hab, ⟨neighborhood, hopen, hIcc, hT, _, hM, _, _⟩,
      _, _, _, _, hstate⟩
  let invariant : ℝ → ℝ := fun t =>
    adiabaticInvariantCoordinate D (L.process.state t).temperature
      (L.process.state t).magnetization
  have hinvariantDifferentiable :
      DifferentiableOn ℝ invariant (Set.Icc L.process.a L.process.b) := by
    intro t ht
    have htn : t ∈ neighborhood := hIcc ht
    have hTdiff : DifferentiableAt ℝ
        (fun x => coherentCoordinate D.torus.unitSystem
          (L.process.state x).temperature) t :=
      (hT.differentiableOn_one t htn).differentiableAt (hopen.mem_nhds htn)
    have hMdiff : DifferentiableAt ℝ
        (fun x => coherentCoordinate D.torus.unitSystem
          (L.process.state x).magnetization) t :=
      (hM.differentiableOn_one t htn).differentiableAt (hopen.mem_nhds htn)
    have hTne : coherentCoordinate D.torus.unitSystem
        (L.process.state t).temperature ≠ 0 := ne_of_gt (hstate t ht).1.1
    have hfirst : DifferentiableAt ℝ
        (fun x => 1 /
          coherentCoordinate D.torus.unitSystem
            (L.process.state x).temperature ^ 2) t := by
      have hinverse := (hTdiff.pow 2).inv (pow_ne_zero 2 hTne)
      apply hinverse.congr_of_eventuallyEq
      filter_upwards [] with x
      simp only [Pi.inv_apply, Pi.pow_apply, one_div]
    have hsecond : DifferentiableAt ℝ
        (fun x =>
          (coherentCoordinate D.torus.unitSystem
                D.material.vacuumPermeability *
              coherentCoordinate D.torus.unitSystem D.torus.volume ^ 2 /
            (coherentCoordinate D.torus.unitSystem D.material.amount ^ 2 *
              coherentCoordinate D.torus.unitSystem D.material.curieParameter *
              coherentCoordinate D.torus.unitSystem
                D.material.heatCapacityCoefficient)) *
            coherentCoordinate D.torus.unitSystem
              (L.process.state x).magnetization ^ 2) t :=
      (hMdiff.pow 2).const_mul _
    exact (hfirst.add hsecond).differentiableWithinAt
  have hderivWithin : ∀ t ∈ Set.Ico L.process.a L.process.b,
      derivWithin invariant (Set.Icc L.process.a L.process.b) t = 0 := by
    intro t ht
    have htIcc : t ∈ Set.Icc L.process.a L.process.b := ⟨ht.1, ht.2.le⟩
    have htn : t ∈ neighborhood := hIcc htIcc
    have hTdiff : DifferentiableAt ℝ
        (fun x => coherentCoordinate D.torus.unitSystem
          (L.process.state x).temperature) t :=
      (hT.differentiableOn_one t htn).differentiableAt (hopen.mem_nhds htn)
    have hMdiff : DifferentiableAt ℝ
        (fun x => coherentCoordinate D.torus.unitSystem
          (L.process.state x).magnetization) t :=
      (hM.differentiableOn_one t htn).differentiableAt (hopen.mem_nhds htn)
    have hTne : coherentCoordinate D.torus.unitSystem
        (L.process.state t).temperature ≠ 0 := ne_of_gt (hstate t htIcc).1.1
    have hfirst : DifferentiableAt ℝ
        (fun x => 1 /
          coherentCoordinate D.torus.unitSystem
            (L.process.state x).temperature ^ 2) t := by
      have hinverse := (hTdiff.pow 2).inv (pow_ne_zero 2 hTne)
      apply hinverse.congr_of_eventuallyEq
      filter_upwards [] with x
      simp only [Pi.inv_apply, Pi.pow_apply, one_div]
    have hsecond : DifferentiableAt ℝ
        (fun x =>
          (coherentCoordinate D.torus.unitSystem
                D.material.vacuumPermeability *
              coherentCoordinate D.torus.unitSystem D.torus.volume ^ 2 /
            (coherentCoordinate D.torus.unitSystem D.material.amount ^ 2 *
              coherentCoordinate D.torus.unitSystem D.material.curieParameter *
              coherentCoordinate D.torus.unitSystem
                D.material.heatCapacityCoefficient)) *
            coherentCoordinate D.torus.unitSystem
              (L.process.state x).magnetization ^ 2) t :=
      (hMdiff.pow 2).const_mul _
    have hinvariantAt : DifferentiableAt ℝ invariant t := hfirst.add hsecond
    rw [hinvariantAt.derivWithin ((uniqueDiffOn_Icc hab) t htIcc)]
    exact adiabaticInvariant_deriv_eq_zero D L hadiabatic t htIcc
  have hconstant := constant_of_derivWithin_zero hinvariantDifferentiable hderivWithin
  have hend := hconstant L.process.b ⟨hab.le, le_rfl⟩
  rcases hendpoints with ⟨hstart, hfinish⟩
  unfold StartsAt at hstart
  unfold FinishesAt at hfinish
  rw [← hstart, ← hfinish]
  change invariant L.process.a = invariant L.process.b
  exact hend.symm

/-- An ordered pair of adiabatic legs directed respectively from hot to cold
and from cold to hot. -/
def OpposedAdiabaticPair {D : ParamagneticData}
    (C : ComposedFourLegCycle D) (pair : CycleLeg × CycleLeg) : Prop :=
  pair.1 ≠ pair.2 ∧
  IsAdiabaticCycleLeg C pair.1 ∧
  IsAdiabaticCycleLeg C pair.2 ∧
  (C.state pair.1.startVertex).temperature = C.hotTemperature ∧
  (C.state pair.1.finishVertex).temperature = C.coldTemperature ∧
  (C.state pair.2.startVertex).temperature = C.coldTemperature ∧
  (C.state pair.2.finishVertex).temperature = C.hotTemperature

/-- The two adiabatic legs have uniquely determined opposite temperature
directions. -/
lemma opposedAdiabaticPair_existsUnique {D : ParamagneticData}
    (C : ComposedFourLegCycle D) :
    ∃! pair : CycleLeg × CycleLeg, OpposedAdiabaticPair C pair := by
  classical
  rcases C.hotLegUnique with ⟨eₕ, hhot, hhotUnique⟩
  rcases C.coldLegUnique with ⟨e_c, hcold, hcoldUnique⟩
  have hhotEq : ∀ e, IsHotIsothermalLeg C e → e = eₕ := hhotUnique
  have hcoldEq : ∀ e, IsColdIsothermalLeg C e → e = e_c := hcoldUnique
  have hadiIff : ∀ e, IsAdiabaticCycleLeg C e ↔ e ≠ eₕ ∧ e ≠ e_c := by
    intro e
    constructor
    · intro hadi
      constructor
      · intro he
        subst e
        exact (C.roleExactlyOne eₕ).2.2.1 ⟨hhot, hadi⟩
      · intro he
        subst e
        exact (C.roleExactlyOne e_c).2.2.2 ⟨hcold, hadi⟩
    · rintro ⟨hehot, hecold⟩
      rcases (C.roleExactlyOne e).1 with he | he | he
      · exact False.elim (hehot (hhotEq e he))
      · exact False.elim (hecold (hcoldEq e he))
      · exact he
  have endpointTemperatures (e : CycleLeg) (T : Temperature)
      (hiso : IsIsothermal D (C.leg e).process T) :
      (C.state e.startVertex).temperature = T ∧
        (C.state e.finishVertex).temperature = T := by
    have hab : (C.leg e).process.a < (C.leg e).process.b :=
      (C.leg e).isReversible.1.2.1
    have hstart := hiso.2 (C.leg e).process.a ⟨le_rfl, hab.le⟩
    have hfinish := hiso.2 (C.leg e).process.b ⟨hab.le, le_rfl⟩
    have hs := C.legStarts e
    have hf := C.legFinishes e
    unfold StartsAt at hs
    unfold FinishesAt at hf
    rw [hs] at hstart
    rw [hf] at hfinish
    exact ⟨hstart, hfinish⟩
  have hhotEndpoints := endpointTemperatures eₕ C.hotTemperature hhot
  have hcoldEndpoints := endpointTemperatures e_c C.coldTemperature hcold
  have hcoldNeHot : C.coldTemperature ≠ C.hotTemperature := by
    intro heq
    have hlt := C.temperatureOrder.2
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  have hcolumns :=
    (thermalRole_partition C).2.2.2.2 eₕ e_c hhot hcold
  cases eₕ <;> cases e_c <;>
    simp [CycleLeg.startVertex, CycleLeg.finishVertex] at hcolumns
  · refine ⟨(.e1, .e3), ?_, ?_⟩
    · exact ⟨by decide, (hadiIff .e1).2 (by decide),
        (hadiIff .e3).2 (by decide), hhotEndpoints.2,
        hcoldEndpoints.1, hcoldEndpoints.2, hhotEndpoints.1⟩
    · rintro ⟨a, b⟩ hp
      rcases hp with ⟨hab, ha, hb, haStart, _, _, _⟩
      have haNe := (hadiIff a).1 ha
      have hbNe := (hadiIff b).1 hb
      have haCases : a = .e1 ∨ a = .e3 := by
        cases a with
        | e0 => exact (haNe.1 rfl).elim
        | e1 => exact Or.inl rfl
        | e2 => exact (haNe.2 rfl).elim
        | e3 => exact Or.inr rfl
      have hbCases : b = .e1 ∨ b = .e3 := by
        cases b with
        | e0 => exact (hbNe.1 rfl).elim
        | e1 => exact Or.inl rfl
        | e2 => exact (hbNe.2 rfl).elim
        | e3 => exact Or.inr rfl
      rcases haCases with rfl | rfl <;> rcases hbCases with rfl | rfl
      · exact (hab rfl).elim
      · rfl
      · exact (hcoldNeHot (hcoldEndpoints.2.symm.trans haStart)).elim
      · exact (hab rfl).elim
  · refine ⟨(.e2, .e0), ?_, ?_⟩
    · exact ⟨by decide, (hadiIff .e2).2 (by decide),
        (hadiIff .e0).2 (by decide), hhotEndpoints.2,
        hcoldEndpoints.1, hcoldEndpoints.2, hhotEndpoints.1⟩
    · rintro ⟨a, b⟩ hp
      rcases hp with ⟨hab, ha, hb, haStart, _, _, _⟩
      have haNe := (hadiIff a).1 ha
      have hbNe := (hadiIff b).1 hb
      have haCases : a = .e0 ∨ a = .e2 := by
        cases a with
        | e0 => exact Or.inl rfl
        | e1 => exact (haNe.1 rfl).elim
        | e2 => exact Or.inr rfl
        | e3 => exact (haNe.2 rfl).elim
      have hbCases : b = .e0 ∨ b = .e2 := by
        cases b with
        | e0 => exact Or.inl rfl
        | e1 => exact (hbNe.1 rfl).elim
        | e2 => exact Or.inr rfl
        | e3 => exact (hbNe.2 rfl).elim
      rcases haCases with rfl | rfl <;> rcases hbCases with rfl | rfl
      · exact (hab rfl).elim
      · exact (hcoldNeHot (hcoldEndpoints.2.symm.trans haStart)).elim
      · rfl
      · exact (hab rfl).elim
  · refine ⟨(.e3, .e1), ?_, ?_⟩
    · exact ⟨by decide, (hadiIff .e3).2 (by decide),
        (hadiIff .e1).2 (by decide), hhotEndpoints.2,
        hcoldEndpoints.1, hcoldEndpoints.2, hhotEndpoints.1⟩
    · rintro ⟨a, b⟩ hp
      rcases hp with ⟨hab, ha, hb, haStart, _, _, _⟩
      have haNe := (hadiIff a).1 ha
      have hbNe := (hadiIff b).1 hb
      have haCases : a = .e1 ∨ a = .e3 := by
        cases a with
        | e0 => exact (haNe.2 rfl).elim
        | e1 => exact Or.inl rfl
        | e2 => exact (haNe.1 rfl).elim
        | e3 => exact Or.inr rfl
      have hbCases : b = .e1 ∨ b = .e3 := by
        cases b with
        | e0 => exact (hbNe.2 rfl).elim
        | e1 => exact Or.inl rfl
        | e2 => exact (hbNe.1 rfl).elim
        | e3 => exact Or.inr rfl
      rcases haCases with rfl | rfl <;> rcases hbCases with rfl | rfl
      · exact (hab rfl).elim
      · exact (hcoldNeHot (hcoldEndpoints.2.symm.trans haStart)).elim
      · rfl
      · exact (hab rfl).elim
  · refine ⟨(.e0, .e2), ?_, ?_⟩
    · exact ⟨by decide, (hadiIff .e0).2 (by decide),
        (hadiIff .e2).2 (by decide), hhotEndpoints.2,
        hcoldEndpoints.1, hcoldEndpoints.2, hhotEndpoints.1⟩
    · rintro ⟨a, b⟩ hp
      rcases hp with ⟨hab, ha, hb, haStart, _, _, _⟩
      have haNe := (hadiIff a).1 ha
      have hbNe := (hadiIff b).1 hb
      have haCases : a = .e0 ∨ a = .e2 := by
        cases a with
        | e0 => exact Or.inl rfl
        | e1 => exact (haNe.2 rfl).elim
        | e2 => exact Or.inr rfl
        | e3 => exact (haNe.1 rfl).elim
      have hbCases : b = .e0 ∨ b = .e2 := by
        cases b with
        | e0 => exact Or.inl rfl
        | e1 => exact (hbNe.2 rfl).elim
        | e2 => exact Or.inr rfl
        | e3 => exact (hbNe.1 rfl).elim
      rcases haCases with rfl | rfl <;> rcases hbCases with rfl | rfl
      · exact (hab rfl).elim
      · rfl
      · exact (hcoldNeHot (hcoldEndpoints.2.symm.trans haStart)).elim
      · exact (hab rfl).elim

/-- Governing relation for the four positive endpoint magnetizations of two
oppositely directed adiabatic branches. -/
def AdiabaticStateComposition (D : ParamagneticData)
    (Tₕ T_c : Temperature)
    (MₕA M_cA M_cB MₕB : Magnetization) : Prop :=
  D.IsPhysical ∧
  0 < coherentCoordinate D.torus.unitSystem Tₕ ∧
  0 < coherentCoordinate D.torus.unitSystem T_c ∧
  0 < coherentCoordinate D.torus.unitSystem MₕA ∧
  0 < coherentCoordinate D.torus.unitSystem M_cA ∧
  0 < coherentCoordinate D.torus.unitSystem M_cB ∧
  0 < coherentCoordinate D.torus.unitSystem MₕB ∧
  adiabaticInvariantCoordinate D Tₕ MₕA =
    adiabaticInvariantCoordinate D T_c M_cA ∧
  adiabaticInvariantCoordinate D T_c M_cB =
    adiabaticInvariantCoordinate D Tₕ MₕB

/-- Exchanging the two adiabatic branches preserves the composition law. -/
lemma adiabaticStateComposition_swap (D : ParamagneticData)
    (Tₕ T_c : Temperature)
    (MₕA M_cA M_cB MₕB : Magnetization) :
    AdiabaticStateComposition D Tₕ T_c MₕA M_cA M_cB MₕB ↔
      AdiabaticStateComposition D Tₕ T_c MₕB M_cB M_cA MₕA := by
  constructor
  · rintro ⟨hD, hTₕ, hT_c, hMₕA, hM_cA, hM_cB, hMₕB, hA, hB⟩
    exact ⟨hD, hTₕ, hT_c, hMₕB, hM_cB, hM_cA, hMₕA, hB.symm, hA.symm⟩
  · rintro ⟨hD, hTₕ, hT_c, hMₕB, hM_cB, hM_cA, hMₕA, hB, hA⟩
    exact ⟨hD, hTₕ, hT_c, hMₕA, hM_cA, hM_cB, hMₕB, hA.symm, hB.symm⟩

/-- The endpoint states of the cycle's opposed pair satisfy the generic
adiabatic composition relation. -/
theorem cycle_adiabaticStateComposition {D : ParamagneticData}
    (C : ComposedFourLegCycle D) (pair : CycleLeg × CycleLeg)
    (hpair : OpposedAdiabaticPair C pair) :
    AdiabaticStateComposition D C.hotTemperature C.coldTemperature
      (C.state pair.1.startVertex).magnetization
      (C.state pair.1.finishVertex).magnetization
      (C.state pair.2.startVertex).magnetization
      (C.state pair.2.finishVertex).magnetization := by
  rcases hpair with
    ⟨_, hadi₁, hadi₂, h₁start, h₁finish, h₂start, h₂finish⟩
  have hinvariant₁ := adiabaticInvariant_endpoint D (C.leg pair.1)
    (C.state pair.1.startVertex) (C.state pair.1.finishVertex)
    ⟨C.legStarts pair.1, C.legFinishes pair.1⟩ hadi₁
  have hinvariant₂ := adiabaticInvariant_endpoint D (C.leg pair.2)
    (C.state pair.2.startVertex) (C.state pair.2.finishVertex)
    ⟨C.legStarts pair.2, C.legFinishes pair.2⟩ hadi₂
  rw [h₁start, h₁finish] at hinvariant₁
  rw [h₂start, h₂finish] at hinvariant₂
  exact ⟨C.apparatusPhysical,
    lt_trans C.temperatureOrder.1 C.temperatureOrder.2,
    C.temperatureOrder.1,
    (C.statePhysical pair.1.startVertex).2.2,
    (C.statePhysical pair.1.finishVertex).2.2,
    (C.statePhysical pair.2.startVertex).2.2,
    (C.statePhysical pair.2.finishVertex).2.2,
    hinvariant₁, hinvariant₂⟩

/-- Symmetric square relation among all four positive branch endpoints. -/
theorem magnetizationSquare_composition (D : ParamagneticData)
    (Tₕ T_c : Temperature)
    (MₕA M_cA M_cB MₕB : Magnetization)
    (hcomposition :
      AdiabaticStateComposition D Tₕ T_c MₕA M_cA M_cB MₕB) :
    coherentCoordinate D.torus.unitSystem MₕA ^ 2 +
        coherentCoordinate D.torus.unitSystem M_cB ^ 2 =
      coherentCoordinate D.torus.unitSystem M_cA ^ 2 +
        coherentCoordinate D.torus.unitSystem MₕB ^ 2 := by
  rcases hcomposition with
    ⟨hD, _, _, _, _, _, _, hinvariant₁, hinvariant₂⟩
  let coefficient : ℝ :=
    coherentCoordinate D.torus.unitSystem D.material.vacuumPermeability *
        coherentCoordinate D.torus.unitSystem D.torus.volume ^ 2 /
      (coherentCoordinate D.torus.unitSystem D.material.amount ^ 2 *
        coherentCoordinate D.torus.unitSystem D.material.curieParameter *
        coherentCoordinate D.torus.unitSystem
          D.material.heatCapacityCoefficient)
  have hcoefficient : 0 < coefficient := by
    dsimp [coefficient]
    exact div_pos
      (mul_pos hD.2.1 (sq_pos_of_pos hD.1.2.2.2.1))
      (mul_pos
        (mul_pos (sq_pos_of_pos hD.2.2.1) hD.2.2.2.1)
        hD.2.2.2.2)
  change
    1 / coherentCoordinate D.torus.unitSystem Tₕ ^ 2 +
        coefficient * coherentCoordinate D.torus.unitSystem MₕA ^ 2 =
      1 / coherentCoordinate D.torus.unitSystem T_c ^ 2 +
        coefficient * coherentCoordinate D.torus.unitSystem M_cA ^ 2
    at hinvariant₁
  change
    1 / coherentCoordinate D.torus.unitSystem T_c ^ 2 +
        coefficient * coherentCoordinate D.torus.unitSystem M_cB ^ 2 =
      1 / coherentCoordinate D.torus.unitSystem Tₕ ^ 2 +
        coefficient * coherentCoordinate D.torus.unitSystem MₕB ^ 2
    at hinvariant₂
  nlinarith only [hinvariant₁, hinvariant₂, hcoefficient]

/-- Answer-free predicate for a candidate fourth magnetization. -/
def IsComposedMagnetization (D : ParamagneticData)
    (Tₕ T_c : Temperature) (MₕA M_cA M_cB X : Magnetization) : Prop :=
  AdiabaticStateComposition D Tₕ T_c MₕA M_cA M_cB X

/-- At most one positive candidate satisfies the two invariant equations. -/
theorem composedMagnetization_unique (D : ParamagneticData)
    (Tₕ T_c : Temperature) (MₕA M_cA M_cB : Magnetization)
    {X Y : Magnetization}
    (hX : IsComposedMagnetization D Tₕ T_c MₕA M_cA M_cB X)
    (hY : IsComposedMagnetization D Tₕ T_c MₕA M_cA M_cB Y) :
    X = Y := by
  have hsquareX := magnetizationSquare_composition D Tₕ T_c
    MₕA M_cA M_cB X hX
  have hsquareY := magnetizationSquare_composition D Tₕ T_c
    MₕA M_cA M_cB Y hY
  have hXpos : 0 < coherentCoordinate D.torus.unitSystem X :=
    hX.2.2.2.2.2.2.1
  have hYpos : 0 < coherentCoordinate D.torus.unitSystem Y :=
    hY.2.2.2.2.2.2.1
  apply (coordinateInSI_eq_iff D.torus.unitSystem _ _).mp
  change coherentCoordinate D.torus.unitSystem X =
    coherentCoordinate D.torus.unitSystem Y
  nlinarith only [hsquareX, hsquareY, hXpos, hYpos]

/-- Each actual hot endpoint is characterized uniquely after choosing the
opposed pair, and the conjunction treats the two branch names symmetrically. -/
theorem cycleFourthMagnetization_existsUnique {D : ParamagneticData}
    (C : ComposedFourLegCycle D) (pair : CycleLeg × CycleLeg)
    (hpair : OpposedAdiabaticPair C pair) :
    (∃! X : Magnetization,
      IsComposedMagnetization D C.hotTemperature C.coldTemperature
        (C.state pair.1.startVertex).magnetization
        (C.state pair.1.finishVertex).magnetization
        (C.state pair.2.startVertex).magnetization X) ∧
    (∃! X : Magnetization,
      IsComposedMagnetization D C.hotTemperature C.coldTemperature
        (C.state pair.2.finishVertex).magnetization
        (C.state pair.2.startVertex).magnetization
        (C.state pair.1.finishVertex).magnetization X) := by
  have hcomposition := cycle_adiabaticStateComposition C pair hpair
  have hswapped :=
    (adiabaticStateComposition_swap D C.hotTemperature C.coldTemperature
      (C.state pair.1.startVertex).magnetization
      (C.state pair.1.finishVertex).magnetization
      (C.state pair.2.startVertex).magnetization
      (C.state pair.2.finishVertex).magnetization).mp hcomposition
  constructor
  · refine ⟨(C.state pair.2.finishVertex).magnetization, hcomposition, ?_⟩
    intro X hX
    exact composedMagnetization_unique D C.hotTemperature C.coldTemperature
      (C.state pair.1.startVertex).magnetization
      (C.state pair.1.finishVertex).magnetization
      (C.state pair.2.startVertex).magnetization hX hcomposition
  · refine ⟨(C.state pair.1.startVertex).magnetization, hswapped, ?_⟩
    intro X hX
    exact composedMagnetization_unique D C.hotTemperature C.coldTemperature
      (C.state pair.2.finishVertex).magnetization
      (C.state pair.2.startVertex).magnetization
      (C.state pair.1.finishVertex).magnetization hX hswapped

/-! ## Cold-body state and one completed-cycle update -/

/-- A cold body represented by coherent internal-energy and heat-capacity
coordinate functions over an admissible temperature interval. -/
structure ColdBodyModel where
  unitSystem : SIUnitChoices
  minTemperature : Temperature
  maxTemperature : Temperature
  internalEnergyCoordinate : ℝ → ℝ
  heatCapacityCoordinate : ℝ → ℝ

namespace ColdBodyModel

/-- Positivity, regularity, and the differential internal-energy law for a
cold-body model. -/
def IsPhysical (B : ColdBodyModel) : Prop :=
  let tmin := coherentCoordinate B.unitSystem B.minTemperature
  let tmax := coherentCoordinate B.unitSystem B.maxTemperature
  0 < tmin ∧ tmin < tmax ∧
  ContinuousOn B.internalEnergyCoordinate (Set.Icc tmin tmax) ∧
  DifferentiableOn ℝ B.internalEnergyCoordinate (Set.Ioo tmin tmax) ∧
  ContinuousOn B.heatCapacityCoordinate (Set.Icc tmin tmax) ∧
  (∀ t ∈ Set.Icc tmin tmax, 0 < B.heatCapacityCoordinate t) ∧
  ∀ t ∈ Set.Ioo tmin tmax,
    deriv B.internalEnergyCoordinate t = B.heatCapacityCoordinate t

end ColdBodyModel

/-- Positive heat capacity makes body internal energy strictly increasing on
the admissible interval. -/
lemma bodyInternalEnergy_strictMono (B : ColdBodyModel)
    (hB : B.IsPhysical) :
    StrictMonoOn B.internalEnergyCoordinate
      (Set.Icc (coherentCoordinate B.unitSystem B.minTemperature)
        (coherentCoordinate B.unitSystem B.maxTemperature)) := by
  let tmin := coherentCoordinate B.unitSystem B.minTemperature
  let tmax := coherentCoordinate B.unitSystem B.maxTemperature
  change 0 < tmin ∧ tmin < tmax ∧
      ContinuousOn B.internalEnergyCoordinate (Set.Icc tmin tmax) ∧
      DifferentiableOn ℝ B.internalEnergyCoordinate (Set.Ioo tmin tmax) ∧
      ContinuousOn B.heatCapacityCoordinate (Set.Icc tmin tmax) ∧
      (∀ t ∈ Set.Icc tmin tmax, 0 < B.heatCapacityCoordinate t) ∧
      ∀ t ∈ Set.Ioo tmin tmax,
        deriv B.internalEnergyCoordinate t = B.heatCapacityCoordinate t at hB
  apply strictMonoOn_of_deriv_pos (convex_Icc tmin tmax) hB.2.2.1
  intro t ht
  rw [interior_Icc] at ht
  rw [hB.2.2.2.2.2.2 t ht]
  exact hB.2.2.2.2.2.1 t ⟨ht.1.le, ht.2.le⟩

/-- Instantaneous cold-body and fixed hot-reservoir temperatures. -/
structure BodyReservoirState where
  coldTemperature : Temperature
  hotTemperature : Temperature

namespace BodyReservoirState

/-- A body-reservoir state lies in the body domain and strictly below its
positive hot-reservoir temperature. -/
def IsPhysical (B : ColdBodyModel) (σ : BodyReservoirState) : Prop :=
  coherentCoordinate B.unitSystem B.minTemperature ≤
      coherentCoordinate B.unitSystem σ.coldTemperature ∧
  coherentCoordinate B.unitSystem σ.coldTemperature ≤
      coherentCoordinate B.unitSystem B.maxTemperature ∧
  0 < coherentCoordinate B.unitSystem σ.coldTemperature ∧
  coherentCoordinate B.unitSystem σ.coldTemperature <
    coherentCoordinate B.unitSystem σ.hotTemperature

end BodyReservoirState

/-- The body and magnetic apparatus express quantities in one source unit
system. -/
def SharesUnitSystem (B : ColdBodyModel) (D : ParamagneticData) : Prop :=
  B.unitSystem = D.torus.unitSystem

/-- The cycle reservoirs equal the temperatures of the state at which it is
executed. -/
def CycleMatchesReservoirState {D : ParamagneticData}
    (C : ComposedFourLegCycle D) (σ : BodyReservoirState) : Prop :=
  C.coldTemperature = σ.coldTemperature ∧
  C.hotTemperature = σ.hotTemperature

/-- A single completed cycle extracts exactly its cold-heat magnitude from
the body while leaving the hot reservoir fixed. -/
def OneCycleStateUpdate (B : ColdBodyModel) {D : ParamagneticData}
    (C : ComposedFourLegCycle D)
    (σ σ' : BodyReservoirState) : Prop :=
  B.IsPhysical ∧
  σ.IsPhysical B ∧
  σ'.IsPhysical B ∧
  SharesUnitSystem B D ∧
  CycleMatchesReservoirState C σ ∧
  σ'.hotTemperature = σ.hotTemperature ∧
  B.internalEnergyCoordinate
      (coherentCoordinate B.unitSystem σ'.coldTemperature) =
    B.internalEnergyCoordinate
        (coherentCoordinate B.unitSystem σ.coldTemperature) -
      coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C)

/-- Every physical one-cycle update strictly lowers the cold temperature. -/
lemma oneCycleStateUpdate_cold_lt (B : ColdBodyModel)
    {D : ParamagneticData} (C : ComposedFourLegCycle D)
    (σ σ' : BodyReservoirState)
    (hupdate : OneCycleStateUpdate B C σ σ') :
    coherentCoordinate B.unitSystem σ'.coldTemperature <
      coherentCoordinate B.unitSystem σ.coldTemperature := by
  rcases hupdate with
    ⟨hB, hσ, hσ', _, _, _, henergy⟩
  have hheat := (transferMagnitudes_pos C).1
  have henergyLt :
      B.internalEnergyCoordinate
          (coherentCoordinate B.unitSystem σ'.coldTemperature) <
        B.internalEnergyCoordinate
          (coherentCoordinate B.unitSystem σ.coldTemperature) := by
    linarith
  exact ((bodyInternalEnergy_strictMono B hB).lt_iff_lt
    ⟨hσ'.1, hσ'.2.1⟩ ⟨hσ.1, hσ.2.1⟩).mp henergyLt

/-- If the body's energy above its lower endpoint accommodates the transfer,
the next physical reservoir state exists uniquely. -/
theorem oneCycleNextState_existsUnique (B : ColdBodyModel)
    {D : ParamagneticData} (C : ComposedFourLegCycle D)
    (σ : BodyReservoirState)
    (hB : B.IsPhysical) (hσ : σ.IsPhysical B)
    (hunits : SharesUnitSystem B D)
    (hmatches : CycleMatchesReservoirState C σ)
    (hcapacity :
      coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) ≤
        B.internalEnergyCoordinate
            (coherentCoordinate B.unitSystem σ.coldTemperature) -
          B.internalEnergyCoordinate
            (coherentCoordinate B.unitSystem B.minTemperature)) :
    ∃! σ' : BodyReservoirState,
      OneCycleStateUpdate B C σ σ' := by
  let tmin := coherentCoordinate B.unitSystem B.minTemperature
  let tmax := coherentCoordinate B.unitSystem B.maxTemperature
  let t₀ := coherentCoordinate B.unitSystem σ.coldTemperature
  let q := coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C)
  let target := B.internalEnergyCoordinate t₀ - q
  change 0 < tmin ∧ tmin < tmax ∧
      ContinuousOn B.internalEnergyCoordinate (Set.Icc tmin tmax) ∧
      DifferentiableOn ℝ B.internalEnergyCoordinate (Set.Ioo tmin tmax) ∧
      ContinuousOn B.heatCapacityCoordinate (Set.Icc tmin tmax) ∧
      (∀ t ∈ Set.Icc tmin tmax, 0 < B.heatCapacityCoordinate t) ∧
      ∀ t ∈ Set.Ioo tmin tmax,
        deriv B.internalEnergyCoordinate t = B.heatCapacityCoordinate t at hB
  change tmin ≤ t₀ ∧ t₀ ≤ tmax ∧ 0 < t₀ ∧
      t₀ < coherentCoordinate B.unitSystem σ.hotTemperature at hσ
  have hqpos : 0 < q := by
    exact (transferMagnitudes_pos C).1
  have hlower : B.internalEnergyCoordinate tmin ≤ target := by
    dsimp [target, q, t₀, tmin]
    linarith
  have hupper : target ≤ B.internalEnergyCoordinate t₀ := by
    dsimp [target]
    linarith
  have hcontinuity : ContinuousOn B.internalEnergyCoordinate (Set.Icc tmin t₀) :=
    hB.2.2.1.mono fun _ ht => ⟨ht.1, ht.2.trans hσ.2.1⟩
  obtain ⟨t', ht', htEnergy⟩ :=
    intermediate_value_Icc hσ.1 hcontinuity ⟨hlower, hupper⟩
  let T' : Temperature :=
    quantityFromCoherentCoordinate B.unitSystem temperatureDimension t'
  let σ' : BodyReservoirState :=
    { coldTemperature := T'
      hotTemperature := σ.hotTemperature }
  have hT' : coherentCoordinate B.unitSystem T' = t' := by
    exact coherentCoordinate_quantityFromCoherentCoordinate _ _ _
  have hσ'Physical : σ'.IsPhysical B := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change tmin ≤ coherentCoordinate B.unitSystem T'
      rw [hT']
      exact ht'.1
    · change coherentCoordinate B.unitSystem T' ≤ tmax
      rw [hT']
      exact ht'.2.trans hσ.2.1
    · change 0 < coherentCoordinate B.unitSystem T'
      rw [hT']
      exact lt_of_lt_of_le hB.1 ht'.1
    · change coherentCoordinate B.unitSystem T' <
        coherentCoordinate B.unitSystem σ.hotTemperature
      rw [hT']
      exact lt_of_le_of_lt ht'.2 hσ.2.2.2
  have hupdate : OneCycleStateUpdate B C σ σ' := by
    refine ⟨hB, hσ, hσ'Physical, hunits, hmatches, rfl, ?_⟩
    change B.internalEnergyCoordinate
        (coherentCoordinate B.unitSystem T') =
      B.internalEnergyCoordinate t₀ - q
    rw [hT']
    exact htEnergy
  refine ⟨σ', hupdate, ?_⟩
  intro ρ hρ
  rcases hρ with ⟨_, _, hρPhysical, _, _, hρHot, hρEnergy⟩
  have hρInterval : coherentCoordinate B.unitSystem ρ.coldTemperature ∈
      Set.Icc tmin tmax := ⟨hρPhysical.1, hρPhysical.2.1⟩
  have ht'Interval : t' ∈ Set.Icc tmin tmax :=
    ⟨ht'.1, ht'.2.trans hσ.2.1⟩
  have hρEnergy' :
      B.internalEnergyCoordinate
          (coherentCoordinate B.unitSystem ρ.coldTemperature) =
        B.internalEnergyCoordinate t' := by
    change B.internalEnergyCoordinate
        (coherentCoordinate B.unitSystem ρ.coldTemperature) =
      B.internalEnergyCoordinate t₀ - q at hρEnergy
    exact hρEnergy.trans htEnergy.symm
  have hρCoordinate :
      coherentCoordinate B.unitSystem ρ.coldTemperature = t' :=
    (bodyInternalEnergy_strictMono B hB).injOn
      hρInterval ht'Interval hρEnergy'
  have hρCold : ρ.coldTemperature = T' := by
    apply (coordinateInSI_eq_iff B.unitSystem _ _).mp
    change coherentCoordinate B.unitSystem ρ.coldTemperature =
      coherentCoordinate B.unitSystem T'
    rw [hT']
    exact hρCoordinate
  cases ρ with
  | mk cold hot =>
      dsimp at hρCold hρHot ⊢
      subst cold
      subst hot
      rfl

/-- A prescribed positive heat capacity is constant across the body's full
admissible temperature interval. -/
def HasConstantHeatCapacity (B : ColdBodyModel) (C_c : HeatCapacity) : Prop :=
  0 < coherentCoordinate B.unitSystem C_c ∧
  ∀ t ∈ Set.Icc (coherentCoordinate B.unitSystem B.minTemperature)
      (coherentCoordinate B.unitSystem B.maxTemperature),
    B.heatCapacityCoordinate t = coherentCoordinate B.unitSystem C_c

/-- The body energy difference is linear in temperature under a constant
heat-capacity law. -/
lemma constantHeatCapacity_energyDifference (B : ColdBodyModel)
    (C_c : HeatCapacity) (hB : B.IsPhysical)
    (hconstant : HasConstantHeatCapacity B C_c)
    (x y : ℝ)
    (hx : x ∈ Set.Icc (coherentCoordinate B.unitSystem B.minTemperature)
      (coherentCoordinate B.unitSystem B.maxTemperature))
    (hy : y ∈ Set.Icc (coherentCoordinate B.unitSystem B.minTemperature)
      (coherentCoordinate B.unitSystem B.maxTemperature)) :
    B.internalEnergyCoordinate y - B.internalEnergyCoordinate x =
      coherentCoordinate B.unitSystem C_c * (y - x) := by
  rcases hB with ⟨_, _, hcontinuous, hdifferentiable, _, _, hderivative⟩
  rcases hconstant with ⟨_, hconstant⟩
  have hforward (a b : ℝ)
      (ha : a ∈ Set.Icc (coherentCoordinate B.unitSystem B.minTemperature)
        (coherentCoordinate B.unitSystem B.maxTemperature))
      (hb : b ∈ Set.Icc (coherentCoordinate B.unitSystem B.minTemperature)
        (coherentCoordinate B.unitSystem B.maxTemperature))
      (hab : a ≤ b) :
      B.internalEnergyCoordinate b - B.internalEnergyCoordinate a =
        coherentCoordinate B.unitSystem C_c * (b - a) := by
    rcases hab.eq_or_lt with rfl | hab
    · ring
    · have hcont : ContinuousOn B.internalEnergyCoordinate (Set.Icc a b) :=
        hcontinuous.mono fun _ ht =>
          ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
      have hdiff : DifferentiableOn ℝ B.internalEnergyCoordinate (Set.Ioo a b) :=
        hdifferentiable.mono fun _ ht =>
          ⟨ha.1.trans_lt ht.1, ht.2.trans_le hb.2⟩
      obtain ⟨c, hc, hslope⟩ :=
        exists_deriv_eq_slope B.internalEnergyCoordinate hab hcont hdiff
      have hcFull : c ∈ Set.Ioo
          (coherentCoordinate B.unitSystem B.minTemperature)
          (coherentCoordinate B.unitSystem B.maxTemperature) :=
        ⟨ha.1.trans_lt hc.1, hc.2.trans_le hb.2⟩
      rw [hderivative c hcFull,
        hconstant c ⟨hcFull.1.le, hcFull.2.le⟩] at hslope
      field_simp [sub_ne_zero.mpr hab.ne] at hslope
      linarith
  rcases le_total x y with hxy | hyx
  · exact hforward x y hx hy hxy
  · have hreverse := hforward y x hy hx hyx
    linarith

/-! ## Continuous constant-power cooling histories -/

/-- Constant body heat capacity, input power, and hot-reservoir temperature
expressed in one source unit system. -/
structure CoolingProtocol where
  unitSystem : SIUnitChoices
  coldBodyHeatCapacity : HeatCapacity
  inputPower : HeatRate
  hotReservoirTemperature : Temperature

namespace CoolingProtocol

/-- A nondegenerate cooling protocol has positive capacity, power, and hot
absolute temperature. -/
def IsPhysical (protocol : CoolingProtocol) : Prop :=
  0 < coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity ∧
  0 < coherentCoordinate protocol.unitSystem protocol.inputPower ∧
  0 < coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature

end CoolingProtocol

/-- Temperature and positive-magnitude transfer-rate paths parameterized by
coherent physical time. -/
structure ContinuousCoolingHistory where
  unitSystem : SIUnitChoices
  duration : Time
  temperature : ℝ → Temperature
  coldHeatRate : ℝ → HeatRate
  hotHeatRate : ℝ → HeatRate
  workRate : ℝ → HeatRate

/-- Local Carnot, first-law, and body-energy equations for a regular
quasistatic continuum cooling history. -/
def SatisfiesCoolingProtocol (protocol : CoolingProtocol)
    (H : ContinuousCoolingHistory) : Prop :=
  let τ := coherentCoordinate H.unitSystem H.duration
  protocol.IsPhysical ∧
  H.unitSystem = protocol.unitSystem ∧
  0 ≤ τ ∧
  (∃ neighborhood : Set ℝ,
    IsOpen neighborhood ∧
    Set.Icc 0 τ ⊆ neighborhood ∧
    ContDiffOn ℝ 1
      (fun s => coherentCoordinate H.unitSystem (H.temperature s))
      neighborhood ∧
    ContinuousOn
      (fun s => coherentCoordinate H.unitSystem (H.coldHeatRate s))
      neighborhood ∧
    ContinuousOn
      (fun s => coherentCoordinate H.unitSystem (H.hotHeatRate s))
      neighborhood ∧
    ContinuousOn
      (fun s => coherentCoordinate H.unitSystem (H.workRate s))
      neighborhood) ∧
  ∀ s ∈ Set.Icc 0 τ,
    0 < coherentCoordinate H.unitSystem (H.temperature s) ∧
    coherentCoordinate H.unitSystem (H.temperature s) <
      coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature ∧
    coherentCoordinate H.unitSystem (H.workRate s) =
      coherentCoordinate protocol.unitSystem protocol.inputPower ∧
    0 < coherentCoordinate H.unitSystem (H.coldHeatRate s) ∧
    0 < coherentCoordinate H.unitSystem (H.hotHeatRate s) ∧
    coherentCoordinate H.unitSystem (H.hotHeatRate s) =
      coherentCoordinate H.unitSystem (H.coldHeatRate s) +
        coherentCoordinate H.unitSystem (H.workRate s) ∧
    coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature *
        coherentCoordinate H.unitSystem (H.coldHeatRate s) =
      coherentCoordinate H.unitSystem (H.temperature s) *
        coherentCoordinate H.unitSystem (H.hotHeatRate s) ∧
    coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity *
        deriv
          (fun r => coherentCoordinate H.unitSystem (H.temperature r)) s =
      -coherentCoordinate H.unitSystem (H.coldHeatRate s)

/-- Prescribed initial and final temperatures of a history. -/
def HasCoolingEndpoints (H : ContinuousCoolingHistory)
    (T₀ T_f : Temperature) : Prop :=
  H.temperature 0 = T₀ ∧
  H.temperature (coherentCoordinate H.unitSystem H.duration) = T_f

/-- Instantaneous cold-heat rate derived from the local magnitude balance and
cross-multiplied Carnot relation. -/
lemma coldRate_characterization (protocol : CoolingProtocol)
    (H : ContinuousCoolingHistory)
    (hH : SatisfiesCoolingProtocol protocol H) :
    ∀ s ∈ Set.Icc 0 (coherentCoordinate H.unitSystem H.duration),
      coherentCoordinate H.unitSystem (H.coldHeatRate s) =
        coherentCoordinate protocol.unitSystem protocol.inputPower *
          coherentCoordinate H.unitSystem (H.temperature s) /
          (coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature -
            coherentCoordinate H.unitSystem (H.temperature s)) := by
  intro s hs
  rcases hH with ⟨_, _, _, _, hlaws⟩
  rcases hlaws s hs with
    ⟨_, htemperatureLt, hwork, _, _, hbalance, hcarnot, _⟩
  have hdenominator :
      0 < coherentCoordinate protocol.unitSystem
          protocol.hotReservoirTemperature -
      coherentCoordinate H.unitSystem (H.temperature s) :=
    sub_pos.mpr htemperatureLt
  rw [hwork] at hbalance
  apply (eq_div_iff (ne_of_gt hdenominator)).2
  calc
    coherentCoordinate H.unitSystem (H.coldHeatRate s) *
          (coherentCoordinate protocol.unitSystem
              protocol.hotReservoirTemperature -
            coherentCoordinate H.unitSystem (H.temperature s)) =
        coherentCoordinate protocol.unitSystem
              protocol.hotReservoirTemperature *
            coherentCoordinate H.unitSystem (H.coldHeatRate s) -
          coherentCoordinate H.unitSystem (H.temperature s) *
            coherentCoordinate H.unitSystem (H.coldHeatRate s) := by ring
    _ = coherentCoordinate H.unitSystem (H.temperature s) *
          coherentCoordinate H.unitSystem (H.hotHeatRate s) -
        coherentCoordinate H.unitSystem (H.temperature s) *
          coherentCoordinate H.unitSystem (H.coldHeatRate s) := by rw [hcarnot]
    _ = coherentCoordinate protocol.unitSystem protocol.inputPower *
          coherentCoordinate H.unitSystem (H.temperature s) := by
      rw [hbalance]
      ring

/-- Reduced temperature ODE and its strict cooling consequence. -/
lemma coolingTemperature_ODE (protocol : CoolingProtocol)
    (H : ContinuousCoolingHistory)
    (hH : SatisfiesCoolingProtocol protocol H) :
    (∀ s ∈ Set.Icc 0 (coherentCoordinate H.unitSystem H.duration),
      deriv
          (fun r => coherentCoordinate H.unitSystem (H.temperature r)) s =
        -(coherentCoordinate protocol.unitSystem protocol.inputPower /
            coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity) *
          coherentCoordinate H.unitSystem (H.temperature s) /
          (coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature -
            coherentCoordinate H.unitSystem (H.temperature s))) ∧
    StrictAntiOn
      (fun s => coherentCoordinate H.unitSystem (H.temperature s))
      (Set.Icc 0 (coherentCoordinate H.unitSystem H.duration)) := by
  have hcoldRate := coldRate_characterization protocol H hH
  rcases hH with
    ⟨hprotocol, _, hduration, hregular, hlaws⟩
  rcases hprotocol with ⟨hcapacity, hpower, _⟩
  have hderivative : ∀ s ∈ Set.Icc 0
      (coherentCoordinate H.unitSystem H.duration),
      deriv (fun r => coherentCoordinate H.unitSystem (H.temperature r)) s =
        -(coherentCoordinate protocol.unitSystem protocol.inputPower /
            coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity) *
          coherentCoordinate H.unitSystem (H.temperature s) /
          (coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature -
            coherentCoordinate H.unitSystem (H.temperature s)) := by
    intro s hs
    have hrate := hcoldRate s hs
    have hbody := (hlaws s hs).2.2.2.2.2.2.2
    have hcapacityNe :
        coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity ≠ 0 :=
      ne_of_gt hcapacity
    calc
      deriv (fun r => coherentCoordinate H.unitSystem (H.temperature r)) s =
          -coherentCoordinate H.unitSystem (H.coldHeatRate s) /
            coherentCoordinate protocol.unitSystem
              protocol.coldBodyHeatCapacity := by
        apply (eq_div_iff hcapacityNe).2
        nlinarith
      _ = -(coherentCoordinate protocol.unitSystem protocol.inputPower /
            coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity) *
          coherentCoordinate H.unitSystem (H.temperature s) /
          (coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature -
            coherentCoordinate H.unitSystem (H.temperature s)) := by
        rw [hrate]
        field_simp [hcapacityNe]
  refine ⟨hderivative, ?_⟩
  rcases hregular with
    ⟨neighborhood, _, hIcc, htemperatureSmooth, _, _, _⟩
  apply strictAntiOn_of_deriv_neg
    (convex_Icc (0 : ℝ) (coherentCoordinate H.unitSystem H.duration))
    (htemperatureSmooth.continuousOn.mono hIcc)
  intro s hs
  have hsIcc : s ∈ Set.Icc 0
      (coherentCoordinate H.unitSystem H.duration) := interior_subset hs
  rw [hderivative s hsIcc]
  have hlaw := hlaws s hsIcc
  have hdenominator :
      0 < coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature -
        coherentCoordinate H.unitSystem (H.temperature s) :=
    sub_pos.mpr hlaw.2.1
  have hpowerCapacity :
      0 < coherentCoordinate protocol.unitSystem protocol.inputPower /
        coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity :=
    div_pos hpower hcapacity
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hpowerCapacity) hlaw.1)
    hdenominator

/-- Unevaluated physical-time coordinate obtained by separating the cooling
ODE from an initial temperature down to a candidate coordinate. -/
def coolingTimePotential (protocol : CoolingProtocol) (T₀ : Temperature)
    (x : ℝ) : ℝ :=
  (coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity /
      coherentCoordinate protocol.unitSystem protocol.inputPower) *
    ∫ y in x..coherentCoordinate protocol.unitSystem T₀,
      (coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature - y) / y

/-- Regularity, derivative, order reversal, endpoint value, and interval
bijection for the cooling-time potential. -/
lemma coolingTimePotential_properties (protocol : CoolingProtocol)
    (T₀ T_f : Temperature) (hprotocol : protocol.IsPhysical)
    (horder :
      0 < coherentCoordinate protocol.unitSystem T_f ∧
      coherentCoordinate protocol.unitSystem T_f <
        coherentCoordinate protocol.unitSystem T₀ ∧
      coherentCoordinate protocol.unitSystem T₀ <
        coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature) :
    ContDiffOn ℝ 1 (coolingTimePotential protocol T₀)
      (Set.Icc (coherentCoordinate protocol.unitSystem T_f)
        (coherentCoordinate protocol.unitSystem T₀)) ∧
    StrictAntiOn (coolingTimePotential protocol T₀)
      (Set.Icc (coherentCoordinate protocol.unitSystem T_f)
        (coherentCoordinate protocol.unitSystem T₀)) ∧
    (∀ x ∈ Set.Icc (coherentCoordinate protocol.unitSystem T_f)
        (coherentCoordinate protocol.unitSystem T₀),
      deriv (coolingTimePotential protocol T₀) x =
        -(coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity /
          coherentCoordinate protocol.unitSystem protocol.inputPower) *
          (coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature - x) /
          x) ∧
    coolingTimePotential protocol T₀
        (coherentCoordinate protocol.unitSystem T₀) = 0 ∧
    Set.BijOn (coolingTimePotential protocol T₀)
      (Set.Icc (coherentCoordinate protocol.unitSystem T_f)
        (coherentCoordinate protocol.unitSystem T₀))
      (Set.Icc 0 (coolingTimePotential protocol T₀
        (coherentCoordinate protocol.unitSystem T_f))) := by
  let t₀ := coherentCoordinate protocol.unitSystem T₀
  let t_f := coherentCoordinate protocol.unitSystem T_f
  let tₕ := coherentCoordinate protocol.unitSystem
    protocol.hotReservoirTemperature
  let capacity := coherentCoordinate protocol.unitSystem
    protocol.coldBodyHeatCapacity
  let power := coherentCoordinate protocol.unitSystem protocol.inputPower
  let coefficient := capacity / power
  let integrand : ℝ → ℝ := fun y => (tₕ - y) / y
  rcases hprotocol with ⟨hcapacity, hpower, _⟩
  have htf : 0 < t_f := horder.1
  have htfT₀ : t_f < t₀ := horder.2.1
  have hT₀hot : t₀ < tₕ := horder.2.2
  have hcoefficient : 0 < coefficient := div_pos hcapacity hpower
  have hintegrandContinuous : ContinuousOn integrand (Set.Ioi 0) := by
    intro x hx
    exact ((continuousAt_const.sub continuousAt_id).div continuousAt_id
      (ne_of_gt hx)).continuousWithinAt
  have huIccPositive (x : ℝ) (hx : 0 < x) :
      Set.uIcc x t₀ ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact hx.trans_le hy.1
    · exact (lt_trans htf htfT₀).trans_le hy.1
  have hintegrable (x : ℝ) (hx : 0 < x) :
      IntervalIntegrable integrand MeasureTheory.volume x t₀ :=
    (hintegrandContinuous.mono (huIccPositive x hx)).intervalIntegrable
  have hpotentialDeriv (x : ℝ) (hx : 0 < x) :
      HasDerivAt (coolingTimePotential protocol T₀)
        (-coefficient * integrand x) x := by
    have hcontinuousAt : ContinuousAt integrand x :=
      ((continuousAt_const.sub continuousAt_id).div continuousAt_id
        (ne_of_gt hx))
    have hintegral := intervalIntegral.integral_hasDerivAt_left
      (hintegrable x hx)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
        hintegrandContinuous x hx) hcontinuousAt
    have hscaled := hintegral.const_mul coefficient
    apply hscaled.congr_deriv
    ring
  have hpotentialDifferentiable : DifferentiableOn ℝ
      (coolingTimePotential protocol T₀) (Set.Ioi 0) := by
    intro x hx
    exact (hpotentialDeriv x hx).differentiableAt.differentiableWithinAt
  have hderivEq : Set.EqOn (deriv (coolingTimePotential protocol T₀))
      (fun x => -coefficient * integrand x) (Set.Ioi 0) := by
    intro x hx
    exact (hpotentialDeriv x hx).deriv
  have hderivContinuous : ContinuousOn
      (deriv (coolingTimePotential protocol T₀)) (Set.Ioi 0) := by
    have hformulaContinuous : ContinuousOn
        (fun x => -coefficient * integrand x) (Set.Ioi 0) :=
      continuousOn_const.mul hintegrandContinuous
    exact hformulaContinuous.congr fun x hx => hderivEq hx
  have hpotentialContDiffIoi : ContDiffOn ℝ 1
      (coolingTimePotential protocol T₀) (Set.Ioi 0) := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen
      (n := 0) isOpen_Ioi).2
    refine ⟨hpotentialDifferentiable, ?_, ?_⟩
    · simp
    · exact contDiffOn_zero.mpr hderivContinuous
  have hpotentialContDiff : ContDiffOn ℝ 1
      (coolingTimePotential protocol T₀) (Set.Icc t_f t₀) :=
    hpotentialContDiffIoi.mono fun _ hx => htf.trans_le hx.1
  have hderivative : ∀ x ∈ Set.Icc t_f t₀,
      deriv (coolingTimePotential protocol T₀) x =
        -coefficient * integrand x := by
    intro x hx
    exact hderivEq (htf.trans_le hx.1)
  have hstrict : StrictAntiOn (coolingTimePotential protocol T₀)
      (Set.Icc t_f t₀) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc t_f t₀)
      hpotentialContDiff.continuousOn
    intro x hx
    have hxIcc : x ∈ Set.Icc t_f t₀ := interior_subset hx
    rw [hderivative x hxIcc]
    have hxpos : 0 < x := htf.trans_le hxIcc.1
    have hxhot : x < tₕ := hxIcc.2.trans_lt hT₀hot
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hcoefficient)
      (div_pos (sub_pos.mpr hxhot) hxpos)
  have hzero : coolingTimePotential protocol T₀ t₀ = 0 := by
    simp [coolingTimePotential, t₀]
  have hmaps : Set.MapsTo (coolingTimePotential protocol T₀)
      (Set.Icc t_f t₀)
      (Set.Icc 0 (coolingTimePotential protocol T₀ t_f)) := by
    intro x hx
    have hanti := hstrict.antitoneOn
    constructor
    · rw [← hzero]
      exact hanti hx (Set.right_mem_Icc.mpr htfT₀.le) hx.2
    · exact hanti (Set.left_mem_Icc.mpr htfT₀.le) hx hx.1
  have hinjective : Set.InjOn (coolingTimePotential protocol T₀)
      (Set.Icc t_f t₀) := hstrict.injOn
  have hsurjective : Set.SurjOn (coolingTimePotential protocol T₀)
      (Set.Icc t_f t₀)
      (Set.Icc 0 (coolingTimePotential protocol T₀ t_f)) := by
    intro z hz
    have hz' : z ∈ Set.Icc
        (coolingTimePotential protocol T₀ t₀)
        (coolingTimePotential protocol T₀ t_f) := by
      rwa [hzero]
    exact intermediate_value_Icc' htfT₀.le
      hpotentialContDiff.continuousOn hz'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [t_f, t₀] using hpotentialContDiff
  · simpa [t_f, t₀] using hstrict
  · intro x hx
    simpa [coefficient, integrand, capacity, power, t₀, t_f, tₕ,
      div_eq_mul_inv, mul_assoc] using
      hderivative x hx
  · simpa [t₀] using hzero
  · simpa [t_f, t₀] using
      (show Set.BijOn (coolingTimePotential protocol T₀) (Set.Icc t_f t₀)
          (Set.Icc 0 (coolingTimePotential protocol T₀ t_f)) from
        ⟨hmaps, hinjective, hsurjective⟩)

/-- Answer-free elapsed-time solution predicate: a positive time is accepted
only when a regular governing-law history with the requested endpoints
exists. -/
def IsElapsedTimeSolution (protocol : CoolingProtocol)
    (T₀ T_f : Temperature) (τ : Time) : Prop :=
  0 < coherentCoordinate protocol.unitSystem τ ∧
  ∃ H : ContinuousCoolingHistory,
    H.duration = τ ∧
    SatisfiesCoolingProtocol protocol H ∧
    HasCoolingEndpoints H T₀ T_f

/-- Every admissible history obeys the separated, unevaluated elapsed-time
integral. -/
theorem elapsedTime_integral_of_history (protocol : CoolingProtocol)
    (T₀ T_f : Temperature) (τ : Time)
    (hsolution : IsElapsedTimeSolution protocol T₀ T_f τ)
    (horder :
      0 < coherentCoordinate protocol.unitSystem T_f ∧
      coherentCoordinate protocol.unitSystem T_f <
        coherentCoordinate protocol.unitSystem T₀ ∧
      coherentCoordinate protocol.unitSystem T₀ <
        coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature) :
    coherentCoordinate protocol.unitSystem protocol.inputPower *
        coherentCoordinate protocol.unitSystem τ =
      coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity *
        ∫ x in coherentCoordinate protocol.unitSystem T_f..
            coherentCoordinate protocol.unitSystem T₀,
          (coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature - x) / x := by
  rcases hsolution with ⟨hτpositive, H, hduration, hH, hendpoints⟩
  have hH' := hH
  rcases hH with
    ⟨hprotocol, hunits, hdurationNonnegative,
      ⟨neighborhood, hopen, hIcc, htemperatureSmooth, _, _, _⟩, hlaws⟩
  rcases hprotocol with ⟨hcapacity, hpower, hhot⟩
  let duration := coherentCoordinate H.unitSystem H.duration
  let temperature : ℝ → ℝ := fun s =>
    coherentCoordinate H.unitSystem (H.temperature s)
  let t₀ := coherentCoordinate protocol.unitSystem T₀
  let t_f := coherentCoordinate protocol.unitSystem T_f
  let tₕ := coherentCoordinate protocol.unitSystem
    protocol.hotReservoirTemperature
  let capacity := coherentCoordinate protocol.unitSystem
    protocol.coldBodyHeatCapacity
  let power := coherentCoordinate protocol.unitSystem protocol.inputPower
  let coefficient := capacity / power
  let integrand : ℝ → ℝ := fun x => (tₕ - x) / x
  have hdurationCoordinate : duration =
      coherentCoordinate protocol.unitSystem τ := by
    dsimp [duration]
    rw [hduration, hunits]
  have hdurationPositive : 0 < duration := by
    rw [hdurationCoordinate]
    exact hτpositive
  have hstart : temperature 0 = t₀ := by
    dsimp [temperature, t₀]
    rw [hendpoints.1, hunits]
  have hfinish : temperature duration = t_f := by
    dsimp [temperature, duration, t_f]
    rw [hendpoints.2, hunits]
  have htemperatureAnti := (coolingTemperature_ODE protocol H hH').2
  have htemperatureBounds : Set.MapsTo temperature
      (Set.Icc 0 duration) (Set.Icc t_f t₀) := by
    intro s hs
    have hanti := htemperatureAnti.antitoneOn
    constructor
    · rw [← hfinish]
      exact hanti hs (Set.right_mem_Icc.mpr hdurationNonnegative) hs.2
    · rw [← hstart]
      exact hanti (Set.left_mem_Icc.mpr hdurationNonnegative) hs hs.1
  have hproperties := coolingTimePotential_properties protocol T₀ T_f
    ⟨hcapacity, hpower, hhot⟩ horder
  have htemperatureContDiff : ContDiffOn ℝ 1 temperature (Set.Icc 0 duration) :=
    htemperatureSmooth.mono hIcc
  have hcompositionContDiff : ContDiffOn ℝ 1
      (fun s => coolingTimePotential protocol T₀ (temperature s))
      (Set.Icc 0 duration) := by
    simpa only [Function.comp_def] using
      hproperties.1.comp htemperatureContDiff htemperatureBounds
  have huIccPositive (x : ℝ) (hx : 0 < x) :
      Set.uIcc x t₀ ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    rcases Set.mem_uIcc.mp hy with hy | hy
    · exact hx.trans_le hy.1
    · exact horder.1.trans_le (horder.2.1.le.trans hy.1)
  have hpotentialHasDeriv (x : ℝ) (hx : 0 < x) :
      HasDerivAt (coolingTimePotential protocol T₀)
        (-coefficient * integrand x) x := by
    have hintegrandContinuous : ContinuousOn integrand (Set.Ioi 0) := by
      intro y hy
      exact ((continuousAt_const.sub continuousAt_id).div continuousAt_id
        (ne_of_gt hy)).continuousWithinAt
    have hintegrable : IntervalIntegrable integrand MeasureTheory.volume x t₀ :=
      (hintegrandContinuous.mono (huIccPositive x hx)).intervalIntegrable
    have hcontinuousAt : ContinuousAt integrand x :=
      (continuousAt_const.sub continuousAt_id).div continuousAt_id (ne_of_gt hx)
    have hintegral := intervalIntegral.integral_hasDerivAt_left hintegrable
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
        hintegrandContinuous x hx) hcontinuousAt
    have hscaled := hintegral.const_mul coefficient
    apply hscaled.congr_deriv
    ring
  have hcompositionDeriv : ∀ s ∈ Set.Icc 0 duration,
      deriv (fun r => coolingTimePotential protocol T₀ (temperature r)) s = 1 := by
    intro s hs
    have hsn : s ∈ neighborhood := hIcc hs
    have htemperatureDiff : DifferentiableAt ℝ temperature s :=
      (htemperatureSmooth.differentiableOn_one s hsn).differentiableAt
        (hopen.mem_nhds hsn)
    have hlaw := hlaws s hs
    have hchain := (hpotentialHasDeriv (temperature s) hlaw.1).comp s
      htemperatureDiff.hasDerivAt
    have htemperatureODE := (coolingTemperature_ODE protocol H hH').1 s hs
    have hchainDeriv :
        deriv (fun r => coolingTimePotential protocol T₀ (temperature r)) s =
          -coefficient * integrand (temperature s) * deriv temperature s := by
      change deriv (coolingTimePotential protocol T₀ ∘ temperature) s =
        -coefficient * integrand (temperature s) * deriv temperature s
      exact hchain.deriv
    rw [hchainDeriv, htemperatureODE]
    have htemperatureNe : temperature s ≠ 0 := ne_of_gt hlaw.1
    have hdenominatorNe : tₕ - temperature s ≠ 0 :=
      ne_of_gt (sub_pos.mpr hlaw.2.1)
    dsimp [coefficient, integrand, capacity, power, tₕ, temperature]
    have hproductNe :
        coherentCoordinate H.unitSystem (H.temperature s) *
            (coherentCoordinate protocol.unitSystem
                protocol.hotReservoirTemperature -
              coherentCoordinate H.unitSystem (H.temperature s)) ≠ 0 :=
      mul_ne_zero htemperatureNe hdenominatorNe
    have hcollapsed :
        coherentCoordinate H.unitSystem (H.temperature s) *
              (coherentCoordinate protocol.unitSystem
                  protocol.hotReservoirTemperature -
                coherentCoordinate H.unitSystem (H.temperature s)) /
            (coherentCoordinate H.unitSystem (H.temperature s) *
              (coherentCoordinate protocol.unitSystem
                  protocol.hotReservoirTemperature -
                coherentCoordinate H.unitSystem (H.temperature s))) = 1 :=
      div_self hproductNe
    field_simp [ne_of_gt hcapacity, ne_of_gt hpower, htemperatureNe,
      hdenominatorNe]
    exact hcollapsed
  have hfundamental := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    hcompositionContDiff hdurationNonnegative
  have hintegralOne :
      (∫ s in (0 : ℝ)..duration,
        deriv (fun r => coolingTimePotential protocol T₀ (temperature r)) s) =
      ∫ _s in (0 : ℝ)..duration, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hdurationNonnegative] at hs
    exact hcompositionDeriv s hs
  rw [hintegralOne] at hfundamental
  have hdurationPotential :
      duration = coolingTimePotential protocol T₀ t_f := by
    have hzero := hproperties.2.2.2.1
    have hzeroLocal : coolingTimePotential protocol T₀ t₀ = 0 := by
      simpa [t₀] using hzero
    calc
      duration = ∫ _s in (0 : ℝ)..duration, (1 : ℝ) := by simp
      _ = coolingTimePotential protocol T₀ (temperature duration) -
          coolingTimePotential protocol T₀ (temperature 0) := hfundamental
      _ = coolingTimePotential protocol T₀ t_f := by
        rw [hfinish, hstart]
        rw [hzeroLocal, sub_zero]
  rw [← hdurationCoordinate]
  have h := hdurationPotential
  dsimp [coolingTimePotential, duration, t_f, t₀] at h ⊢
  field_simp [ne_of_gt hpower] at h
  simpa [mul_comm] using h

/-- Governing-history existence is equivalent to positivity and the integral
equation; the reverse direction is a genuine history construction. -/
theorem elapsedTime_solution_characterization (protocol : CoolingProtocol)
    (T₀ T_f : Temperature) (τ : Time)
    (hprotocol : protocol.IsPhysical)
    (horder :
      0 < coherentCoordinate protocol.unitSystem T_f ∧
      coherentCoordinate protocol.unitSystem T_f <
        coherentCoordinate protocol.unitSystem T₀ ∧
      coherentCoordinate protocol.unitSystem T₀ <
        coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature) :
    IsElapsedTimeSolution protocol T₀ T_f τ ↔
      0 < coherentCoordinate protocol.unitSystem τ ∧
      coherentCoordinate protocol.unitSystem protocol.inputPower *
          coherentCoordinate protocol.unitSystem τ =
        coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity *
          ∫ x in coherentCoordinate protocol.unitSystem T_f..
              coherentCoordinate protocol.unitSystem T₀,
            (coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature - x) /
              x := by
  constructor
  · intro hsolution
    exact ⟨hsolution.1,
      elapsedTime_integral_of_history protocol T₀ T_f τ hsolution horder⟩
  · rintro ⟨hτpositive, hintegral⟩
    let t_f := coherentCoordinate protocol.unitSystem T_f
    let t₀ := coherentCoordinate protocol.unitSystem T₀
    let tₕ := coherentCoordinate protocol.unitSystem
      protocol.hotReservoirTemperature
    let duration := coherentCoordinate protocol.unitSystem τ
    let capacity := coherentCoordinate protocol.unitSystem
      protocol.coldBodyHeatCapacity
    let power := coherentCoordinate protocol.unitSystem protocol.inputPower
    let coefficient := capacity / power
    let integrand : ℝ → ℝ := fun x => (tₕ - x) / x
    let potential := coolingTimePotential protocol T₀
    rcases hprotocol with ⟨hcapacity, hpower, hhot⟩
    have htf : 0 < t_f := horder.1
    have htfT₀ : t_f < t₀ := horder.2.1
    have hT₀hot : t₀ < tₕ := horder.2.2
    have hduration : 0 < duration := hτpositive
    have hcoefficient : 0 < coefficient := div_pos hcapacity hpower
    have huIccPositive (x : ℝ) (hx : 0 < x) :
        Set.uIcc x t₀ ⊆ Set.Ioi (0 : ℝ) := by
      intro y hy
      rcases Set.mem_uIcc.mp hy with hy | hy
      · exact hx.trans_le hy.1
      · exact htf.trans_le (htfT₀.le.trans hy.1)
    have hintegrandContinuous : ContinuousOn integrand (Set.Ioi 0) := by
      intro x hx
      exact ((continuousAt_const.sub continuousAt_id).div continuousAt_id
        (ne_of_gt hx)).continuousWithinAt
    have hpotentialHasDeriv (x : ℝ) (hx : 0 < x) :
        HasDerivAt potential (-coefficient * integrand x) x := by
      have hintegrable : IntervalIntegrable integrand MeasureTheory.volume x t₀ :=
        (hintegrandContinuous.mono (huIccPositive x hx)).intervalIntegrable
      have hcontinuousAt : ContinuousAt integrand x :=
        (continuousAt_const.sub continuousAt_id).div continuousAt_id (ne_of_gt hx)
      have hintegralDeriv := intervalIntegral.integral_hasDerivAt_left hintegrable
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
          hintegrandContinuous x hx) hcontinuousAt
      have hscaled := hintegralDeriv.const_mul coefficient
      apply hscaled.congr_deriv
      ring
    have hpotentialDifferentiable : DifferentiableOn ℝ potential (Set.Ioi 0) := by
      intro x hx
      exact (hpotentialHasDeriv x hx).differentiableAt.differentiableWithinAt
    have hpotentialDerivEq : Set.EqOn (deriv potential)
        (fun x => -coefficient * integrand x) (Set.Ioi 0) := by
      intro x hx
      exact (hpotentialHasDeriv x hx).deriv
    have hpotentialDerivContinuous : ContinuousOn (deriv potential)
        (Set.Ioi 0) := by
      have hformulaContinuous : ContinuousOn
          (fun x => -coefficient * integrand x) (Set.Ioi 0) :=
        continuousOn_const.mul hintegrandContinuous
      exact hformulaContinuous.congr fun x hx => hpotentialDerivEq hx
    have hpotentialContDiff : ContDiffOn ℝ 1 potential (Set.Ioi 0) := by
      apply (contDiffOn_succ_iff_deriv_of_isOpen
        (n := 0) isOpen_Ioi).2
      refine ⟨hpotentialDifferentiable, ?_, ?_⟩
      · simp
      · exact contDiffOn_zero.mpr hpotentialDerivContinuous
    have hpotentialZero : potential t₀ = 0 := by
      simp [potential, coolingTimePotential, t₀]
    have hpotentialFinal : potential t_f = duration := by
      dsimp [potential, coolingTimePotential, t_f, t₀, duration,
        capacity, power] at hintegral ⊢
      field_simp [ne_of_gt hpower]
      nlinarith only [hintegral]
    let lower := t_f / 2
    let upper := (t₀ + tₕ) / 2
    have hlowerPositive : 0 < lower := by dsimp [lower]; linarith
    have hlowerFinal : lower < t_f := by dsimp [lower]; linarith
    have hfinalUpper : t_f < upper := by
      dsimp [upper]
      linarith
    have hinitialUpper : t₀ < upper := by
      dsimp [upper]
      linarith
    have hupperHot : upper < tₕ := by
      dsimp [upper]
      linarith
    have hlowerUpper : lower < upper := lt_trans hlowerFinal hfinalUpper
    have hclosedPositive : Set.Icc lower upper ⊆ Set.Ioi (0 : ℝ) := by
      intro x hx
      exact hlowerPositive.trans_le hx.1
    have hpotentialContDiffClosed : ContDiffOn ℝ 1 potential
        (Set.Icc lower upper) := hpotentialContDiff.mono hclosedPositive
    have hpotentialStrict : StrictAntiOn potential (Set.Icc lower upper) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc lower upper)
        hpotentialContDiffClosed.continuousOn
      intro x hx
      have hxIcc : x ∈ Set.Icc lower upper := interior_subset hx
      rw [hpotentialDerivEq (hclosedPositive hxIcc)]
      have hxpos : 0 < x := hlowerPositive.trans_le hxIcc.1
      have hxhot : x < tₕ := hxIcc.2.trans_lt hupperHot
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hcoefficient)
        (div_pos (sub_pos.mpr hxhot) hxpos)
    have himage : potential '' Set.Ioo lower upper =
        Set.Ioo (potential upper) (potential lower) :=
      hpotentialContDiffClosed.continuousOn.image_Ioo_of_strictAntiOn
        hlowerUpper.le hpotentialStrict
    let neighborhood := Set.Ioo (potential upper) (potential lower)
    have hopen : IsOpen neighborhood := isOpen_Ioo
    have hupperNegative : potential upper < 0 := by
      rw [← hpotentialZero]
      exact hpotentialStrict
        ⟨(lt_trans hlowerFinal htfT₀).le, hinitialUpper.le⟩
        ⟨hlowerUpper.le, le_rfl⟩
        hinitialUpper
    have hlowerAboveDuration : duration < potential lower := by
      rw [← hpotentialFinal]
      exact hpotentialStrict
        ⟨le_rfl, hlowerUpper.le⟩
        ⟨hlowerFinal.le, hfinalUpper.le⟩
        hlowerFinal
    have hintervalNeighborhood : Set.Icc 0 duration ⊆ neighborhood := by
      intro s hs
      exact ⟨hupperNegative.trans_le hs.1, hs.2.trans_lt hlowerAboveDuration⟩
    let inverseTemperature := Function.invFunOn potential (Set.Ioo lower upper)
    have hpreimage (s : ℝ) (hs : s ∈ neighborhood) :
        ∃ x ∈ Set.Ioo lower upper, potential x = s := by
      have hs' : s ∈ potential '' Set.Ioo lower upper := by
        rw [himage]
        exact hs
      simpa only [Set.mem_image] using hs'
    have hinverseMem (s : ℝ) (hs : s ∈ neighborhood) :
        inverseTemperature s ∈ Set.Ioo lower upper :=
      Function.invFunOn_mem (hpreimage s hs)
    have hrightInverse (s : ℝ) (hs : s ∈ neighborhood) :
        potential (inverseTemperature s) = s :=
      Function.invFunOn_eq (hpreimage s hs)
    have hstrictInj : Set.InjOn potential (Set.Ioo lower upper) :=
      hpotentialStrict.injOn.mono Set.Ioo_subset_Icc_self
    have hleftInverse (x : ℝ) (hx : x ∈ Set.Ioo lower upper) :
        inverseTemperature (potential x) = x :=
      hstrictInj.leftInvOn_invFunOn hx
    have hinverseContDiffAt (s : ℝ) (hs : s ∈ neighborhood) :
        ContDiffAt ℝ 1 inverseTemperature s := by
      let x := inverseTemperature s
      have hx : x ∈ Set.Ioo lower upper := hinverseMem s hs
      have hxpositive : 0 < x := lt_trans hlowerPositive hx.1
      have hxhot : x < tₕ := hx.2.trans hupperHot
      have hphiAt : ContDiffAt ℝ 1 potential x :=
        (hpotentialContDiff x hxpositive).contDiffAt
          (isOpen_Ioi.mem_nhds hxpositive)
      have hphiDeriv := hpotentialHasDeriv x hxpositive
      have hphiDerivNeg : -coefficient * integrand x < 0 :=
        mul_neg_of_neg_of_pos (neg_lt_zero.mpr hcoefficient)
          (div_pos (sub_pos.mpr hxhot) hxpositive)
      have hphiEquiv := hphiDeriv.hasFDerivAt_equiv hphiDerivNeg.ne
      let localInverse := hphiAt.localInverse hphiEquiv (by norm_num)
      let localHomeomorph :=
        hphiAt.toOpenPartialHomeomorph potential hphiEquiv (by norm_num)
      have hphis : potential x = s := hrightInverse s hs
      have hlocalContDiff : ContDiffAt ℝ 1 localInverse s := by
        have hlocal := hphiAt.to_localInverse hphiEquiv (by norm_num)
        rw [hphis] at hlocal
        exact hlocal
      have htarget : s ∈ localHomeomorph.target := by
        have ht := hphiAt.image_mem_toOpenPartialHomeomorph_target
          hphiEquiv (by norm_num)
        rwa [hphis] at ht
      have hlocalAt : localInverse s = x := by
        have hlocal := hphiAt.localInverse_apply_image hphiEquiv (by norm_num)
        rw [hphis] at hlocal
        exact hlocal
      have heventuallyTarget : ∀ᶠ y in nhds s,
          y ∈ localHomeomorph.target :=
        localHomeomorph.open_target.mem_nhds htarget
      have heventuallyDomain : ∀ᶠ y in nhds s,
          localInverse y ∈ Set.Ioo lower upper := by
        have hdomainNhd : Set.Ioo lower upper ∈
            nhds (localInverse s) := by
          rw [hlocalAt]
          exact isOpen_Ioo.mem_nhds hx
        exact hlocalContDiff.continuousAt hdomainNhd
      have heventuallyEq : Filter.EventuallyEq (nhds s)
          inverseTemperature localInverse := by
        filter_upwards [heventuallyTarget, heventuallyDomain] with y hytarget hydomain
        have hlocalRight : potential (localInverse y) = y := by
          exact localHomeomorph.right_inv hytarget
        have hchosenMem : inverseTemperature y ∈ Set.Ioo lower upper :=
          Function.invFunOn_mem ⟨localInverse y, hydomain, hlocalRight⟩
        have hchosenRight : potential (inverseTemperature y) = y :=
          Function.invFunOn_eq ⟨localInverse y, hydomain, hlocalRight⟩
        exact hstrictInj hchosenMem hydomain
          (hchosenRight.trans hlocalRight.symm)
      exact hlocalContDiff.congr_of_eventuallyEq heventuallyEq
    have hinverseContDiff : ContDiffOn ℝ 1 inverseTemperature neighborhood := by
      intro s hs
      exact (hinverseContDiffAt s hs).contDiffWithinAt
    have hinverseHasDeriv (s : ℝ) (hs : s ∈ neighborhood) :
        HasDerivAt inverseTemperature
          (-coefficient * integrand (inverseTemperature s))⁻¹ s := by
      have hx := hinverseMem s hs
      have hxpositive : 0 < inverseTemperature s :=
        lt_trans hlowerPositive hx.1
      have hxhot : inverseTemperature s < tₕ := hx.2.trans hupperHot
      have hderivativeNonzero :
          -coefficient * integrand (inverseTemperature s) ≠ 0 := by
        apply mul_ne_zero
        · exact neg_ne_zero.mpr (ne_of_gt hcoefficient)
        · exact div_ne_zero (sub_ne_zero.mpr hxhot.ne') (ne_of_gt hxpositive)
      have hrightEventually : ∀ᶠ y in nhds s,
          potential (inverseTemperature y) = y := by
        filter_upwards [hopen.mem_nhds hs] with y hy
        exact hrightInverse y hy
      exact (hpotentialHasDeriv (inverseTemperature s) hxpositive).of_local_left_inverse
        (hinverseContDiffAt s hs).continuousAt hderivativeNonzero hrightEventually
    have hinverseDeriv (s : ℝ) (hs : s ∈ neighborhood) :
        deriv inverseTemperature s =
          -(power / capacity) * inverseTemperature s /
            (tₕ - inverseTemperature s) := by
      rw [(hinverseHasDeriv s hs).deriv]
      have hx := hinverseMem s hs
      have hxpositive : 0 < inverseTemperature s :=
        lt_trans hlowerPositive hx.1
      have hxhot : inverseTemperature s < tₕ := hx.2.trans hupperHot
      dsimp [coefficient, integrand]
      field_simp [ne_of_gt hcapacity, ne_of_gt hpower,
        ne_of_gt hxpositive, ne_of_gt (sub_pos.mpr hxhot)]
    have hzeroMem : t₀ ∈ Set.Ioo lower upper :=
      ⟨lt_trans hlowerFinal htfT₀, hinitialUpper⟩
    have hfinalMem : t_f ∈ Set.Ioo lower upper :=
      ⟨hlowerFinal, hfinalUpper⟩
    have hinverseZero : inverseTemperature 0 = t₀ := by
      rw [← hpotentialZero]
      exact hleftInverse t₀ hzeroMem
    have hinverseFinal : inverseTemperature duration = t_f := by
      rw [← hpotentialFinal]
      exact hleftInverse t_f hfinalMem
    let coldRate : ℝ → ℝ := fun s =>
      power * inverseTemperature s / (tₕ - inverseTemperature s)
    let hotRate : ℝ → ℝ := fun s => coldRate s + power
    let temperaturePath : ℝ → Temperature := fun s =>
      quantityFromCoherentCoordinate protocol.unitSystem temperatureDimension
        (inverseTemperature s)
    let H : ContinuousCoolingHistory :=
      { unitSystem := protocol.unitSystem
        duration := τ
        temperature := temperaturePath
        coldHeatRate := fun s =>
          quantityFromCoherentCoordinate protocol.unitSystem heatRateDimension
            (coldRate s)
        hotHeatRate := fun s =>
          quantityFromCoherentCoordinate protocol.unitSystem heatRateDimension
            (hotRate s)
        workRate := fun _ =>
          quantityFromCoherentCoordinate protocol.unitSystem heatRateDimension power }
    have htemperatureCoordinate (s : ℝ) :
        coherentCoordinate H.unitSystem (H.temperature s) = inverseTemperature s := by
      exact coherentCoordinate_quantityFromCoherentCoordinate _ _ _
    have hcoldCoordinate (s : ℝ) :
        coherentCoordinate H.unitSystem (H.coldHeatRate s) = coldRate s := by
      exact coherentCoordinate_quantityFromCoherentCoordinate _ _ _
    have hhotCoordinate (s : ℝ) :
        coherentCoordinate H.unitSystem (H.hotHeatRate s) = hotRate s := by
      exact coherentCoordinate_quantityFromCoherentCoordinate _ _ _
    have hworkCoordinate (s : ℝ) :
        coherentCoordinate H.unitSystem (H.workRate s) = power := by
      exact coherentCoordinate_quantityFromCoherentCoordinate _ _ _
    have hdenominatorNonzero : ∀ s ∈ neighborhood,
        tₕ - inverseTemperature s ≠ 0 := by
      intro s hs
      exact ne_of_gt (sub_pos.mpr ((hinverseMem s hs).2.trans hupperHot))
    have hcoldContinuous : ContinuousOn coldRate neighborhood := by
      change ContinuousOn
        (fun s => power * inverseTemperature s /
          (tₕ - inverseTemperature s)) neighborhood
      exact (continuousOn_const.mul hinverseContDiff.continuousOn).div
        (continuousOn_const.sub hinverseContDiff.continuousOn)
        hdenominatorNonzero
    have hhotContinuous : ContinuousOn hotRate neighborhood := by
      exact hcoldContinuous.add continuousOn_const
    have hH : SatisfiesCoolingProtocol protocol H := by
      refine ⟨⟨hcapacity, hpower, hhot⟩, rfl, hτpositive.le,
        ⟨neighborhood, hopen, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa [H] using hintervalNeighborhood
      · simpa only [htemperatureCoordinate] using hinverseContDiff
      · simpa only [hcoldCoordinate] using hcoldContinuous
      · simpa only [hhotCoordinate] using hhotContinuous
      · simpa only [hworkCoordinate] using continuousOn_const
      · intro s hs
        have hsn : s ∈ neighborhood := hintervalNeighborhood (by simpa [H] using hs)
        have hx := hinverseMem s hsn
        have hxpositive : 0 < inverseTemperature s :=
          lt_trans hlowerPositive hx.1
        have hxhot : inverseTemperature s < tₕ := hx.2.trans hupperHot
        have hdenPos : 0 < tₕ - inverseTemperature s := sub_pos.mpr hxhot
        have hcoldPos : 0 < coldRate s := by
          exact div_pos (mul_pos hpower hxpositive) hdenPos
        have hhotPos : 0 < hotRate s := by
          exact add_pos hcoldPos hpower
        have htemperatureDeriv :
            deriv (fun r => coherentCoordinate H.unitSystem (H.temperature r)) s =
              -(power / capacity) * inverseTemperature s /
                (tₕ - inverseTemperature s) := by
          have heq : (fun r => coherentCoordinate H.unitSystem (H.temperature r)) =
              inverseTemperature := funext htemperatureCoordinate
          rw [heq]
          exact hinverseDeriv s hsn
        rw [htemperatureCoordinate, hcoldCoordinate, hhotCoordinate,
          hworkCoordinate]
        refine ⟨hxpositive, hxhot, rfl, hcoldPos, hhotPos, rfl, ?_, ?_⟩
        · dsimp [hotRate, coldRate]
          field_simp [ne_of_gt hdenPos]
          ring
        · rw [htemperatureDeriv]
          dsimp [coldRate]
          dsimp [capacity]
          field_simp [ne_of_gt hcapacity, ne_of_gt hdenPos]
    have hendpoints : HasCoolingEndpoints H T₀ T_f := by
      constructor
      · apply (coordinateInSI_eq_iff protocol.unitSystem _ _).mp
        change coherentCoordinate H.unitSystem (H.temperature 0) = t₀
        rw [htemperatureCoordinate, hinverseZero]
      · apply (coordinateInSI_eq_iff protocol.unitSystem _ _).mp
        have hdurationCoordinate : coherentCoordinate H.unitSystem H.duration = duration := by
          rfl
        change coherentCoordinate H.unitSystem
            (H.temperature (coherentCoordinate H.unitSystem H.duration)) = t_f
        rw [hdurationCoordinate, htemperatureCoordinate, hinverseFinal]
    exact ⟨hτpositive, H, rfl, hH, hendpoints⟩

/-- A physical protocol and ordered positive endpoints determine a unique
dimensioned elapsed time through the history predicate. -/
theorem elapsedTime_existsUnique (protocol : CoolingProtocol)
    (T₀ T_f : Temperature) (hprotocol : protocol.IsPhysical)
    (horder :
      0 < coherentCoordinate protocol.unitSystem T_f ∧
      coherentCoordinate protocol.unitSystem T_f <
        coherentCoordinate protocol.unitSystem T₀ ∧
      coherentCoordinate protocol.unitSystem T₀ <
        coherentCoordinate protocol.unitSystem protocol.hotReservoirTemperature) :
    ∃! τ : Time, IsElapsedTimeSolution protocol T₀ T_f τ := by
  let elapsed := coolingTimePotential protocol T₀
    (coherentCoordinate protocol.unitSystem T_f)
  let τ : Time := quantityFromCoherentCoordinate protocol.unitSystem
    timeDimension elapsed
  have hproperties := coolingTimePotential_properties protocol T₀ T_f
    hprotocol horder
  have helapsedPositive : 0 < elapsed := by
    have hstrict := hproperties.2.1
    have hcompare := hstrict
      (Set.left_mem_Icc.mpr horder.2.1.le)
      (Set.right_mem_Icc.mpr horder.2.1.le) horder.2.1
    rw [hproperties.2.2.2.1] at hcompare
    exact hcompare
  have hτCoordinate : coherentCoordinate protocol.unitSystem τ = elapsed :=
    coherentCoordinate_quantityFromCoherentCoordinate _ _ _
  have hequation :
      coherentCoordinate protocol.unitSystem protocol.inputPower *
          coherentCoordinate protocol.unitSystem τ =
        coherentCoordinate protocol.unitSystem protocol.coldBodyHeatCapacity *
          ∫ x in coherentCoordinate protocol.unitSystem T_f..
              coherentCoordinate protocol.unitSystem T₀,
            (coherentCoordinate protocol.unitSystem
                protocol.hotReservoirTemperature - x) / x := by
    rw [hτCoordinate]
    dsimp [elapsed, coolingTimePotential]
    field_simp [ne_of_gt hprotocol.2.1]
  have hsolution : IsElapsedTimeSolution protocol T₀ T_f τ :=
    (elapsedTime_solution_characterization protocol T₀ T_f τ
      hprotocol horder).2 ⟨hτCoordinate.symm ▸ helapsedPositive, hequation⟩
  refine ⟨τ, hsolution, ?_⟩
  intro σ hσ
  have hσEquation :=
    (elapsedTime_solution_characterization protocol T₀ T_f σ
      hprotocol horder).1 hσ
  apply (coordinateInSI_eq_iff protocol.unitSystem _ _).mp
  change coherentCoordinate protocol.unitSystem σ =
    coherentCoordinate protocol.unitSystem τ
  have hpower := hprotocol.2.1
  exact mul_left_cancel₀ (ne_of_gt hpower) (hσEquation.2.trans hequation.symm)

/-! ## Cumulative transfers and overall performance -/

/-- Cumulative cold heat over a continuous history segment. -/
def continuousCumulativeColdHeat (H : ContinuousCoolingHistory)
    (s : ℝ) : Energy :=
  quantityFromCoherentCoordinate H.unitSystem energyDimension
    (∫ r in (0 : ℝ)..s,
      coherentCoordinate H.unitSystem (H.coldHeatRate r))

/-- Cumulative input work over a continuous history segment. -/
def continuousCumulativeWork (H : ContinuousCoolingHistory)
    (s : ℝ) : Energy :=
  quantityFromCoherentCoordinate H.unitSystem energyDimension
    (∫ r in (0 : ℝ)..s,
      coherentCoordinate H.unitSystem (H.workRate r))

/-- Cumulative hot-reservoir heat magnitude over a continuous segment. -/
def continuousCumulativeHotHeat (H : ContinuousCoolingHistory)
    (s : ℝ) : Energy :=
  quantityFromCoherentCoordinate H.unitSystem energyDimension
    (∫ r in (0 : ℝ)..s,
      coherentCoordinate H.unitSystem (H.hotHeatRate r))

/-- Pointwise first-law balance integrates to every physical history segment. -/
theorem continuousCumulative_balance (protocol : CoolingProtocol)
    (H : ContinuousCoolingHistory)
    (hH : SatisfiesCoolingProtocol protocol H) (s : ℝ)
    (hs : s ∈ Set.Icc 0 (coherentCoordinate H.unitSystem H.duration)) :
    continuousCumulativeHotHeat H s =
      continuousCumulativeColdHeat H s + continuousCumulativeWork H s := by
  rcases hH with ⟨_, _, _, hregular, hlaws⟩
  rcases hregular with
    ⟨neighborhood, _, hIcc, _, hcoldContinuous, _, hworkContinuous⟩
  have hsegment : Set.Icc 0 s ⊆ neighborhood := by
    intro r hr
    exact hIcc ⟨hr.1, hr.2.trans hs.2⟩
  have hcoldIntegrable : IntervalIntegrable
      (fun r => coherentCoordinate H.unitSystem (H.coldHeatRate r))
      MeasureTheory.volume 0 s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hs.1
    exact hcoldContinuous.mono hsegment
  have hworkIntegrable : IntervalIntegrable
      (fun r => coherentCoordinate H.unitSystem (H.workRate r))
      MeasureTheory.volume 0 s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hs.1
    exact hworkContinuous.mono hsegment
  apply (coordinateInSI_eq_iff H.unitSystem _ _).mp
  change coherentCoordinate H.unitSystem (continuousCumulativeHotHeat H s) =
    coherentCoordinate H.unitSystem
      (continuousCumulativeColdHeat H s + continuousCumulativeWork H s)
  have hcoordinateAdd (x y : Energy) :
      coherentCoordinate H.unitSystem (x + y) =
        coherentCoordinate H.unitSystem x + coherentCoordinate H.unitSystem y := by
    simp [coherentCoordinate, coordinateInSI]
    ring
  rw [hcoordinateAdd]
  simp only [continuousCumulativeHotHeat, continuousCumulativeColdHeat,
    continuousCumulativeWork,
    coherentCoordinate_quantityFromCoherentCoordinate]
  rw [← intervalIntegral.integral_add hcoldIntegrable hworkIntegrable]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le hs.1] at hr
  exact (hlaws r ⟨hr.1, hr.2.trans hs.2⟩).2.2.2.2.2.1

/-- Positive constant input power gives positive work on every nonzero
physical segment. -/
lemma continuousCumulativeWork_pos (protocol : CoolingProtocol)
    (H : ContinuousCoolingHistory)
    (hH : SatisfiesCoolingProtocol protocol H) (s : ℝ)
    (hs : 0 < s ∧ s ≤ coherentCoordinate H.unitSystem H.duration) :
    0 < coherentCoordinate H.unitSystem (continuousCumulativeWork H s) := by
  rcases hH with ⟨hprotocol, _, _, _, hlaws⟩
  have hintegral :
      (∫ r in (0 : ℝ)..s,
          coherentCoordinate H.unitSystem (H.workRate r)) =
        ∫ _r in (0 : ℝ)..s,
          coherentCoordinate protocol.unitSystem protocol.inputPower := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le hs.1.le] at hr
    exact (hlaws r ⟨hr.1, hr.2.trans hs.2⟩).2.2.1
  simp only [continuousCumulativeWork,
    coherentCoordinate_quantityFromCoherentCoordinate]
  rw [hintegral]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  exact mul_pos hs.1 hprotocol.2.1

/-- A nonzero physical continuous segment, which guarantees a positive work
denominator for cumulative performance. -/
structure PositiveContinuousSegment where
  protocol : CoolingProtocol
  history : ContinuousCoolingHistory
  time : ℝ
  satisfies : SatisfiesCoolingProtocol protocol history
  timePositive : 0 < time
  timeWithinDuration :
    time ≤ coherentCoordinate history.unitSystem history.duration

/-- Cumulative cold heat divided by cumulative work on a continuous segment. -/
def continuousOverallCOP (segment : PositiveContinuousSegment) : ℝ :=
  coherentCoordinate segment.history.unitSystem
      (continuousCumulativeColdHeat segment.history segment.time) /
    coherentCoordinate segment.history.unitSystem
      (continuousCumulativeWork segment.history segment.time)

/-- A finite sequence of completed cycles and the body-reservoir state update
between every adjacent pair of states. -/
structure CompletedCycleHistory (B : ColdBodyModel)
    (D : ParamagneticData) where
  cycleCount : ℕ
  states : Fin (cycleCount + 1) → BodyReservoirState
  cycles : Fin cycleCount → ComposedFourLegCycle D
  updates : ∀ i : Fin cycleCount,
    OneCycleStateUpdate B (cycles i)
      (states i.castSucc) (states i.succ)

/-- Sum of cold heat absorbed over all completed cycles. -/
def cumulativeColdHeat {B : ColdBodyModel} {D : ParamagneticData}
    (H : CompletedCycleHistory B D) : Energy :=
  ∑ i : Fin H.cycleCount, coldHeatMagnitude (H.cycles i)

/-- Sum of material-work input over all completed cycles. -/
def cumulativeWork {B : ColdBodyModel} {D : ParamagneticData}
    (H : CompletedCycleHistory B D) : Energy :=
  ∑ i : Fin H.cycleCount, cycleWorkInput (H.cycles i)

/-- Sum of hot heat rejected over all completed cycles. -/
def cumulativeHotHeat {B : ColdBodyModel} {D : ParamagneticData}
    (H : CompletedCycleHistory B D) : Energy :=
  ∑ i : Fin H.cycleCount, hotHeatMagnitude (H.cycles i)

/-- Finite cumulative heat-work magnitude balance, including the empty
history. -/
theorem cumulative_balance {B : ColdBodyModel} {D : ParamagneticData}
    (H : CompletedCycleHistory B D) :
    cumulativeHotHeat H = cumulativeColdHeat H + cumulativeWork H := by
  unfold cumulativeHotHeat cumulativeColdHeat cumulativeWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact cycle_magnitude_balance (H.cycles i)

/-- The cumulative cold heat equals the body's telescoping internal-energy
loss from its first to final state. -/
theorem cumulative_body_energy_balance {B : ColdBodyModel}
    {D : ParamagneticData} (H : CompletedCycleHistory B D) :
    coherentCoordinate D.torus.unitSystem (cumulativeColdHeat H) =
      B.internalEnergyCoordinate
          (coherentCoordinate B.unitSystem
            (H.states ⟨0, Nat.succ_pos H.cycleCount⟩).coldTemperature) -
        B.internalEnergyCoordinate
          (coherentCoordinate B.unitSystem
            (H.states ⟨H.cycleCount,
              Nat.lt_succ_self H.cycleCount⟩).coldTemperature) := by
  let energy : Fin (H.cycleCount + 1) → ℝ := fun j =>
    B.internalEnergyCoordinate
      (coherentCoordinate B.unitSystem (H.states j).coldTemperature)
  have hcoordinateAdd (x y : Energy) :
      coherentCoordinate D.torus.unitSystem (x + y) =
        coherentCoordinate D.torus.unitSystem x +
          coherentCoordinate D.torus.unitSystem y := by
    simp [coherentCoordinate, coordinateInSI]
    ring
  have hcoordinateSum (s : Finset (Fin H.cycleCount)) :
      coherentCoordinate D.torus.unitSystem
          (∑ i ∈ s, coldHeatMagnitude (H.cycles i)) =
        ∑ i ∈ s, coherentCoordinate D.torus.unitSystem
          (coldHeatMagnitude (H.cycles i)) := by
    induction s using Finset.induction_on with
    | empty => simp [coherentCoordinate, coordinateInSI]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hcoordinateAdd, ih]
  have hterm (i : Fin H.cycleCount) :
      coherentCoordinate D.torus.unitSystem
          (coldHeatMagnitude (H.cycles i)) =
        energy i.castSucc - energy i.succ := by
    have henergy := (H.updates i).2.2.2.2.2.2
    dsimp [energy]
    linarith
  have htelescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ),
      (∑ i : Fin n, (f i.castSucc - f i.succ)) =
        f ⟨0, Nat.succ_pos n⟩ - f ⟨n, Nat.lt_succ_self n⟩ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro f
        rw [Fin.sum_univ_succ]
        simp_rw [Fin.castSucc_succ]
        rw [ih (fun i : Fin (n + 1) => f i.succ)]
        have hzero : f (Fin.castSucc (0 : Fin (n + 1))) =
            f ⟨0, Nat.succ_pos (n + 1)⟩ := congrArg f (Fin.ext rfl)
        have hone : f (Fin.succ (0 : Fin (n + 1))) =
            f (Fin.succ ⟨0, Nat.succ_pos n⟩) := congrArg f (Fin.ext rfl)
        have hlast : f (Fin.succ ⟨n, Nat.lt_succ_self n⟩) =
            f ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ := congrArg f (Fin.ext rfl)
        rw [hzero, hone, hlast]
        ring
  calc
    coherentCoordinate D.torus.unitSystem (cumulativeColdHeat H) =
        ∑ i : Fin H.cycleCount, coherentCoordinate D.torus.unitSystem
          (coldHeatMagnitude (H.cycles i)) := by
      simpa [cumulativeColdHeat] using hcoordinateSum Finset.univ
    _ = ∑ i : Fin H.cycleCount,
        (energy i.castSucc - energy i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    _ = energy ⟨0, Nat.succ_pos H.cycleCount⟩ -
        energy ⟨H.cycleCount, Nat.lt_succ_self H.cycleCount⟩ :=
      htelescope H.cycleCount energy
    _ = _ := rfl

/-- A nonempty completed history has positive total work. -/
lemma cumulativeWork_pos {B : ColdBodyModel} {D : ParamagneticData}
    (H : CompletedCycleHistory B D) (hN : 0 < H.cycleCount) :
    0 < coherentCoordinate D.torus.unitSystem (cumulativeWork H) := by
  have hcoordinateAdd (x y : Energy) :
      coherentCoordinate D.torus.unitSystem (x + y) =
        coherentCoordinate D.torus.unitSystem x +
          coherentCoordinate D.torus.unitSystem y := by
    simp [coherentCoordinate, coordinateInSI]
    ring
  have hcoordinateSum (s : Finset (Fin H.cycleCount)) :
      coherentCoordinate D.torus.unitSystem
          (∑ i ∈ s, cycleWorkInput (H.cycles i)) =
        ∑ i ∈ s, coherentCoordinate D.torus.unitSystem
          (cycleWorkInput (H.cycles i)) := by
    induction s using Finset.induction_on with
    | empty => simp [coherentCoordinate, coordinateInSI]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hcoordinateAdd, ih]
  rw [show coherentCoordinate D.torus.unitSystem (cumulativeWork H) =
      ∑ i : Fin H.cycleCount, coherentCoordinate D.torus.unitSystem
        (cycleWorkInput (H.cycles i)) by
    simpa [cumulativeWork] using hcoordinateSum Finset.univ]
  apply Finset.sum_pos
  · intro i _
    exact (transferMagnitudes_pos (H.cycles i)).2.2
  · exact ⟨⟨0, hN⟩, Finset.mem_univ _⟩

/-- A completed-cycle history with the nondegenerate positive-work condition
needed by overall performance. -/
structure PositiveWorkHistory (B : ColdBodyModel)
    (D : ParamagneticData) where
  history : CompletedCycleHistory B D
  workPositive :
    0 < coherentCoordinate D.torus.unitSystem (cumulativeWork history)

/-- Overall finite-history coefficient of performance: a ratio of cumulative
sums, not the coefficient of the final cycle. -/
def OverallCOP {B : ColdBodyModel} {D : ParamagneticData}
    (H : PositiveWorkHistory B D) : ℝ :=
  coherentCoordinate D.torus.unitSystem (cumulativeColdHeat H.history) /
    coherentCoordinate D.torus.unitSystem (cumulativeWork H.history)

/-- Coefficient of performance for one completed cycle. -/
def segmentCOP {D : ParamagneticData}
    (C : ComposedFourLegCycle D) : ℝ :=
  coherentCoordinate D.torus.unitSystem (coldHeatMagnitude C) /
    coherentCoordinate D.torus.unitSystem (cycleWorkInput C)

/-- Overall performance is the work-weighted aggregate of every completed
cycle coefficient. -/
theorem overallCOP_weighted_sum {B : ColdBodyModel}
    {D : ParamagneticData} (H : PositiveWorkHistory B D) :
    OverallCOP H =
      (∑ i : Fin H.history.cycleCount,
        coherentCoordinate D.torus.unitSystem
            (cycleWorkInput (H.history.cycles i)) *
          segmentCOP (H.history.cycles i)) /
        coherentCoordinate D.torus.unitSystem
          (cumulativeWork H.history) := by
  have hcoordinateAdd (x y : Energy) :
      coherentCoordinate D.torus.unitSystem (x + y) =
        coherentCoordinate D.torus.unitSystem x +
          coherentCoordinate D.torus.unitSystem y := by
    simp [coherentCoordinate, coordinateInSI]
    ring
  have hcoordinateSum (q : Fin H.history.cycleCount → Energy)
      (s : Finset (Fin H.history.cycleCount)) :
      coherentCoordinate D.torus.unitSystem (∑ i ∈ s, q i) =
        ∑ i ∈ s, coherentCoordinate D.torus.unitSystem (q i) := by
    induction s using Finset.induction_on with
    | empty => simp [coherentCoordinate, coordinateInSI]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hcoordinateAdd, ih]
  have hcoldSum :
      coherentCoordinate D.torus.unitSystem
          (cumulativeColdHeat H.history) =
        ∑ i : Fin H.history.cycleCount,
          coherentCoordinate D.torus.unitSystem
            (coldHeatMagnitude (H.history.cycles i)) := by
    simpa [cumulativeColdHeat] using
      hcoordinateSum (fun i => coldHeatMagnitude (H.history.cycles i)) Finset.univ
  unfold OverallCOP
  rw [hcoldSum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold segmentCOP
  exact (mul_div_cancel₀
    (coherentCoordinate D.torus.unitSystem
      (coldHeatMagnitude (H.history.cycles i)))
    (ne_of_gt (transferMagnitudes_pos (H.history.cycles i)).2.2)).symm

end Ipho2026Gpt56solBlind.Shared.RefrigeratorCycle
