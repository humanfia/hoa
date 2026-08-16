import Ipho2026Gpt56solBlind.Shared.RefrigeratorCycle

/-!
# IPhO 2026 Problem 3, part C.2

This file gives an answer-free specification of the first magnetization in
the numbered Figure 3b refrigerator cycle.  The source adapter identifies the
four numbered vertices and directed legs with the shared abstract cycle.  The
requested magnetization is then characterized by the two opposed adiabatic
invariant equations; no derived value is stored in the statement.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_3_C_2

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics
open Ipho2026Gpt56solBlind.Shared.RefrigeratorCycle

/-- Source-faithful identification of the numbered Figure 3b states with a
physical composed four-leg cycle.  Besides fixing the vertex and leg order,
the predicate records the physical state domain, equation of state,
reservoir-temperature order, opposed adiabatic pair, and the temperature
columns visible in the figure. -/
def IsFigure3bSourceAdapter (D : ParamagneticData)
    (C : ComposedFourLegCycle D)
    (s₁ s₂ s₃ s₄ : EquilibriumState) : Prop :=
  s₁ = C.state CycleVertex.v0 ∧
  s₂ = C.state CycleVertex.v1 ∧
  s₃ = C.state CycleVertex.v2 ∧
  s₄ = C.state CycleVertex.v3 ∧
  D.IsPhysical ∧
  s₁.IsPhysical D.torus.unitSystem ∧
  s₂.IsPhysical D.torus.unitSystem ∧
  s₃.IsPhysical D.torus.unitSystem ∧
  s₄.IsPhysical D.torus.unitSystem ∧
  SatisfiesEquationOfState D s₁ ∧
  SatisfiesEquationOfState D s₂ ∧
  SatisfiesEquationOfState D s₃ ∧
  SatisfiesEquationOfState D s₄ ∧
  0 < coherentCoordinate D.torus.unitSystem C.coldTemperature ∧
  coherentCoordinate D.torus.unitSystem C.coldTemperature <
    coherentCoordinate D.torus.unitSystem C.hotTemperature ∧
  StartsAt (C.leg CycleLeg.e0).process s₁ ∧
  FinishesAt (C.leg CycleLeg.e0).process s₂ ∧
  StartsAt (C.leg CycleLeg.e1).process s₂ ∧
  FinishesAt (C.leg CycleLeg.e1).process s₃ ∧
  StartsAt (C.leg CycleLeg.e2).process s₃ ∧
  FinishesAt (C.leg CycleLeg.e2).process s₄ ∧
  StartsAt (C.leg CycleLeg.e3).process s₄ ∧
  FinishesAt (C.leg CycleLeg.e3).process s₁ ∧
  OpposedAdiabaticPair C (CycleLeg.e0, CycleLeg.e2) ∧
  s₁.temperature = C.hotTemperature ∧
  s₂.temperature = C.coldTemperature ∧
  s₃.temperature = C.coldTemperature ∧
  s₄.temperature = C.hotTemperature

/-- In the numbered Figure 3b orientation, `e1` is the cold isotherm on
which heat enters the torus and `e3` is the hot isotherm on which heat leaves
it. -/
lemma figure3b_thermalRolesAndHeatFlow (D : ParamagneticData)
    (C : ComposedFourLegCycle D)
    (s₁ s₂ s₃ s₄ : EquilibriumState)
    (hfigure : IsFigure3bSourceAdapter D C s₁ s₂ s₃ s₄) :
    IsColdIsothermalLeg C CycleLeg.e1 ∧
      IsHotIsothermalLeg C CycleLeg.e3 ∧
      coherentCoordinate D.torus.unitSystem
          (C.leg CycleLeg.e3).heat < 0 ∧
      0 < coherentCoordinate D.torus.unitSystem
          (C.leg CycleLeg.e1).heat := by
  rcases hfigure with
    ⟨_, hs₂, _, _, _, _, _, _, _, _, _, _, _, _, htemperatureOrder,
      _, _, _, _, _, _, _, _, hpair, _, hs₂Temperature, _, _⟩
  rw [hs₂] at hs₂Temperature
  rcases hpair with ⟨_, hadi₀, hadi₂, _, _, _, _⟩
  rcases completeDiagramAnnotation_existsUnique C with ⟨A, hA, _⟩
  rcases hA with
    ⟨hhot, hcold, _, _, _, _, hlegsNe, _, _, _, _, hhotHeat, hcoldHeat⟩
  have startTemperature (e : CycleLeg) (T : Temperature)
      (hiso : IsIsothermal D (C.leg e).process T) :
      (C.state e.startVertex).temperature = T := by
    have hab : (C.leg e).process.a < (C.leg e).process.b :=
      (C.leg e).isReversible.1.2.1
    have hstart :=
      hiso.2 (C.leg e).process.a ⟨le_rfl, hab.le⟩
    have hs := C.legStarts e
    unfold StartsAt at hs
    rw [hs] at hstart
    exact hstart
  have hcoldNeHot : C.coldTemperature ≠ C.hotTemperature := by
    intro htemperatures
    rw [htemperatures] at htemperatureOrder
    exact lt_irrefl _ htemperatureOrder
  have hhotLeg : A.hotDeliveryLeg = CycleLeg.e3 := by
    cases hleg : A.hotDeliveryLeg with
    | e0 =>
        exfalso
        apply (C.roleExactlyOne CycleLeg.e0).2.2.1
        exact
          ⟨by simpa [IsHotIsothermalLeg, hleg] using hhot,
            by simpa [IsAdiabaticCycleLeg] using hadi₀⟩
    | e1 =>
        exfalso
        have hhot₁ : IsHotIsothermalLeg C CycleLeg.e1 := by
          simpa [hleg] using hhot
        have hv₁Hot :
            (C.state CycleVertex.v1).temperature = C.hotTemperature := by
          simpa [CycleLeg.startVertex] using
            startTemperature CycleLeg.e1 C.hotTemperature hhot₁
        exact hcoldNeHot (hs₂Temperature.symm.trans hv₁Hot)
    | e2 =>
        exfalso
        apply (C.roleExactlyOne CycleLeg.e2).2.2.1
        exact
          ⟨by simpa [IsHotIsothermalLeg, hleg] using hhot,
            by simpa [IsAdiabaticCycleLeg] using hadi₂⟩
    | e3 =>
        rfl
  have hcoldLeg : A.coldAbsorptionLeg = CycleLeg.e1 := by
    cases hleg : A.coldAbsorptionLeg with
    | e0 =>
        exfalso
        apply (C.roleExactlyOne CycleLeg.e0).2.2.2
        exact
          ⟨by simpa [IsColdIsothermalLeg, hleg] using hcold,
            by simpa [IsAdiabaticCycleLeg] using hadi₀⟩
    | e1 =>
        rfl
    | e2 =>
        exfalso
        apply (C.roleExactlyOne CycleLeg.e2).2.2.2
        exact
          ⟨by simpa [IsColdIsothermalLeg, hleg] using hcold,
            by simpa [IsAdiabaticCycleLeg] using hadi₂⟩
    | e3 =>
        exfalso
        exact hlegsNe (hhotLeg.trans hleg.symm)
  exact
    ⟨by simpa [hcoldLeg] using hcold,
      by simpa [hhotLeg] using hhot,
      by simpa [hhotLeg] using hhotHeat,
      by simpa [hcoldLeg] using hcoldHeat⟩

/-- The opposed adiabatic legs have the numbered endpoint order
`(M₁, M₂, M₃, M₄)`. -/
lemma figure3b_adiabaticStateComposition (D : ParamagneticData)
    (C : ComposedFourLegCycle D)
    (s₁ s₂ s₃ s₄ : EquilibriumState)
    (hfigure : IsFigure3bSourceAdapter D C s₁ s₂ s₃ s₄) :
    AdiabaticStateComposition D C.hotTemperature C.coldTemperature
      s₁.magnetization s₂.magnetization
      s₃.magnetization s₄.magnetization := by
  rcases hfigure with
    ⟨hs₁, hs₂, hs₃, hs₄, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, hpair, _, _, _, _⟩
  simpa [CycleLeg.startVertex, CycleLeg.finishVertex, hs₁, hs₂, hs₃, hs₄]
    using cycle_adiabaticStateComposition C
      (CycleLeg.e0, CycleLeg.e2) hpair

/-- A candidate for the requested first magnetization.  Swapping the two
opposed branches puts the unknown in the fourth (hot-endpoint) slot of the
shared governing composition relation. -/
def IsRequestedFirstMagnetization (D : ParamagneticData)
    (Tₕ T_c : Temperature) (M₂ M₃ M₄ X : Magnetization) : Prop :=
  IsComposedMagnetization D Tₕ T_c M₄ M₃ M₂ X

/-- The magnetization at the actual first vertex satisfies the answer-free
candidate predicate. -/
lemma figure3b_firstMagnetization_isRequested (D : ParamagneticData)
    (C : ComposedFourLegCycle D)
    (s₁ s₂ s₃ s₄ : EquilibriumState)
    (hfigure : IsFigure3bSourceAdapter D C s₁ s₂ s₃ s₄) :
    IsRequestedFirstMagnetization D C.hotTemperature C.coldTemperature
      s₂.magnetization s₃.magnetization s₄.magnetization
      s₁.magnetization := by
  exact
    (adiabaticStateComposition_swap D C.hotTemperature C.coldTemperature
      s₁.magnetization s₂.magnetization
      s₃.magnetization s₄.magnetization).mp
      (figure3b_adiabaticStateComposition D C s₁ s₂ s₃ s₄ hfigure)

/-- Every requested-first-magnetization candidate obeys the symmetric
squared-coordinate consequence of the two adiabatic invariant equations. -/
lemma requestedFirstMagnetization_square (D : ParamagneticData)
    (Tₕ T_c : Temperature) (M₂ M₃ M₄ X : Magnetization)
    (hX : IsRequestedFirstMagnetization D Tₕ T_c M₂ M₃ M₄ X) :
    coherentCoordinate D.torus.unitSystem M₄ ^ 2 +
        coherentCoordinate D.torus.unitSystem M₂ ^ 2 =
      coherentCoordinate D.torus.unitSystem M₃ ^ 2 +
        coherentCoordinate D.torus.unitSystem X ^ 2 := by
  exact magnetizationSquare_composition D Tₕ T_c M₄ M₃ M₂ X hX

/-- The governing equations select exactly one physical first
magnetization for Figure 3b.  The proof may use the actual first endpoint as
the witness, but that witness and its derived value are absent from the
final conclusion. -/
theorem requestedFirstMagnetization_existsUnique (D : ParamagneticData)
    (C : ComposedFourLegCycle D)
    (s₁ s₂ s₃ s₄ : EquilibriumState)
    (hfigure : IsFigure3bSourceAdapter D C s₁ s₂ s₃ s₄) :
    ∃! X : Magnetization,
      IsRequestedFirstMagnetization D C.hotTemperature C.coldTemperature
        s₂.magnetization s₃.magnetization s₄.magnetization X := by
  rcases hfigure with
    ⟨_, hs₂, hs₃, hs₄, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, hpair, _, _, _, _⟩
  change ∃! X : Magnetization,
    IsComposedMagnetization D C.hotTemperature C.coldTemperature
      s₄.magnetization s₃.magnetization s₂.magnetization X
  rw [hs₂, hs₃, hs₄]
  exact (cycleFourthMagnetization_existsUnique C
    (CycleLeg.e0, CycleLeg.e2) hpair).2

end Ipho2026Gpt56solBlind.ProblemIPhO2026_3_C_2
