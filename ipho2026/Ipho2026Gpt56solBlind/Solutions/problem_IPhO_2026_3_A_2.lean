import Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics

/-!
# IPhO 2026 Problem 3 A.2: instantaneous source work

This file gives an answer-free model of the work performed by the external
voltage source during an oriented infinitesimal change of magnetic flux
density in a densely wound, thin paramagnetic torus.  The requested work is
characterized by Ampere's law, uniform flux linkage, Faraday--Lenz induction,
source-emf balance, and the lossless-wire idealization; no eliminated work
formula is part of the theorem signature.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_3_A_2

open Ipho2026Gpt56solBlind.Shared.ISQDimensions
open Ipho2026Gpt56solBlind.Shared.ParamagneticThermodynamics

/-! ## Typed instantaneous source data and electromagnetic witness -/

/-- The prescribed thin-torus geometry, homogeneous magnetic-field strength,
and oriented magnetic-flux-density increment.  The requested source work is
deliberately not stored in the source data. -/
structure SourceData where
  torus : TorusData
  fieldStrength : MagneticFieldStrength
  fluxDensityIncrement : MagneticFluxDensity

/-- Physical source data have physical thin-torus geometry and strictly
positive field-strength magnitude.  The flux-density increment remains
signed and is not required to be positive. -/
def SourceData.IsPhysical (D : SourceData) : Prop :=
  D.torus.IsPhysical ∧
    0 < coherentCoordinate D.torus.unitSystem D.fieldStrength

/-- Auxiliary electromagnetic quantities at the chosen instant.  The two
emf increments have magnetic-flux dimension because the process parameter is
dimensionless.  Source work is kept outside this witness. -/
structure InstantaneousElectromagneticWitness where
  windingCurrent : ElectricCurrent
  linkedFluxChange : MagneticFlux
  inducedEmfIncrement : MagneticFlux
  sourceEmfIncrement : MagneticFlux
  wireLossIncrement : Energy

/-! ## Instantaneous governing laws -/

/-- Uniform oriented Ampere balance around the torus mean loop. -/
def SatisfiesAmpereBalance (D : SourceData)
    (X : InstantaneousElectromagneticWitness) : Prop :=
  coherentCoordinate D.torus.unitSystem D.torus.meanLoopLength *
      coherentCoordinate D.torus.unitSystem D.fieldStrength =
    (D.torus.turns : ℝ) *
      coherentCoordinate D.torus.unitSystem X.windingCurrent

/-- Every positively linked turn sees the same cross-sectional flux change. -/
def SatisfiesLinkedFluxChange (D : SourceData)
    (X : InstantaneousElectromagneticWitness) : Prop :=
  coherentCoordinate D.torus.unitSystem X.linkedFluxChange =
    (D.torus.turns : ℝ) *
      coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
        coherentCoordinate D.torus.unitSystem D.fluxDensityIncrement

/-- Differential Faraday--Lenz law in the fixed winding/flux orientation. -/
def SatisfiesFaradayLenzLaw (D : SourceData)
    (X : InstantaneousElectromagneticWitness) : Prop :=
  coherentCoordinate D.torus.unitSystem X.inducedEmfIncrement =
    -coherentCoordinate D.torus.unitSystem X.linkedFluxChange

/-- The external source emf exactly balances the induced back emf. -/
def SatisfiesSourceEmfBalance (D : SourceData)
    (X : InstantaneousElectromagneticWitness) : Prop :=
  coherentCoordinate D.torus.unitSystem X.sourceEmfIncrement =
    -coherentCoordinate D.torus.unitSystem X.inducedEmfIncrement

/-- The negligible wire-heating approximation, represented as an explicit
zero signed-energy channel. -/
def SatisfiesZeroWireLoss (D : SourceData)
    (X : InstantaneousElectromagneticWitness) : Prop :=
  coherentCoordinate D.torus.unitSystem X.wireLossIncrement = 0

/-- Entering-positive source-work balance.  Current times a magnetic-flux
increment has the energy dimension by
`current_mul_magneticFlux_dimension`. -/
def SatisfiesSourceWorkLaw (D : SourceData)
    (X : InstantaneousElectromagneticWitness) (W : Energy) : Prop :=
  coherentCoordinate D.torus.unitSystem W =
    coherentCoordinate D.torus.unitSystem X.windingCurrent *
        coherentCoordinate D.torus.unitSystem X.sourceEmfIncrement +
      coherentCoordinate D.torus.unitSystem X.wireLossIncrement

/-- The five answer-independent electromagnetic equations for a lossless
dense winding. -/
def SatisfiesElectromagneticLaws (D : SourceData)
    (X : InstantaneousElectromagneticWitness) : Prop :=
  SatisfiesAmpereBalance D X ∧
    SatisfiesLinkedFluxChange D X ∧
    SatisfiesFaradayLenzLaw D X ∧
    SatisfiesSourceEmfBalance D X ∧
    SatisfiesZeroWireLoss D X

/-- The electromagnetic equations together with the source-work balance for
a signed energy candidate. -/
def SatisfiesInstantaneousLaws (D : SourceData)
    (X : InstantaneousElectromagneticWitness) (W : Energy) : Prop :=
  SatisfiesElectromagneticLaws D X ∧ SatisfiesSourceWorkLaw D X W

/-- A signed energy increment is a solution exactly when some typed
electromagnetic witness satisfies all governing equations. -/
def IsSourceWorkIncrementSolution (D : SourceData) (W : Energy) : Prop :=
  ∃ X : InstantaneousElectromagneticWitness,
    SatisfiesInstantaneousLaws D X W

/-! ## Componentwise determinacy -/

/-- Ampere balance determines the typed winding current for physical data. -/
lemma windingCurrent_unique (D : SourceData) (hD : D.IsPhysical)
    (X₁ X₂ : InstantaneousElectromagneticWitness)
    (h₁ : SatisfiesAmpereBalance D X₁)
    (h₂ : SatisfiesAmpereBalance D X₂) :
    X₁.windingCurrent = X₂.windingCurrent := by
  have hturnsNat : D.torus.turns ≠ 0 :=
    Nat.ne_of_gt hD.1.2.2.2.2.2.2.2.1
  have hturns : (D.torus.turns : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hturnsNat
  apply (coordinateInSI_eq_iff D.torus.unitSystem
    X₁.windingCurrent X₂.windingCurrent).mp
  change coherentCoordinate D.torus.unitSystem X₁.windingCurrent =
    coherentCoordinate D.torus.unitSystem X₂.windingCurrent
  apply mul_left_cancel₀ hturns
  calc
    (D.torus.turns : ℝ) *
        coherentCoordinate D.torus.unitSystem X₁.windingCurrent =
      coherentCoordinate D.torus.unitSystem D.torus.meanLoopLength *
        coherentCoordinate D.torus.unitSystem D.fieldStrength := h₁.symm
    _ = (D.torus.turns : ℝ) *
        coherentCoordinate D.torus.unitSystem X₂.windingCurrent := h₂

/-- Uniform flux linkage determines the typed linked-flux increment. -/
lemma linkedFluxChange_unique (D : SourceData)
    (X₁ X₂ : InstantaneousElectromagneticWitness)
    (h₁ : SatisfiesLinkedFluxChange D X₁)
    (h₂ : SatisfiesLinkedFluxChange D X₂) :
    X₁.linkedFluxChange = X₂.linkedFluxChange := by
  apply (coordinateInSI_eq_iff D.torus.unitSystem
    X₁.linkedFluxChange X₂.linkedFluxChange).mp
  change coherentCoordinate D.torus.unitSystem X₁.linkedFluxChange =
    coherentCoordinate D.torus.unitSystem X₂.linkedFluxChange
  exact h₁.trans h₂.symm

/-- Linked-flux and Faraday--Lenz laws determine the induced-emf increment. -/
lemma inducedEmfIncrement_unique (D : SourceData)
    (X₁ X₂ : InstantaneousElectromagneticWitness)
    (hflux₁ : SatisfiesLinkedFluxChange D X₁)
    (hfaraday₁ : SatisfiesFaradayLenzLaw D X₁)
    (hflux₂ : SatisfiesLinkedFluxChange D X₂)
    (hfaraday₂ : SatisfiesFaradayLenzLaw D X₂) :
    X₁.inducedEmfIncrement = X₂.inducedEmfIncrement := by
  have hlinked : X₁.linkedFluxChange = X₂.linkedFluxChange :=
    linkedFluxChange_unique D X₁ X₂ hflux₁ hflux₂
  apply (coordinateInSI_eq_iff D.torus.unitSystem
    X₁.inducedEmfIncrement X₂.inducedEmfIncrement).mp
  change coherentCoordinate D.torus.unitSystem X₁.inducedEmfIncrement =
    coherentCoordinate D.torus.unitSystem X₂.inducedEmfIncrement
  calc
    coherentCoordinate D.torus.unitSystem X₁.inducedEmfIncrement =
        -coherentCoordinate D.torus.unitSystem X₁.linkedFluxChange := hfaraday₁
    _ = -coherentCoordinate D.torus.unitSystem X₂.linkedFluxChange := by
      rw [hlinked]
    _ = coherentCoordinate D.torus.unitSystem X₂.inducedEmfIncrement :=
      hfaraday₂.symm

/-- Flux linkage, Faraday--Lenz, and source balance determine the source emf. -/
lemma sourceEmfIncrement_unique (D : SourceData)
    (X₁ X₂ : InstantaneousElectromagneticWitness)
    (hflux₁ : SatisfiesLinkedFluxChange D X₁)
    (hfaraday₁ : SatisfiesFaradayLenzLaw D X₁)
    (hsource₁ : SatisfiesSourceEmfBalance D X₁)
    (hflux₂ : SatisfiesLinkedFluxChange D X₂)
    (hfaraday₂ : SatisfiesFaradayLenzLaw D X₂)
    (hsource₂ : SatisfiesSourceEmfBalance D X₂) :
    X₁.sourceEmfIncrement = X₂.sourceEmfIncrement := by
  have hinduced : X₁.inducedEmfIncrement = X₂.inducedEmfIncrement :=
    inducedEmfIncrement_unique D X₁ X₂
      hflux₁ hfaraday₁ hflux₂ hfaraday₂
  apply (coordinateInSI_eq_iff D.torus.unitSystem
    X₁.sourceEmfIncrement X₂.sourceEmfIncrement).mp
  change coherentCoordinate D.torus.unitSystem X₁.sourceEmfIncrement =
    coherentCoordinate D.torus.unitSystem X₂.sourceEmfIncrement
  calc
    coherentCoordinate D.torus.unitSystem X₁.sourceEmfIncrement =
        -coherentCoordinate D.torus.unitSystem X₁.inducedEmfIncrement := hsource₁
    _ = -coherentCoordinate D.torus.unitSystem X₂.inducedEmfIncrement := by
      rw [hinduced]
    _ = coherentCoordinate D.torus.unitSystem X₂.sourceEmfIncrement :=
      hsource₂.symm

/-- The zero-loss law uniquely determines the typed wire-loss increment. -/
lemma wireLossIncrement_unique (D : SourceData)
    (X₁ X₂ : InstantaneousElectromagneticWitness)
    (h₁ : SatisfiesZeroWireLoss D X₁)
    (h₂ : SatisfiesZeroWireLoss D X₂) :
    X₁.wireLossIncrement = X₂.wireLossIncrement := by
  apply (coordinateInSI_eq_iff D.torus.unitSystem
    X₁.wireLossIncrement X₂.wireLossIncrement).mp
  change coherentCoordinate D.torus.unitSystem X₁.wireLossIncrement =
    coherentCoordinate D.torus.unitSystem X₂.wireLossIncrement
  exact h₁.trans h₂.symm

/-- For physical data, all five electromagnetic components are unique. -/
lemma electromagneticWitness_unique (D : SourceData) (hD : D.IsPhysical)
    (X₁ X₂ : InstantaneousElectromagneticWitness)
    (h₁ : SatisfiesElectromagneticLaws D X₁)
    (h₂ : SatisfiesElectromagneticLaws D X₂) :
    X₁ = X₂ := by
  rcases h₁ with ⟨hampere₁, hflux₁, hfaraday₁, hsource₁, hloss₁⟩
  rcases h₂ with ⟨hampere₂, hflux₂, hfaraday₂, hsource₂, hloss₂⟩
  have hwinding : X₁.windingCurrent = X₂.windingCurrent :=
    windingCurrent_unique D hD X₁ X₂ hampere₁ hampere₂
  have hlinked : X₁.linkedFluxChange = X₂.linkedFluxChange :=
    linkedFluxChange_unique D X₁ X₂ hflux₁ hflux₂
  have hinduced : X₁.inducedEmfIncrement = X₂.inducedEmfIncrement :=
    inducedEmfIncrement_unique D X₁ X₂
      hflux₁ hfaraday₁ hflux₂ hfaraday₂
  have hsource : X₁.sourceEmfIncrement = X₂.sourceEmfIncrement :=
    sourceEmfIncrement_unique D X₁ X₂
      hflux₁ hfaraday₁ hsource₁ hflux₂ hfaraday₂ hsource₂
  have hloss : X₁.wireLossIncrement = X₂.wireLossIncrement :=
    wireLossIncrement_unique D X₁ X₂ hloss₁ hloss₂
  cases X₁ with
  | mk winding₁ linked₁ induced₁ source₁ loss₁ =>
    cases X₂ with
    | mk winding₂ linked₂ induced₂ source₂ loss₂ =>
      dsimp only at hwinding hlinked hinduced hsource hloss
      subst winding₂
      subst linked₂
      subst induced₂
      subst source₂
      subst loss₂
      rfl

/-- Any two law-defined source-work candidates for physical data coincide. -/
theorem sourceWorkIncrement_unique (D : SourceData) (hD : D.IsPhysical)
    (W₁ W₂ : Energy)
    (h₁ : IsSourceWorkIncrementSolution D W₁)
    (h₂ : IsSourceWorkIncrementSolution D W₂) :
    W₁ = W₂ := by
  rcases h₁ with ⟨X₁, hEM₁, hwork₁⟩
  rcases h₂ with ⟨X₂, hEM₂, hwork₂⟩
  have hX : X₁ = X₂ :=
    electromagneticWitness_unique D hD X₁ X₂ hEM₁ hEM₂
  subst X₂
  apply (coordinateInSI_eq_iff D.torus.unitSystem W₁ W₂).mp
  change coherentCoordinate D.torus.unitSystem W₁ =
    coherentCoordinate D.torus.unitSystem W₂
  exact hwork₁.trans hwork₂.symm

/-! ## Existence and the answer-free target -/

/-- Physical source data have at least one witness-defined signed source
work increment. -/
lemma sourceWorkIncrement_exists (D : SourceData) (hD : D.IsPhysical) :
    ∃ W : Energy, IsSourceWorkIncrementSolution D W := by
  have hturnsNat : D.torus.turns ≠ 0 :=
    Nat.ne_of_gt hD.1.2.2.2.2.2.2.2.1
  have hturns : (D.torus.turns : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hturnsNat
  let currentCoordinate : ℝ :=
    coherentCoordinate D.torus.unitSystem D.torus.meanLoopLength *
      coherentCoordinate D.torus.unitSystem D.fieldStrength /
        (D.torus.turns : ℝ)
  let linkedCoordinate : ℝ :=
    (D.torus.turns : ℝ) *
      coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
        coherentCoordinate D.torus.unitSystem D.fluxDensityIncrement
  let inducedCoordinate : ℝ := -linkedCoordinate
  let sourceCoordinate : ℝ := -inducedCoordinate
  let lossCoordinate : ℝ := 0
  let X : InstantaneousElectromagneticWitness :=
    { windingCurrent :=
        quantityFromCoherentCoordinate D.torus.unitSystem
          currentDimension currentCoordinate
      linkedFluxChange :=
        quantityFromCoherentCoordinate D.torus.unitSystem
          magneticFluxDimension linkedCoordinate
      inducedEmfIncrement :=
        quantityFromCoherentCoordinate D.torus.unitSystem
          magneticFluxDimension inducedCoordinate
      sourceEmfIncrement :=
        quantityFromCoherentCoordinate D.torus.unitSystem
          magneticFluxDimension sourceCoordinate
      wireLossIncrement :=
        quantityFromCoherentCoordinate D.torus.unitSystem
          energyDimension lossCoordinate }
  let workCoordinate : ℝ :=
    currentCoordinate * sourceCoordinate + lossCoordinate
  let W : Energy :=
    quantityFromCoherentCoordinate D.torus.unitSystem
      energyDimension workCoordinate
  refine ⟨W, X, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change coherentCoordinate D.torus.unitSystem D.torus.meanLoopLength *
          coherentCoordinate D.torus.unitSystem D.fieldStrength =
        (D.torus.turns : ℝ) *
          coherentCoordinate D.torus.unitSystem
            (quantityFromCoherentCoordinate D.torus.unitSystem
              currentDimension currentCoordinate)
      rw [coherentCoordinate_quantityFromCoherentCoordinate]
      dsimp [currentCoordinate]
      exact (mul_div_cancel₀
        (coherentCoordinate D.torus.unitSystem D.torus.meanLoopLength *
          coherentCoordinate D.torus.unitSystem D.fieldStrength) hturns).symm
    · change coherentCoordinate D.torus.unitSystem
          (quantityFromCoherentCoordinate D.torus.unitSystem
            magneticFluxDimension linkedCoordinate) =
        (D.torus.turns : ℝ) *
          coherentCoordinate D.torus.unitSystem D.torus.crossSectionArea *
            coherentCoordinate D.torus.unitSystem D.fluxDensityIncrement
      rw [coherentCoordinate_quantityFromCoherentCoordinate]
    · change coherentCoordinate D.torus.unitSystem
          (quantityFromCoherentCoordinate D.torus.unitSystem
            magneticFluxDimension inducedCoordinate) =
        -coherentCoordinate D.torus.unitSystem
          (quantityFromCoherentCoordinate D.torus.unitSystem
            magneticFluxDimension linkedCoordinate)
      rw [coherentCoordinate_quantityFromCoherentCoordinate,
        coherentCoordinate_quantityFromCoherentCoordinate]
    · change coherentCoordinate D.torus.unitSystem
          (quantityFromCoherentCoordinate D.torus.unitSystem
            magneticFluxDimension sourceCoordinate) =
        -coherentCoordinate D.torus.unitSystem
          (quantityFromCoherentCoordinate D.torus.unitSystem
            magneticFluxDimension inducedCoordinate)
      rw [coherentCoordinate_quantityFromCoherentCoordinate,
        coherentCoordinate_quantityFromCoherentCoordinate]
    · change coherentCoordinate D.torus.unitSystem
          (quantityFromCoherentCoordinate D.torus.unitSystem
            energyDimension lossCoordinate) = 0
      rw [coherentCoordinate_quantityFromCoherentCoordinate]
  · change coherentCoordinate D.torus.unitSystem
        (quantityFromCoherentCoordinate D.torus.unitSystem
          energyDimension workCoordinate) =
      coherentCoordinate D.torus.unitSystem
          (quantityFromCoherentCoordinate D.torus.unitSystem
            currentDimension currentCoordinate) *
        coherentCoordinate D.torus.unitSystem
          (quantityFromCoherentCoordinate D.torus.unitSystem
            magneticFluxDimension sourceCoordinate) +
      coherentCoordinate D.torus.unitSystem
        (quantityFromCoherentCoordinate D.torus.unitSystem
          energyDimension lossCoordinate)
    rw [coherentCoordinate_quantityFromCoherentCoordinate,
      coherentCoordinate_quantityFromCoherentCoordinate,
      coherentCoordinate_quantityFromCoherentCoordinate,
      coherentCoordinate_quantityFromCoherentCoordinate]

/-- The external source performs a unique signed work increment determined by
the instantaneous electromagnetic laws, without placing its eliminated value
in the theorem signature. -/
theorem existsUnique_sourceWorkIncrement (D : SourceData)
    (hD : D.IsPhysical) :
    ∃! W : Energy, IsSourceWorkIncrementSolution D W := by
  rcases sourceWorkIncrement_exists D hD with ⟨W, hW⟩
  refine ⟨W, hW, ?_⟩
  intro other hother
  exact sourceWorkIncrement_unique D hD other W hother hW

end Ipho2026Gpt56solBlind.ProblemIPhO2026_3_A_2
