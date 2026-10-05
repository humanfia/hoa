import Ipho2026Gpt56solBlind.Shared.CoulombOrbit

/-!
# IPhO 2026 Problem 1 B.2

An answer-free model of the oriented electron--positron Coulomb-scattering
question.  The requested degree value appears only as the unknown in
`AsymptoticAngleDegreesSolution`.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_1_B_2

open Ipho2026Gpt56solBlind.Shared.CoulombOrbit

noncomputable section

/-- The positive source constants, together with the two identities stated
in the problem.  The charge field is the positive charge magnitude; the two
particle charges are `+chargeMagnitude` and `-chargeMagnitude`. -/
structure SourceParameters where
  mass : ℝ
  chargeMagnitude : ℝ
  vacuumPermittivity : ℝ
  reducedPlanckConstant : ℝ
  coulombConstant : ℝ
  bohrRadius : ℝ
  mass_pos : 0 < mass
  chargeMagnitude_pos : 0 < chargeMagnitude
  vacuumPermittivity_pos : 0 < vacuumPermittivity
  reducedPlanckConstant_pos : 0 < reducedPlanckConstant
  coulombConstant_pos : 0 < coulombConstant
  bohrRadius_pos : 0 < bohrRadius
  coulombConstant_eq :
    coulombConstant = 1 / (4 * Real.pi * vacuumPermittivity)
  bohrRadius_eq :
    bohrRadius =
      4 * Real.pi * vacuumPermittivity * reducedPlanckConstant ^ 2 /
        (mass * chargeMagnitude ^ 2)

/-- The shared attractive Coulomb system specialized to equal masses and
opposite charges of common magnitude. -/
def sourceSystem (parameters : SourceParameters) : System where
  mass₁ := parameters.mass
  mass₂ := parameters.mass
  coupling := parameters.coulombConstant * parameters.chargeMagnitude ^ 2
  mass₁_pos := parameters.mass_pos
  mass₂_pos := parameters.mass_pos
  coupling_pos :=
    mul_pos parameters.coulombConstant_pos
      (pow_pos parameters.chargeMagnitude_pos 2)

/-- Equal masses give reduced mass `m / 2`, and the two source identities
give the unit-cancelling Bohr-scale relation. -/
lemma sourceSystem_identities (parameters : SourceParameters) :
    reducedMass (sourceSystem parameters) = parameters.mass / 2 ∧
      (sourceSystem parameters).coupling =
        parameters.coulombConstant * parameters.chargeMagnitude ^ 2 ∧
      parameters.mass * (sourceSystem parameters).coupling *
          parameters.bohrRadius =
        parameters.reducedPlanckConstant ^ 2 := by
  refine ⟨?_, rfl, ?_⟩
  · change
      parameters.mass * parameters.mass /
          (parameters.mass + parameters.mass) =
        parameters.mass / 2
    apply (div_eq_iff (ne_of_gt (add_pos parameters.mass_pos parameters.mass_pos))).2
    ring
  · change parameters.mass *
      (parameters.coulombConstant * parameters.chargeMagnitude ^ 2) *
        parameters.bohrRadius = parameters.reducedPlanckConstant ^ 2
    rw [parameters.coulombConstant_eq, parameters.bohrRadius_eq]
    have hdenom₁ :
        4 * Real.pi * parameters.vacuumPermittivity ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        parameters.vacuumPermittivity_pos.ne'
    have hdenom₂ :
        parameters.mass * parameters.chargeMagnitude ^ 2 ≠ 0 :=
      mul_ne_zero parameters.mass_pos.ne'
        (pow_ne_zero 2 parameters.chargeMagnitude_pos.ne')
    calc
      parameters.mass *
            (1 / (4 * Real.pi * parameters.vacuumPermittivity) *
              parameters.chargeMagnitude ^ 2) *
          (4 * Real.pi * parameters.vacuumPermittivity *
              parameters.reducedPlanckConstant ^ 2 /
            (parameters.mass * parameters.chargeMagnitude ^ 2)) =
          ((4 * Real.pi * parameters.vacuumPermittivity)⁻¹ *
              (4 * Real.pi * parameters.vacuumPermittivity)) *
            ((parameters.mass * parameters.chargeMagnitude ^ 2) *
              (parameters.mass * parameters.chargeMagnitude ^ 2)⁻¹) *
            parameters.reducedPlanckConstant ^ 2 := by
              rw [one_div, div_eq_mul_inv]
              ring
      _ = parameters.reducedPlanckConstant ^ 2 := by
        rw [inv_mul_cancel₀ hdenom₁, mul_inv_cancel₀ hdenom₂]
        ring

/-- Signed angular momenta of the positron and electron about the equal-mass
centre of mass.  The relative position points from electron to positron. -/
def individualAngularMomenta
    (parameters : SourceParameters)
    (relativePosition positronVelocity electronVelocity :
      EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  (parameters.mass *
      planarCross ((1 / 2 : ℝ) • relativePosition) positronVelocity,
    parameters.mass *
      planarCross ((-1 / 2 : ℝ) • relativePosition) electronVelocity)

/-- The finite-time source data with the orientation shown in Figure 1b.
The reference direction points along the positron's initial velocity. -/
def OrientedInitialData
    (parameters : SourceParameters) (trajectory : Trajectory)
    (referenceTime : ℝ)
    (initialDirection positronVelocity electronVelocity :
      EuclideanSpace ℝ (Fin 2)) : Prop :=
  let relativePosition := trajectory.position referenceTime
  ‖initialDirection‖ = 1 ∧
    ‖relativePosition‖ = 100 * parameters.bohrRadius ∧
    inner ℝ relativePosition initialDirection = 0 ∧
    planarCross initialDirection relativePosition =
      100 * parameters.bohrRadius ∧
    (∃ positronSpeed electronSpeed : ℝ,
      0 < positronSpeed ∧
      0 < electronSpeed ∧
      positronVelocity = positronSpeed • initialDirection ∧
      electronVelocity = (-electronSpeed) • initialDirection ∧
      trajectory.velocity referenceTime =
        positronVelocity - electronVelocity) ∧
    |(individualAngularMomenta parameters relativePosition
        positronVelocity electronVelocity).1| =
      (15 / 2 : ℝ) * parameters.reducedPlanckConstant ∧
    |(individualAngularMomenta parameters relativePosition
        positronVelocity electronVelocity).2| =
      (15 / 2 : ℝ) * parameters.reducedPlanckConstant

/-- Figure 1b fixes the signs of both individual angular momenta and of the
carrier's total relative angular momentum. -/
lemma orientedInitialData_angularMomenta
    (parameters : SourceParameters) (trajectory : Trajectory)
    (referenceTime : ℝ)
    (initialDirection positronVelocity electronVelocity :
      EuclideanSpace ℝ (Fin 2))
    (hInitial : OrientedInitialData parameters trajectory referenceTime
      initialDirection positronVelocity electronVelocity) :
    let moments := individualAngularMomenta parameters
      (trajectory.position referenceTime) positronVelocity electronVelocity
    let H := (OrbitalInvariants (sourceSystem parameters) trajectory
      referenceTime).2
    moments.1 = moments.2 ∧
      H = moments.1 + moments.2 ∧
      moments.1 < 0 ∧ moments.2 < 0 ∧ H < 0 := by
  dsimp only
  unfold OrientedInitialData at hInitial
  dsimp only at hInitial
  rcases hInitial with
    ⟨hDirectionNorm, hPositionNorm, hOrthogonal, hOrientation,
      ⟨positronSpeed, electronSpeed, hPositronSpeed, hElectronSpeed,
        hPositronVelocity, hElectronVelocity, hRelativeVelocity⟩,
      hPositronMagnitude, hElectronMagnitude⟩
  have hCrossReverse :
      planarCross (trajectory.position referenceTime) initialDirection =
        -(100 * parameters.bohrRadius) := by
    unfold planarCross at hOrientation ⊢
    linarith
  have hPositronMoment :
      (individualAngularMomenta parameters
        (trajectory.position referenceTime) positronVelocity electronVelocity).1 =
        parameters.mass * ((1 / 2 : ℝ) * positronSpeed *
          planarCross (trajectory.position referenceTime) initialDirection) := by
    rw [hPositronVelocity]
    unfold individualAngularMomenta planarCross
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hElectronMoment :
      (individualAngularMomenta parameters
        (trajectory.position referenceTime) positronVelocity electronVelocity).2 =
        parameters.mass * ((1 / 2 : ℝ) * electronSpeed *
          planarCross (trajectory.position referenceTime) initialDirection) := by
    rw [hElectronVelocity]
    unfold individualAngularMomenta planarCross
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hPositronMomentNeg :
      (individualAngularMomenta parameters
        (trajectory.position referenceTime) positronVelocity electronVelocity).1 < 0 := by
    rw [hPositronMoment, hCrossReverse]
    exact mul_neg_of_pos_of_neg parameters.mass_pos
      (mul_neg_of_pos_of_neg (mul_pos (by norm_num) hPositronSpeed)
        (neg_neg_of_pos (mul_pos (by norm_num) parameters.bohrRadius_pos)))
  have hElectronMomentNeg :
      (individualAngularMomenta parameters
        (trajectory.position referenceTime) positronVelocity electronVelocity).2 < 0 := by
    rw [hElectronMoment, hCrossReverse]
    exact mul_neg_of_pos_of_neg parameters.mass_pos
      (mul_neg_of_pos_of_neg (mul_pos (by norm_num) hElectronSpeed)
        (neg_neg_of_pos (mul_pos (by norm_num) parameters.bohrRadius_pos)))
  have hMomentsEqual :
      (individualAngularMomenta parameters
        (trajectory.position referenceTime) positronVelocity electronVelocity).1 =
      (individualAngularMomenta parameters
        (trajectory.position referenceTime) positronVelocity electronVelocity).2 := by
    have hAbsEqual := hPositronMagnitude.trans hElectronMagnitude.symm
    rw [abs_of_neg hPositronMomentNeg, abs_of_neg hElectronMomentNeg] at hAbsEqual
    linarith
  have hTotalMoment :
      (OrbitalInvariants (sourceSystem parameters) trajectory referenceTime).2 =
        (individualAngularMomenta parameters
          (trajectory.position referenceTime) positronVelocity electronVelocity).1 +
        (individualAngularMomenta parameters
          (trajectory.position referenceTime) positronVelocity electronVelocity).2 := by
    unfold OrbitalInvariants
    rw [(sourceSystem_identities parameters).1, hRelativeVelocity,
      hPositronMoment, hElectronMoment, hPositronVelocity, hElectronVelocity]
    unfold planarCross
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  refine ⟨hMomentsEqual, hTotalMoment, hPositronMomentNeg,
    hElectronMomentNeg, ?_⟩
  rw [hTotalMoment]
  linarith

/-- All oriented initial-data realizations for fixed source parameters have
the same scalar energy and the same signed angular momentum. -/
lemma orientedInitialData_invariants_determined
    (parameters : SourceParameters)
    (trajectory₁ trajectory₂ : Trajectory)
    (referenceTime₁ referenceTime₂ : ℝ)
    (initialDirection₁ positronVelocity₁ electronVelocity₁
      initialDirection₂ positronVelocity₂ electronVelocity₂ :
      EuclideanSpace ℝ (Fin 2))
    (hInitial₁ : OrientedInitialData parameters trajectory₁ referenceTime₁
      initialDirection₁ positronVelocity₁ electronVelocity₁)
    (hInitial₂ : OrientedInitialData parameters trajectory₂ referenceTime₂
      initialDirection₂ positronVelocity₂ electronVelocity₂) :
    (OrbitalInvariants (sourceSystem parameters) trajectory₁ referenceTime₁).1 =
        (OrbitalInvariants (sourceSystem parameters) trajectory₂ referenceTime₂).1 ∧
      (OrbitalInvariants (sourceSystem parameters) trajectory₁ referenceTime₁).2 =
        (OrbitalInvariants (sourceSystem parameters) trajectory₂ referenceTime₂).2 := by
  have hAngular₁ := orientedInitialData_angularMomenta parameters trajectory₁
    referenceTime₁ initialDirection₁ positronVelocity₁ electronVelocity₁ hInitial₁
  have hAngular₂ := orientedInitialData_angularMomenta parameters trajectory₂
    referenceTime₂ initialDirection₂ positronVelocity₂ electronVelocity₂ hInitial₂
  dsimp only at hAngular₁ hAngular₂
  unfold OrientedInitialData at hInitial₁ hInitial₂
  dsimp only at hInitial₁ hInitial₂
  rcases hInitial₁ with
    ⟨hDirectionNorm₁, hPositionNorm₁, hOrthogonal₁, hOrientation₁,
      ⟨positronSpeed₁, electronSpeed₁, hPositronSpeed₁, hElectronSpeed₁,
        hPositronVelocity₁, hElectronVelocity₁, hRelativeVelocity₁⟩,
      hPositronMagnitude₁, hElectronMagnitude₁⟩
  rcases hInitial₂ with
    ⟨hDirectionNorm₂, hPositionNorm₂, hOrthogonal₂, hOrientation₂,
      ⟨positronSpeed₂, electronSpeed₂, hPositronSpeed₂, hElectronSpeed₂,
        hPositronVelocity₂, hElectronVelocity₂, hRelativeVelocity₂⟩,
      hPositronMagnitude₂, hElectronMagnitude₂⟩
  have hFirstMomentEqual :
      (individualAngularMomenta parameters
        (trajectory₁.position referenceTime₁) positronVelocity₁ electronVelocity₁).1 =
      (individualAngularMomenta parameters
        (trajectory₂.position referenceTime₂) positronVelocity₂ electronVelocity₂).1 := by
    have hAbsEqual := hPositronMagnitude₁.trans hPositronMagnitude₂.symm
    rw [abs_of_neg hAngular₁.2.2.1, abs_of_neg hAngular₂.2.2.1] at hAbsEqual
    linarith
  have hAngularEqual :
      (OrbitalInvariants (sourceSystem parameters) trajectory₁ referenceTime₁).2 =
        (OrbitalInvariants (sourceSystem parameters) trajectory₂ referenceTime₂).2 := by
    calc
      (OrbitalInvariants (sourceSystem parameters) trajectory₁ referenceTime₁).2 =
          (individualAngularMomenta parameters
              (trajectory₁.position referenceTime₁) positronVelocity₁ electronVelocity₁).1 +
            (individualAngularMomenta parameters
              (trajectory₁.position referenceTime₁) positronVelocity₁ electronVelocity₁).2 :=
        hAngular₁.2.1
      _ = 2 * (individualAngularMomenta parameters
              (trajectory₁.position referenceTime₁) positronVelocity₁ electronVelocity₁).1 := by
        rw [hAngular₁.1]
        ring
      _ = 2 * (individualAngularMomenta parameters
              (trajectory₂.position referenceTime₂) positronVelocity₂ electronVelocity₂).1 := by
        rw [hFirstMomentEqual]
      _ = (individualAngularMomenta parameters
              (trajectory₂.position referenceTime₂) positronVelocity₂ electronVelocity₂).1 +
            (individualAngularMomenta parameters
              (trajectory₂.position referenceTime₂) positronVelocity₂ electronVelocity₂).2 := by
        rw [hAngular₂.1]
        ring
      _ = (OrbitalInvariants (sourceSystem parameters) trajectory₂ referenceTime₂).2 :=
        hAngular₂.2.1.symm
  have hVelocityOrthogonal₁ :
      inner ℝ (trajectory₁.position referenceTime₁)
        (trajectory₁.velocity referenceTime₁) = 0 := by
    rw [hRelativeVelocity₁, hPositronVelocity₁, hElectronVelocity₁]
    simp only [inner_sub_right, inner_smul_right]
    rw [hOrthogonal₁]
    ring
  have hVelocityOrthogonal₂ :
      inner ℝ (trajectory₂.position referenceTime₂)
        (trajectory₂.velocity referenceTime₂) = 0 := by
    rw [hRelativeVelocity₂, hPositronVelocity₂, hElectronVelocity₂]
    simp only [inner_sub_right, inner_smul_right]
    rw [hOrthogonal₂]
    ring
  have hCrossEqual :
      planarCross (trajectory₁.position referenceTime₁)
          (trajectory₁.velocity referenceTime₁) =
        planarCross (trajectory₂.position referenceTime₂)
          (trajectory₂.velocity referenceTime₂) := by
    unfold OrbitalInvariants at hAngularEqual
    exact mul_left_cancel₀ (reducedMass_pos (sourceSystem parameters)).ne'
      hAngularEqual
  have hLagrange₁ := norm_mul_norm_eq_dot_sq_add_cross_sq
    (trajectory₁.position referenceTime₁) (trajectory₁.velocity referenceTime₁)
  have hLagrange₂ := norm_mul_norm_eq_dot_sq_add_cross_sq
    (trajectory₂.position referenceTime₂) (trajectory₂.velocity referenceTime₂)
  rw [hVelocityOrthogonal₁, hPositionNorm₁] at hLagrange₁
  rw [hVelocityOrthogonal₂, hPositionNorm₂] at hLagrange₂
  norm_num at hLagrange₁ hLagrange₂
  have hNormProducts :
      (100 * parameters.bohrRadius) ^ 2 *
          ‖trajectory₁.velocity referenceTime₁‖ ^ 2 =
        (100 * parameters.bohrRadius) ^ 2 *
          ‖trajectory₂.velocity referenceTime₂‖ ^ 2 := by
    calc
      (100 * parameters.bohrRadius) ^ 2 *
          ‖trajectory₁.velocity referenceTime₁‖ ^ 2 =
        planarCross (trajectory₁.position referenceTime₁)
            (trajectory₁.velocity referenceTime₁) ^ 2 := hLagrange₁
      _ = planarCross (trajectory₂.position referenceTime₂)
            (trajectory₂.velocity referenceTime₂) ^ 2 := by rw [hCrossEqual]
      _ = (100 * parameters.bohrRadius) ^ 2 *
          ‖trajectory₂.velocity referenceTime₂‖ ^ 2 := hLagrange₂.symm
  have hVelocityNormSqEqual :
      ‖trajectory₁.velocity referenceTime₁‖ ^ 2 =
        ‖trajectory₂.velocity referenceTime₂‖ ^ 2 := by
    exact mul_left_cancel₀
      (pow_ne_zero 2 (mul_ne_zero (by norm_num) parameters.bohrRadius_pos.ne'))
      hNormProducts
  refine ⟨?_, hAngularEqual⟩
  unfold OrbitalInvariants radius
  rw [hVelocityNormSqEqual, hPositionNorm₁, hPositionNorm₂]

/-- Data carried by one lawful scattering realization. -/
structure ScatteringRealization where
  trajectory : Trajectory
  frame : OrbitalFrame
  phase : ℝ → ℝ
  energy : ℝ
  signedAngularMomentum : ℝ
  conicNumerator : ℝ
  eccentricity : ℝ
  asymptoticPhase : ℝ
  referenceTime : ℝ
  initialDirection : EuclideanSpace ℝ (Fin 2)
  positronVelocity : EuclideanSpace ℝ (Fin 2)
  electronVelocity : EuclideanSpace ℝ (Fin 2)
  incomingRelativeVelocity : EuclideanSpace ℝ (Fin 2)
  outgoingRelativeVelocity : EuclideanSpace ℝ (Fin 2)

/-- A realization obeys the oriented source data, the positive-energy
attractive scattering carrier, and the ordered incoming/outgoing limits. -/
def IsAdmissibleScattering
    (parameters : SourceParameters) (realization : ScatteringRealization) : Prop :=
  OrientedInitialData parameters realization.trajectory realization.referenceTime
      realization.initialDirection realization.positronVelocity
      realization.electronVelocity ∧
    0 < realization.energy ∧
    SatisfiesScatteringConicCarrier (sourceSystem parameters)
      realization.trajectory realization.energy realization.signedAngularMomentum
      realization.conicNumerator realization.eccentricity
      realization.asymptoticPhase realization.frame realization.phase
      realization.referenceTime ∧
    SatisfiesAsymptoticDirectionCarrier realization.trajectory
      realization.incomingRelativeVelocity realization.outgoingRelativeVelocity

/-- Nonvacuity of the source's stated unbound scattering case. -/
def HasAdmissibleScattering (parameters : SourceParameters) : Prop :=
  ∃ realization : ScatteringRealization,
    IsAdmissibleScattering parameters realization

/-- Remove a planar vector's magnitude, leaving its dimensionless direction. -/
def normalizedDirection (vector : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  ‖vector‖⁻¹ • vector

/-- The future asymptotic relative velocity in an admissible realization is
nonzero. -/
lemma admissible_outgoing_ne_zero
    (parameters : SourceParameters) (realization : ScatteringRealization)
    (hAdmissible : IsAdmissibleScattering parameters realization) :
    realization.outgoingRelativeVelocity ≠ 0 := by
  rcases hAdmissible with ⟨hInitial, hEnergy, hCarrier, hAsymptotic⟩
  have hDirections := scatteringConic_asymptotic_directions
    (sourceSystem parameters) realization.trajectory realization.energy
    realization.signedAngularMomentum realization.conicNumerator
    realization.eccentricity realization.asymptoticPhase realization.frame
    realization.phase realization.referenceTime realization.incomingRelativeVelocity
    realization.outgoingRelativeVelocity hCarrier hAsymptotic
  intro hzero
  have hNorm := hDirections.2.2.1
  rw [hzero, norm_zero] at hNorm
  linarith [hDirections.2.2.2.1]

/-- The dot and oriented-cross components of the future unit direction,
relative to the initial positron direction, do not depend on the realization. -/
lemma admissible_outgoing_direction_components_eq
    (parameters : SourceParameters)
    (realization₁ realization₂ : ScatteringRealization)
    (hAdmissible₁ : IsAdmissibleScattering parameters realization₁)
    (hAdmissible₂ : IsAdmissibleScattering parameters realization₂) :
    inner ℝ (normalizedDirection realization₁.initialDirection)
        (normalizedDirection realization₁.outgoingRelativeVelocity) =
      inner ℝ (normalizedDirection realization₂.initialDirection)
        (normalizedDirection realization₂.outgoingRelativeVelocity) ∧
    planarCross (normalizedDirection realization₁.initialDirection)
        (normalizedDirection realization₁.outgoingRelativeVelocity) =
      planarCross (normalizedDirection realization₂.initialDirection)
        (normalizedDirection realization₂.outgoingRelativeVelocity) := by
  have realization_components
      (realization : ScatteringRealization)
      (hAdmissible : IsAdmissibleScattering parameters realization) :
      inner ℝ (normalizedDirection realization.initialDirection)
          (normalizedDirection realization.outgoingRelativeVelocity) =
          Real.sin realization.asymptoticPhase ∧
        planarCross (normalizedDirection realization.initialDirection)
          (normalizedDirection realization.outgoingRelativeVelocity) =
          -Real.cos realization.asymptoticPhase := by
    rcases hAdmissible with
      ⟨hInitialForAngular, hEnergyPositive, hCarrierForTheorems, hAsymptotic⟩
    have hAngularInitial := orientedInitialData_angularMomenta parameters
      realization.trajectory realization.referenceTime realization.initialDirection
      realization.positronVelocity realization.electronVelocity hInitialForAngular
    dsimp only at hAngularInitial
    have hInitial := hInitialForAngular
    unfold OrientedInitialData at hInitial
    dsimp only at hInitial
    rcases hInitial with
      ⟨hDirectionNorm, hPositionNorm, hOrthogonal, hOrientation,
        ⟨positronSpeed, electronSpeed, hPositronSpeed, hElectronSpeed,
          hPositronVelocity, hElectronVelocity, hRelativeVelocity⟩,
        hPositronMagnitude, hElectronMagnitude⟩
    have hCarrier := hCarrierForTheorems
    rcases hCarrier with
      ⟨hLaw, hEnergyInvariant, hAngularInvariant, hNumeratorPositive,
        hEccentricityGt, hAlphaPositive, hAlphaLt, hEccentricityCos,
        hEccentricityRelation, hPhase, hPosition⟩
    rcases hPhase with
      ⟨hPhaseAlphaPositive, hPhaseAlphaLt, hPhaseContDiff, hPhaseStrict,
        hPhaseDerivPositive, hPhaseRange, hPhaseAtBot, hPhaseAtTop⟩
    have hTotalSpeedPositive : 0 < positronSpeed + electronSpeed :=
      add_pos hPositronSpeed hElectronSpeed
    have hVelocityDirection :
        realization.trajectory.velocity realization.referenceTime =
          (positronSpeed + electronSpeed) • realization.initialDirection := by
      rw [hRelativeVelocity, hPositronVelocity, hElectronVelocity]
      ext i
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hNormalizedInitialDirection :
        normalizedDirection realization.initialDirection =
          realization.initialDirection := by
      unfold normalizedDirection
      rw [hDirectionNorm]
      norm_num
    have hVelocityNorm :
        ‖realization.trajectory.velocity realization.referenceTime‖ =
          positronSpeed + electronSpeed := by
      rw [hVelocityDirection, norm_smul, hDirectionNorm]
      simp only [mul_one, Real.norm_eq_abs]
      rw [abs_of_pos hTotalSpeedPositive]
    have hNormalizedVelocity :
        normalizedDirection
            (realization.trajectory.velocity realization.referenceTime) =
          realization.initialDirection := by
      unfold normalizedDirection
      rw [hVelocityNorm, hVelocityDirection, smul_smul,
        inv_mul_cancel₀ hTotalSpeedPositive.ne', one_smul]
    have hVelocityOrthogonal :
        inner ℝ (realization.trajectory.position realization.referenceTime)
          (realization.trajectory.velocity realization.referenceTime) = 0 := by
      rw [hVelocityDirection, inner_smul_right, hOrthogonal]
      simp
    have hRadialSpeedZero :
        radialSpeed realization.trajectory realization.referenceTime = 0 := by
      unfold radialSpeed
      rw [hVelocityOrthogonal]
      simp
    have hRadiusPositive :
        0 < radius realization.trajectory realization.referenceTime := by
      unfold radius
      rw [hPositionNorm]
      exact mul_pos (by norm_num) parameters.bohrRadius_pos
    have hParameters := scatteringConic_parameter_identities
      (sourceSystem parameters) realization.trajectory realization.energy
      realization.signedAngularMomentum realization.conicNumerator
      realization.eccentricity realization.asymptoticPhase realization.frame
      realization.phase realization.referenceTime hCarrierForTheorems
    have hTurningRoot :
        turningPolynomial (sourceSystem parameters) realization.energy
            realization.signedAngularMomentum
            (radius realization.trajectory realization.referenceTime) = 0 :=
      (radialSpeed_eq_zero_iff_turningPolynomial_eq_zero
        (sourceSystem parameters) realization.trajectory realization.energy
        realization.signedAngularMomentum realization.referenceTime
        hEnergyInvariant hAngularInvariant).mp hRadialSpeedZero
    have hRadiusPeriapsis :
        radius realization.trajectory realization.referenceTime =
          realization.conicNumerator / (1 + realization.eccentricity) :=
      (hParameters.2.2.2.2.1
        (radius realization.trajectory realization.referenceTime)
        hRadiusPositive).mp hTurningRoot
    have hAlphaMem :
        realization.asymptoticPhase ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hAlphaPositive.le, by nlinarith only [hAlphaLt, Real.pi_pos]⟩
    have hDenominatorPositive (t : ℝ) :
        0 < 1 - realization.eccentricity * Real.cos (realization.phase t) := by
      have hThetaMem : realization.phase t ∈
          Set.Ioo realization.asymptoticPhase
            (2 * Real.pi - realization.asymptoticPhase) := by
        rw [← hPhaseRange]
        exact Set.mem_range_self t
      have hEccentricityPositive : 0 < realization.eccentricity :=
        lt_trans zero_lt_one hEccentricityGt
      have hCosLt : Real.cos (realization.phase t) <
          Real.cos realization.asymptoticPhase := by
        by_cases hle : realization.phase t ≤ Real.pi
        · exact Real.strictAntiOn_cos hAlphaMem
            ⟨(lt_trans hAlphaPositive hThetaMem.1).le, hle⟩ hThetaMem.1
        · have hgt : Real.pi < realization.phase t := lt_of_not_ge hle
          have hReflectedMem : 2 * Real.pi - realization.phase t ∈
              Set.Icc (0 : ℝ) Real.pi := by
            constructor
            · nlinarith only [hThetaMem.2, hAlphaPositive]
            · nlinarith only [hgt]
          have hAlphaReflected : realization.asymptoticPhase <
              2 * Real.pi - realization.phase t := by
            nlinarith only [hThetaMem.2]
          have hlt := Real.strictAntiOn_cos hAlphaMem hReflectedMem
            hAlphaReflected
          rwa [Real.cos_two_pi_sub] at hlt
      have hScaledCos := mul_lt_mul_of_pos_left hCosLt hEccentricityPositive
      rw [hEccentricityCos] at hScaledCos
      linarith
    have hRadiusFormula :
        radius realization.trajectory realization.referenceTime =
          realization.conicNumerator /
            (1 - realization.eccentricity *
              Real.cos (realization.phase realization.referenceTime)) := by
      unfold radius
      rw [hPosition realization.referenceTime, norm_smul,
        (polarDirection_identities realization.frame
          (realization.phase realization.referenceTime)).1]
      simp only [mul_one, Real.norm_eq_abs]
      rw [abs_of_pos (div_pos hNumeratorPositive
        (hDenominatorPositive realization.referenceTime))]
    have hDenominatorEqual :
        1 + realization.eccentricity =
          1 - realization.eccentricity *
            Real.cos (realization.phase realization.referenceTime) := by
      have hCrossMultiplication :=
        (div_eq_div_iff
          (hDenominatorPositive realization.referenceTime).ne'
          (by nlinarith only [hEccentricityGt] :
            (1 + realization.eccentricity) ≠ 0)).mp
          (hRadiusFormula.symm.trans hRadiusPeriapsis)
      exact mul_left_cancel₀ hNumeratorPositive.ne' hCrossMultiplication
    have hCosReference :
        Real.cos (realization.phase realization.referenceTime) = -1 := by
      have hEccentricityPositive : 0 < realization.eccentricity :=
        lt_trans zero_lt_one hEccentricityGt
      nlinarith only [hDenominatorEqual, hEccentricityPositive]
    have hThetaMem : realization.phase realization.referenceTime ∈
        Set.Ioo realization.asymptoticPhase
          (2 * Real.pi - realization.asymptoticPhase) := by
      rw [← hPhaseRange]
      exact Set.mem_range_self realization.referenceTime
    have hPhaseReference :
        realization.phase realization.referenceTime = Real.pi := by
      have hThetaPositive :
          0 < realization.phase realization.referenceTime :=
        lt_trans hAlphaPositive hThetaMem.1
      by_cases hle : realization.phase realization.referenceTime ≤ Real.pi
      · by_contra hne
        have hlt : realization.phase realization.referenceTime < Real.pi :=
          lt_of_le_of_ne hle hne
        have hCosStrict := Real.strictAntiOn_cos
          ⟨hThetaPositive.le, hle⟩ ⟨Real.pi_pos.le, le_rfl⟩ hlt
        rw [hCosReference, Real.cos_pi] at hCosStrict
        linarith
      · exfalso
        have hgt : Real.pi < realization.phase realization.referenceTime :=
          lt_of_not_ge hle
        have hReflectedPositive :
            0 < 2 * Real.pi - realization.phase realization.referenceTime := by
          nlinarith only [hThetaMem.2, hAlphaPositive]
        have hReflectedLt :
            2 * Real.pi - realization.phase realization.referenceTime < Real.pi := by
          nlinarith only [hgt]
        have hReflectedCos :
            Real.cos (2 * Real.pi - realization.phase realization.referenceTime) =
              -1 := by
          rw [Real.cos_two_pi_sub, hCosReference]
        have hCosStrict := Real.strictAntiOn_cos
          ⟨hReflectedPositive.le, hReflectedLt.le⟩
          ⟨Real.pi_pos.le, le_rfl⟩ hReflectedLt
        rw [hReflectedCos, Real.cos_pi] at hCosStrict
        linarith
    have hThetaDerivative :
        HasDerivAt realization.phase
          (deriv realization.phase realization.referenceTime)
          realization.referenceTime :=
      (hPhaseContDiff.differentiable (by norm_num)
        realization.referenceTime).hasDerivAt
    have hRhoDerivative :
        HasDerivAt
          (fun z ↦ realization.conicNumerator /
            (1 - realization.eccentricity * Real.cos (realization.phase z)))
          (-(realization.conicNumerator * realization.eccentricity *
              Real.sin (realization.phase realization.referenceTime) *
              deriv realization.phase realization.referenceTime) /
            (1 - realization.eccentricity *
              Real.cos (realization.phase realization.referenceTime)) ^ 2)
          realization.referenceTime := by
      have hCosDerivative :=
        (Real.hasDerivAt_cos
          (realization.phase realization.referenceTime)).comp
            realization.referenceTime hThetaDerivative
      have hDenominatorDerivative :
          HasDerivAt
            (fun z ↦ 1 - realization.eccentricity *
              Real.cos (realization.phase z))
            (realization.eccentricity *
              Real.sin (realization.phase realization.referenceTime) *
              deriv realization.phase realization.referenceTime)
            realization.referenceTime := by
        convert! (hasDerivAt_const realization.referenceTime (1 : ℝ)).sub
          (hCosDerivative.const_mul realization.eccentricity) using 1
        ring
      convert! (hasDerivAt_const realization.referenceTime
        realization.conicNumerator).div hDenominatorDerivative
          (hDenominatorPositive realization.referenceTime).ne' using 1
      ring
    have hPolarDerivative :
        HasDerivAt
          (fun z ↦ (polarDirection realization.frame (realization.phase z)).1)
          (deriv realization.phase realization.referenceTime •
            (polarDirection realization.frame
              (realization.phase realization.referenceTime)).2)
          realization.referenceTime := by
      have hBase := (polarDirection_identities realization.frame
        (realization.phase realization.referenceTime)).2.2.2.2.2
      simpa [Function.comp_def] using!
        hBase.scomp realization.referenceTime hThetaDerivative
    have hPositionDerivative := (hRhoDerivative.smul hPolarDerivative).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hPosition)
    have hVelocityPolar :
        realization.trajectory.velocity realization.referenceTime =
          (realization.conicNumerator / (1 + realization.eccentricity)) •
            (deriv realization.phase realization.referenceTime •
              (polarDirection realization.frame Real.pi).2) := by
      have hVelocity :=
        (realization.trajectory.hasDerivAt_position
          realization.referenceTime).unique hPositionDerivative
      simpa [hPhaseReference] using hVelocity
    have hRhoPositive :
        0 < realization.conicNumerator / (1 + realization.eccentricity) :=
      div_pos hNumeratorPositive (by nlinarith only [hEccentricityGt])
    have hPolarSpeedPositive :
        0 < realization.conicNumerator / (1 + realization.eccentricity) *
          deriv realization.phase realization.referenceTime :=
      mul_pos hRhoPositive (hPhaseDerivPositive realization.referenceTime)
    have hVelocityPolar' :
        realization.trajectory.velocity realization.referenceTime =
          (realization.conicNumerator / (1 + realization.eccentricity) *
            deriv realization.phase realization.referenceTime) •
              (polarDirection realization.frame Real.pi).2 := by
      rw [hVelocityPolar, smul_smul]
    have hVelocityPolarNorm :
        ‖realization.trajectory.velocity realization.referenceTime‖ =
          realization.conicNumerator / (1 + realization.eccentricity) *
            deriv realization.phase realization.referenceTime := by
      rw [hVelocityPolar', norm_smul,
        (polarDirection_identities realization.frame Real.pi).2.1]
      simp only [mul_one, Real.norm_eq_abs]
      rw [abs_of_pos hPolarSpeedPositive]
    have hNormalizedVelocityPolar :
        normalizedDirection
            (realization.trajectory.velocity realization.referenceTime) =
          (polarDirection realization.frame Real.pi).2 := by
      unfold normalizedDirection
      rw [hVelocityPolarNorm, hVelocityPolar', smul_smul,
        inv_mul_cancel₀ hPolarSpeedPositive.ne', one_smul]
    have hInitialDirectionPolar :
        realization.initialDirection =
          (polarDirection realization.frame Real.pi).2 :=
      hNormalizedVelocity.symm.trans hNormalizedVelocityPolar
    have hPositionPolar :
        realization.trajectory.position realization.referenceTime =
          (realization.conicNumerator / (1 + realization.eccentricity)) •
            (polarDirection realization.frame Real.pi).1 := by
      simpa [hPhaseReference] using hPosition realization.referenceTime
    have cross_smul_left (a : ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
        planarCross (a • x) y = a * planarCross x y := by
      unfold planarCross
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    have cross_smul_right (a : ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
        planarCross x (a • y) = a * planarCross x y := by
      unfold planarCross
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    have hInvariantPolar :
        (OrbitalInvariants (sourceSystem parameters) realization.trajectory
          realization.referenceTime).2 =
          reducedMass (sourceSystem parameters) *
            (realization.conicNumerator / (1 + realization.eccentricity)) ^ 2 *
            deriv realization.phase realization.referenceTime *
            planarCross realization.frame.radialAxis
              realization.frame.transverseAxis := by
      unfold OrbitalInvariants
      rw [hPositionPolar, hVelocityPolar, cross_smul_left, cross_smul_right,
        cross_smul_right,
        (polarDirection_identities realization.frame Real.pi).2.2.2.1]
      ring
    have hInvariantNegative :
        (OrbitalInvariants (sourceSystem parameters) realization.trajectory
          realization.referenceTime).2 < 0 := hAngularInitial.2.2.2.2
    rw [hInvariantPolar] at hInvariantNegative
    have hFrameCoefficientPositive :
        0 < reducedMass (sourceSystem parameters) *
            (realization.conicNumerator / (1 + realization.eccentricity)) ^ 2 *
            deriv realization.phase realization.referenceTime :=
      mul_pos
        (mul_pos (reducedMass_pos (sourceSystem parameters))
          (sq_pos_of_pos hRhoPositive))
        (hPhaseDerivPositive realization.referenceTime)
    have hFrameCrossNegative :
        planarCross realization.frame.radialAxis
          realization.frame.transverseAxis < 0 := by
      rcases mul_neg_iff.mp hInvariantNegative with hGood | hImpossible
      · exact hGood.2
      · exact False.elim (not_lt_of_ge hFrameCoefficientPositive.le hImpossible.1)
    have hFrameCrossSq :=
      (polarDirection_identities realization.frame Real.pi).2.2.2.2.1
    have hFrameCross :
        planarCross realization.frame.radialAxis
          realization.frame.transverseAxis = -1 := by
      nlinarith only [hFrameCrossNegative, hFrameCrossSq]
    have hOutgoingDirection :
        normalizedDirection realization.outgoingRelativeVelocity =
          (polarDirection realization.frame
            (2 * Real.pi - realization.asymptoticPhase)).1 := by
      exact (scatteringConic_asymptotic_directions
        (sourceSystem parameters) realization.trajectory realization.energy
        realization.signedAngularMomentum realization.conicNumerator
        realization.eccentricity realization.asymptoticPhase realization.frame
        realization.phase realization.referenceTime realization.incomingRelativeVelocity
        realization.outgoingRelativeVelocity hCarrierForTheorems hAsymptotic).2.2.2.2.2
    have hRadialSelf :
        inner ℝ realization.frame.radialAxis realization.frame.radialAxis = 1 := by
      rw [real_inner_self_eq_norm_sq, realization.frame.radialAxis_norm]
      norm_num
    have hTransverseSelf :
        inner ℝ realization.frame.transverseAxis realization.frame.transverseAxis = 1 := by
      rw [real_inner_self_eq_norm_sq, realization.frame.transverseAxis_norm]
      norm_num
    have hRadialTransverse :
        inner ℝ realization.frame.radialAxis realization.frame.transverseAxis = 0 :=
      realization.frame.axes_orthogonal
    have hTransverseRadial :
        inner ℝ realization.frame.transverseAxis realization.frame.radialAxis = 0 := by
      simpa [hRadialTransverse] using real_inner_comm
        realization.frame.radialAxis realization.frame.transverseAxis
    constructor
    · rw [hNormalizedInitialDirection, hInitialDirectionPolar, hOutgoingDirection]
      simp only [polarDirection, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, conj_trivial]
      rw [hRadialSelf, hTransverseSelf, hRadialTransverse, hTransverseRadial,
        Real.sin_pi, Real.cos_pi, Real.sin_two_pi_sub, Real.cos_two_pi_sub]
      ring
    · rw [hNormalizedInitialDirection, hInitialDirectionPolar, hOutgoingDirection]
      unfold polarDirection planarCross
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [Real.sin_pi, Real.cos_pi, Real.sin_two_pi_sub, Real.cos_two_pi_sub]
      unfold planarCross at hFrameCross
      linear_combination Real.cos realization.asymptoticPhase * hFrameCross
  have hInitial₁ := hAdmissible₁.1
  have hInitial₂ := hAdmissible₂.1
  have hInvariantsEqual := orientedInitialData_invariants_determined parameters
    realization₁.trajectory realization₂.trajectory realization₁.referenceTime
    realization₂.referenceTime realization₁.initialDirection
    realization₁.positronVelocity realization₁.electronVelocity
    realization₂.initialDirection realization₂.positronVelocity
    realization₂.electronVelocity hInitial₁ hInitial₂
  have hCarrierData₁ := hAdmissible₁.2.2.1
  have hCarrierData₂ := hAdmissible₂.2.2.1
  rcases hCarrierData₁ with
    ⟨hLaw₁, hEnergyInvariant₁, hAngularInvariant₁, hNumeratorPositive₁,
      hEccentricityGt₁, hAlphaPositive₁, hAlphaLt₁, hEccentricityCos₁,
      hEccentricityRelation₁, hPhaseData₁, hPositionData₁⟩
  rcases hCarrierData₂ with
    ⟨hLaw₂, hEnergyInvariant₂, hAngularInvariant₂, hNumeratorPositive₂,
      hEccentricityGt₂, hAlphaPositive₂, hAlphaLt₂, hEccentricityCos₂,
      hEccentricityRelation₂, hPhaseData₂, hPositionData₂⟩
  have hEnergyEqual : realization₁.energy = realization₂.energy :=
    hEnergyInvariant₁.trans (hInvariantsEqual.1.trans hEnergyInvariant₂.symm)
  have hAngularEqual :
      realization₁.signedAngularMomentum = realization₂.signedAngularMomentum :=
    hAngularInvariant₁.trans (hInvariantsEqual.2.trans hAngularInvariant₂.symm)
  have hEccentricitySqEqual :
      realization₁.eccentricity ^ 2 = realization₂.eccentricity ^ 2 := by
    calc
      realization₁.eccentricity ^ 2 =
          1 + 2 * realization₁.energy * realization₁.signedAngularMomentum ^ 2 /
            (reducedMass (sourceSystem parameters) *
              (sourceSystem parameters).coupling ^ 2) := hEccentricityRelation₁
      _ = 1 + 2 * realization₂.energy * realization₂.signedAngularMomentum ^ 2 /
            (reducedMass (sourceSystem parameters) *
              (sourceSystem parameters).coupling ^ 2) := by
        rw [hEnergyEqual, hAngularEqual]
      _ = realization₂.eccentricity ^ 2 := hEccentricityRelation₂.symm
  have hEccentricityEqual : realization₁.eccentricity = realization₂.eccentricity := by
    nlinarith only [hEccentricitySqEqual, hEccentricityGt₁, hEccentricityGt₂]
  have hEccentricityCos₁' := hEccentricityCos₁
  rw [hEccentricityEqual] at hEccentricityCos₁'
  have hAlphaCosEqual :
      Real.cos realization₁.asymptoticPhase =
        Real.cos realization₂.asymptoticPhase := by
    exact mul_left_cancel₀ (ne_of_gt (lt_trans zero_lt_one hEccentricityGt₂))
      (hEccentricityCos₁'.trans hEccentricityCos₂.symm)
  have hAlphaMem₁ : realization₁.asymptoticPhase ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hAlphaPositive₁.le, by nlinarith only [hAlphaLt₁, Real.pi_pos]⟩
  have hAlphaMem₂ : realization₂.asymptoticPhase ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hAlphaPositive₂.le, by nlinarith only [hAlphaLt₂, Real.pi_pos]⟩
  have hAlphaEqual :
      realization₁.asymptoticPhase = realization₂.asymptoticPhase :=
    Real.strictAntiOn_cos.injOn hAlphaMem₁ hAlphaMem₂ hAlphaCosEqual
  have hComponents₁ := realization_components realization₁ hAdmissible₁
  have hComponents₂ := realization_components realization₂ hAdmissible₂
  constructor
  · rw [hComponents₁.1, hComponents₂.1, hAlphaEqual]
  · rw [hComponents₁.2, hComponents₂.2, hAlphaEqual]

/-- The canonical unsigned angle between two nonzero planar vectors, measured
in radians in the closed interval `[0, π]`. -/
def CanonicalUnsignedAngle
    (x y : EuclideanSpace ℝ (Fin 2)) (β : ℝ) : Prop :=
  x ≠ 0 ∧
    y ≠ 0 ∧
    0 ≤ β ∧
    β ≤ Real.pi ∧
    Real.cos β = inner ℝ (normalizedDirection x) (normalizedDirection y)

/-- Every pair of nonzero planar vectors has one canonical unsigned angle. -/
lemma canonicalUnsignedAngle_existsUnique
    (x y : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃! β : ℝ, CanonicalUnsignedAngle x y β := by
  have hxNorm : ‖normalizedDirection x‖ = 1 := by
    unfold normalizedDirection
    rw [norm_smul, norm_inv, norm_norm]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hyNorm : ‖normalizedDirection y‖ = 1 := by
    unfold normalizedDirection
    rw [norm_smul, norm_inv, norm_norm]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  have hInnerBound := abs_real_inner_le_norm
    (normalizedDirection x) (normalizedDirection y)
  rw [hxNorm, hyNorm, mul_one] at hInnerBound
  let c := inner ℝ (normalizedDirection x) (normalizedDirection y)
  have hcLower : -1 ≤ c := neg_le_of_abs_le hInnerBound
  have hcUpper : c ≤ 1 := le_of_abs_le hInnerBound
  refine ⟨Real.arccos c, ?_, ?_⟩
  · exact ⟨hx, hy, Real.arccos_nonneg c, Real.arccos_le_pi c,
      Real.cos_arccos hcLower hcUpper⟩
  · intro β hβ
    rcases hβ with ⟨hβx, hβy, hβNonneg, hβLe, hβCos⟩
    calc
      β = Real.arccos (Real.cos β) :=
        (Real.arccos_cos hβNonneg hβLe).symm
      _ = Real.arccos c := by rw [hβCos]

/-- Conversion relation from a radian measure to a degree measure. -/
def DegreeMeasure (β degrees : ℝ) : Prop :=
  degrees * Real.pi = 180 * β

/-- Every radian measure has one degree measure. -/
lemma degreeMeasure_existsUnique (β : ℝ) :
    ∃! degrees : ℝ, DegreeMeasure β degrees := by
  refine ⟨180 * β / Real.pi, ?_, ?_⟩
  · unfold DegreeMeasure
    exact div_mul_cancel₀ (180 * β) Real.pi_ne_zero
  · intro degrees hDegrees
    unfold DegreeMeasure at hDegrees
    exact (eq_div_iff Real.pi_ne_zero).2 hDegrees

/-- Answer-free solution predicate for the requested angle in degrees.  It is
nonvacuous and requires one value to work for every lawful realization. -/
def AsymptoticAngleDegreesSolution
    (parameters : SourceParameters) (degrees : ℝ) : Prop :=
  HasAdmissibleScattering parameters ∧
    ∀ realization : ScatteringRealization,
      IsAdmissibleScattering parameters realization →
        ∃ β : ℝ,
          CanonicalUnsignedAngle realization.initialDirection
              realization.outgoingRelativeVelocity β ∧
            DegreeMeasure β degrees

/-- Provided the stated unbound case is physically realizable, its requested
asymptotic angle has a unique degree value. -/
theorem existsUnique_asymptoticAngleDegrees
    (parameters : SourceParameters)
    (hExists : HasAdmissibleScattering parameters) :
    ∃! degrees : ℝ, AsymptoticAngleDegreesSolution parameters degrees := by
  rcases hExists with ⟨referenceRealization, hReferenceAdmissible⟩
  have hReferenceDirectionNorm :
      ‖referenceRealization.initialDirection‖ = 1 := by
    exact hReferenceAdmissible.1.1
  have hReferenceDirectionNe : referenceRealization.initialDirection ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hReferenceDirectionNorm
    norm_num at hReferenceDirectionNorm
  have hReferenceOutgoingNe := admissible_outgoing_ne_zero parameters
    referenceRealization hReferenceAdmissible
  rcases canonicalUnsignedAngle_existsUnique
      referenceRealization.initialDirection referenceRealization.outgoingRelativeVelocity
      hReferenceDirectionNe hReferenceOutgoingNe with
    ⟨referenceAngle, hReferenceAngle, hReferenceAngleUnique⟩
  rcases degreeMeasure_existsUnique referenceAngle with
    ⟨referenceDegrees, hReferenceDegrees, hReferenceDegreesUnique⟩
  refine ⟨referenceDegrees, ?_, ?_⟩
  · refine ⟨⟨referenceRealization, hReferenceAdmissible⟩, ?_⟩
    intro realization hAdmissible
    have hDirectionNorm : ‖realization.initialDirection‖ = 1 :=
      hAdmissible.1.1
    have hDirectionNe : realization.initialDirection ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hDirectionNorm
      norm_num at hDirectionNorm
    have hOutgoingNe := admissible_outgoing_ne_zero parameters realization hAdmissible
    have hComponents := admissible_outgoing_direction_components_eq parameters
      referenceRealization realization hReferenceAdmissible hAdmissible
    refine ⟨referenceAngle, ?_, hReferenceDegrees⟩
    exact ⟨hDirectionNe, hOutgoingNe, hReferenceAngle.2.2.1,
      hReferenceAngle.2.2.2.1, hReferenceAngle.2.2.2.2.trans hComponents.1⟩
  · intro degrees hSolution
    rcases hSolution.2 referenceRealization hReferenceAdmissible with
      ⟨angle, hAngle, hDegrees⟩
    have hAngleEq := hReferenceAngleUnique angle hAngle
    subst angle
    exact hReferenceDegreesUnique degrees hDegrees

end

end Ipho2026Gpt56solBlind.ProblemIPhO2026_1_B_2
