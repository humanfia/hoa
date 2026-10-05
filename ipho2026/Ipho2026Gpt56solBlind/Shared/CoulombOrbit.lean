import Mathlib

/-!
# Shared attractive Coulomb-orbit carrier

This module records an answer-free, generic planar two-body carrier for an
attractive inverse-square interaction.  The relative position points from
body 2 to body 1, so the force coefficient has the negative attractive sign.
-/

namespace Ipho2026Gpt56solBlind.Shared.CoulombOrbit

open Filter Set

noncomputable section

/-- Positive masses and attractive Coulomb coupling for a two-body system. -/
structure System where
  mass₁ : ℝ
  mass₂ : ℝ
  coupling : ℝ
  mass₁_pos : 0 < mass₁
  mass₂_pos : 0 < mass₂
  coupling_pos : 0 < coupling

/-- The reduced mass `m₁ m₂ / (m₁ + m₂)`. -/
def reducedMass (system : System) : ℝ :=
  system.mass₁ * system.mass₂ / (system.mass₁ + system.mass₂)

/-- The reduced mass of a physical system is positive. -/
lemma reducedMass_pos (system : System) : 0 < reducedMass system := by
  unfold reducedMass
  exact div_pos (mul_pos system.mass₁_pos system.mass₂_pos)
    (add_pos system.mass₁_pos system.mass₂_pos)

/-- The oriented scalar cross product of two planar vectors. -/
def planarCross
    (x y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  x 0 * y 1 - x 1 * y 0

/-- Planar Lagrange identity separating radial and tangential components. -/
lemma norm_mul_norm_eq_dot_sq_add_cross_sq
    (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ^ 2 * ‖y‖ ^ 2 =
      (inner ℝ x y) ^ 2 + planarCross x y ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, planarCross]
  ring

/-- A globally regular, noncolliding relative trajectory. -/
structure Trajectory where
  position : ℝ → EuclideanSpace ℝ (Fin 2)
  velocity : ℝ → EuclideanSpace ℝ (Fin 2)
  acceleration : ℝ → EuclideanSpace ℝ (Fin 2)
  hasDerivAt_position : ∀ t : ℝ, HasDerivAt position (velocity t) t
  hasDerivAt_velocity : ∀ t : ℝ, HasDerivAt velocity (acceleration t) t
  noncollision : ∀ t : ℝ, position t ≠ 0

/-- Relative separation along a trajectory. -/
def radius (trajectory : Trajectory) (t : ℝ) : ℝ :=
  ‖trajectory.position t‖

/-- Signed radial speed. -/
def radialSpeed (trajectory : Trajectory) (t : ℝ) : ℝ :=
  inner ℝ (trajectory.position t) (trajectory.velocity t) / radius trajectory t

/-- Attractive reduced-mass Newton law. -/
def SatisfiesAttractiveCoulombLaw
    (system : System) (trajectory : Trajectory) : Prop :=
  ∀ t : ℝ,
    reducedMass system • trajectory.acceleration t =
      (-system.coupling / radius trajectory t ^ 3) • trajectory.position t

/-- Relative orbital energy and signed angular momentum at one time. -/
def OrbitalInvariants
    (system : System) (trajectory : Trajectory) (t : ℝ) : ℝ × ℝ :=
  (reducedMass system / 2 * ‖trajectory.velocity t‖ ^ 2 -
      system.coupling / radius trajectory t,
    reducedMass system * planarCross (trajectory.position t) (trajectory.velocity t))

/-- The derivative of the nonzero relative radius is the signed radial speed. -/
lemma hasDerivAt_radius (trajectory : Trajectory) (t : ℝ) :
    HasDerivAt (radius trajectory) (radialSpeed trajectory t) t := by
  have hpos := trajectory.hasDerivAt_position t
  have hr_ne : radius trajectory t ≠ 0 := by
    simp only [radius, norm_ne_zero_iff]
    exact trajectory.noncollision t
  have hdiff : DifferentiableAt ℝ (radius trajectory) t := by
    exact hpos.differentiableAt.norm ℝ (trajectory.noncollision t)
  have hnormSq :
      HasDerivAt (fun u ↦ radius trajectory u ^ 2)
        (2 * inner ℝ (trajectory.position t) (trajectory.velocity t)) t := by
    simpa only [radius] using hpos.norm_sq
  have hpow := hdiff.hasDerivAt.pow 2
  have hderiv :
      2 * radius trajectory t * deriv (radius trajectory) t =
        2 * inner ℝ (trajectory.position t) (trajectory.velocity t) := by
    simpa [mul_assoc] using hpow.unique hnormSq
  apply hdiff.hasDerivAt.congr_deriv
  unfold radialSpeed
  field_simp
  linarith

/-- Reciprocal-radius derivative, in radial-speed and dot-product forms. -/
lemma hasDerivAt_inv_radius (trajectory : Trajectory) (t : ℝ) :
    HasDerivAt (fun u ↦ (radius trajectory u)⁻¹)
        (-radialSpeed trajectory t / radius trajectory t ^ 2) t ∧
      -radialSpeed trajectory t / radius trajectory t ^ 2 =
        -(inner ℝ (trajectory.position t) (trajectory.velocity t)) /
          radius trajectory t ^ 3 := by
  have hr_ne : radius trajectory t ≠ 0 := by
    simp only [radius, norm_ne_zero_iff]
    exact trajectory.noncollision t
  constructor
  · convert! (hasDerivAt_radius trajectory t).inv hr_ne using 1
  · unfold radialSpeed
    field_simp

/-- Differential formulas for energy and signed angular momentum. -/
lemma hasDerivAt_orbitalInvariants
    (system : System) (trajectory : Trajectory) (t : ℝ) :
    HasDerivAt (fun u ↦ (OrbitalInvariants system trajectory u).1)
        (reducedMass system *
            inner ℝ (trajectory.velocity t) (trajectory.acceleration t) +
          system.coupling *
            inner ℝ (trajectory.position t) (trajectory.velocity t) /
              radius trajectory t ^ 3) t ∧
      HasDerivAt (fun u ↦ (OrbitalInvariants system trajectory u).2)
        (reducedMass system *
          planarCross (trajectory.position t) (trajectory.acceleration t)) t := by
  have hinv := (hasDerivAt_inv_radius trajectory t).1
  have hvelSq := (trajectory.hasDerivAt_velocity t).norm_sq
  constructor
  · have h :=
      (hvelSq.const_mul (reducedMass system / 2)).sub
        (hinv.const_mul system.coupling)
    have hr_ne : radius trajectory t ≠ 0 := by
      simp only [radius, norm_ne_zero_iff]
      exact trajectory.noncollision t
    convert! h using 1
    unfold radialSpeed
    field_simp
    ring
  · have hposCoord (i : Fin 2) :
        HasDerivAt (fun u ↦ trajectory.position u i)
          (trajectory.velocity t i) t := by
      convert! (((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t
        (trajectory.hasDerivAt_position t).hasFDerivAt).hasDerivAt) using 1 <;>
        simp [Function.comp_def]
    have hvelCoord (i : Fin 2) :
        HasDerivAt (fun u ↦ trajectory.velocity u i)
          (trajectory.acceleration t i) t := by
      convert! (((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t
        (trajectory.hasDerivAt_velocity t).hasFDerivAt).hasDerivAt) using 1 <;>
        simp [Function.comp_def]
    have hcross :
        HasDerivAt
          (fun u ↦ planarCross (trajectory.position u) (trajectory.velocity u))
          (planarCross (trajectory.velocity t) (trajectory.velocity t) +
            planarCross (trajectory.position t) (trajectory.acceleration t)) t := by
      unfold planarCross
      convert! ((hposCoord 0).mul (hvelCoord 1)).sub
        ((hposCoord 1).mul (hvelCoord 0)) using 1
      ring
    convert! hcross.const_mul (reducedMass system) using 1
    unfold planarCross
    ring

/-- Energy and signed angular momentum are conserved under the attractive law. -/
lemma invariants_conserved
    (system : System) (trajectory : Trajectory)
    (hLaw : SatisfiesAttractiveCoulombLaw system trajectory) (s t : ℝ) :
    (OrbitalInvariants system trajectory s).1 =
        (OrbitalInvariants system trajectory t).1 ∧
      (OrbitalInvariants system trajectory s).2 =
        (OrbitalInvariants system trajectory t).2 := by
  have henergyDeriv (u : ℝ) :
      HasDerivAt (fun z ↦ (OrbitalInvariants system trajectory z).1) 0 u := by
    have hformula := (hasDerivAt_orbitalInvariants system trajectory u).1
    apply hformula.congr_deriv
    have hinner := congrArg
      (fun w ↦ inner ℝ (trajectory.velocity u) w) (hLaw u)
    simp only [inner_smul_right] at hinner
    rw [real_inner_comm (trajectory.position u) (trajectory.velocity u)] at hinner
    linear_combination hinner
  have hangDeriv (u : ℝ) :
      HasDerivAt (fun z ↦ (OrbitalInvariants system trajectory z).2) 0 u := by
    have hformula := (hasDerivAt_orbitalInvariants system trajectory u).2
    apply hformula.congr_deriv
    have hcross := congrArg
      (fun w ↦ planarCross (trajectory.position u) w) (hLaw u)
    simp only [planarCross, PiLp.smul_apply, smul_eq_mul] at hcross
    have hzero : reducedMass system *
        planarCross (trajectory.position u) (trajectory.acceleration u) = 0 := by
      unfold planarCross
      nlinarith
    exact hzero
  constructor
  · exact is_const_of_deriv_eq_zero
      (fun u ↦ (henergyDeriv u).differentiableAt)
      (fun u ↦ (henergyDeriv u).deriv) s t
  · exact is_const_of_deriv_eq_zero
      (fun u ↦ (hangDeriv u).differentiableAt)
      (fun u ↦ (hangDeriv u).deriv) s t

/-- Radial/effective-potential decomposition of the orbital energy. -/
lemma energy_eq_radial_effective
    (system : System) (trajectory : Trajectory) (t : ℝ) :
    (OrbitalInvariants system trajectory t).1 =
      reducedMass system / 2 * radialSpeed trajectory t ^ 2 +
        (OrbitalInvariants system trajectory t).2 ^ 2 /
          (2 * reducedMass system * radius trajectory t ^ 2) -
        system.coupling / radius trajectory t := by
  have hmu : reducedMass system ≠ 0 := (reducedMass_pos system).ne'
  have hr : radius trajectory t ≠ 0 := by
    simp only [radius, norm_ne_zero_iff]
    exact trajectory.noncollision t
  have hlagrange := norm_mul_norm_eq_dot_sq_add_cross_sq
    (trajectory.position t) (trajectory.velocity t)
  unfold OrbitalInvariants radialSpeed radius at *
  field_simp
  linear_combination reducedMass system * hlagrange

/-- Invariant radial turning polynomial. -/
def turningPolynomial (system : System) (E H r : ℝ) : ℝ :=
  2 * reducedMass system * E * r ^ 2 +
    2 * reducedMass system * system.coupling * r - H ^ 2

/-- At a trajectory time, the turning polynomial is a squared radial term. -/
lemma turningPolynomial_at_time
    (system : System) (trajectory : Trajectory) (t : ℝ) :
    turningPolynomial system
        (OrbitalInvariants system trajectory t).1
        (OrbitalInvariants system trajectory t).2
        (radius trajectory t) =
      reducedMass system ^ 2 * radius trajectory t ^ 2 *
        radialSpeed trajectory t ^ 2 := by
  have hmu : reducedMass system ≠ 0 := (reducedMass_pos system).ne'
  have hr : radius trajectory t ≠ 0 := by
    simp only [radius, norm_ne_zero_iff]
    exact trajectory.noncollision t
  have henergy := energy_eq_radial_effective system trajectory t
  unfold turningPolynomial
  field_simp at henergy ⊢
  nlinarith

/-- Radial rest is equivalent to the invariant turning equation. -/
lemma radialSpeed_eq_zero_iff_turningPolynomial_eq_zero
    (system : System) (trajectory : Trajectory) (E H t : ℝ)
    (hE : E = (OrbitalInvariants system trajectory t).1)
    (hH : H = (OrbitalInvariants system trajectory t).2) :
    radialSpeed trajectory t = 0 ↔
      turningPolynomial system E H (radius trajectory t) = 0 := by
  subst E
  subst H
  rw [turningPolynomial_at_time]
  have hmu : reducedMass system ≠ 0 := (reducedMass_pos system).ne'
  have hr : radius trajectory t ≠ 0 := by
    simp only [radius, norm_ne_zero_iff]
    exact trajectory.noncollision t
  constructor
  · intro h
    simp [h]
  · intro h
    simp [hmu, hr] at h
    exact h

/-- A positive, dynamically attained invariant turning point. -/
def IsPositiveTurningPoint
    (system : System) (trajectory : Trajectory)
    (E H t r : ℝ) : Prop :=
  0 < r ∧
  radius trajectory t = r ∧
  radialSpeed trajectory t = 0 ∧
  (OrbitalInvariants system trajectory t).1 = E ∧
  (OrbitalInvariants system trajectory t).2 = H ∧
  turningPolynomial system E H r = 0

/-- An oriented orthonormal frame for the orbital plane. -/
structure OrbitalFrame where
  radialAxis : EuclideanSpace ℝ (Fin 2)
  transverseAxis : EuclideanSpace ℝ (Fin 2)
  radialAxis_norm : ‖radialAxis‖ = 1
  transverseAxis_norm : ‖transverseAxis‖ = 1
  axes_orthogonal : inner ℝ radialAxis transverseAxis = 0

/-- Radial and tangential unit directions at polar phase `φ`. -/
def polarDirection
    (frame : OrbitalFrame) (φ : ℝ) :
    EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
  (Real.cos φ • frame.radialAxis + Real.sin φ • frame.transverseAxis,
    (-Real.sin φ) • frame.radialAxis + Real.cos φ • frame.transverseAxis)

/-- Norm, orthogonality, orientation, and derivative identities of a polar frame. -/
lemma polarDirection_identities (frame : OrbitalFrame) (φ : ℝ) :
    ‖(polarDirection frame φ).1‖ = 1 ∧
    ‖(polarDirection frame φ).2‖ = 1 ∧
    inner ℝ (polarDirection frame φ).1 (polarDirection frame φ).2 = 0 ∧
    planarCross (polarDirection frame φ).1 (polarDirection frame φ).2 =
      planarCross frame.radialAxis frame.transverseAxis ∧
    planarCross frame.radialAxis frame.transverseAxis ^ 2 = 1 ∧
    HasDerivAt (fun ψ ↦ (polarDirection frame ψ).1)
      (polarDirection frame φ).2 φ := by
  have huu : inner ℝ frame.radialAxis frame.radialAxis = 1 := by
    rw [real_inner_self_eq_norm_sq, frame.radialAxis_norm]
    norm_num
  have hww : inner ℝ frame.transverseAxis frame.transverseAxis = 1 := by
    rw [real_inner_self_eq_norm_sq, frame.transverseAxis_norm]
    norm_num
  have huw : inner ℝ frame.radialAxis frame.transverseAxis = 0 :=
    frame.axes_orthogonal
  have hwu : inner ℝ frame.transverseAxis frame.radialAxis = 0 := by
    simpa [huw] using real_inner_comm frame.radialAxis frame.transverseAxis
  have norm_linear (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
      ‖a • frame.radialAxis + b • frame.transverseAxis‖ = 1 := by
    rw [← (sq_eq_sq₀ (norm_nonneg _) zero_le_one)]
    simp only [one_pow]
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, RCLike.star_def, conj_trivial, huu, hww, huw, hwu]
    nlinarith
  have hn : ‖(polarDirection frame φ).1‖ = 1 := by
    apply norm_linear
    exact Real.cos_sq_add_sin_sq φ
  have htau : ‖(polarDirection frame φ).2‖ = 1 := by
    apply norm_linear
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have horth :
      inner ℝ (polarDirection frame φ).1 (polarDirection frame φ).2 = 0 := by
    simp only [polarDirection, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, RCLike.star_def, conj_trivial,
      huu, hww, huw, hwu]
    ring
  have horient :
      planarCross (polarDirection frame φ).1 (polarDirection frame φ).2 =
        planarCross frame.radialAxis frame.transverseAxis := by
    unfold polarDirection planarCross
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination (Real.sin_sq_add_cos_sq φ) *
      (frame.radialAxis 0 * frame.transverseAxis 1 -
        frame.radialAxis 1 * frame.transverseAxis 0)
  have hcrossSq : planarCross frame.radialAxis frame.transverseAxis ^ 2 = 1 := by
    have h := norm_mul_norm_eq_dot_sq_add_cross_sq
      frame.radialAxis frame.transverseAxis
    rw [frame.radialAxis_norm, frame.transverseAxis_norm,
      frame.axes_orthogonal] at h
    norm_num at h
    exact h.symm
  have hderiv : HasDerivAt (fun ψ ↦ (polarDirection frame ψ).1)
      (polarDirection frame φ).2 φ := by
    simpa [polarDirection] using!
      ((Real.hasDerivAt_cos φ).smul_const frame.radialAxis).add
        ((Real.hasDerivAt_sin φ).smul_const frame.transverseAxis)
  exact ⟨hn, htau, horth, horient, hcrossSq, hderiv⟩

/-- A continuously differentiable canonical one-turn bound phase. -/
def FullBoundPhaseTraversal
    (θ : ℝ → ℝ) (tLeft tRight : ℝ) : Prop :=
  tLeft < tRight ∧
  ContDiff ℝ 1 θ ∧
  θ tLeft = -Real.pi / 2 ∧
  θ tRight = 3 * Real.pi / 2 ∧
  StrictMonoOn θ (Icc tLeft tRight) ∧
  ∀ t ∈ Ioo tLeft tRight, 0 < deriv θ t

/-- Unique phase-zero and phase-`π` times in a full canonical turn. -/
lemma fullBoundPhase_unique_zero_pi
    (θ : ℝ → ℝ) (tLeft tRight : ℝ)
    (hPhase : FullBoundPhaseTraversal θ tLeft tRight) :
    ∃ tZero tPi : ℝ,
      tZero ∈ Ico tLeft tRight ∧
      tPi ∈ Ico tLeft tRight ∧
      θ tZero = 0 ∧
      θ tPi = Real.pi ∧
      tLeft < tZero ∧ tZero < tPi ∧ tPi < tRight ∧
      (∀ t ∈ Ico tLeft tRight, θ t = 0 → t = tZero) ∧
      (∀ t ∈ Ico tLeft tRight, θ t = Real.pi → t = tPi) := by
  rcases hPhase with ⟨hLeftRight, hContDiff, hLeft, hRight, hMono, hDeriv⟩
  have hContinuous : ContinuousOn θ (Icc tLeft tRight) :=
    hContDiff.continuous.continuousOn
  have hZeroBetween : (0 : ℝ) ∈ Ioo (θ tLeft) (θ tRight) := by
    rw [hLeft, hRight]
    constructor <;> nlinarith [Real.pi_pos]
  have hPiBetween : Real.pi ∈ Ioo (θ tLeft) (θ tRight) := by
    rw [hLeft, hRight]
    constructor <;> nlinarith [Real.pi_pos]
  rcases intermediate_value_Ioo hLeftRight.le hContinuous hZeroBetween with
    ⟨tZero, htZero, hθZero⟩
  rcases intermediate_value_Ioo hLeftRight.le hContinuous hPiBetween with
    ⟨tPi, htPi, hθPi⟩
  have htZeroIcc : tZero ∈ Icc tLeft tRight :=
    ⟨htZero.1.le, htZero.2.le⟩
  have htPiIcc : tPi ∈ Icc tLeft tRight :=
    ⟨htPi.1.le, htPi.2.le⟩
  have hZeroPi : tZero < tPi := by
    by_contra h
    have hle : tPi ≤ tZero := le_of_not_gt h
    rcases eq_or_lt_of_le hle with heq | hlt
    · subst tPi
      rw [hθZero] at hθPi
      exact Real.pi_ne_zero hθPi.symm
    · have hphaseLt := hMono htPiIcc htZeroIcc hlt
      rw [hθPi, hθZero] at hphaseLt
      linarith [Real.pi_pos]
  refine ⟨tZero, tPi, ⟨htZero.1.le, htZero.2⟩,
    ⟨htPi.1.le, htPi.2⟩, hθZero, hθPi, htZero.1, hZeroPi,
    htPi.2, ?_, ?_⟩
  · intro t ht hθ
    apply hMono.injOn (Ico_subset_Icc_self ht) htZeroIcc
    rw [hθ, hθZero]
  · intro t ht hθ
    apply hMono.injOn (Ico_subset_Icc_self ht) htPiIcc
    rw [hθ, hθPi]

/-- Cosine extrema and equality cases on the canonical half-open turn. -/
lemma cos_extrema_on_canonical_turn (φ : ℝ)
    (hφ : φ ∈ Ico (-Real.pi / 2) (3 * Real.pi / 2)) :
    -1 ≤ Real.cos φ ∧
    Real.cos φ ≤ 1 ∧
    (Real.cos φ = 1 ↔ φ = 0) ∧
    (Real.cos φ = -1 ↔ φ = Real.pi) := by
  rcases hφ with ⟨hφLeft, hφRight⟩
  refine ⟨Real.neg_one_le_cos φ, Real.cos_le_one φ, ?_, ?_⟩
  · constructor
    · intro h
      apply (Real.cos_eq_one_iff_of_lt_of_lt (x := φ) ?_ ?_).mp h
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    · rintro rfl
      exact Real.cos_zero
  · constructor
    · intro h
      have hcos : Real.cos (φ - Real.pi) = 1 := by
        rw [Real.cos_sub_pi, h]
        norm_num
      have hshift := (Real.cos_eq_one_iff_of_lt_of_lt
        (x := φ - Real.pi) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])).mp hcos
      linarith
    · rintro rfl
      exact Real.cos_pi

/-- Bound inverse-square conic carrier, including dynamics and one full traversal. -/
def SatisfiesBoundConicCarrier
    (system : System) (trajectory : Trajectory) (E H p eccentricity : ℝ)
    (frame : OrbitalFrame) (θ : ℝ → ℝ) (tLeft tRight : ℝ) : Prop :=
  SatisfiesAttractiveCoulombLaw system trajectory ∧
  E = (OrbitalInvariants system trajectory tLeft).1 ∧
  H = (OrbitalInvariants system trajectory tLeft).2 ∧
  0 < p ∧
  0 < eccentricity ∧
  eccentricity < 1 ∧
  eccentricity ^ 2 =
    1 + 2 * E * H ^ 2 /
      (reducedMass system * system.coupling ^ 2) ∧
  FullBoundPhaseTraversal θ tLeft tRight ∧
  ∀ t ∈ Icc tLeft tRight,
    trajectory.position t =
      (p / (1 - eccentricity * Real.cos (θ t))) •
        (polarDirection frame (θ t)).1

/-- Polar radius, radial speed, and angular momentum along a bound carrier. -/
lemma boundConic_polar_kinematics
    (system : System) (trajectory : Trajectory) (E H p eccentricity : ℝ)
    (frame : OrbitalFrame) (θ : ℝ → ℝ) (tLeft tRight : ℝ)
    (hCarrier : SatisfiesBoundConicCarrier system trajectory E H p eccentricity
      frame θ tLeft tRight) :
    (∀ t ∈ Icc tLeft tRight,
      radius trajectory t = p / (1 - eccentricity * Real.cos (θ t))) ∧
    (∀ t ∈ Ioo tLeft tRight,
      radialSpeed trajectory t =
          -(p * eccentricity * Real.sin (θ t) * deriv θ t) /
            (1 - eccentricity * Real.cos (θ t)) ^ 2 ∧
      (OrbitalInvariants system trajectory t).2 =
        reducedMass system * p ^ 2 * deriv θ t *
            planarCross frame.radialAxis frame.transverseAxis /
          (1 - eccentricity * Real.cos (θ t)) ^ 2) ∧
    H ≠ 0 := by
  rcases hCarrier with
    ⟨hLaw, hE, hH, hp, hePos, heLt, heRelation, hPhase, hPosition⟩
  rcases hPhase with
    ⟨hLeftRight, hContDiff, hθLeft, hθRight, hMono, hθDerivPos⟩
  have hdenPos (u : ℝ) : 0 < 1 - eccentricity * Real.cos (θ u) := by
    have hcos := Real.cos_le_one (θ u)
    nlinarith
  have hRadius (u : ℝ) (hu : u ∈ Icc tLeft tRight) :
      radius trajectory u = p / (1 - eccentricity * Real.cos (θ u)) := by
    unfold radius
    rw [hPosition u hu, norm_smul,
      (polarDirection_identities frame (θ u)).1]
    simp only [mul_one, Real.norm_eq_abs]
    rw [abs_of_pos (div_pos hp (hdenPos u))]
  have hThetaDeriv (u : ℝ) : HasDerivAt θ (deriv θ u) u :=
    (hContDiff.differentiable (by norm_num) u).hasDerivAt
  have hRhoDeriv (u : ℝ) :
      HasDerivAt
        (fun z ↦ p / (1 - eccentricity * Real.cos (θ z)))
        (-(p * eccentricity * Real.sin (θ u) * deriv θ u) /
          (1 - eccentricity * Real.cos (θ u)) ^ 2) u := by
    have hcos := (Real.hasDerivAt_cos (θ u)).comp u (hThetaDeriv u)
    have hden :
        HasDerivAt (fun z ↦ 1 - eccentricity * Real.cos (θ z))
          (eccentricity * Real.sin (θ u) * deriv θ u) u := by
      convert! (hasDerivAt_const u (1 : ℝ)).sub
        (hcos.const_mul eccentricity) using 1
      ring
    convert! (hasDerivAt_const u p).div hden (hdenPos u).ne' using 1
    ring
  have hRadial (u : ℝ) (hu : u ∈ Ioo tLeft tRight) :
      radialSpeed trajectory u =
        -(p * eccentricity * Real.sin (θ u) * deriv θ u) /
          (1 - eccentricity * Real.cos (θ u)) ^ 2 := by
    have hevent :
        (fun z ↦ radius trajectory z) =ᶠ[nhds u]
          (fun z ↦ p / (1 - eccentricity * Real.cos (θ z))) := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with z hz
      exact hRadius z (Ioo_subset_Icc_self hz)
    have hrho := (hRhoDeriv u).congr_of_eventuallyEq hevent
    exact (hasDerivAt_radius trajectory u).unique hrho
  have hPolarDeriv (u : ℝ) :
      HasDerivAt (fun z ↦ (polarDirection frame (θ z)).1)
        (deriv θ u • (polarDirection frame (θ u)).2) u := by
    have hbase := (polarDirection_identities frame (θ u)).2.2.2.2.2
    have hcomp := hbase.scomp u (hThetaDeriv u)
    simpa [Function.comp_def] using! hcomp
  have hVelocity (u : ℝ) (hu : u ∈ Ioo tLeft tRight) :
      trajectory.velocity u =
        (p / (1 - eccentricity * Real.cos (θ u))) •
            (deriv θ u • (polarDirection frame (θ u)).2) +
          (-(p * eccentricity * Real.sin (θ u) * deriv θ u) /
            (1 - eccentricity * Real.cos (θ u)) ^ 2) •
              (polarDirection frame (θ u)).1 := by
    have hProduct := (hRhoDeriv u).smul (hPolarDeriv u)
    have hevent :
        trajectory.position =ᶠ[nhds u]
          (fun z ↦ (p / (1 - eccentricity * Real.cos (θ z))) •
            (polarDirection frame (θ z)).1) := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with z hz
      exact hPosition z (Ioo_subset_Icc_self hz)
    have hPositionDeriv := hProduct.congr_of_eventuallyEq hevent
    exact (trajectory.hasDerivAt_position u).unique hPositionDeriv
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
  have cross_add_right (x y z : EuclideanSpace ℝ (Fin 2)) :
      planarCross x (y + z) = planarCross x y + planarCross x z := by
    unfold planarCross
    simp only [PiLp.add_apply]
    ring
  have cross_self (x : EuclideanSpace ℝ (Fin 2)) : planarCross x x = 0 := by
    unfold planarCross
    ring
  have hAngular (u : ℝ) (hu : u ∈ Ioo tLeft tRight) :
      (OrbitalInvariants system trajectory u).2 =
        reducedMass system * p ^ 2 * deriv θ u *
            planarCross frame.radialAxis frame.transverseAxis /
          (1 - eccentricity * Real.cos (θ u)) ^ 2 := by
    have hpos := hPosition u (Ioo_subset_Icc_self hu)
    have hvel := hVelocity u hu
    have horient := (polarDirection_identities frame (θ u)).2.2.2.1
    unfold OrbitalInvariants
    simp only [Prod.snd]
    rw [hpos, hvel, cross_smul_left, cross_add_right,
      cross_smul_right, cross_smul_right, cross_smul_right, cross_self,
      mul_zero, add_zero,
      horient]
    field_simp
  have hHne : H ≠ 0 := by
    let u := (tLeft + tRight) / 2
    have hu : u ∈ Ioo tLeft tRight := by
      dsimp [u]
      constructor <;> linarith
    have hInv : (OrbitalInvariants system trajectory u).2 = H := by
      exact (hH.trans
        (invariants_conserved system trajectory hLaw tLeft u).2).symm
    have hcrossSq := (polarDirection_identities frame (θ u)).2.2.2.2.1
    have hcrossNe : planarCross frame.radialAxis frame.transverseAxis ≠ 0 := by
      intro hzero
      rw [hzero] at hcrossSq
      norm_num at hcrossSq
    have hnumNe :
        reducedMass system * p ^ 2 * deriv θ u *
          planarCross frame.radialAxis frame.transverseAxis ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (reducedMass_pos system).ne' (pow_ne_zero 2 hp.ne'))
          (hθDerivPos u hu).ne')
        hcrossNe
    have hvalueNe : (OrbitalInvariants system trajectory u).2 ≠ 0 := by
      rw [hAngular u hu]
      exact div_ne_zero hnumNe (pow_ne_zero 2 (hdenPos u).ne')
    rwa [hInv] at hvalueNe
  refine ⟨hRadius, ?_, hHne⟩
  intro u hu
  exact ⟨hRadial u hu, hAngular u hu⟩

/-- Bound-carrier periapsis/apoapsis bounds and their phase equality cases. -/
lemma boundConic_radius_bounds
    (system : System) (trajectory : Trajectory) (E H p eccentricity : ℝ)
    (frame : OrbitalFrame) (θ : ℝ → ℝ) (tLeft tRight : ℝ)
    (hCarrier : SatisfiesBoundConicCarrier system trajectory E H p eccentricity
      frame θ tLeft tRight) :
    let rPeri := p / (1 + eccentricity)
    let rApo := p / (1 - eccentricity)
    0 < rPeri ∧
    rPeri < rApo ∧
    ∀ t ∈ Ico tLeft tRight,
      rPeri ≤ radius trajectory t ∧
      radius trajectory t ≤ rApo ∧
      (radius trajectory t = rPeri ↔ θ t = Real.pi) ∧
      (radius trajectory t = rApo ↔ θ t = 0) := by
  dsimp only
  have hKinematics := boundConic_polar_kinematics system trajectory E H p
    eccentricity frame θ tLeft tRight hCarrier
  rcases hCarrier with
    ⟨hLaw, hE, hH, hp, hePos, heLt, heRelation, hPhase, hPosition⟩
  rcases hPhase with
    ⟨hLeftRight, hContDiff, hθLeft, hθRight, hMono, hDerivPos⟩
  have hPlus : 0 < 1 + eccentricity := by linarith
  have hMinus : 0 < 1 - eccentricity := by linarith
  have hPeriPos : 0 < p / (1 + eccentricity) := div_pos hp hPlus
  have hOrder : p / (1 + eccentricity) < p / (1 - eccentricity) := by
    apply (div_lt_div_iff₀ hPlus hMinus).2
    nlinarith
  refine ⟨hPeriPos, hOrder, ?_⟩
  intro t ht
  have htIcc : t ∈ Icc tLeft tRight := Ico_subset_Icc_self ht
  have hθLower : -Real.pi / 2 ≤ θ t := by
    rw [← hθLeft]
    exact hMono.monotoneOn (left_mem_Icc.2 hLeftRight.le) htIcc ht.1
  have hθUpper : θ t < 3 * Real.pi / 2 := by
    rw [← hθRight]
    exact hMono htIcc (right_mem_Icc.2 hLeftRight.le) ht.2
  have hcos := cos_extrema_on_canonical_turn (θ t) ⟨hθLower, hθUpper⟩
  have hden : 0 < 1 - eccentricity * Real.cos (θ t) := by
    nlinarith [Real.cos_le_one (θ t)]
  have hRadius := hKinematics.1 t htIcc
  rw [hRadius]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ hPlus hden).2
    exact mul_le_mul_of_nonneg_left (by nlinarith [hcos.1]) hp.le
  · apply (div_le_div_iff₀ hden hMinus).2
    exact mul_le_mul_of_nonneg_left (by nlinarith [hcos.2.1]) hp.le
  · constructor
    · intro heq
      have hcross : Real.cos (θ t) = -1 := by
        field_simp [hp.ne', hPlus.ne', hden.ne'] at heq
        nlinarith
      exact hcos.2.2.2.mp hcross
    · intro hθ
      rw [hθ, Real.cos_pi]
      ring
  · constructor
    · intro heq
      have hcross : Real.cos (θ t) = 1 := by
        field_simp [hp.ne', hMinus.ne', hden.ne'] at heq
        nlinarith
      exact hcos.2.2.1.mp hcross
    · intro hθ
      rw [hθ, Real.cos_zero, mul_one]

/-- Invariant determination and factorization of every bound carrier. -/
lemma boundConic_parameter_identities
    (system : System) (trajectory : Trajectory) (E H p eccentricity : ℝ)
    (frame : OrbitalFrame) (θ : ℝ → ℝ) (tLeft tRight : ℝ)
    (hCarrier : SatisfiesBoundConicCarrier system trajectory E H p eccentricity
      frame θ tLeft tRight) :
    H ≠ 0 ∧
    E < 0 ∧
    p = H ^ 2 / (reducedMass system * system.coupling) ∧
    E = system.coupling * (eccentricity ^ 2 - 1) / (2 * p) ∧
    ∀ r : ℝ,
      turningPolynomial system E H r =
        (reducedMass system * system.coupling / p) *
          (eccentricity ^ 2 - 1) *
          (r - p / (1 + eccentricity)) *
          (r - p / (1 - eccentricity)) := by
  have hKinematics := boundConic_polar_kinematics system trajectory E H p
    eccentricity frame θ tLeft tRight hCarrier
  rcases hCarrier with
    ⟨hLaw, hE, hH, hp, hePos, heLt, heRelation, hPhase, hPosition⟩
  obtain ⟨tZero, tPi, htZero, htPi, hθZero, hθPi, hLeftZero,
    hZeroPi, hPiRight, hZeroUnique, hPiUnique⟩ :=
      fullBoundPhase_unique_zero_pi θ tLeft tRight hPhase
  have htZeroIoo : tZero ∈ Ioo tLeft tRight :=
    ⟨hLeftZero, lt_trans hZeroPi hPiRight⟩
  have htPiIoo : tPi ∈ Ioo tLeft tRight :=
    ⟨lt_trans hLeftZero hZeroPi, hPiRight⟩
  have hRadiusZero : radius trajectory tZero = p / (1 - eccentricity) := by
    simpa [hθZero] using hKinematics.1 tZero (Ico_subset_Icc_self htZero)
  have hRadiusPi : radius trajectory tPi = p / (1 + eccentricity) := by
    simpa [hθPi] using hKinematics.1 tPi (Ico_subset_Icc_self htPi)
  have hRadialZero : radialSpeed trajectory tZero = 0 := by
    simpa [hθZero] using (hKinematics.2.1 tZero htZeroIoo).1
  have hRadialPi : radialSpeed trajectory tPi = 0 := by
    simpa [hθPi] using (hKinematics.2.1 tPi htPiIoo).1
  have hEZero : E = (OrbitalInvariants system trajectory tZero).1 :=
    hE.trans (invariants_conserved system trajectory hLaw tLeft tZero).1
  have hHZero : H = (OrbitalInvariants system trajectory tZero).2 :=
    hH.trans (invariants_conserved system trajectory hLaw tLeft tZero).2
  have hEPi : E = (OrbitalInvariants system trajectory tPi).1 :=
    hE.trans (invariants_conserved system trajectory hLaw tLeft tPi).1
  have hHPi : H = (OrbitalInvariants system trajectory tPi).2 :=
    hH.trans (invariants_conserved system trajectory hLaw tLeft tPi).2
  have hRootApo : turningPolynomial system E H (p / (1 - eccentricity)) = 0 := by
    rw [← hRadiusZero]
    exact (radialSpeed_eq_zero_iff_turningPolynomial_eq_zero system trajectory
      E H tZero hEZero hHZero).mp hRadialZero
  have hRootPeri : turningPolynomial system E H (p / (1 + eccentricity)) = 0 := by
    rw [← hRadiusPi]
    exact (radialSpeed_eq_zero_iff_turningPolynomial_eq_zero system trajectory
      E H tPi hEPi hHPi).mp hRadialPi
  have hmu : reducedMass system ≠ 0 := (reducedMass_pos system).ne'
  have hk : system.coupling ≠ 0 := system.coupling_pos.ne'
  have hpne : p ≠ 0 := hp.ne'
  have hPlus : 1 + eccentricity ≠ 0 := by nlinarith
  have hMinus : 1 - eccentricity ≠ 0 := by nlinarith
  unfold turningPolynomial at hRootApo hRootPeri
  field_simp [hPlus, hMinus] at hRootApo hRootPeri
  have hfactor :
      4 * eccentricity *
        (H ^ 2 - reducedMass system * system.coupling * p) = 0 := by
    linear_combination hRootApo - hRootPeri
  have hHsq : H ^ 2 = reducedMass system * system.coupling * p := by
    have hnonzero : 4 * eccentricity ≠ 0 := mul_ne_zero (by norm_num) hePos.ne'
    have hz := (mul_eq_zero.mp hfactor).resolve_left hnonzero
    linarith only [hz]
  have hP : p = H ^ 2 / (reducedMass system * system.coupling) := by
    field_simp [hmu, hk]
    nlinarith only [hHsq]
  have hEformula :
      E = system.coupling * (eccentricity ^ 2 - 1) / (2 * p) := by
    rw [hHsq] at heRelation
    field_simp [hmu, hk, hpne] at heRelation ⊢
    nlinarith only [heRelation]
  have hENeg : E < 0 := by
    have heSqLt : eccentricity ^ 2 < 1 := by
      nlinarith only [hePos, heLt]
    rw [hEformula]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg system.coupling_pos (sub_neg.mpr heSqLt))
      (mul_pos (by norm_num) hp)
  refine ⟨hKinematics.2.2, hENeg, hP, hEformula, ?_⟩
  intro r
  unfold turningPolynomial
  rw [hEformula, hHsq]
  field_simp [hpne, hPlus, hMinus]
  ring

/-- Classification and order of the positive bound turning roots. -/
lemma boundConic_positive_turning_roots
    (system : System) (trajectory : Trajectory) (E H p eccentricity : ℝ)
    (frame : OrbitalFrame) (θ : ℝ → ℝ) (tLeft tRight : ℝ)
    (hCarrier : SatisfiesBoundConicCarrier system trajectory E H p eccentricity
      frame θ tLeft tRight) :
    0 < p / (1 + eccentricity) ∧
    p / (1 + eccentricity) < p / (1 - eccentricity) ∧
    ∀ r : ℝ, 0 < r →
      (turningPolynomial system E H r = 0 ↔
        r = p / (1 + eccentricity) ∨ r = p / (1 - eccentricity)) := by
  have hBounds := boundConic_radius_bounds system trajectory E H p eccentricity
    frame θ tLeft tRight hCarrier
  have hParams := boundConic_parameter_identities system trajectory E H p
    eccentricity frame θ tLeft tRight hCarrier
  rcases hCarrier with
    ⟨hLaw, hE, hH, hp, hePos, heLt, heRelation, hPhase, hPosition⟩
  have hmu : reducedMass system ≠ 0 := (reducedMass_pos system).ne'
  have hk : system.coupling ≠ 0 := system.coupling_pos.ne'
  have hpne : p ≠ 0 := hp.ne'
  have hLeading : reducedMass system * system.coupling / p ≠ 0 :=
    div_ne_zero (mul_ne_zero hmu hk) hpne
  have heSqLt : eccentricity ^ 2 < 1 := by
    nlinarith only [hePos, heLt]
  have heFactor : eccentricity ^ 2 - 1 ≠ 0 :=
    (sub_neg.mpr heSqLt).ne
  refine ⟨hBounds.1, hBounds.2.1, ?_⟩
  intro r hr
  rw [hParams.2.2.2.2 r]
  simp [hLeading, heFactor, sub_eq_zero]

/-- Attained periapsis and apoapsis characterize all positive turning roots. -/
theorem boundConic_apsides_characterization
    (system : System) (trajectory : Trajectory) (E H p eccentricity : ℝ)
    (frame : OrbitalFrame) (θ : ℝ → ℝ) (tLeft tRight : ℝ)
    (hCarrier : SatisfiesBoundConicCarrier system trajectory E H p eccentricity
      frame θ tLeft tRight) :
    let rPeri := p / (1 + eccentricity)
    let rApo := p / (1 - eccentricity)
    0 < rPeri ∧
    rPeri < rApo ∧
    (∃! tPeri : ℝ,
      tPeri ∈ Ico tLeft tRight ∧
      IsPositiveTurningPoint system trajectory E H tPeri rPeri ∧
      θ tPeri = Real.pi) ∧
    (∃! tApo : ℝ,
      tApo ∈ Ico tLeft tRight ∧
      IsPositiveTurningPoint system trajectory E H tApo rApo ∧
      θ tApo = 0) ∧
    (∀ t ∈ Ico tLeft tRight,
      rPeri ≤ radius trajectory t ∧
      radius trajectory t ≤ rApo ∧
      (radius trajectory t = rPeri ↔ θ t = Real.pi) ∧
      (radius trajectory t = rApo ↔ θ t = 0)) ∧
    (∀ r : ℝ, 0 < r →
      (turningPolynomial system E H r = 0 ↔
        r = rPeri ∨ r = rApo) ∧
      (turningPolynomial system E H r = 0 ↔
        ∃ t ∈ Ico tLeft tRight,
          IsPositiveTurningPoint system trajectory E H t r)) := by
  dsimp only
  have hKinematics := boundConic_polar_kinematics system trajectory E H p
    eccentricity frame θ tLeft tRight hCarrier
  have hBounds := boundConic_radius_bounds system trajectory E H p eccentricity
    frame θ tLeft tRight hCarrier
  have hRoots := boundConic_positive_turning_roots system trajectory E H p
    eccentricity frame θ tLeft tRight hCarrier
  rcases hCarrier with
    ⟨hLaw, hE, hH, hp, hePos, heLt, heRelation, hPhase, hPosition⟩
  obtain ⟨tZero, tPi, htZero, htPi, hθZero, hθPi, hLeftZero,
    hZeroPi, hPiRight, hZeroUnique, hPiUnique⟩ :=
      fullBoundPhase_unique_zero_pi θ tLeft tRight hPhase
  have htZeroIoo : tZero ∈ Ioo tLeft tRight :=
    ⟨hLeftZero, lt_trans hZeroPi hPiRight⟩
  have htPiIoo : tPi ∈ Ioo tLeft tRight :=
    ⟨lt_trans hLeftZero hZeroPi, hPiRight⟩
  have hRadiusPeri :
      radius trajectory tPi = p / (1 + eccentricity) :=
    ((hBounds.2.2 tPi htPi).2.2.1).mpr hθPi
  have hRadiusApo :
      radius trajectory tZero = p / (1 - eccentricity) :=
    ((hBounds.2.2 tZero htZero).2.2.2).mpr hθZero
  have hRadialPeri : radialSpeed trajectory tPi = 0 := by
    simpa [hθPi] using (hKinematics.2.1 tPi htPiIoo).1
  have hRadialApo : radialSpeed trajectory tZero = 0 := by
    simpa [hθZero] using (hKinematics.2.1 tZero htZeroIoo).1
  have hInvE (u : ℝ) : (OrbitalInvariants system trajectory u).1 = E :=
    (hE.trans (invariants_conserved system trajectory hLaw tLeft u).1).symm
  have hInvH (u : ℝ) : (OrbitalInvariants system trajectory u).2 = H :=
    (hH.trans (invariants_conserved system trajectory hLaw tLeft u).2).symm
  have hRootPeri :
      turningPolynomial system E H (p / (1 + eccentricity)) = 0 :=
    (hRoots.2.2 (p / (1 + eccentricity)) hRoots.1).mpr (Or.inl rfl)
  have hRootApo :
      turningPolynomial system E H (p / (1 - eccentricity)) = 0 :=
    (hRoots.2.2 (p / (1 - eccentricity))
      (lt_trans hRoots.1 hRoots.2.1)).mpr (Or.inr rfl)
  have hTurningPeri : IsPositiveTurningPoint system trajectory E H tPi
      (p / (1 + eccentricity)) :=
    ⟨hRoots.1, hRadiusPeri, hRadialPeri, hInvE tPi, hInvH tPi,
      hRootPeri⟩
  have hTurningApo : IsPositiveTurningPoint system trajectory E H tZero
      (p / (1 - eccentricity)) :=
    ⟨lt_trans hRoots.1 hRoots.2.1, hRadiusApo, hRadialApo,
      hInvE tZero, hInvH tZero, hRootApo⟩
  refine ⟨hBounds.1, hBounds.2.1, ?_, ?_, hBounds.2.2, ?_⟩
  · refine ⟨tPi, ⟨htPi, hTurningPeri, hθPi⟩, ?_⟩
    intro u hu
    exact hPiUnique u hu.1 hu.2.2
  · refine ⟨tZero, ⟨htZero, hTurningApo, hθZero⟩, ?_⟩
    intro u hu
    exact hZeroUnique u hu.1 hu.2.2
  · intro r hr
    refine ⟨hRoots.2.2 r hr, ?_⟩
    constructor
    · intro hroot
      rcases (hRoots.2.2 r hr).mp hroot with hPeri | hApo
      · subst r
        exact ⟨tPi, htPi, hTurningPeri⟩
      · subst r
        exact ⟨tZero, htZero, hTurningApo⟩
    · rintro ⟨u, hu, hTurning⟩
      exact hTurning.2.2.2.2.2

/-- A canonical increasing traversal of the physical scattering branch. -/
def FullScatteringPhaseTraversal (θ : ℝ → ℝ) (α : ℝ) : Prop :=
  0 < α ∧
  α < Real.pi / 2 ∧
  ContDiff ℝ 1 θ ∧
  StrictMono θ ∧
  (∀ t : ℝ, 0 < deriv θ t) ∧
  Set.range θ = Ioo α (2 * Real.pi - α) ∧
  Tendsto θ atBot (nhds α) ∧
  Tendsto θ atTop (nhds (2 * Real.pi - α))

/-- Scattering inverse-square conic carrier. -/
def SatisfiesScatteringConicCarrier
    (system : System) (trajectory : Trajectory) (E H p eccentricity α : ℝ)
    (frame : OrbitalFrame) (θ : ℝ → ℝ) (referenceTime : ℝ) : Prop :=
  SatisfiesAttractiveCoulombLaw system trajectory ∧
  E = (OrbitalInvariants system trajectory referenceTime).1 ∧
  H = (OrbitalInvariants system trajectory referenceTime).2 ∧
  0 < p ∧
  1 < eccentricity ∧
  0 < α ∧
  α < Real.pi / 2 ∧
  eccentricity * Real.cos α = 1 ∧
  eccentricity ^ 2 =
    1 + 2 * E * H ^ 2 /
      (reducedMass system * system.coupling ^ 2) ∧
  FullScatteringPhaseTraversal θ α ∧
  ∀ t : ℝ,
    trajectory.position t =
      (p / (1 - eccentricity * Real.cos (θ t))) •
        (polarDirection frame (θ t)).1

/-- Invariant parameters and unique positive turning point of a scattering carrier. -/
lemma scatteringConic_parameter_identities
    (system : System) (trajectory : Trajectory) (E H p eccentricity α : ℝ)
    (frame : OrbitalFrame) (θ : ℝ → ℝ) (referenceTime : ℝ)
    (hCarrier : SatisfiesScatteringConicCarrier system trajectory E H p eccentricity α
      frame θ referenceTime) :
    H ≠ 0 ∧
    0 < E ∧
    p = H ^ 2 / (reducedMass system * system.coupling) ∧
    E = system.coupling * (eccentricity ^ 2 - 1) / (2 * p) ∧
    (∀ r : ℝ, 0 < r →
      (turningPolynomial system E H r = 0 ↔
        r = p / (1 + eccentricity))) ∧
    (∃! tPeri : ℝ,
      θ tPeri = Real.pi ∧
      IsPositiveTurningPoint system trajectory E H tPeri
        (p / (1 + eccentricity))) := by
  rcases hCarrier with
    ⟨hLaw, hE, hH, hp, heGt, hαPos, hαLt, heCos, heRelation,
      hPhase, hPosition⟩
  rcases hPhase with
    ⟨hPhaseαPos, hPhaseαLt, hContDiff, hStrict, hDerivPos,
      hRange, hTendstoBot, hTendstoTop⟩
  have hPiMem : Real.pi ∈ Set.range θ := by
    rw [hRange]
    constructor <;> nlinarith [Real.pi_pos]
  rcases hPiMem with ⟨tPi, hθPi⟩
  have hPiUnique (u : ℝ) (hu : θ u = Real.pi) : u = tPi :=
    hStrict.injective (hu.trans hθPi.symm)
  have hThetaDeriv : HasDerivAt θ (deriv θ tPi) tPi :=
    (hContDiff.differentiable (by norm_num) tPi).hasDerivAt
  have hdenPi : 1 - eccentricity * Real.cos (θ tPi) ≠ 0 := by
    rw [hθPi, Real.cos_pi]
    nlinarith
  have hRhoDeriv :
      HasDerivAt
        (fun z ↦ p / (1 - eccentricity * Real.cos (θ z)))
        (-(p * eccentricity * Real.sin (θ tPi) * deriv θ tPi) /
          (1 - eccentricity * Real.cos (θ tPi)) ^ 2) tPi := by
    have hcos := (Real.hasDerivAt_cos (θ tPi)).comp tPi hThetaDeriv
    have hden :
        HasDerivAt (fun z ↦ 1 - eccentricity * Real.cos (θ z))
          (eccentricity * Real.sin (θ tPi) * deriv θ tPi) tPi := by
      convert! (hasDerivAt_const tPi (1 : ℝ)).sub
        (hcos.const_mul eccentricity) using 1
      ring
    convert! (hasDerivAt_const tPi p).div hden hdenPi using 1
    ring
  have hPolarDeriv :
      HasDerivAt (fun z ↦ (polarDirection frame (θ z)).1)
        (deriv θ tPi • (polarDirection frame (θ tPi)).2) tPi := by
    have hbase := (polarDirection_identities frame (θ tPi)).2.2.2.2.2
    simpa [Function.comp_def] using! hbase.scomp tPi hThetaDeriv
  have hProduct := hRhoDeriv.smul hPolarDeriv
  have hPositionEvent :
      trajectory.position =ᶠ[nhds tPi]
        (fun z ↦ (p / (1 - eccentricity * Real.cos (θ z))) •
          (polarDirection frame (θ z)).1) := by
    filter_upwards [] with z
    exact hPosition z
  have hPositionDeriv := hProduct.congr_of_eventuallyEq hPositionEvent
  have hVelocityPi : trajectory.velocity tPi =
      (p / (1 + eccentricity)) •
        (deriv θ tPi • (polarDirection frame Real.pi).2) := by
    have hvel := (trajectory.hasDerivAt_position tPi).unique hPositionDeriv
    simpa [hθPi] using hvel
  have hPositionPi : trajectory.position tPi =
      (p / (1 + eccentricity)) • (polarDirection frame Real.pi).1 := by
    simpa [hθPi] using hPosition tPi
  have hRadiusPi : radius trajectory tPi = p / (1 + eccentricity) := by
    unfold radius
    rw [hPositionPi, norm_smul,
      (polarDirection_identities frame Real.pi).1]
    simp only [mul_one, Real.norm_eq_abs]
    rw [abs_of_pos (div_pos hp (by nlinarith))]
  have hRadialPi : radialSpeed trajectory tPi = 0 := by
    unfold radialSpeed
    rw [hPositionPi, hVelocityPi]
    simp only [inner_smul_left, inner_smul_right, RCLike.star_def,
      conj_trivial, (polarDirection_identities frame Real.pi).2.2.1,
      mul_zero, zero_div]
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
  have hInvariantPi :
      (OrbitalInvariants system trajectory tPi).2 =
        reducedMass system * (p / (1 + eccentricity)) ^ 2 * deriv θ tPi *
          planarCross frame.radialAxis frame.transverseAxis := by
    unfold OrbitalInvariants
    simp only [Prod.snd]
    rw [hPositionPi, hVelocityPi, cross_smul_left, cross_smul_right,
      cross_smul_right,
      (polarDirection_identities frame Real.pi).2.2.2.1]
    ring
  have hHAtPi : H = (OrbitalInvariants system trajectory tPi).2 :=
    hH.trans (invariants_conserved system trajectory hLaw referenceTime tPi).2
  have hHne : H ≠ 0 := by
    have hcrossSq :=
      (polarDirection_identities frame Real.pi).2.2.2.2.1
    have hcrossNe : planarCross frame.radialAxis frame.transverseAxis ≠ 0 := by
      intro hz
      rw [hz] at hcrossSq
      norm_num at hcrossSq
    have hvalueNe : (OrbitalInvariants system trajectory tPi).2 ≠ 0 := by
      rw [hInvariantPi]
      exact mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (reducedMass_pos system).ne'
            (pow_ne_zero 2 (div_ne_zero hp.ne' (by nlinarith))))
          (hDerivPos tPi).ne')
        hcrossNe
    rwa [← hHAtPi] at hvalueNe
  have hEAtPi : E = (OrbitalInvariants system trajectory tPi).1 :=
    hE.trans (invariants_conserved system trajectory hLaw referenceTime tPi).1
  have hRoot : turningPolynomial system E H (p / (1 + eccentricity)) = 0 := by
    rw [← hRadiusPi]
    exact (radialSpeed_eq_zero_iff_turningPolynomial_eq_zero system trajectory
      E H tPi hEAtPi hHAtPi).mp hRadialPi
  have hmu : reducedMass system ≠ 0 := (reducedMass_pos system).ne'
  have hk : system.coupling ≠ 0 := system.coupling_pos.ne'
  have hpne : p ≠ 0 := hp.ne'
  have hHsqNe : H ^ 2 ≠ 0 := pow_ne_zero 2 hHne
  have hPlus : 1 + eccentricity ≠ 0 := by nlinarith
  have hMinus : 1 - eccentricity ≠ 0 := by nlinarith
  have hESqGt : 1 < eccentricity ^ 2 := by nlinarith only [heGt]
  have hEPos : 0 < E := by
    have hdenPos : 0 < reducedMass system * system.coupling ^ 2 :=
      mul_pos (reducedMass_pos system) (sq_pos_of_pos system.coupling_pos)
    have hquot : 0 < 2 * E * H ^ 2 /
        (reducedMass system * system.coupling ^ 2) := by
      nlinarith only [heRelation, hESqGt]
    have hnum : 0 < 2 * E * H ^ 2 :=
      (div_pos_iff_of_pos_right hdenPos).mp hquot
    have hfac : 0 < 2 * H ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hHne)
    rw [show 2 * E * H ^ 2 = E * (2 * H ^ 2) by ring] at hnum
    exact pos_of_mul_pos_left hnum hfac.le
  have hRootOriginal := hRoot
  unfold turningPolynomial at hRoot
  field_simp [hPlus] at hRoot
  field_simp [hmu, hk, hHsqNe] at heRelation
  let A := reducedMass system * system.coupling * p
  let B := H ^ 2
  have hfactor :
      (1 + eccentricity) * (A - B) *
        ((eccentricity - 1) * A + (eccentricity + 1) * B) = 0 := by
    dsimp [A, B]
    linear_combination H ^ 2 * hRoot + reducedMass system * p ^ 2 * heRelation
  have hsecondPos : 0 <
      (eccentricity - 1) * A + (eccentricity + 1) * B := by
    dsimp [A, B]
    have hApos : 0 < reducedMass system * system.coupling * p :=
      mul_pos (mul_pos (reducedMass_pos system) system.coupling_pos) hp
    have hBpos : 0 < H ^ 2 := sq_pos_of_ne_zero hHne
    exact add_pos (mul_pos (sub_pos.mpr heGt) hApos)
      (mul_pos (by nlinarith) hBpos)
  have hAB : A = B := by
    rcases mul_eq_zero.mp hfactor with h | h
    · rcases mul_eq_zero.mp h with hOne | hABzero
      · nlinarith
      · linarith
    · exact False.elim (hsecondPos.ne' h)
  have hHsq : H ^ 2 = reducedMass system * system.coupling * p := by
    exact hAB.symm
  have hP : p = H ^ 2 / (reducedMass system * system.coupling) := by
    field_simp [hmu, hk]
    nlinarith only [hHsq]
  have hEformula :
      E = system.coupling * (eccentricity ^ 2 - 1) / (2 * p) := by
    rw [hHsq] at heRelation
    field_simp [hmu, hk, hpne] at heRelation ⊢
    nlinarith only [heRelation]
  have hFactorization (r : ℝ) :
      turningPolynomial system E H r =
        (reducedMass system * system.coupling / p) *
          (eccentricity ^ 2 - 1) *
          (r - p / (1 + eccentricity)) *
          (r - p / (1 - eccentricity)) := by
    unfold turningPolynomial
    rw [hEformula, hHsq]
    field_simp [hpne, hPlus, hMinus]
    ring
  have hLeading : reducedMass system * system.coupling / p ≠ 0 :=
    div_ne_zero (mul_ne_zero hmu hk) hpne
  have heFactor : eccentricity ^ 2 - 1 ≠ 0 :=
    (sub_pos.mpr hESqGt).ne'
  have hRootClassification : ∀ r : ℝ, 0 < r →
      (turningPolynomial system E H r = 0 ↔
        r = p / (1 + eccentricity)) := by
    intro r hr
    rw [hFactorization r]
    constructor
    · intro hzero
      rcases mul_eq_zero.mp hzero with hleft | hnegative
      · rcases mul_eq_zero.mp hleft with hpref | hperi
        · exact False.elim ((mul_ne_zero hLeading heFactor) hpref)
        · exact sub_eq_zero.mp hperi
      · have hneg : p / (1 - eccentricity) < 0 :=
          div_neg_of_pos_of_neg hp (sub_neg.mpr heGt)
        have := sub_eq_zero.mp hnegative
        linarith
    · rintro rfl
      ring
  have hTurning : IsPositiveTurningPoint system trajectory E H tPi
      (p / (1 + eccentricity)) := by
    refine ⟨div_pos hp (by nlinarith only [heGt]), hRadiusPi, hRadialPi,
      hEAtPi.symm, hHAtPi.symm, hRootOriginal⟩
  refine ⟨hHne, hEPos, hP, hEformula, hRootClassification, ?_⟩
  refine ⟨tPi, ⟨hθPi, hTurning⟩, ?_⟩
  intro u hu
  exact hPiUnique u hu.1

/-- Divergent radii and limiting position directions on both scattering ends. -/
lemma scatteringConic_position_limits
    (system : System) (trajectory : Trajectory) (E H p eccentricity α : ℝ)
    (frame : OrbitalFrame) (θ : ℝ → ℝ) (referenceTime : ℝ)
    (hCarrier : SatisfiesScatteringConicCarrier system trajectory E H p eccentricity α
      frame θ referenceTime) :
    Tendsto (radius trajectory) atBot atTop ∧
    Tendsto
        (fun t ↦ (radius trajectory t)⁻¹ • trajectory.position t)
        atBot (nhds (polarDirection frame α).1) ∧
    Tendsto (radius trajectory) atTop atTop ∧
    Tendsto
        (fun t ↦ (radius trajectory t)⁻¹ • trajectory.position t)
        atTop (nhds (polarDirection frame (2 * Real.pi - α)).1) := by
  rcases hCarrier with
    ⟨hLaw, hE, hH, hp, heGt, hαPos, hαLt, heCos, heRelation,
      hPhase, hPosition⟩
  rcases hPhase with
    ⟨hPhaseαPos, hPhaseαLt, hContDiff, hStrict, hDerivPos,
      hRange, hThetaBot, hThetaTop⟩
  have hePos : 0 < eccentricity := lt_trans zero_lt_one heGt
  have hαMem : α ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · exact hαPos.le
    · nlinarith [Real.pi_pos]
  have hdenPos (t : ℝ) : 0 < 1 - eccentricity * Real.cos (θ t) := by
    have hθMem : θ t ∈ Ioo α (2 * Real.pi - α) := by
      rw [← hRange]
      exact mem_range_self t
    have hcosLt : Real.cos (θ t) < Real.cos α := by
      by_cases hle : θ t ≤ Real.pi
      · exact Real.strictAntiOn_cos hαMem
          ⟨(lt_trans hαPos hθMem.1).le, hle⟩ hθMem.1
      · have hgt : Real.pi < θ t := lt_of_not_ge hle
        have hβMem : 2 * Real.pi - θ t ∈ Icc (0 : ℝ) Real.pi := by
          constructor
          · nlinarith only [hθMem.2, hαPos]
          · nlinarith only [hgt]
        have hαβ : α < 2 * Real.pi - θ t := by
          nlinarith only [hθMem.2]
        have hlt := Real.strictAntiOn_cos hαMem hβMem hαβ
        rwa [Real.cos_two_pi_sub] at hlt
    have hmul := mul_lt_mul_of_pos_left hcosLt hePos
    rw [heCos] at hmul
    linarith
  have hRadius (t : ℝ) :
      radius trajectory t = p / (1 - eccentricity * Real.cos (θ t)) := by
    unfold radius
    rw [hPosition t, norm_smul,
      (polarDirection_identities frame (θ t)).1]
    simp only [mul_one, Real.norm_eq_abs]
    rw [abs_of_pos (div_pos hp (hdenPos t))]
  have hNormalized (t : ℝ) :
      (radius trajectory t)⁻¹ • trajectory.position t =
        (polarDirection frame (θ t)).1 := by
    rw [hRadius t, hPosition t]
    rw [smul_smul, inv_mul_cancel₀
      (div_ne_zero hp.ne' (hdenPos t).ne'), one_smul]
  have hDenContinuous : Continuous
      (fun x : ℝ ↦ 1 - eccentricity * Real.cos x) := by
    fun_prop
  have hDenBot : Tendsto
      (fun t ↦ 1 - eccentricity * Real.cos (θ t)) atBot (nhds 0) := by
    simpa [Function.comp_def, heCos] using
      (hDenContinuous.tendsto α).comp hThetaBot
  have hDenTop : Tendsto
      (fun t ↦ 1 - eccentricity * Real.cos (θ t)) atTop (nhds 0) := by
    simpa [Function.comp_def, Real.cos_two_pi_sub, heCos] using
      (hDenContinuous.tendsto (2 * Real.pi - α)).comp hThetaTop
  have hDenBotGT : Tendsto
      (fun t ↦ 1 - eccentricity * Real.cos (θ t)) atBot
        (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hDenBot, ?_⟩
    filter_upwards [] with t
    exact hdenPos t
  have hDenTopGT : Tendsto
      (fun t ↦ 1 - eccentricity * Real.cos (θ t)) atTop
        (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hDenTop, ?_⟩
    filter_upwards [] with t
    exact hdenPos t
  have hRhoBot : Tendsto
      (fun t ↦ p / (1 - eccentricity * Real.cos (θ t))) atBot atTop := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_nhdsGT_zero.comp hDenBotGT).const_mul_atTop hp
  have hRhoTop : Tendsto
      (fun t ↦ p / (1 - eccentricity * Real.cos (θ t))) atTop atTop := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_nhdsGT_zero.comp hDenTopGT).const_mul_atTop hp
  have hRadiusBot : Tendsto (radius trajectory) atBot atTop :=
    hRhoBot.congr' (Filter.Eventually.of_forall fun t ↦ (hRadius t).symm)
  have hRadiusTop : Tendsto (radius trajectory) atTop atTop :=
    hRhoTop.congr' (Filter.Eventually.of_forall fun t ↦ (hRadius t).symm)
  have hPolarContinuous : Continuous
      (fun x : ℝ ↦ (polarDirection frame x).1) := by
    unfold polarDirection
    fun_prop
  have hDirectionBot : Tendsto
      (fun t ↦ (radius trajectory t)⁻¹ • trajectory.position t)
      atBot (nhds (polarDirection frame α).1) := by
    refine ((hPolarContinuous.tendsto α).comp hThetaBot).congr' ?_
    exact Filter.Eventually.of_forall fun t ↦ (hNormalized t).symm
  have hDirectionTop : Tendsto
      (fun t ↦ (radius trajectory t)⁻¹ • trajectory.position t)
      atTop (nhds (polarDirection frame (2 * Real.pi - α)).1) := by
    refine ((hPolarContinuous.tendsto (2 * Real.pi - α)).comp hThetaTop).congr' ?_
    exact Filter.Eventually.of_forall fun t ↦ (hNormalized t).symm
  exact ⟨hRadiusBot, hDirectionBot, hRadiusTop, hDirectionTop⟩

/-- Existence of incoming and outgoing asymptotic relative velocities. -/
def SatisfiesAsymptoticDirectionCarrier
    (trajectory : Trajectory)
    (incoming outgoing : EuclideanSpace ℝ (Fin 2)) : Prop :=
  Tendsto trajectory.velocity atBot (nhds incoming) ∧
  Tendsto trajectory.velocity atTop (nhds outgoing)

/-- Magnitudes and normalized directions of the scattering asymptotic velocities. -/
theorem scatteringConic_asymptotic_directions
    (system : System) (trajectory : Trajectory) (E H p eccentricity α : ℝ)
    (frame : OrbitalFrame) (θ : ℝ → ℝ) (referenceTime : ℝ)
    (incoming outgoing : EuclideanSpace ℝ (Fin 2))
    (hCarrier : SatisfiesScatteringConicCarrier system trajectory E H p eccentricity α
      frame θ referenceTime)
    (hAsymptotic : SatisfiesAsymptoticDirectionCarrier trajectory incoming outgoing) :
    0 < E ∧
    ‖incoming‖ = Real.sqrt (2 * E / reducedMass system) ∧
    ‖outgoing‖ = Real.sqrt (2 * E / reducedMass system) ∧
    0 < Real.sqrt (2 * E / reducedMass system) ∧
    ‖incoming‖⁻¹ • incoming = -(polarDirection frame α).1 ∧
    ‖outgoing‖⁻¹ • outgoing =
      (polarDirection frame (2 * Real.pi - α)).1 := by
  have hParams := scatteringConic_parameter_identities system trajectory E H p
    eccentricity α frame θ referenceTime hCarrier
  have hLimits := scatteringConic_position_limits system trajectory E H p
    eccentricity α frame θ referenceTime hCarrier
  rcases hAsymptotic with ⟨hVelocityBot, hVelocityTop⟩
  rcases hCarrier with
    ⟨hLaw, hE, hH, hp, heGt, hαPos, hαLt, heCos, heRelation,
      hPhase, hPosition⟩
  rcases hPhase with
    ⟨hPhaseαPos, hPhaseαLt, hContDiff, hStrict, hDerivPos,
      hRange, hThetaBot, hThetaTop⟩
  have hmuPos := reducedMass_pos system
  have hmu : reducedMass system ≠ 0 := hmuPos.ne'
  have hePos : 0 < eccentricity := lt_trans zero_lt_one heGt
  have hEnergyConst (t : ℝ) :
      (OrbitalInvariants system trajectory t).1 = E :=
    (hE.trans (invariants_conserved system trajectory hLaw referenceTime t).1).symm
  have hAngularConst (t : ℝ) :
      (OrbitalInvariants system trajectory t).2 = H :=
    (hH.trans (invariants_conserved system trajectory hLaw referenceTime t).2).symm
  have hEnergyExpression (t : ℝ) :
      reducedMass system / 2 * ‖trajectory.velocity t‖ ^ 2 -
          system.coupling * (radius trajectory t)⁻¹ = E := by
    simpa [OrbitalInvariants, div_eq_mul_inv] using hEnergyConst t
  have hEnergyLimitBot : Tendsto
      (fun t ↦ reducedMass system / 2 * ‖trajectory.velocity t‖ ^ 2 -
        system.coupling * (radius trajectory t)⁻¹) atBot
      (nhds (reducedMass system / 2 * ‖incoming‖ ^ 2)) := by
    simpa using
      (tendsto_const_nhds.mul (hVelocityBot.norm.pow 2)).sub
        (tendsto_const_nhds.mul hLimits.1.inv_tendsto_atTop)
  have hEnergyLimitTop : Tendsto
      (fun t ↦ reducedMass system / 2 * ‖trajectory.velocity t‖ ^ 2 -
        system.coupling * (radius trajectory t)⁻¹) atTop
      (nhds (reducedMass system / 2 * ‖outgoing‖ ^ 2)) := by
    simpa using
      (tendsto_const_nhds.mul (hVelocityTop.norm.pow 2)).sub
        (tendsto_const_nhds.mul hLimits.2.2.1.inv_tendsto_atTop)
  have hEnergyIncoming :
      E = reducedMass system / 2 * ‖incoming‖ ^ 2 := by
    exact tendsto_nhds_unique tendsto_const_nhds
      (hEnergyLimitBot.congr'
        (Filter.Eventually.of_forall hEnergyExpression))
  have hEnergyOutgoing :
      E = reducedMass system / 2 * ‖outgoing‖ ^ 2 := by
    exact tendsto_nhds_unique tendsto_const_nhds
      (hEnergyLimitTop.congr'
        (Filter.Eventually.of_forall hEnergyExpression))
  have hRatioPos : 0 < 2 * E / reducedMass system :=
    div_pos (mul_pos (by norm_num) hParams.2.1) hmuPos
  have hIncomingSq : ‖incoming‖ ^ 2 = 2 * E / reducedMass system := by
    field_simp [hmu]
    nlinarith only [hEnergyIncoming]
  have hOutgoingSq : ‖outgoing‖ ^ 2 = 2 * E / reducedMass system := by
    field_simp [hmu]
    nlinarith only [hEnergyOutgoing]
  have hIncomingNorm : ‖incoming‖ = Real.sqrt (2 * E / reducedMass system) := by
    apply (sq_eq_sq₀ (norm_nonneg incoming) (Real.sqrt_nonneg _)).mp
    rw [hIncomingSq, Real.sq_sqrt hRatioPos.le]
  have hOutgoingNorm : ‖outgoing‖ = Real.sqrt (2 * E / reducedMass system) := by
    apply (sq_eq_sq₀ (norm_nonneg outgoing) (Real.sqrt_nonneg _)).mp
    rw [hOutgoingSq, Real.sq_sqrt hRatioPos.le]
  have hSqrtPos : 0 < Real.sqrt (2 * E / reducedMass system) :=
    Real.sqrt_pos.2 hRatioPos
  have hαMem : α ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · exact hαPos.le
    · nlinarith [Real.pi_pos]
  have hdenPos (t : ℝ) : 0 < 1 - eccentricity * Real.cos (θ t) := by
    have hθMem : θ t ∈ Ioo α (2 * Real.pi - α) := by
      rw [← hRange]
      exact mem_range_self t
    have hcosLt : Real.cos (θ t) < Real.cos α := by
      by_cases hle : θ t ≤ Real.pi
      · exact Real.strictAntiOn_cos hαMem
          ⟨(lt_trans hαPos hθMem.1).le, hle⟩ hθMem.1
      · have hgt : Real.pi < θ t := lt_of_not_ge hle
        have hβMem : 2 * Real.pi - θ t ∈ Icc (0 : ℝ) Real.pi := by
          constructor
          · nlinarith only [hθMem.2, hαPos]
          · nlinarith only [hgt]
        have hαβ : α < 2 * Real.pi - θ t := by
          nlinarith only [hθMem.2]
        have hlt := Real.strictAntiOn_cos hαMem hβMem hαβ
        rwa [Real.cos_two_pi_sub] at hlt
    have hmul := mul_lt_mul_of_pos_left hcosLt hePos
    rw [heCos] at hmul
    linarith
  have hRadius (t : ℝ) :
      radius trajectory t = p / (1 - eccentricity * Real.cos (θ t)) := by
    unfold radius
    rw [hPosition t, norm_smul,
      (polarDirection_identities frame (θ t)).1]
    simp only [mul_one, Real.norm_eq_abs]
    rw [abs_of_pos (div_pos hp (hdenPos t))]
  have hThetaDeriv (t : ℝ) : HasDerivAt θ (deriv θ t) t :=
    (hContDiff.differentiable (by norm_num) t).hasDerivAt
  have hRhoDeriv (t : ℝ) :
      HasDerivAt
        (fun z ↦ p / (1 - eccentricity * Real.cos (θ z)))
        (-(p * eccentricity * Real.sin (θ t) * deriv θ t) /
          (1 - eccentricity * Real.cos (θ t)) ^ 2) t := by
    have hcos := (Real.hasDerivAt_cos (θ t)).comp t (hThetaDeriv t)
    have hden :
        HasDerivAt (fun z ↦ 1 - eccentricity * Real.cos (θ z))
          (eccentricity * Real.sin (θ t) * deriv θ t) t := by
      convert! (hasDerivAt_const t (1 : ℝ)).sub
        (hcos.const_mul eccentricity) using 1
      ring
    convert! (hasDerivAt_const t p).div hden (hdenPos t).ne' using 1
    ring
  have hRadial (t : ℝ) :
      radialSpeed trajectory t =
        -(p * eccentricity * Real.sin (θ t) * deriv θ t) /
          (1 - eccentricity * Real.cos (θ t)) ^ 2 := by
    have hradiusDeriv := (hRhoDeriv t).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hRadius)
    exact (hasDerivAt_radius trajectory t).unique hradiusDeriv
  have hαPi : α < Real.pi := by nlinarith [Real.pi_pos]
  have hPiEndpoint : Real.pi < 2 * Real.pi - α := by
    nlinarith [Real.pi_pos]
  have hRadialNegative : ∀ᶠ t in atBot, radialSpeed trajectory t < 0 := by
    filter_upwards [hThetaBot.eventually (Iio_mem_nhds hαPi)] with t hθlt
    have hθMem : θ t ∈ Ioo α (2 * Real.pi - α) := by
      rw [← hRange]
      exact mem_range_self t
    have hsin : 0 < Real.sin (θ t) :=
      Real.sin_pos_of_pos_of_lt_pi (lt_trans hαPos hθMem.1) hθlt
    rw [hRadial t]
    exact div_neg_of_neg_of_pos
      (neg_neg_of_pos
        (mul_pos (mul_pos (mul_pos hp hePos) hsin) (hDerivPos t)))
      (sq_pos_of_pos (hdenPos t))
  have hRadialPositive : ∀ᶠ t in atTop, 0 < radialSpeed trajectory t := by
    filter_upwards [hThetaTop.eventually (Ioi_mem_nhds hPiEndpoint)] with t hθgt
    have hθMem : θ t ∈ Ioo α (2 * Real.pi - α) := by
      rw [← hRange]
      exact mem_range_self t
    have hsinShift : Real.sin (θ t - 2 * Real.pi) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith only [hθMem.2, hαPos])
        (by nlinarith only [hθgt])
    have hsin : Real.sin (θ t) < 0 := by
      rwa [Real.sin_sub_two_pi] at hsinShift
    have hnum :
        p * eccentricity * Real.sin (θ t) * deriv θ t < 0 :=
      mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (mul_pos hp hePos) hsin) (hDerivPos t)
    rw [hRadial t]
    exact div_pos (neg_pos.mpr hnum) (sq_pos_of_pos (hdenPos t))
  have hRadialIdentity (t : ℝ) :
      inner ℝ ((radius trajectory t)⁻¹ • trajectory.position t)
          (trajectory.velocity t) = radialSpeed trajectory t := by
    unfold radialSpeed
    simp only [inner_smul_left, RCLike.star_def, conj_trivial]
    rw [div_eq_mul_inv, mul_comm]
  have hRadialLimitBot : Tendsto (radialSpeed trajectory) atBot
      (nhds (inner ℝ (polarDirection frame α).1 incoming)) := by
    exact (hLimits.2.1.inner hVelocityBot).congr'
      (Filter.Eventually.of_forall hRadialIdentity)
  have hRadialLimitTop : Tendsto (radialSpeed trajectory) atTop
      (nhds (inner ℝ (polarDirection frame (2 * Real.pi - α)).1 outgoing)) := by
    exact (hLimits.2.2.2.inner hVelocityTop).congr'
      (Filter.Eventually.of_forall hRadialIdentity)
  have hIncomingInnerNonpos :
      inner ℝ (polarDirection frame α).1 incoming ≤ 0 :=
    le_of_tendsto hRadialLimitBot
      (hRadialNegative.mono fun _ ht ↦ ht.le)
  have hOutgoingInnerNonneg :
      0 ≤ inner ℝ (polarDirection frame (2 * Real.pi - α)).1 outgoing :=
    ge_of_tendsto hRadialLimitTop
      (hRadialPositive.mono fun _ ht ↦ ht.le)
  have cross_smul_left (a : ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
      planarCross (a • x) y = a * planarCross x y := by
    unfold planarCross
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hCrossIdentity (t : ℝ) :
      planarCross ((radius trajectory t)⁻¹ • trajectory.position t)
          (trajectory.velocity t) =
        (H / reducedMass system) * (radius trajectory t)⁻¹ := by
    have hconst := hAngularConst t
    unfold OrbitalInvariants at hconst
    simp only [Prod.snd] at hconst
    rw [cross_smul_left]
    have hr : radius trajectory t ≠ 0 := by
      simp only [radius, norm_ne_zero_iff]
      exact trajectory.noncollision t
    field_simp [hmu, hr]
    linear_combination hconst
  have hCrossZeroBot : Tendsto
      (fun t ↦ planarCross
        ((radius trajectory t)⁻¹ • trajectory.position t)
        (trajectory.velocity t)) atBot (nhds 0) := by
    have h : Tendsto
        (fun t : ℝ ↦ (H / reducedMass system) * (radius trajectory t)⁻¹)
        atBot (nhds ((H / reducedMass system) * 0)) :=
      tendsto_const_nhds.mul hLimits.1.inv_tendsto_atTop
    have hrhs : Tendsto
        (fun t ↦ (H / reducedMass system) * (radius trajectory t)⁻¹)
        atBot (nhds 0) := by simpa using h
    exact hrhs.congr'
      (Filter.Eventually.of_forall fun t ↦ (hCrossIdentity t).symm)
  have hCrossZeroTop : Tendsto
      (fun t ↦ planarCross
        ((radius trajectory t)⁻¹ • trajectory.position t)
        (trajectory.velocity t)) atTop (nhds 0) := by
    have h : Tendsto
        (fun t : ℝ ↦ (H / reducedMass system) * (radius trajectory t)⁻¹)
        atTop (nhds ((H / reducedMass system) * 0)) :=
      tendsto_const_nhds.mul hLimits.2.2.1.inv_tendsto_atTop
    have hrhs : Tendsto
        (fun t ↦ (H / reducedMass system) * (radius trajectory t)⁻¹)
        atTop (nhds 0) := by simpa using h
    exact hrhs.congr'
      (Filter.Eventually.of_forall fun t ↦ (hCrossIdentity t).symm)
  have hPlanarContinuous : Continuous
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
        planarCross z.1 z.2) := by
    unfold planarCross
    fun_prop
  have hCrossLimitBot : Tendsto
      (fun t ↦ planarCross
        ((radius trajectory t)⁻¹ • trajectory.position t)
        (trajectory.velocity t)) atBot
      (nhds (planarCross (polarDirection frame α).1 incoming)) := by
    simpa [Function.comp_def] using
      (hPlanarContinuous.tendsto ((polarDirection frame α).1, incoming)).comp
        (hLimits.2.1.prodMk_nhds hVelocityBot)
  have hCrossLimitTop : Tendsto
      (fun t ↦ planarCross
        ((radius trajectory t)⁻¹ • trajectory.position t)
        (trajectory.velocity t)) atTop
      (nhds (planarCross
        (polarDirection frame (2 * Real.pi - α)).1 outgoing)) := by
    simpa [Function.comp_def] using
      (hPlanarContinuous.tendsto
        ((polarDirection frame (2 * Real.pi - α)).1, outgoing)).comp
          (hLimits.2.2.2.prodMk_nhds hVelocityTop)
  have hCrossIncoming : planarCross (polarDirection frame α).1 incoming = 0 :=
    tendsto_nhds_unique hCrossLimitBot hCrossZeroBot
  have hCrossOutgoing :
      planarCross (polarDirection frame (2 * Real.pi - α)).1 outgoing = 0 :=
    tendsto_nhds_unique hCrossLimitTop hCrossZeroTop
  have hCollinear (n w : EuclideanSpace ℝ (Fin 2))
      (hn : ‖n‖ = 1) (hcross : planarCross n w = 0) :
      w = (inner ℝ n w) • n := by
    have hlagrange := norm_mul_norm_eq_dot_sq_add_cross_sq n w
    rw [hn, hcross] at hlagrange
    norm_num at hlagrange
    have hsquare : ‖w - (inner ℝ n w) • n‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, inner_smul_right,
        real_inner_comm n w, norm_smul, hn, mul_one, Real.norm_eq_abs,
        sq_abs]
      nlinarith only [hlagrange]
    have hnormzero : ‖w - (inner ℝ n w) • n‖ = 0 :=
      sq_eq_zero_iff.mp hsquare
    exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
  have hIncomingCollinear :
      incoming = (inner ℝ (polarDirection frame α).1 incoming) •
        (polarDirection frame α).1 :=
    hCollinear _ _ (polarDirection_identities frame α).1 hCrossIncoming
  have hOutgoingCollinear :
      outgoing =
        (inner ℝ (polarDirection frame (2 * Real.pi - α)).1 outgoing) •
          (polarDirection frame (2 * Real.pi - α)).1 :=
    hCollinear _ _
      (polarDirection_identities frame (2 * Real.pi - α)).1 hCrossOutgoing
  have hIncomingInner :
      inner ℝ (polarDirection frame α).1 incoming = -‖incoming‖ := by
    have hnorm := congrArg norm hIncomingCollinear
    rw [norm_smul, (polarDirection_identities frame α).1, mul_one,
      Real.norm_eq_abs, abs_of_nonpos hIncomingInnerNonpos] at hnorm
    linarith
  have hOutgoingInner :
      inner ℝ (polarDirection frame (2 * Real.pi - α)).1 outgoing = ‖outgoing‖ := by
    have hnorm := congrArg norm hOutgoingCollinear
    rw [norm_smul,
      (polarDirection_identities frame (2 * Real.pi - α)).1, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hOutgoingInnerNonneg] at hnorm
    exact hnorm.symm
  have hIncomingDirection :
      ‖incoming‖⁻¹ • incoming = -(polarDirection frame α).1 := by
    have hnormNe : ‖incoming‖ ≠ 0 := by
      rw [hIncomingNorm]
      exact hSqrtPos.ne'
    calc
      ‖incoming‖⁻¹ • incoming =
          ‖incoming‖⁻¹ •
            ((inner ℝ (polarDirection frame α).1 incoming) •
              (polarDirection frame α).1) :=
        congrArg (fun w ↦ ‖incoming‖⁻¹ • w) hIncomingCollinear
      _ = (‖incoming‖⁻¹ *
            inner ℝ (polarDirection frame α).1 incoming) •
              (polarDirection frame α).1 := by rw [smul_smul]
      _ = -((polarDirection frame α).1) := by
        rw [hIncomingInner]
        have hcoeff : ‖incoming‖⁻¹ * -‖incoming‖ = -1 := by
          field_simp
        rw [hcoeff]
        simp
  have hOutgoingDirection :
      ‖outgoing‖⁻¹ • outgoing =
        (polarDirection frame (2 * Real.pi - α)).1 := by
    have hnormNe : ‖outgoing‖ ≠ 0 := by
      rw [hOutgoingNorm]
      exact hSqrtPos.ne'
    calc
      ‖outgoing‖⁻¹ • outgoing =
          ‖outgoing‖⁻¹ •
            ((inner ℝ (polarDirection frame (2 * Real.pi - α)).1 outgoing) •
              (polarDirection frame (2 * Real.pi - α)).1) :=
        congrArg (fun w ↦ ‖outgoing‖⁻¹ • w) hOutgoingCollinear
      _ = (‖outgoing‖⁻¹ *
            inner ℝ (polarDirection frame (2 * Real.pi - α)).1 outgoing) •
              (polarDirection frame (2 * Real.pi - α)).1 := by rw [smul_smul]
      _ = (polarDirection frame (2 * Real.pi - α)).1 := by
        rw [hOutgoingInner, inv_mul_cancel₀ hnormNe, one_smul]
  exact ⟨hParams.2.1, hIncomingNorm, hOutgoingNorm, hSqrtPos,
    hIncomingDirection, hOutgoingDirection⟩

end

end Ipho2026Gpt56solBlind.Shared.CoulombOrbit
