import Mathlib

/- USER: Sterile clean-room retry. This live file is the authorized statement-only
scaffold. Reconstruct every proof from scratch using only this file, its matching
clean-room blueprint chapter, project manifests/toolchain, and installed public
Lean/Mathlib APIs. Do not inspect Git history, prior iteration logs or reports,
task-result archives, any other Solution proof, or any previously written proof
of this module. Record the access boundary explicitly in the handoff report. -/

/-!
# Generic two-fragment photodissociation kinematics

This file gives an answer-free carrier for absorption of one photon by a
stationary parent followed by classical, non-relativistic dissociation into
two fragments.  Momenta live in a two-dimensional Euclidean space, with the
incident photon travelling along the first coordinate axis.
-/

namespace Ipho2026Gpt56solBlind.Shared.PhotodissociationKinematics

noncomputable section

open scoped InnerProductSpace

/-- Physical parameters for a two-fragment photodissociation experiment. -/
structure Setup where
  fragmentOneMass : ℝ
  fragmentTwoMass : ℝ
  propagationSpeed : ℝ
  reducedAction : ℝ
  energyGap : ℝ
  angle : ℝ
  fragmentOneMass_pos : 0 < fragmentOneMass
  fragmentTwoMass_pos : 0 < fragmentTwoMass
  propagationSpeed_pos : 0 < propagationSpeed
  reducedAction_pos : 0 < reducedAction
  energyGap_pos : 0 < energyGap
  angle_nonneg : 0 ≤ angle
  angle_le_pi : angle ≤ Real.pi

/-- Energy of the absorbed photon at angular frequency `ω`. -/
def photonEnergy (s : Setup) (ω : ℝ) : ℝ :=
  s.reducedAction * ω

/-- Magnitude of the absorbed photon's momentum. -/
def photonMomentumMagnitude (s : Setup) (ω : ℝ) : ℝ :=
  photonEnergy s ω / s.propagationSpeed

/-- Exact momentum and energy conservation, together with the prescribed
unsigned angle of fragment one from the incident direction. -/
def ConservationOutcome
    (s : Setup) (ω : ℝ)
    (p₁ p₂ : EuclideanSpace ℝ (Fin 2)) : Prop :=
  let incidentDirection : EuclideanSpace ℝ (Fin 2) := !₂[(1 : ℝ), 0]
  0 < ω ∧
    0 < ‖p₁‖ ∧
    p₁ + p₂ = photonMomentumMagnitude s ω • incidentDirection ∧
    photonEnergy s ω =
      s.energyGap +
        ‖p₁‖ ^ 2 / (2 * s.fragmentOneMass) +
        ‖p₂‖ ^ 2 / (2 * s.fragmentTwoMass) ∧
    ⟪p₁, incidentDirection⟫_ℝ =
      ‖p₁‖ * Real.cos s.angle

/-- A frequency is feasible when some two fragment momenta obey the full
conservation laws and angular constraint. -/
def Feasible (s : Setup) (ω : ℝ) : Prop :=
  ∃ p₁ p₂ : EuclideanSpace ℝ (Fin 2), ConservationOutcome s ω p₁ p₂

/-- Kinetic-energy cost after eliminating fragment two by momentum
conservation, with `r` representing the magnitude of fragment one. -/
def reducedKineticCost (s : Setup) (ω r : ℝ) : ℝ :=
  r ^ 2 / (2 * s.fragmentOneMass) +
    (photonMomentumMagnitude s ω ^ 2 + r ^ 2 -
        2 * photonMomentumMagnitude s ω * r * Real.cos s.angle) /
      (2 * s.fragmentTwoMass)

/-- Full vector conservation is equivalent to the reduced scalar energy
equation on the physical domain `r > 0`. -/
lemma feasible_iff_reducedCost (s : Setup) (ω : ℝ) :
    Feasible s ω ↔
      0 < ω ∧
        ∃ r : ℝ, 0 < r ∧
          photonEnergy s ω = s.energyGap + reducedKineticCost s ω r := by
  let e : EuclideanSpace ℝ (Fin 2) := !₂[(1 : ℝ), 0]
  constructor
  · rintro ⟨p₁, p₂, hω, hp₁, hmomentum, henergy, hangle⟩
    refine ⟨hω, ‖p₁‖, hp₁, ?_⟩
    have hp₂ : p₂ = photonMomentumMagnitude s ω • e - p₁ := by
      rw [eq_sub_iff_add_eq]
      simpa [e, add_comm] using hmomentum
    have hp₂_sq :
        ‖p₂‖ ^ 2 =
          photonMomentumMagnitude s ω ^ 2 + ‖p₁‖ ^ 2 -
            2 * photonMomentumMagnitude s ω * ‖p₁‖ * Real.cos s.angle := by
      rw [hp₂, norm_sub_sq_real]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      simp only [real_inner_smul_left]
      have he_norm : ‖e‖ = 1 := by
        rw [EuclideanSpace.norm_eq]
        simp [e, Fin.sum_univ_two]
      have he_inner : ⟪e, p₁⟫_ℝ = ‖p₁‖ * Real.cos s.angle := by
        rw [real_inner_comm]
        simpa [e] using hangle
      rw [he_norm, he_inner]
      ring
    rw [henergy]
    simp only [reducedKineticCost, hp₂_sq]
    ring
  · rintro ⟨hω, r, hr, henergy⟩
    let p₁ : EuclideanSpace ℝ (Fin 2) :=
      !₂[r * Real.cos s.angle, r * Real.sin s.angle]
    let p₂ : EuclideanSpace ℝ (Fin 2) :=
      !₂[photonMomentumMagnitude s ω - r * Real.cos s.angle,
        -(r * Real.sin s.angle)]
    have hp₁_sq : ‖p₁‖ ^ 2 = r ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [p₁, Fin.sum_univ_two]
      nlinarith [Real.sin_sq_add_cos_sq s.angle]
    have hp₁_norm : ‖p₁‖ = r := by
      nlinarith [norm_nonneg p₁]
    have hp₂_sq :
        ‖p₂‖ ^ 2 =
          photonMomentumMagnitude s ω ^ 2 + r ^ 2 -
            2 * photonMomentumMagnitude s ω * r * Real.cos s.angle := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [p₂, Fin.sum_univ_two]
      nlinarith [Real.sin_sq_add_cos_sq s.angle]
    refine ⟨p₁, p₂, ?_⟩
    dsimp only [ConservationOutcome]
    refine ⟨hω, ?_, ?_, ?_, ?_⟩
    · simpa [hp₁_norm] using hr
    · ext i
      fin_cases i <;> simp [p₁, p₂, e]
    · rw [henergy]
      simp only [hp₁_norm, hp₂_sq, reducedKineticCost]
      ring
    · rw [hp₁_norm]
      simp [p₁, PiLp.inner_apply, Fin.sum_univ_two]

/-- Angular factor obtained by minimizing the recoil cost over the relaxed
half-line `r ≥ 0`. -/
def relaxedAngularFactor (s : Setup) : ℝ :=
  1 -
    s.fragmentOneMass / (s.fragmentOneMass + s.fragmentTwoMass) *
      max (Real.cos s.angle) 0 ^ 2

/-- Minimizing fragment-one magnitude on the relaxed half-line `r ≥ 0`. -/
def relaxedMinimizingMagnitude (s : Setup) (ω : ℝ) : ℝ :=
  photonMomentumMagnitude s ω *
    (s.fragmentOneMass / (s.fragmentOneMass + s.fragmentTwoMass)) *
      max (Real.cos s.angle) 0

/-- Minimum (or physical-domain infimum) of the reduced kinetic cost. -/
def relaxedKineticCost (s : Setup) (ω : ℝ) : ℝ :=
  relaxedAngularFactor s * photonMomentumMagnitude s ω ^ 2 /
    (2 * s.fragmentTwoMass)

/-- The relaxed angular factor is at most one and is bounded below by the
strictly positive fragment-two mass fraction. -/
lemma relaxedAngularFactor_bounds (s : Setup) :
    0 < s.fragmentTwoMass / (s.fragmentOneMass + s.fragmentTwoMass) ∧
      s.fragmentTwoMass / (s.fragmentOneMass + s.fragmentTwoMass) ≤
        relaxedAngularFactor s ∧
      relaxedAngularFactor s ≤ 1 := by
  have hsum : 0 < s.fragmentOneMass + s.fragmentTwoMass :=
    add_pos s.fragmentOneMass_pos s.fragmentTwoMass_pos
  have hfrac_pos :
      0 < s.fragmentTwoMass /
        (s.fragmentOneMass + s.fragmentTwoMass) :=
    div_pos s.fragmentTwoMass_pos hsum
  have hρ_nonneg :
      0 ≤ s.fragmentOneMass /
        (s.fragmentOneMass + s.fragmentTwoMass) :=
    (div_pos s.fragmentOneMass_pos hsum).le
  have hmax_nonneg : 0 ≤ max (Real.cos s.angle) 0 := le_max_right _ _
  have hmax_le_one : max (Real.cos s.angle) 0 ≤ 1 :=
    max_le (Real.cos_le_one s.angle) (by norm_num)
  have hmax_sq_le_one : max (Real.cos s.angle) 0 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (max (Real.cos s.angle) 0)]
  have hprod_nonneg :
      0 ≤ s.fragmentOneMass /
          (s.fragmentOneMass + s.fragmentTwoMass) *
        max (Real.cos s.angle) 0 ^ 2 :=
    mul_nonneg hρ_nonneg (sq_nonneg _)
  have hprod_le :
      s.fragmentOneMass /
          (s.fragmentOneMass + s.fragmentTwoMass) *
        max (Real.cos s.angle) 0 ^ 2 ≤
      s.fragmentOneMass /
        (s.fragmentOneMass + s.fragmentTwoMass) :=
    mul_le_of_le_one_right hρ_nonneg hmax_sq_le_one
  have hmass_fraction :
      s.fragmentTwoMass / (s.fragmentOneMass + s.fragmentTwoMass) =
        1 - s.fragmentOneMass /
          (s.fragmentOneMass + s.fragmentTwoMass) := by
    field_simp [ne_of_gt hsum]
    ring
  refine ⟨hfrac_pos, ?_, ?_⟩
  · rw [hmass_fraction]
    unfold relaxedAngularFactor
    linarith
  · unfold relaxedAngularFactor
    linarith

/-- Expanded quadratic and completed-square descriptions of the reduced
kinetic cost. -/
lemma reducedCost_quadratic (s : Setup) (ω r : ℝ) :
    let q := photonMomentumMagnitude s ω
    let μ := Real.cos s.angle
    let a := (s.fragmentOneMass + s.fragmentTwoMass) /
      (2 * s.fragmentOneMass * s.fragmentTwoMass)
    let rᵤ := q * s.fragmentOneMass /
      (s.fragmentOneMass + s.fragmentTwoMass) * μ
    0 < a ∧
      reducedKineticCost s ω r =
        a * r ^ 2 - q * μ / s.fragmentTwoMass * r +
          q ^ 2 / (2 * s.fragmentTwoMass) ∧
      reducedKineticCost s ω r =
        a * (r - rᵤ) ^ 2 +
          q ^ 2 / (2 * s.fragmentTwoMass) *
            (1 - s.fragmentOneMass /
              (s.fragmentOneMass + s.fragmentTwoMass) * μ ^ 2) := by
  dsimp
  have hm₁ : s.fragmentOneMass ≠ 0 := ne_of_gt s.fragmentOneMass_pos
  have hm₂ : s.fragmentTwoMass ≠ 0 := ne_of_gt s.fragmentTwoMass_pos
  have hsum : s.fragmentOneMass + s.fragmentTwoMass ≠ 0 :=
    ne_of_gt (add_pos s.fragmentOneMass_pos s.fragmentTwoMass_pos)
  refine ⟨?_, ?_, ?_⟩
  · exact div_pos (add_pos s.fragmentOneMass_pos s.fragmentTwoMass_pos)
      (mul_pos (mul_pos (by norm_num) s.fragmentOneMass_pos)
        s.fragmentTwoMass_pos)
  · unfold reducedKineticCost
    field_simp [hm₁, hm₂]
    ring
  · unfold reducedKineticCost
    field_simp [hm₁, hm₂, hsum]
    ring

/-- On positive magnitudes, the relaxed cost is an attained unique minimum
for acute angles and a non-attained infimum for right or obtuse angles. -/
lemma reducedCost_minimum_or_infimum (s : Setup) (ω : ℝ) (hω : 0 < ω) :
    (0 < Real.cos s.angle →
      0 < relaxedMinimizingMagnitude s ω ∧
        (∀ r : ℝ, 0 < r →
          relaxedKineticCost s ω ≤ reducedKineticCost s ω r) ∧
        (∀ r : ℝ, 0 < r →
          (reducedKineticCost s ω r = relaxedKineticCost s ω ↔
            r = relaxedMinimizingMagnitude s ω))) ∧
    (Real.cos s.angle ≤ 0 →
      relaxedMinimizingMagnitude s ω = 0 ∧
        (∀ r : ℝ, 0 < r →
          relaxedKineticCost s ω < reducedKineticCost s ω r) ∧
        (∀ ε : ℝ, 0 < ε →
          ∃ r : ℝ, 0 < r ∧
            relaxedKineticCost s ω < reducedKineticCost s ω r ∧
            reducedKineticCost s ω r < relaxedKineticCost s ω + ε)) := by
  let q := photonMomentumMagnitude s ω
  let μ := Real.cos s.angle
  let a := (s.fragmentOneMass + s.fragmentTwoMass) /
    (2 * s.fragmentOneMass * s.fragmentTwoMass)
  have hq : 0 < q := by
    exact div_pos (mul_pos s.reducedAction_pos hω) s.propagationSpeed_pos
  have hsum : 0 < s.fragmentOneMass + s.fragmentTwoMass :=
    add_pos s.fragmentOneMass_pos s.fragmentTwoMass_pos
  have hm₁ : s.fragmentOneMass ≠ 0 := ne_of_gt s.fragmentOneMass_pos
  have hm₂ : s.fragmentTwoMass ≠ 0 := ne_of_gt s.fragmentTwoMass_pos
  have hsum_ne : s.fragmentOneMass + s.fragmentTwoMass ≠ 0 := ne_of_gt hsum
  have ha : 0 < a := by
    exact div_pos hsum
      (mul_pos (mul_pos (by norm_num) s.fragmentOneMass_pos)
        s.fragmentTwoMass_pos)
  constructor
  · intro hμ
    have hmax : max (Real.cos s.angle) 0 = Real.cos s.angle :=
      max_eq_left hμ.le
    have hr₀ : 0 < relaxedMinimizingMagnitude s ω := by
      unfold relaxedMinimizingMagnitude
      rw [hmax]
      exact mul_pos
        (mul_pos hq (div_pos s.fragmentOneMass_pos hsum)) hμ
    have hcost : ∀ r : ℝ,
        reducedKineticCost s ω r =
          relaxedKineticCost s ω +
            a * (r - relaxedMinimizingMagnitude s ω) ^ 2 := by
      intro r
      dsimp [a]
      unfold reducedKineticCost relaxedKineticCost relaxedAngularFactor
        relaxedMinimizingMagnitude
      rw [hmax]
      field_simp [hm₁, hm₂, hsum_ne]
      ring
    refine ⟨hr₀, ?_, ?_⟩
    · intro r hr
      rw [hcost r]
      exact le_add_of_nonneg_right (mul_nonneg ha.le (sq_nonneg _))
    · intro r hr
      rw [hcost r]
      constructor
      · intro heq
        have hsquare : (r - relaxedMinimizingMagnitude s ω) ^ 2 = 0 := by
          nlinarith [sq_nonneg (r - relaxedMinimizingMagnitude s ω)]
        nlinarith
      · intro heq
        subst r
        ring
  · intro hμ
    have hmax : max (Real.cos s.angle) 0 = 0 := max_eq_right hμ
    have hr₀ : relaxedMinimizingMagnitude s ω = 0 := by
      unfold relaxedMinimizingMagnitude
      rw [hmax]
      ring
    let d := -(q * μ) / s.fragmentTwoMass
    have hd : 0 ≤ d := by
      dsimp [d]
      exact div_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hq.le hμ))
        s.fragmentTwoMass_pos.le
    have hcost : ∀ r : ℝ,
        reducedKineticCost s ω r =
          relaxedKineticCost s ω + a * r ^ 2 + d * r := by
      intro r
      dsimp [a, d, q, μ]
      unfold reducedKineticCost relaxedKineticCost relaxedAngularFactor
      rw [hmax]
      field_simp [hm₁, hm₂]
      ring
    have hstrict : ∀ r : ℝ, 0 < r →
        relaxedKineticCost s ω < reducedKineticCost s ω r := by
      intro r hr
      rw [hcost r]
      have har : 0 < a * r ^ 2 :=
        mul_pos ha (sq_pos_of_pos hr)
      have hdr : 0 ≤ d * r := mul_nonneg hd hr.le
      linarith
    refine ⟨hr₀, hstrict, ?_⟩
    intro ε hε
    have had : 0 < a + d := lt_of_lt_of_le ha (le_add_of_nonneg_right hd)
    let r := min 1 (ε / (2 * (a + d)))
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min (by norm_num)
        (div_pos hε (mul_pos (by norm_num) had))
    have hr_one : r ≤ 1 := by
      dsimp [r]
      exact min_le_left _ _
    have hr_frac : r ≤ ε / (2 * (a + d)) := by
      dsimp [r]
      exact min_le_right _ _
    have hr_sq : r ^ 2 ≤ r := by nlinarith
    have hcost_le : a * r ^ 2 + d * r ≤ (a + d) * r := by
      nlinarith [mul_le_mul_of_nonneg_left hr_sq ha.le]
    have hcancel :
        (a + d) * (ε / (2 * (a + d))) = ε / 2 := by
      field_simp [ne_of_gt had]
    have hsmall : (a + d) * r ≤ ε / 2 := by
      calc
        (a + d) * r ≤ (a + d) * (ε / (2 * (a + d))) :=
          mul_le_mul_of_nonneg_left hr_frac had.le
        _ = ε / 2 := hcancel
    refine ⟨r, hr, hstrict r hr, ?_⟩
    rw [hcost r]
    nlinarith

/-- Exact range of the reduced cost on strictly positive fragment-one
magnitudes. -/
lemma reducedCost_positive_range (s : Setup) (ω T : ℝ) (hω : 0 < ω) :
    (0 < Real.cos s.angle →
      ((∃ r : ℝ, 0 < r ∧ reducedKineticCost s ω r = T) ↔
        relaxedKineticCost s ω ≤ T)) ∧
    (Real.cos s.angle ≤ 0 →
      ((∃ r : ℝ, 0 < r ∧ reducedKineticCost s ω r = T) ↔
        relaxedKineticCost s ω < T)) := by
  let q := photonMomentumMagnitude s ω
  let μ := Real.cos s.angle
  let a := (s.fragmentOneMass + s.fragmentTwoMass) /
    (2 * s.fragmentOneMass * s.fragmentTwoMass)
  have hq : 0 < q :=
    div_pos (mul_pos s.reducedAction_pos hω) s.propagationSpeed_pos
  have hsum : 0 < s.fragmentOneMass + s.fragmentTwoMass :=
    add_pos s.fragmentOneMass_pos s.fragmentTwoMass_pos
  have hm₁ : s.fragmentOneMass ≠ 0 := ne_of_gt s.fragmentOneMass_pos
  have hm₂ : s.fragmentTwoMass ≠ 0 := ne_of_gt s.fragmentTwoMass_pos
  have hsum_ne : s.fragmentOneMass + s.fragmentTwoMass ≠ 0 := ne_of_gt hsum
  have ha : 0 < a := by
    exact div_pos hsum
      (mul_pos (mul_pos (by norm_num) s.fragmentOneMass_pos)
        s.fragmentTwoMass_pos)
  obtain ⟨hacute, hnonacute⟩ := reducedCost_minimum_or_infimum s ω hω
  constructor
  · intro hμ
    obtain ⟨hr₀, hminimum, hequality⟩ := hacute hμ
    constructor
    · rintro ⟨r, hr, hcost⟩
      rw [← hcost]
      exact hminimum r hr
    · intro hT
      have hmax : max (Real.cos s.angle) 0 = Real.cos s.angle :=
        max_eq_left hμ.le
      have hcost : ∀ r : ℝ,
          reducedKineticCost s ω r =
            relaxedKineticCost s ω +
              a * (r - relaxedMinimizingMagnitude s ω) ^ 2 := by
        intro r
        dsimp [a]
        unfold reducedKineticCost relaxedKineticCost relaxedAngularFactor
          relaxedMinimizingMagnitude
        rw [hmax]
        field_simp [hm₁, hm₂, hsum_ne]
        ring
      let z := T - relaxedKineticCost s ω
      have hz : 0 ≤ z := by dsimp [z]; linarith
      have hza : 0 ≤ z / a := div_nonneg hz ha.le
      let r := relaxedMinimizingMagnitude s ω + Real.sqrt (z / a)
      have hr : 0 < r := by
        dsimp [r]
        nlinarith [Real.sqrt_nonneg (z / a)]
      refine ⟨r, hr, ?_⟩
      rw [hcost r]
      dsimp [r]
      have hsqrt := Real.sq_sqrt hza
      have hdiff :
          relaxedMinimizingMagnitude s ω + Real.sqrt (z / a) -
              relaxedMinimizingMagnitude s ω = Real.sqrt (z / a) := by
        ring
      rw [hdiff, hsqrt]
      dsimp [z]
      field_simp [ne_of_gt ha]
      ring
  · intro hμ
    obtain ⟨hr₀, hstrict, happroach⟩ := hnonacute hμ
    constructor
    · rintro ⟨r, hr, hcost⟩
      rw [← hcost]
      exact hstrict r hr
    · intro hT
      have hmax : max (Real.cos s.angle) 0 = 0 := max_eq_right hμ
      let d := -(q * μ) / s.fragmentTwoMass
      have hd : 0 ≤ d := by
        dsimp [d]
        exact div_nonneg
          (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hq.le hμ))
          s.fragmentTwoMass_pos.le
      have hcost : ∀ r : ℝ,
          reducedKineticCost s ω r =
            relaxedKineticCost s ω + a * r ^ 2 + d * r := by
        intro r
        dsimp [a, d, q, μ]
        unfold reducedKineticCost relaxedKineticCost relaxedAngularFactor
        rw [hmax]
        field_simp [hm₁, hm₂]
        ring
      let z := T - relaxedKineticCost s ω
      have hz : 0 < z := by dsimp [z]; linarith
      let D := d ^ 2 + 4 * a * z
      have hD : 0 ≤ D := by
        dsimp [D]
        positivity
      have hD_gt : d ^ 2 < D := by
        dsimp [D]
        nlinarith [mul_pos ha hz]
      have hsqrt_sq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
      have hd_sqrt : d < Real.sqrt D := by
        nlinarith [Real.sqrt_nonneg D]
      let r := (Real.sqrt D - d) / (2 * a)
      have hr : 0 < r :=
        div_pos (sub_pos.mpr hd_sqrt) (mul_pos (by norm_num) ha)
      have har : a * r ^ 2 + d * r = z := by
        dsimp [r]
        field_simp [ne_of_gt ha]
        nlinarith
      refine ⟨r, hr, ?_⟩
      rw [hcost r]
      calc
        relaxedKineticCost s ω + a * r ^ 2 + d * r =
            relaxedKineticCost s ω + (a * r ^ 2 + d * r) := by ring
        _ = relaxedKineticCost s ω + z := by rw [har]
        _ = T := by dsimp [z]; ring

/-- Positive coefficient of the quadratic photon-energy boundary. -/
def boundaryCoefficient (s : Setup) : ℝ :=
  relaxedAngularFactor s /
    (2 * s.fragmentTwoMass * s.propagationSpeed ^ 2)

/-- Energy remaining above the relaxed fragment kinetic cost. -/
def boundaryMargin (s : Setup) (x : ℝ) : ℝ :=
  x - s.energyGap - boundaryCoefficient s * x ^ 2

/-- The relaxed conservation boundary at a given angular frequency. -/
def ConservationBoundary (s : Setup) (ω : ℝ) : Prop :=
  photonEnergy s ω = s.energyGap + relaxedKineticCost s ω

/-- The positive-energy portion of the conservation boundary below the
vertex of its concave quadratic margin. -/
def OnLowerPhysicalBranch (s : Setup) (ω : ℝ) : Prop :=
  0 < photonEnergy s ω ∧
    2 * boundaryCoefficient s * photonEnergy s ω < 1

/-- Parameter regime in which the concave boundary margin crosses zero below
its vertex. -/
def SubcriticalParameters (s : Setup) : Prop :=
  4 * boundaryCoefficient s * s.energyGap < 1

/-- Feasibility is nonnegative boundary margin at acute angles and strictly
positive boundary margin at right or obtuse angles. -/
lemma feasible_iff_boundaryMargin (s : Setup) (ω : ℝ) :
    (0 < Real.cos s.angle →
      (Feasible s ω ↔
        0 < ω ∧ 0 ≤ boundaryMargin s (photonEnergy s ω))) ∧
    (Real.cos s.angle ≤ 0 →
      (Feasible s ω ↔
        0 < ω ∧ 0 < boundaryMargin s (photonEnergy s ω))) := by
  have hm₂ : s.fragmentTwoMass ≠ 0 := ne_of_gt s.fragmentTwoMass_pos
  have hc : s.propagationSpeed ≠ 0 := ne_of_gt s.propagationSpeed_pos
  have hmargin :
      boundaryMargin s (photonEnergy s ω) =
        photonEnergy s ω - s.energyGap - relaxedKineticCost s ω := by
    unfold boundaryMargin boundaryCoefficient relaxedKineticCost
      photonMomentumMagnitude
    field_simp [hm₂, hc]
  constructor
  · intro hμ
    constructor
    · intro hfeasible
      obtain ⟨hω, r, hr, henergy⟩ :=
        (feasible_iff_reducedCost s ω).mp hfeasible
      have hrange :=
        (reducedCost_positive_range s ω
          (photonEnergy s ω - s.energyGap) hω).1 hμ
      have htarget :
          ∃ r : ℝ, 0 < r ∧
            reducedKineticCost s ω r = photonEnergy s ω - s.energyGap := by
        refine ⟨r, hr, ?_⟩
        linarith
      have hle := hrange.mp htarget
      refine ⟨hω, ?_⟩
      rw [hmargin]
      linarith
    · rintro ⟨hω, hnonneg⟩
      rw [hmargin] at hnonneg
      have hrange :=
        (reducedCost_positive_range s ω
          (photonEnergy s ω - s.energyGap) hω).1 hμ
      obtain ⟨r, hr, hcost⟩ := hrange.mpr (by linarith)
      apply (feasible_iff_reducedCost s ω).mpr
      refine ⟨hω, r, hr, ?_⟩
      linarith
  · intro hμ
    constructor
    · intro hfeasible
      obtain ⟨hω, r, hr, henergy⟩ :=
        (feasible_iff_reducedCost s ω).mp hfeasible
      have hrange :=
        (reducedCost_positive_range s ω
          (photonEnergy s ω - s.energyGap) hω).2 hμ
      have htarget :
          ∃ r : ℝ, 0 < r ∧
            reducedKineticCost s ω r = photonEnergy s ω - s.energyGap := by
        refine ⟨r, hr, ?_⟩
        linarith
      have hlt := hrange.mp htarget
      refine ⟨hω, ?_⟩
      rw [hmargin]
      linarith
    · rintro ⟨hω, hpos⟩
      rw [hmargin] at hpos
      have hrange :=
        (reducedCost_positive_range s ω
          (photonEnergy s ω - s.energyGap) hω).2 hμ
      obtain ⟨r, hr, hcost⟩ := hrange.mpr (by linarith)
      apply (feasible_iff_reducedCost s ω).mpr
      refine ⟨hω, r, hr, ?_⟩
      linarith

/-- The boundary margin is strictly increasing below its vertex. -/
lemma boundaryMargin_strictMono_belowVertex
    (s : Setup) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x < y)
    (hy : 2 * boundaryCoefficient s * y ≤ 1) :
    boundaryMargin s x < boundaryMargin s y := by
  obtain ⟨hfrac, hfrac_le, halpha_le⟩ := relaxedAngularFactor_bounds s
  have halpha : 0 < relaxedAngularFactor s := lt_of_lt_of_le hfrac hfrac_le
  have hκ : 0 < boundaryCoefficient s := by
    unfold boundaryCoefficient
    exact div_pos halpha
      (mul_pos
        (mul_pos (by norm_num) s.fragmentTwoMass_pos)
        (sq_pos_of_pos s.propagationSpeed_pos))
  have hsum_lt : boundaryCoefficient s * (x + y) < 1 := by
    have hxy_sum : x + y < 2 * y := by linarith
    have hmul := mul_lt_mul_of_pos_left hxy_sum hκ
    nlinarith
  have hfactor : 0 < 1 - boundaryCoefficient s * (x + y) := by
    linarith
  have hdiff :
      boundaryMargin s y - boundaryMargin s x =
        (y - x) * (1 - boundaryCoefficient s * (x + y)) := by
    unfold boundaryMargin
    ring
  have hdiff_pos : 0 < boundaryMargin s y - boundaryMargin s x := by
    rw [hdiff]
    exact mul_pos (sub_pos.mpr hxy) hfactor
  linarith

/-- Subcritical parameters admit feasible frequencies and a unique relaxed
boundary frequency on the lower physical branch. -/
theorem existsUnique_lowerBoundary (s : Setup) (hs : SubcriticalParameters s) :
    (∃ ν : ℝ, Feasible s ν) ∧
      ∃! ω₀ : ℝ,
        ConservationBoundary s ω₀ ∧ OnLowerPhysicalBranch s ω₀ := by
  let κ := boundaryCoefficient s
  obtain ⟨hfrac, hfrac_le, halpha_le⟩ := relaxedAngularFactor_bounds s
  have halpha : 0 < relaxedAngularFactor s := lt_of_lt_of_le hfrac hfrac_le
  have hκ : 0 < κ := by
    dsimp [κ]
    unfold boundaryCoefficient
    exact div_pos halpha
      (mul_pos
        (mul_pos (by norm_num) s.fragmentTwoMass_pos)
        (sq_pos_of_pos s.propagationSpeed_pos))
  have hs' : 4 * κ * s.energyGap < 1 := by
    simpa [SubcriticalParameters, κ] using hs
  have hm₂ : s.fragmentTwoMass ≠ 0 := ne_of_gt s.fragmentTwoMass_pos
  have hc : s.propagationSpeed ≠ 0 := ne_of_gt s.propagationSpeed_pos
  have hℏ : s.reducedAction ≠ 0 := ne_of_gt s.reducedAction_pos
  have hrelaxed : ∀ w : ℝ,
      relaxedKineticCost s w = κ * photonEnergy s w ^ 2 := by
    intro w
    dsimp [κ]
    unfold relaxedKineticCost boundaryCoefficient photonMomentumMagnitude
    field_simp [hm₂, hc] <;> ring
  have hmargin : ∀ w : ℝ,
      boundaryMargin s (photonEnergy s w) =
        photonEnergy s w - s.energyGap - relaxedKineticCost s w := by
    intro w
    unfold boundaryMargin boundaryCoefficient relaxedKineticCost
      photonMomentumMagnitude
    field_simp [hm₂, hc] <;> ring
  have hboundary_zero : ∀ {w : ℝ}, ConservationBoundary s w →
      boundaryMargin s (photonEnergy s w) = 0 := by
    intro w hw
    rw [hmargin w]
    unfold ConservationBoundary at hw
    linarith
  let D := 1 - 4 * κ * s.energyGap
  have hD_pos : 0 < D := by dsimp [D]; linarith
  have hD_lt_one : D < 1 := by
    dsimp [D]
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hκ)
      s.energyGap_pos
    linarith
  have hsqrt_sq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD_pos.le
  have hsqrt_pos : 0 < Real.sqrt D := Real.sqrt_pos.2 hD_pos
  have hsqrt_lt_one : Real.sqrt D < 1 := by
    nlinarith [Real.sqrt_nonneg D]
  let x₀ := (1 - Real.sqrt D) / (2 * κ)
  have hx₀ : 0 < x₀ :=
    div_pos (sub_pos.mpr hsqrt_lt_one) (mul_pos (by norm_num) hκ)
  have htwice_x₀ : 2 * κ * x₀ = 1 - Real.sqrt D := by
    dsimp [x₀]
    field_simp [ne_of_gt hκ]
  have htwice_x₀_lt : 2 * κ * x₀ < 1 := by
    rw [htwice_x₀]
    linarith
  have hroot : x₀ - s.energyGap - κ * x₀ ^ 2 = 0 := by
    dsimp [x₀]
    field_simp [ne_of_gt hκ]
    nlinarith
  have hB₀ : boundaryMargin s x₀ = 0 := by
    change x₀ - s.energyGap - κ * x₀ ^ 2 = 0
    exact hroot
  let ω₀ := x₀ / s.reducedAction
  have hE₀ : photonEnergy s ω₀ = x₀ := by
    dsimp [ω₀]
    unfold photonEnergy
    field_simp [hℏ]
  have hboundary₀ : ConservationBoundary s ω₀ := by
    unfold ConservationBoundary
    rw [hrelaxed, hE₀]
    linarith
  have hlower₀ : OnLowerPhysicalBranch s ω₀ := by
    refine ⟨?_, ?_⟩
    · rw [hE₀]
      exact hx₀
    · rw [hE₀]
      simpa [κ] using htwice_x₀_lt
  let xᵥ := 1 / (2 * κ)
  have hxᵥ : 0 < xᵥ := div_pos (by norm_num) (mul_pos (by norm_num) hκ)
  have hvertex_value :
      xᵥ - s.energyGap - κ * xᵥ ^ 2 = D / (4 * κ) := by
    dsimp [xᵥ, D]
    field_simp [ne_of_gt hκ]
    ring
  have hBᵥ : 0 < boundaryMargin s xᵥ := by
    change 0 < xᵥ - s.energyGap - κ * xᵥ ^ 2
    rw [hvertex_value]
    exact div_pos hD_pos (mul_pos (by norm_num) hκ)
  let ν := xᵥ / s.reducedAction
  have hν : 0 < ν := div_pos hxᵥ s.reducedAction_pos
  have hEν : photonEnergy s ν = xᵥ := by
    dsimp [ν]
    unfold photonEnergy
    field_simp [hℏ]
  have hfeasibleν : Feasible s ν := by
    by_cases hμ : 0 < Real.cos s.angle
    · apply ((feasible_iff_boundaryMargin s ν).1 hμ).mpr
      refine ⟨hν, ?_⟩
      rw [hEν]
      exact hBᵥ.le
    · have hμ' : Real.cos s.angle ≤ 0 := le_of_not_gt hμ
      apply ((feasible_iff_boundaryMargin s ν).2 hμ').mpr
      refine ⟨hν, ?_⟩
      rw [hEν]
      exact hBᵥ
  refine ⟨⟨ν, hfeasibleν⟩, ω₀, ⟨hboundary₀, hlower₀⟩, ?_⟩
  intro y hy
  let yE := photonEnergy s y
  have hyE_pos : 0 < yE := hy.2.1
  have hyE_vertex : 2 * κ * yE < 1 := by
    simpa [κ, yE] using hy.2.2
  have hBy : boundaryMargin s yE = 0 := by
    dsimp [yE]
    exact hboundary_zero hy.1
  have hyE_le : yE ≤ x₀ := by
    by_contra hnot
    have hlt : x₀ < yE := lt_of_not_ge hnot
    have hmono := boundaryMargin_strictMono_belowVertex s hx₀.le hlt
      (by simpa [κ] using hyE_vertex.le)
    rw [hB₀, hBy] at hmono
    exact (lt_irrefl 0 hmono)
  have hx₀_le : x₀ ≤ yE := by
    by_contra hnot
    have hlt : yE < x₀ := lt_of_not_ge hnot
    have hmono := boundaryMargin_strictMono_belowVertex s hyE_pos.le hlt
      (by simpa [κ] using htwice_x₀_lt.le)
    rw [hBy, hB₀] at hmono
    exact (lt_irrefl 0 hmono)
  have henergy_eq : photonEnergy s y = photonEnergy s ω₀ := by
    dsimp [yE] at hyE_le hx₀_le
    rw [hE₀]
    exact le_antisymm hyE_le hx₀_le
  unfold photonEnergy at henergy_eq
  exact mul_left_cancel₀ hℏ henergy_eq

/-- Every feasible frequency is at least a lower-branch boundary frequency. -/
lemma lowerBoundary_le_feasible
    (s : Setup) {ω₀ ν : ℝ}
    (hboundary : ConservationBoundary s ω₀)
    (hlower : OnLowerPhysicalBranch s ω₀)
    (hfeasible : Feasible s ν) :
    ω₀ ≤ ν := by
  have hm₂ : s.fragmentTwoMass ≠ 0 := ne_of_gt s.fragmentTwoMass_pos
  have hc : s.propagationSpeed ≠ 0 := ne_of_gt s.propagationSpeed_pos
  have hmargin : ∀ w : ℝ,
      boundaryMargin s (photonEnergy s w) =
        photonEnergy s w - s.energyGap - relaxedKineticCost s w := by
    intro w
    unfold boundaryMargin boundaryCoefficient relaxedKineticCost
      photonMomentumMagnitude
    field_simp [hm₂, hc] <;> ring
  have hB₀ : boundaryMargin s (photonEnergy s ω₀) = 0 := by
    rw [hmargin ω₀]
    unfold ConservationBoundary at hboundary
    linarith
  have hν_data :
      0 < ν ∧ 0 ≤ boundaryMargin s (photonEnergy s ν) := by
    by_cases hμ : 0 < Real.cos s.angle
    · exact ((feasible_iff_boundaryMargin s ν).1 hμ).mp hfeasible
    · have hμ' : Real.cos s.angle ≤ 0 := le_of_not_gt hμ
      obtain ⟨hν, hBν⟩ :=
        ((feasible_iff_boundaryMargin s ν).2 hμ').mp hfeasible
      exact ⟨hν, hBν.le⟩
  by_contra hnot
  have hνω : ν < ω₀ := lt_of_not_ge hnot
  have hEν_pos : 0 < photonEnergy s ν := by
    unfold photonEnergy
    exact mul_pos s.reducedAction_pos hν_data.1
  have henergy_lt : photonEnergy s ν < photonEnergy s ω₀ := by
    unfold photonEnergy
    exact mul_lt_mul_of_pos_left hνω s.reducedAction_pos
  have hmono := boundaryMargin_strictMono_belowVertex s hEν_pos.le
    henergy_lt hlower.2.le
  rw [hB₀] at hmono
  linarith [hν_data.2]

/-- Answer-free characterization of the generic feasibility threshold.  It
distinguishes an attained acute-angle threshold from a non-attained right- or
obtuse-angle infimum. -/
def FeasibilityThreshold (s : Setup) (ω₀ : ℝ) : Prop :=
  ConservationBoundary s ω₀ ∧
    OnLowerPhysicalBranch s ω₀ ∧
    (∃ ν : ℝ, Feasible s ν) ∧
    (∀ ν : ℝ, Feasible s ν → ω₀ ≤ ν) ∧
    (0 < Real.cos s.angle → Feasible s ω₀) ∧
    (Real.cos s.angle ≤ 0 →
      ¬Feasible s ω₀ ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ ν : ℝ, Feasible s ν ∧ ω₀ < ν ∧ ν < ω₀ + ε)

/-- Under subcritical parameters there is exactly one generic feasibility
threshold. -/
theorem existsUnique_feasibilityThreshold
    (s : Setup) (hs : SubcriticalParameters s) :
    ∃! ω₀ : ℝ, FeasibilityThreshold s ω₀ := by
  obtain ⟨hfeasible_exists, ω₀, hω₀, hboundary_unique⟩ :=
    existsUnique_lowerBoundary s hs
  let κ := boundaryCoefficient s
  obtain ⟨hfrac, hfrac_le, halpha_le⟩ := relaxedAngularFactor_bounds s
  have halpha : 0 < relaxedAngularFactor s := lt_of_lt_of_le hfrac hfrac_le
  have hκ : 0 < κ := by
    dsimp [κ]
    unfold boundaryCoefficient
    exact div_pos halpha
      (mul_pos
        (mul_pos (by norm_num) s.fragmentTwoMass_pos)
        (sq_pos_of_pos s.propagationSpeed_pos))
  have hm₂ : s.fragmentTwoMass ≠ 0 := ne_of_gt s.fragmentTwoMass_pos
  have hc : s.propagationSpeed ≠ 0 := ne_of_gt s.propagationSpeed_pos
  have hmargin : ∀ w : ℝ,
      boundaryMargin s (photonEnergy s w) =
        photonEnergy s w - s.energyGap - relaxedKineticCost s w := by
    intro w
    unfold boundaryMargin boundaryCoefficient relaxedKineticCost
      photonMomentumMagnitude
    field_simp [hm₂, hc] <;> ring
  have hB₀ : boundaryMargin s (photonEnergy s ω₀) = 0 := by
    rw [hmargin ω₀]
    unfold ConservationBoundary at hω₀
    linarith
  have hω₀_pos : 0 < ω₀ := by
    have henergy_pos := hω₀.2.1
    unfold photonEnergy at henergy_pos
    exact (mul_pos_iff_of_pos_left s.reducedAction_pos).mp henergy_pos
  refine ⟨ω₀, ?_, ?_⟩
  · unfold FeasibilityThreshold
    refine ⟨hω₀.1, hω₀.2, hfeasible_exists, ?_, ?_, ?_⟩
    · intro ν hν
      exact lowerBoundary_le_feasible s hω₀.1 hω₀.2 hν
    · intro hμ
      apply ((feasible_iff_boundaryMargin s ω₀).1 hμ).mpr
      refine ⟨hω₀_pos, ?_⟩
      rw [hB₀]
    · intro hμ
      refine ⟨?_, ?_⟩
      · intro hfeasible₀
        have hdata :=
          ((feasible_iff_boundaryMargin s ω₀).2 hμ).mp hfeasible₀
        rw [hB₀] at hdata
        linarith
      · intro ε hε
        let E₀ := photonEnergy s ω₀
        let σ := 1 - 2 * κ * E₀
        have hσ : 0 < σ := by
          dsimp [σ, E₀]
          simpa [κ] using sub_pos.mpr hω₀.2.2
        let η := min (ε / 2)
          (σ / (4 * κ * s.reducedAction))
        have hden : 0 < 4 * κ * s.reducedAction :=
          mul_pos (mul_pos (by norm_num) hκ) s.reducedAction_pos
        have hη : 0 < η := by
          dsimp [η]
          exact lt_min (div_pos hε (by norm_num)) (div_pos hσ hden)
        have hη_eps_half : η ≤ ε / 2 := by
          dsimp [η]
          exact min_le_left _ _
        have hη_eps : η < ε := by linarith
        have hη_bound : η ≤ σ / (4 * κ * s.reducedAction) := by
          dsimp [η]
          exact min_le_right _ _
        let ν := ω₀ + η
        have hων : ω₀ < ν := by dsimp [ν]; linarith
        have hνωε : ν < ω₀ + ε := by dsimp [ν]; linarith
        have hEν : photonEnergy s ν = E₀ + s.reducedAction * η := by
          dsimp [ν, E₀]
          unfold photonEnergy
          ring
        have henergy_lt : E₀ < photonEnergy s ν := by
          rw [hEν]
          have := mul_pos s.reducedAction_pos hη
          linarith
        have hscale :
            2 * κ * s.reducedAction * η ≤ σ / 2 := by
          calc
            2 * κ * s.reducedAction * η ≤
                2 * κ * s.reducedAction *
                  (σ / (4 * κ * s.reducedAction)) :=
              mul_le_mul_of_nonneg_left hη_bound
                (mul_nonneg (mul_nonneg (by norm_num) hκ.le)
                  s.reducedAction_pos.le)
            _ = σ / 2 := by
              field_simp [ne_of_gt hκ,
                ne_of_gt s.reducedAction_pos] <;> ring
        have hvertexνκ :
            2 * κ * (E₀ + s.reducedAction * η) ≤ 1 := by
          dsimp [σ] at hscale
          nlinarith
        have hvertexν :
            2 * boundaryCoefficient s * photonEnergy s ν ≤ 1 := by
          rw [hEν]
          simpa [κ] using hvertexνκ
        have hBν : 0 < boundaryMargin s (photonEnergy s ν) := by
          have hmono := boundaryMargin_strictMono_belowVertex s
            hω₀.2.1.le henergy_lt hvertexν
          rw [hB₀] at hmono
          exact hmono
        have hν_pos : 0 < ν := lt_trans hω₀_pos hων
        have hfeasibleν : Feasible s ν :=
          ((feasible_iff_boundaryMargin s ν).2 hμ).mpr ⟨hν_pos, hBν⟩
        exact ⟨ν, hfeasibleν, hων, hνωε⟩
  · intro y hy
    apply hboundary_unique y
    exact ⟨hy.1, hy.2.1⟩

end

end Ipho2026Gpt56solBlind.Shared.PhotodissociationKinematics
