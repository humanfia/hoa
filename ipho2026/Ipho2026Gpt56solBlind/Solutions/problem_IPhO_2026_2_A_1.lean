import Mathlib
import Physlib

/-!
# IPhO 2026 Problem 2, part A.1

Answer-blind model of multiple specular reflections inside a half-cylindrical
mirror.  The cylinder is translation-invariant along its axis, so the model
uses the two-dimensional cross-section shown in Figures 2c--2e.  Every real
coordinate below is measured in one common unit of length.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_2_A_1

/-- A point or displacement vector in the mirror's transverse cross-section. -/
structure Vec2 where
  x : ℝ
  y : ℝ

namespace Vec2

def add (u v : Vec2) : Vec2 :=
  ⟨u.x + v.x, u.y + v.y⟩

def sub (u v : Vec2) : Vec2 :=
  ⟨u.x - v.x, u.y - v.y⟩

def smul (a : ℝ) (v : Vec2) : Vec2 :=
  ⟨a * v.x, a * v.y⟩

def dot (u v : Vec2) : ℝ :=
  u.x * v.x + u.y * v.y

def normSq (v : Vec2) : ℝ :=
  dot v v

end Vec2

/-- The semicircular cross-section of the inner surface of the half-cylinder. -/
structure SemicircularMirror where
  radius : ℝ
  radius_pos : 0 < radius

/-- Points strictly inside the optical cavity, above its open diameter. -/
def InsideCavity (mirror : SemicircularMirror) (p : Vec2) : Prop :=
  0 < p.y ∧ Vec2.normSq p < mirror.radius ^ 2

/-- The reflecting part of the boundary.  The two rim points belong to the
open aperture rather than to the reflecting arc. -/
def OnReflectingArc (mirror : SemicircularMirror) (p : Vec2) : Prop :=
  0 < p.y ∧ Vec2.normSq p = mirror.radius ^ 2

/-- The diameter through which a ray enters and eventually leaves the cavity.
Its endpoints are included so that a limiting ray which reaches a rim exits. -/
def OnAperture (mirror : SemicircularMirror) (p : Vec2) : Prop :=
  p.y = 0 ∧ -mirror.radius ≤ p.x ∧ p.x ≤ mirror.radius

/-- A directed ray leg, starting at `position` and travelling in `direction`. -/
structure RayState where
  position : Vec2
  direction : Vec2

def RayState.pointAt (state : RayState) (t : ℝ) : Vec2 :=
  Vec2.add state.position (Vec2.smul t state.direction)

/-- `q` is the first boundary point reached in the forward direction from
`state`.  Requiring every strictly intermediate point to be inside the cavity
encodes unobstructed straight-line propagation and rules out skipping an
earlier collision. -/
def FirstBoundaryHit
    (mirror : SemicircularMirror) (state : RayState) (q : Vec2) : Prop :=
  0 < Vec2.normSq state.direction ∧
    ∃ t : ℝ,
      0 < t ∧
      q = state.pointAt t ∧
      (OnReflectingArc mirror q ∨ OnAperture mirror q) ∧
      ∀ u : ℝ, 0 < u → u < t → InsideCavity mirror (state.pointAt u)

/-- Specular reflection in the tangent line at `hit`.  The radius vector is a
normal to the circular mirror, and subtracting twice the normal projection is
the vector form of equality of incidence and reflection angles. -/
noncomputable def reflectedDirection (hit incoming : Vec2) : Vec2 :=
  Vec2.sub incoming
    (Vec2.smul (2 * Vec2.dot incoming hit / Vec2.normSq hit) hit)

noncomputable def stateAfterReflection (hit incoming : Vec2) : RayState :=
  ⟨hit, reflectedDirection hit incoming⟩

/-- A complete ray starting from `state` exits through the aperture after
exactly the indicated number of reflections from the circular arc. -/
inductive ExitsAfter (mirror : SemicircularMirror) : RayState → ℕ → Prop
  | throughAperture {state : RayState} {exitPoint : Vec2}
      (first : FirstBoundaryHit mirror state exitPoint)
      (atAperture : OnAperture mirror exitPoint) :
      ExitsAfter mirror state 0
  | afterReflection {state : RayState} {hit : Vec2} {remaining : ℕ}
      (first : FirstBoundaryHit mirror state hit)
      (atMirror : OnReflectingArc mirror hit)
      (rest : ExitsAfter mirror
        (stateAfterReflection hit state.direction) remaining) :
      ExitsAfter mirror state (Nat.succ remaining)

/-- The vertical incident ray of Figure 2d at signed transverse coordinate
`x`, launched upward from the aperture. -/
def incidentRay (x : ℝ) : RayState :=
  ⟨⟨x, 0⟩, ⟨0, 1⟩⟩

/-- The incident coordinate lies strictly between the two rims. -/
def IsIncidentCoordinate (mirror : SemicircularMirror) (x : ℝ) : Prop :=
  -mirror.radius < x ∧ x < mirror.radius

/-- Relational definition of the exact reflection count of the ray at `x`. -/
def HasReflectionCount
    (mirror : SemicircularMirror) (x : ℝ) (count : ℕ) : Prop :=
  IsIncidentCoordinate mirror x ∧ ExitsAfter mirror (incidentRay x) count

/-- The ray at `x` leaves the mirror after no more than `bound` reflections. -/
def HasAtMostReflections
    (mirror : SemicircularMirror) (x : ℝ) (bound : ℕ) : Prop :=
  ∃ count : ℕ, count ≤ bound ∧ HasReflectionCount mirror x count

/-- Distances from the optical axis attained by incident rays with at most
`bound` reflections.  Taking `|x|` preserves both symmetric halves of Figure
2e rather than choosing one sign of the transverse coordinate. -/
def AdmissibleDistances
    (mirror : SemicircularMirror) (bound : ℕ) : Set ℝ :=
  {distance | 0 ≤ distance ∧
    ∃ x : ℝ, |x| = distance ∧ HasAtMostReflections mirror x bound}

/-- Answer-free specification of the requested threshold `x_N`: it is
positive, lies inside the rim radius, is attained by a qualifying ray, and is
the supremum of all qualifying distances from the optical axis. -/
def IsThreshold
    (mirror : SemicircularMirror) (bound : ℕ) (threshold : ℝ) : Prop :=
  0 < threshold ∧
    threshold < mirror.radius ∧
    threshold ∈ AdmissibleDistances mirror bound ∧
    IsLUB (AdmissibleDistances mirror bound) threshold

/-- For every positive integer `N`, the mirror geometry and the law of
specular reflection determine one and only one threshold `x_N`.

No closed form for `x_N` is included in the statement. -/
theorem existsUniqueThreshold
    (R : ℝ) (R_pos : 0 < R) (N : ℕ) (N_pos : 0 < N) :
    ∃! xN : ℝ, IsThreshold ⟨R, R_pos⟩ N xN := by
  let mirror : SemicircularMirror := ⟨R, R_pos⟩
  let polar (angle : ℝ) : Vec2 :=
    ⟨R * Real.cos angle, R * Real.sin angle⟩
  let outgoing (angle : ℝ) : Vec2 :=
    ⟨-Real.sin angle, Real.cos angle⟩
  let hitAngle (alpha : ℝ) (j : ℕ) : ℝ :=
    (2 * (j : ℝ) - 1) * alpha
  let midAngle (alpha : ℝ) (j : ℕ) : ℝ :=
    2 * (j : ℝ) * alpha
  let nextAngle (alpha : ℝ) (j : ℕ) : ℝ :=
    (2 * (j : ℝ) + 1) * alpha
  let bounce (alpha : ℝ) (j : ℕ) : RayState :=
    ⟨polar (hitAngle alpha j), outgoing (midAngle alpha j)⟩
  change ∃! xN : ℝ, IsThreshold mirror N xN

  have vec2_ext (u v : Vec2) (hx : u.x = v.x) (hy : u.y = v.y) : u = v := by
    cases u
    cases v
    cases hx
    cases hy
    rfl

  have ray_state_ext (u v : RayState)
      (hp : u.position = v.position) (hd : u.direction = v.direction) : u = v := by
    cases u
    cases v
    cases hp
    cases hd
    rfl

  have cancel_radius (u v : ℝ) :
      (2 * (R * u) / R ^ 2) * (R * v) = 2 * u * v := by
    rw [div_mul_eq_mul_div]
    have hnumerator : 2 * (R * u) * (R * v) = R ^ 2 * (2 * u * v) := by
      ring
    rw [hnumerator, mul_div_cancel_left₀ _
      (pow_ne_zero 2 (ne_of_gt R_pos))]

  have hitAngle_succ (alpha : ℝ) (j : ℕ) :
      hitAngle alpha (j + 1) = nextAngle alpha j := by
    dsimp [hitAngle, nextAngle]
    push_cast
    ring

  have boundary_not_inside (q : Vec2) :
      (OnReflectingArc mirror q ∨ OnAperture mirror q) →
        ¬ InsideCavity mirror q := by
    rintro (harc | hap) hin
    · exact (ne_of_lt hin.2) harc.2
    · exact (ne_of_gt hin.1) hap.1

  have first_hit_unique (state : RayState) (q₁ q₂ : Vec2)
      (h₁ : FirstBoundaryHit mirror state q₁)
      (h₂ : FirstBoundaryHit mirror state q₂) : q₁ = q₂ := by
    rcases h₁ with ⟨_, t₁, ht₁, hq₁, hb₁, hi₁⟩
    rcases h₂ with ⟨_, t₂, ht₂, hq₂, hb₂, hi₂⟩
    rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
    · have hinside : InsideCavity mirror q₁ := by
        rw [hq₁]
        exact hi₂ t₁ ht₁ hlt
      exact False.elim (boundary_not_inside q₁ hb₁ hinside)
    · rw [hq₁, hq₂, heq]
    · have hinside : InsideCavity mirror q₂ := by
        rw [hq₂]
        exact hi₁ t₂ ht₂ hgt
      exact False.elim (boundary_not_inside q₂ hb₂ hinside)

  have arc_aperture_disjoint (q : Vec2)
      (harc : OnReflectingArc mirror q) (hap : OnAperture mirror q) : False := by
    exact (ne_of_gt harc.1) hap.1

  have bounce_next_arc :
      ∀ (alpha : ℝ) (j : ℕ),
        1 ≤ j →
        0 < alpha →
        alpha ≤ Real.pi / 2 →
        hitAngle alpha j < Real.pi →
        nextAngle alpha j < Real.pi →
        let q := polar (nextAngle alpha j)
        FirstBoundaryHit mirror (bounce alpha j) q ∧
          OnReflectingArc mirror q ∧
          stateAfterReflection q (bounce alpha j).direction = bounce alpha (j + 1) := by
    intro alpha j hj halpha halpha_half hhit hnext
    dsimp only
    let A : ℝ := hitAngle alpha j
    let B : ℝ := midAngle alpha j
    let C : ℝ := nextAngle alpha j
    let travel : ℝ := 2 * R * Real.sin alpha
    have hj_real : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hA : A = B - alpha := by
      dsimp [A, B, hitAngle, midAngle]
      ring
    have hC : C = B + alpha := by
      dsimp [C, B, nextAngle, midAngle]
      ring
    have hA_pos : 0 < A := by
      dsimp [A, hitAngle]
      have hcoefficient : 0 < 2 * (j : ℝ) - 1 := by
        linarith only [hj_real]
      exact mul_pos hcoefficient halpha
    have hC_pos : 0 < C := by
      dsimp [C, nextAngle]
      have hcoefficient : 0 < 2 * (j : ℝ) + 1 := by
        linarith only [hj_real]
      exact mul_pos hcoefficient halpha
    have hA_lt : A < Real.pi := by simpa [A] using hhit
    have hC_lt : C < Real.pi := by simpa [C] using hnext
    have halpha_pi : alpha < Real.pi := by
      linarith only [halpha_half, Real.pi_pos]
    have hsina_pos : 0 < Real.sin alpha :=
      Real.sin_pos_of_pos_of_lt_pi halpha halpha_pi
    have htravel_pos : 0 < travel := by
      dsimp [travel]
      exact mul_pos (mul_pos (by norm_num) R_pos) hsina_pos
    have hpoint : polar C = (bounce alpha j).pointAt travel := by
      apply vec2_ext
      · change R * Real.cos C =
          R * Real.cos A + travel * (-Real.sin B)
        rw [hA, hC]
        dsimp [travel]
        rw [Real.cos_add, Real.cos_sub]
        ring
      · change R * Real.sin C =
          R * Real.sin A + travel * Real.cos B
        rw [hA, hC]
        dsimp [travel]
        rw [Real.sin_add, Real.sin_sub]
        ring
    have hcircleA :
        (R * Real.cos A) ^ 2 + (R * Real.sin A) ^ 2 = R ^ 2 := by
      calc
        (R * Real.cos A) ^ 2 + (R * Real.sin A) ^ 2 =
            R ^ 2 * (Real.sin A ^ 2 + Real.cos A ^ 2) := by ring
        _ = R ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
    have hcircleC :
        (R * Real.cos C) ^ 2 + (R * Real.sin C) ^ 2 = R ^ 2 := by
      calc
        (R * Real.cos C) ^ 2 + (R * Real.sin C) ^ 2 =
            R ^ 2 * (Real.sin C ^ 2 + Real.cos C ^ 2) := by ring
        _ = R ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
    have hdir_unit :
        (-Real.sin B) ^ 2 + (Real.cos B) ^ 2 = 1 := by
      calc
        (-Real.sin B) ^ 2 + (Real.cos B) ^ 2 =
            Real.sin B ^ 2 + Real.cos B ^ 2 := by ring
        _ = 1 := Real.sin_sq_add_cos_sq B
    have hdot_start :
        (R * Real.cos A) * (-Real.sin B) +
            (R * Real.sin A) * Real.cos B = -R * Real.sin alpha := by
      calc
        (R * Real.cos A) * (-Real.sin B) +
              (R * Real.sin A) * Real.cos B =
            R * (Real.sin A * Real.cos B - Real.cos A * Real.sin B) := by ring
        _ = R * Real.sin (A - B) := by rw [Real.sin_sub]
        _ = -R * Real.sin alpha := by rw [hA]; simp
    have hq_arc : OnReflectingArc mirror (polar C) := by
      constructor
      · change 0 < R * Real.sin C
        exact mul_pos R_pos (Real.sin_pos_of_pos_of_lt_pi hC_pos hC_lt)
      · change
          (R * Real.cos C) * (R * Real.cos C) +
              (R * Real.sin C) * (R * Real.sin C) = R ^ 2
        simpa only [pow_two] using hcircleC
    have hfirst : FirstBoundaryHit mirror (bounce alpha j) (polar C) := by
      refine ⟨?_, travel, htravel_pos, hpoint, Or.inl hq_arc, ?_⟩
      · change 0 <
          (-Real.sin B) * (-Real.sin B) + Real.cos B * Real.cos B
        have hdir_one :
            (-Real.sin B) * (-Real.sin B) + Real.cos B * Real.cos B = 1 := by
          simpa only [pow_two] using hdir_unit
        rw [hdir_one]
        norm_num
      · intro u hu hut
        have hA_y : 0 < R * Real.sin A :=
          mul_pos R_pos (Real.sin_pos_of_pos_of_lt_pi hA_pos hA_lt)
        have hC_y : 0 < R * Real.sin C :=
          mul_pos R_pos (Real.sin_pos_of_pos_of_lt_pi hC_pos hC_lt)
        have hy_at_travel :
            R * Real.sin A + travel * Real.cos B = R * Real.sin C := by
          have := congrArg Vec2.y hpoint
          exact this.symm
        have hy_combo_pos :
            0 < (travel - u) * (R * Real.sin A) + u * (R * Real.sin C) :=
          add_pos (mul_pos (sub_pos.mpr hut) hA_y) (mul_pos hu hC_y)
        have hy_pos :
            0 < R * Real.sin A + u * Real.cos B := by
          have hproduct_pos :
              0 < travel * (R * Real.sin A + u * Real.cos B) := by
            calc
              0 < (travel - u) * (R * Real.sin A) + u * (R * Real.sin C) :=
                hy_combo_pos
              _ = travel * (R * Real.sin A + u * Real.cos B) := by
                rw [← hy_at_travel]
                ring
          rcases (mul_pos_iff.mp hproduct_pos) with hboth | hboth
          · exact hboth.2
          · exact False.elim ((not_lt_of_ge htravel_pos.le) hboth.1)
        have hnorm :
            Vec2.normSq ((bounce alpha j).pointAt u) =
              R ^ 2 + u * (u - travel) := by
          change
            (R * Real.cos A + u * (-Real.sin B)) *
                  (R * Real.cos A + u * (-Real.sin B)) +
                (R * Real.sin A + u * Real.cos B) *
                  (R * Real.sin A + u * Real.cos B) =
              R ^ 2 + u * (u - travel)
          calc
            (R * Real.cos A + u * (-Real.sin B)) *
                    (R * Real.cos A + u * (-Real.sin B)) +
                  (R * Real.sin A + u * Real.cos B) *
                    (R * Real.sin A + u * Real.cos B) =
                ((R * Real.cos A) ^ 2 + (R * Real.sin A) ^ 2) +
                  2 * u *
                    ((R * Real.cos A) * (-Real.sin B) +
                      (R * Real.sin A) * Real.cos B) +
                  u ^ 2 * ((-Real.sin B) ^ 2 + (Real.cos B) ^ 2) := by ring
            _ = R ^ 2 + u * (u - travel) := by
              rw [hcircleA, hdot_start, hdir_unit]
              dsimp [travel]
              ring
        constructor
        · exact hy_pos
        · rw [hnorm]
          have hneg := mul_neg_of_pos_of_neg hu (sub_neg.mpr hut)
          linarith only [hneg]
    have hdot_hit :
        Vec2.dot (outgoing B) (polar C) = R * Real.sin alpha := by
      change
        (-Real.sin B) * (R * Real.cos C) +
            Real.cos B * (R * Real.sin C) = R * Real.sin alpha
      calc
        (-Real.sin B) * (R * Real.cos C) +
              Real.cos B * (R * Real.sin C) =
            R * (Real.sin C * Real.cos B - Real.cos C * Real.sin B) := by ring
        _ = R * Real.sin (C - B) := by rw [Real.sin_sub]
        _ = R * Real.sin alpha := by rw [hC]; ring_nf
    have hnorm_hit : Vec2.normSq (polar C) = R ^ 2 := by
      change
        (R * Real.cos C) * (R * Real.cos C) +
            (R * Real.sin C) * (R * Real.sin C) = R ^ 2
      simpa [pow_two] using hcircleC
    have hreflection :
        reflectedDirection (polar C) (outgoing B) = outgoing (B + 2 * alpha) := by
      apply vec2_ext
      · change
          -Real.sin B -
                (2 * Vec2.dot (outgoing B) (polar C) /
                    Vec2.normSq (polar C)) * (R * Real.cos C) =
            -Real.sin (B + 2 * alpha)
        rw [hdot_hit, hnorm_hit, hC]
        rw [cancel_radius]
        rw [Real.cos_add, Real.sin_add, Real.sin_two_mul,
          Real.cos_two_mul_eq_one_sub]
        ring
      · change
          Real.cos B -
                (2 * Vec2.dot (outgoing B) (polar C) /
                    Vec2.normSq (polar C)) * (R * Real.sin C) =
            Real.cos (B + 2 * alpha)
        rw [hdot_hit, hnorm_hit, hC]
        rw [cancel_radius]
        rw [Real.sin_add, Real.cos_add, Real.sin_two_mul,
          Real.cos_two_mul_eq_one_sub]
        ring
    have hhit_succ : hitAngle alpha (j + 1) = C := by
      dsimp [hitAngle, C, nextAngle]
      push_cast
      ring
    have hmid_succ : midAngle alpha (j + 1) = B + 2 * alpha := by
      dsimp [midAngle, B]
      push_cast
      ring
    have hstate :
        stateAfterReflection (polar C) (bounce alpha j).direction =
          bounce alpha (j + 1) := by
      apply ray_state_ext
      · change polar C = polar (hitAngle alpha (j + 1))
        rw [hhit_succ]
      · change reflectedDirection (polar C) (outgoing B) =
          outgoing (midAngle alpha (j + 1))
        rw [hmid_succ, hreflection]
    simpa [C] using And.intro hfirst (And.intro hq_arc hstate)

  have bounce_next_exit :
      ∀ (alpha : ℝ) (j : ℕ),
        1 ≤ j →
        0 < alpha →
        alpha ≤ Real.pi / 2 →
        hitAngle alpha j < Real.pi →
        Real.pi ≤ nextAngle alpha j →
        ∃ q : Vec2,
          FirstBoundaryHit mirror (bounce alpha j) q ∧
            OnAperture mirror q := by
    intro alpha j hj halpha halpha_half hhit hnext
    let A : ℝ := hitAngle alpha j
    let B : ℝ := midAngle alpha j
    let C : ℝ := nextAngle alpha j
    let travel : ℝ := 2 * R * Real.sin alpha
    have hj_real : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hA : A = B - alpha := by
      dsimp [A, B, hitAngle, midAngle]
      ring
    have hC : C = B + alpha := by
      dsimp [C, B, nextAngle, midAngle]
      ring
    have hA_pos : 0 < A := by
      dsimp [A, hitAngle]
      have hcoefficient : 0 < 2 * (j : ℝ) - 1 := by
        linarith only [hj_real]
      exact mul_pos hcoefficient halpha
    have hA_lt : A < Real.pi := by simpa [A] using hhit
    have hC_ge : Real.pi ≤ C := by simpa [C] using hnext
    have halpha_pi : alpha < Real.pi := by
      linarith only [halpha_half, Real.pi_pos]
    have hsina_pos : 0 < Real.sin alpha :=
      Real.sin_pos_of_pos_of_lt_pi halpha halpha_pi
    have htravel_pos : 0 < travel := by
      dsimp [travel]
      exact mul_pos (mul_pos (by norm_num) R_pos) hsina_pos
    have hB_ge_two_alpha : 2 * alpha ≤ B := by
      dsimp [B, midAngle]
      nlinarith only [hj_real, halpha]
    have hB_half_pi : Real.pi / 2 < B := by
      rw [hC] at hC_ge
      nlinarith only [hC_ge, hB_ge_two_alpha, halpha, halpha_half, Real.pi_pos]
    have hB_three_half_pi : B < Real.pi + Real.pi / 2 := by
      rw [hA] at hA_lt
      linarith only [hA_lt, halpha_half]
    have hcosB_neg : Real.cos B < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt hB_half_pi hB_three_half_pi
    have hC_lt_two_pi : C < 2 * Real.pi := by
      rw [hA] at hA_lt
      rw [hC]
      linarith only [hA_lt, halpha_half]
    have hsinC_nonpos : Real.sin C ≤ 0 := by
      have hdelta : 0 ≤ Real.sin (C - Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith only [hC_ge]) (by linarith only [hC_lt_two_pi])
      calc
        Real.sin C = Real.sin ((C - Real.pi) + Real.pi) := by
          congr 1
          ring
        _ = -Real.sin (C - Real.pi) := Real.sin_add_pi _
        _ ≤ 0 := neg_nonpos.mpr hdelta
    have hpoint : polar C = (bounce alpha j).pointAt travel := by
      apply vec2_ext
      · change R * Real.cos C =
          R * Real.cos A + travel * (-Real.sin B)
        rw [hA, hC]
        dsimp [travel]
        rw [Real.cos_add, Real.cos_sub]
        ring
      · change R * Real.sin C =
          R * Real.sin A + travel * Real.cos B
        rw [hA, hC]
        dsimp [travel]
        rw [Real.sin_add, Real.sin_sub]
        ring
    have hcircleA :
        (R * Real.cos A) ^ 2 + (R * Real.sin A) ^ 2 = R ^ 2 := by
      calc
        (R * Real.cos A) ^ 2 + (R * Real.sin A) ^ 2 =
            R ^ 2 * (Real.sin A ^ 2 + Real.cos A ^ 2) := by ring
        _ = R ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
    have hdir_unit :
        (-Real.sin B) ^ 2 + (Real.cos B) ^ 2 = 1 := by
      calc
        (-Real.sin B) ^ 2 + (Real.cos B) ^ 2 =
            Real.sin B ^ 2 + Real.cos B ^ 2 := by ring
        _ = 1 := Real.sin_sq_add_cos_sq B
    have hdot_start :
        (R * Real.cos A) * (-Real.sin B) +
            (R * Real.sin A) * Real.cos B = -R * Real.sin alpha := by
      calc
        (R * Real.cos A) * (-Real.sin B) +
              (R * Real.sin A) * Real.cos B =
            R * (Real.sin A * Real.cos B - Real.cos A * Real.sin B) := by ring
        _ = R * Real.sin (A - B) := by rw [Real.sin_sub]
        _ = -R * Real.sin alpha := by rw [hA]; simp
    have hy_at_travel :
        R * Real.sin A + travel * Real.cos B = R * Real.sin C := by
      have := congrArg Vec2.y hpoint
      exact this.symm
    let exitTime : ℝ := -(R * Real.sin A) / Real.cos B
    have hA_y : 0 < R * Real.sin A :=
      mul_pos R_pos (Real.sin_pos_of_pos_of_lt_pi hA_pos hA_lt)
    have hexit_pos : 0 < exitTime := by
      dsimp [exitTime]
      exact div_pos_of_neg_of_neg (neg_lt_zero.mpr hA_y) hcosB_neg
    have hy_at_exit :
        R * Real.sin A + exitTime * Real.cos B = 0 := by
      dsimp [exitTime]
      rw [div_mul_cancel₀ _ (ne_of_lt hcosB_neg)]
      ring
    have hexit_le_travel : exitTime ≤ travel := by
      by_contra hle
      have hlt : travel < exitTime := lt_of_not_ge hle
      have hmul : exitTime * Real.cos B < travel * Real.cos B :=
        mul_lt_mul_of_neg_right hlt hcosB_neg
      have hRsinC_nonpos : R * Real.sin C ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos R_pos.le hsinC_nonpos
      linarith only [hmul, hy_at_exit, hy_at_travel, hRsinC_nonpos]
    let q : Vec2 := (bounce alpha j).pointAt exitTime
    have hq_y : q.y = 0 := by
      change R * Real.sin A + exitTime * Real.cos B = 0
      exact hy_at_exit
    have hnorm (u : ℝ) :
        Vec2.normSq ((bounce alpha j).pointAt u) =
          R ^ 2 + u * (u - travel) := by
      change
        (R * Real.cos A + u * (-Real.sin B)) *
              (R * Real.cos A + u * (-Real.sin B)) +
            (R * Real.sin A + u * Real.cos B) *
              (R * Real.sin A + u * Real.cos B) =
          R ^ 2 + u * (u - travel)
      calc
        (R * Real.cos A + u * (-Real.sin B)) *
                (R * Real.cos A + u * (-Real.sin B)) +
              (R * Real.sin A + u * Real.cos B) *
                (R * Real.sin A + u * Real.cos B) =
            ((R * Real.cos A) ^ 2 + (R * Real.sin A) ^ 2) +
              2 * u *
                ((R * Real.cos A) * (-Real.sin B) +
                  (R * Real.sin A) * Real.cos B) +
              u ^ 2 * ((-Real.sin B) ^ 2 + (Real.cos B) ^ 2) := by ring
        _ = R ^ 2 + u * (u - travel) := by
          rw [hcircleA, hdot_start, hdir_unit]
          dsimp [travel]
          ring
    have hq_norm_le : Vec2.normSq q ≤ R ^ 2 := by
      change Vec2.normSq ((bounce alpha j).pointAt exitTime) ≤ R ^ 2
      rw [hnorm]
      have hprod : exitTime * (exitTime - travel) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hexit_pos.le
          (sub_nonpos.mpr hexit_le_travel)
      linarith only [hprod]
    have hq_x_sq : q.x ^ 2 ≤ R ^ 2 := by
      have hq_norm_le' := hq_norm_le
      change q.x * q.x + q.y * q.y ≤ R ^ 2 at hq_norm_le'
      rw [hq_y] at hq_norm_le'
      simpa [pow_two] using hq_norm_le'
    have hq_abs : |q.x| ≤ R :=
      abs_le_of_sq_le_sq hq_x_sq R_pos.le
    have hq_aperture : OnAperture mirror q := by
      exact ⟨hq_y, (abs_le.mp hq_abs).1, (abs_le.mp hq_abs).2⟩
    have hfirst : FirstBoundaryHit mirror (bounce alpha j) q := by
      refine ⟨?_, exitTime, hexit_pos, rfl, Or.inr hq_aperture, ?_⟩
      · change 0 <
          (-Real.sin B) * (-Real.sin B) + Real.cos B * Real.cos B
        have hdir_one :
            (-Real.sin B) * (-Real.sin B) + Real.cos B * Real.cos B = 1 := by
          simpa only [pow_two] using hdir_unit
        rw [hdir_one]
        norm_num
      · intro u hu hut
        have hu_travel : u < travel := lt_of_lt_of_le hut hexit_le_travel
        constructor
        · change 0 < R * Real.sin A + u * Real.cos B
          have hmul : exitTime * Real.cos B < u * Real.cos B :=
            mul_lt_mul_of_neg_right hut hcosB_neg
          linarith only [hmul, hy_at_exit]
        · rw [hnorm]
          have hneg := mul_neg_of_pos_of_neg hu (sub_neg.mpr hu_travel)
          linarith only [hneg]
    exact ⟨q, hfirst, hq_aperture⟩

  have bounce_exits_iff :
      ∀ (alpha : ℝ) (j n : ℕ),
        1 ≤ j →
        0 < alpha →
        alpha ≤ Real.pi / 2 →
        hitAngle alpha j < Real.pi →
        (ExitsAfter mirror (bounce alpha j) n ↔
          hitAngle alpha (j + n) < Real.pi ∧
            Real.pi ≤ nextAngle alpha (j + n)) := by
    intro alpha j n
    induction n generalizing j with
    | zero =>
        intro hj halpha halpha_half hcurrent
        constructor
        · intro htrace
          cases htrace with
          | throughAperture first atAperture =>
              refine ⟨by simpa using hcurrent, ?_⟩
              by_contra hupper
              have hnext_lt : nextAngle alpha j < Real.pi :=
                lt_of_not_ge hupper
              have hcanonical :=
                bounce_next_arc alpha j hj halpha halpha_half hcurrent hnext_lt
              have hsame := first_hit_unique _ _ _ first hcanonical.1
              rw [hsame] at atAperture
              exact arc_aperture_disjoint _ hcanonical.2.1 atAperture
        · rintro ⟨_, hupper⟩
          rcases bounce_next_exit alpha j hj halpha halpha_half hcurrent hupper with
            ⟨q, hfirst, haperture⟩
          exact ExitsAfter.throughAperture hfirst haperture
    | succ n ih =>
        intro hj halpha halpha_half hcurrent
        constructor
        · intro htrace
          cases htrace with
          | afterReflection first atMirror rest =>
              have hnext_lt : nextAngle alpha j < Real.pi := by
                by_contra hnext_not_lt
                have hnext_ge : Real.pi ≤ nextAngle alpha j :=
                  le_of_not_gt hnext_not_lt
                rcases bounce_next_exit alpha j hj halpha halpha_half hcurrent hnext_ge with
                  ⟨q, hq_first, hq_aperture⟩
                have hsame := first_hit_unique _ _ _ first hq_first
                rw [hsame] at atMirror
                exact arc_aperture_disjoint q atMirror hq_aperture
              have hcanonical :=
                bounce_next_arc alpha j hj halpha halpha_half hcurrent hnext_lt
              have hsame := first_hit_unique _ _ _ first hcanonical.1
              rw [hsame] at rest
              rw [hcanonical.2.2] at rest
              have hnext_hit : hitAngle alpha (j + 1) < Real.pi := by
                rw [hitAngle_succ]
                exact hnext_lt
              have htail :=
                (ih (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
                  halpha halpha_half hnext_hit).1 rest
              have hindex : j + Nat.succ n = (j + 1) + n :=
                (Nat.add_succ j n).trans (Nat.succ_add j n).symm
              rw [hindex]
              exact htail
        · intro hfinal
          have hn_real : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          have hnext_le_final :
              nextAngle alpha j ≤ hitAngle alpha (j + Nat.succ n) := by
            dsimp [nextAngle, hitAngle]
            push_cast
            nlinarith only [hn_real, halpha]
          have hnext_lt : nextAngle alpha j < Real.pi :=
            lt_of_le_of_lt hnext_le_final hfinal.1
          have hcanonical :=
            bounce_next_arc alpha j hj halpha halpha_half hcurrent hnext_lt
          have hindex : j + Nat.succ n = (j + 1) + n :=
            (Nat.add_succ j n).trans (Nat.succ_add j n).symm
          have htail_final :
              hitAngle alpha ((j + 1) + n) < Real.pi ∧
                Real.pi ≤ nextAngle alpha ((j + 1) + n) := by
            rw [← hindex]
            exact hfinal
          have hnext_hit : hitAngle alpha (j + 1) < Real.pi := by
            rw [hitAngle_succ]
            exact hnext_lt
          have htail :=
            (ih (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
              halpha halpha_half hnext_hit).2 htail_final
          apply ExitsAfter.afterReflection hcanonical.1 hcanonical.2.1
          rw [hcanonical.2.2]
          exact htail

  have incident_exits_iff :
      ∀ (alpha : ℝ) (n : ℕ),
        0 < alpha →
        alpha ≤ Real.pi / 2 →
        (ExitsAfter mirror (incidentRay (R * Real.cos alpha)) n ↔
          hitAngle alpha n < Real.pi ∧
            Real.pi ≤ nextAngle alpha n) := by
    intro alpha n halpha halpha_half
    have halpha_pi : alpha < Real.pi := by
      linarith only [halpha_half, Real.pi_pos]
    have hsina_pos : 0 < Real.sin alpha :=
      Real.sin_pos_of_pos_of_lt_pi halpha halpha_pi
    let firstTime : ℝ := R * Real.sin alpha
    have hfirst_time_pos : 0 < firstTime := by
      dsimp [firstTime]
      exact mul_pos R_pos hsina_pos
    have hcircle :
        (R * Real.cos alpha) ^ 2 + (R * Real.sin alpha) ^ 2 = R ^ 2 := by
      calc
        (R * Real.cos alpha) ^ 2 + (R * Real.sin alpha) ^ 2 =
            R ^ 2 * (Real.sin alpha ^ 2 + Real.cos alpha ^ 2) := by ring
        _ = R ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
    have hfirst_point :
        polar alpha =
          (incidentRay (R * Real.cos alpha)).pointAt firstTime := by
      apply vec2_ext
      · change R * Real.cos alpha = R * Real.cos alpha + firstTime * 0
        ring
      · change R * Real.sin alpha = 0 + firstTime * 1
        dsimp [firstTime]
        ring
    have hfirst_arc : OnReflectingArc mirror (polar alpha) := by
      constructor
      · change 0 < R * Real.sin alpha
        exact mul_pos R_pos hsina_pos
      · change
          (R * Real.cos alpha) * (R * Real.cos alpha) +
              (R * Real.sin alpha) * (R * Real.sin alpha) = R ^ 2
        simpa only [pow_two] using hcircle
    have hfirst_hit :
        FirstBoundaryHit mirror (incidentRay (R * Real.cos alpha)) (polar alpha) := by
      refine ⟨?_, firstTime, hfirst_time_pos, hfirst_point,
        Or.inl hfirst_arc, ?_⟩
      · change 0 < (0 : ℝ) * 0 + 1 * 1
        norm_num
      intro u hu hut
      have hsum_pos : 0 < firstTime + u := add_pos hfirst_time_pos hu
      have hsquares : u ^ 2 < firstTime ^ 2 := by
        nlinarith only [mul_pos (sub_pos.mpr hut) hsum_pos]
      constructor
      · dsimp [incidentRay, RayState.pointAt, Vec2.add, Vec2.smul]
        simpa using hu
      · dsimp [mirror, incidentRay, RayState.pointAt, Vec2.add, Vec2.smul,
          Vec2.normSq, Vec2.dot]
        dsimp [firstTime] at hsquares
        nlinarith only [hcircle, hsquares]
    have hdot_first :
        Vec2.dot ⟨0, 1⟩ (polar alpha) = R * Real.sin alpha := by
      dsimp [polar, Vec2.dot]
      ring
    have hnorm_first : Vec2.normSq (polar alpha) = R ^ 2 := by
      change
        (R * Real.cos alpha) * (R * Real.cos alpha) +
            (R * Real.sin alpha) * (R * Real.sin alpha) = R ^ 2
      simpa [pow_two] using hcircle
    have hreflected_first :
        reflectedDirection (polar alpha) ⟨0, 1⟩ = outgoing (2 * alpha) := by
      apply vec2_ext
      · change
          0 -
                (2 * Vec2.dot ⟨0, 1⟩ (polar alpha) /
                    Vec2.normSq (polar alpha)) * (R * Real.cos alpha) =
            -Real.sin (2 * alpha)
        rw [hdot_first, hnorm_first]
        rw [cancel_radius]
        rw [Real.sin_two_mul]
        ring
      · change
          1 -
                (2 * Vec2.dot ⟨0, 1⟩ (polar alpha) /
                    Vec2.normSq (polar alpha)) * (R * Real.sin alpha) =
            Real.cos (2 * alpha)
        rw [hdot_first, hnorm_first]
        rw [cancel_radius]
        rw [Real.cos_two_mul_eq_one_sub]
        ring
    have hhit_one : hitAngle alpha 1 = alpha := by
      dsimp [hitAngle]
      ring
    have hmid_one : midAngle alpha 1 = 2 * alpha := by
      dsimp [midAngle]
      ring
    have hafter_first :
        stateAfterReflection (polar alpha) ⟨0, 1⟩ = bounce alpha 1 := by
      apply ray_state_ext
      · change polar alpha = polar (hitAngle alpha 1)
        rw [hhit_one]
      · change reflectedDirection (polar alpha) ⟨0, 1⟩ =
          outgoing (midAngle alpha 1)
        rw [hmid_one, hreflected_first]
    cases n with
    | zero =>
        constructor
        · intro htrace
          cases htrace with
          | throughAperture first atAperture =>
              have hsame := first_hit_unique _ _ _ first hfirst_hit
              rw [hsame] at atAperture
              exact False.elim (arc_aperture_disjoint _ hfirst_arc atAperture)
        · rintro ⟨_, hupper⟩
          exfalso
          have hpi_le_alpha : Real.pi ≤ alpha := by
            simpa [nextAngle] using hupper
          exact (not_le_of_gt halpha_pi) hpi_le_alpha
    | succ n =>
        have hcurrent : hitAngle alpha 1 < Real.pi := by
          rw [hhit_one]
          exact halpha_pi
        constructor
        · intro htrace
          cases htrace with
          | afterReflection first atMirror rest =>
              have hsame := first_hit_unique _ _ _ first hfirst_hit
              rw [hsame] at rest
              change ExitsAfter mirror
                (stateAfterReflection (polar alpha) ⟨0, 1⟩) n at rest
              rw [hafter_first] at rest
              have htail :=
                (bounce_exits_iff alpha 1 n (le_refl 1)
                  halpha halpha_half hcurrent).1 rest
              simpa [Nat.add_comm] using htail
        · intro hfinal
          have htail : ExitsAfter mirror (bounce alpha 1) n :=
            (bounce_exits_iff alpha 1 n (le_refl 1)
              halpha halpha_half hcurrent).2
              (by simpa [Nat.add_comm] using hfinal)
          apply ExitsAfter.afterReflection hfirst_hit hfirst_arc
          change ExitsAfter mirror
            (stateAfterReflection (polar alpha) ⟨0, 1⟩) n
          rw [hafter_first]
          exact htail

  have exits_abs :
      ∀ (x : ℝ) (n : ℕ),
        ExitsAfter mirror (incidentRay x) n →
          ExitsAfter mirror (incidentRay |x|) n := by
    let flipVec (v : Vec2) : Vec2 := ⟨-v.x, v.y⟩
    let flipState (state : RayState) : RayState :=
      ⟨flipVec state.position, flipVec state.direction⟩
    have flip_norm (v : Vec2) :
        Vec2.normSq (flipVec v) = Vec2.normSq v := by
      change (-v.x) * (-v.x) + v.y * v.y = v.x * v.x + v.y * v.y
      ring
    have flip_point (state : RayState) (t : ℝ) :
        (flipState state).pointAt t = flipVec (state.pointAt t) := by
      apply vec2_ext
      · dsimp only [flipState, flipVec, RayState.pointAt, Vec2.add, Vec2.smul]
        ring
      · dsimp only [flipState, flipVec, RayState.pointAt, Vec2.add, Vec2.smul]
    have flip_inside (p : Vec2) (hp : InsideCavity mirror p) :
        InsideCavity mirror (flipVec p) := by
      exact ⟨hp.1, by rw [flip_norm]; exact hp.2⟩
    have flip_arc (p : Vec2) (hp : OnReflectingArc mirror p) :
        OnReflectingArc mirror (flipVec p) := by
      exact ⟨hp.1, by rw [flip_norm]; exact hp.2⟩
    have flip_aperture (p : Vec2) (hp : OnAperture mirror p) :
        OnAperture mirror (flipVec p) := by
      refine ⟨hp.1, ?_, ?_⟩
      · change -mirror.radius ≤ -p.x
        exact neg_le_neg hp.2.2
      · change -p.x ≤ mirror.radius
        simpa only [neg_neg] using (neg_le_neg hp.2.1)
    have flip_reflected (hit incoming : Vec2) :
        reflectedDirection (flipVec hit) (flipVec incoming) =
          flipVec (reflectedDirection hit incoming) := by
      apply vec2_ext <;>
        dsimp only [reflectedDirection, flipVec, Vec2.sub, Vec2.smul,
          Vec2.dot, Vec2.normSq] <;>
        ring
    have flip_after (hit incoming : Vec2) :
        flipState (stateAfterReflection hit incoming) =
          stateAfterReflection (flipVec hit) (flipVec incoming) := by
      apply ray_state_ext
      · rfl
      · exact (flip_reflected hit incoming).symm
    have flip_first (state : RayState) (q : Vec2)
        (hfirst : FirstBoundaryHit mirror state q) :
        FirstBoundaryHit mirror (flipState state) (flipVec q) := by
      rcases hfirst with ⟨hdirection, t, ht, hq, hboundary, hinterior⟩
      refine ⟨?_, t, ht, ?_, ?_, ?_⟩
      · rw [flip_norm]
        exact hdirection
      · calc
          flipVec q = flipVec (state.pointAt t) := congrArg flipVec hq
          _ = (flipState state).pointAt t := (flip_point state t).symm
      · rcases hboundary with harc | haperture
        · exact Or.inl (flip_arc q harc)
        · exact Or.inr (flip_aperture q haperture)
      · intro u hu hut
        rw [flip_point]
        exact flip_inside _ (hinterior u hu hut)
    have flip_exits (state : RayState) (n : ℕ)
        (htrace : ExitsAfter mirror state n) :
        ExitsAfter mirror (flipState state) n := by
      induction htrace with
      | throughAperture first atAperture =>
          exact ExitsAfter.throughAperture
            (flip_first _ _ first) (flip_aperture _ atAperture)
      | @afterReflection state hit remaining first atMirror rest ih =>
          apply ExitsAfter.afterReflection
            (flip_first _ _ first) (flip_arc _ atMirror)
          change ExitsAfter mirror
            (stateAfterReflection (flipVec hit) (flipVec state.direction)) remaining
          rw [← flip_after]
          exact ih
    intro x n htrace
    by_cases hx : 0 ≤ x
    · simpa [abs_of_nonneg hx] using htrace
    · have hx_neg : x < 0 := lt_of_not_ge hx
      have hflipped := flip_exits (incidentRay x) n htrace
      have hflip_incident : flipState (incidentRay x) = incidentRay |x| := by
        apply ray_state_ext
        · apply vec2_ext
          · dsimp only [flipState, flipVec, incidentRay]
            rw [abs_of_neg hx_neg]
          · rfl
        · apply vec2_ext <;>
            dsimp only [flipState, flipVec, incidentRay] <;>
            ring
      rw [← hflip_incident]
      exact hflipped

  let denominator : ℝ := 2 * (N : ℝ) + 1
  let theta : ℝ := Real.pi / denominator
  let threshold : ℝ := R * Real.cos theta

  have denominator_pos : 0 < denominator := by
    dsimp [denominator]
    have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have theta_pos : 0 < theta := by
    exact div_pos Real.pi_pos denominator_pos
  have theta_lt_half_pi : theta < Real.pi / 2 := by
    have hN_one : 1 ≤ N := N_pos
    have hN_real : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_one
    have hdenominator_two : (2 : ℝ) < denominator := by
      dsimp [denominator]
      linarith only [hN_real]
    dsimp [theta]
    rw [div_lt_div_iff₀ denominator_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_lt_mul_of_pos_left hdenominator_two Real.pi_pos
  have threshold_pos : 0 < threshold := by
    dsimp [threshold]
    have hcos : 0 < Real.cos theta :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith only [theta_pos, Real.pi_pos], theta_lt_half_pi⟩
    exact mul_pos R_pos hcos
  have threshold_lt_radius : threshold < R := by
    dsimp [threshold]
    have htheta_pi : theta ≤ Real.pi := by
      linarith only [theta_lt_half_pi, Real.pi_pos]
    have hcos_lt : Real.cos theta < Real.cos 0 :=
      (Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
        ⟨theta_pos.le, htheta_pi⟩ theta_pos)
    simpa only [Real.cos_zero, mul_one] using
      (mul_lt_mul_of_pos_left hcos_lt R_pos)

  have at_most_nonnegative_iff (a : ℝ) (ha0 : 0 ≤ a) (haR : a < R) :
      HasAtMostReflections mirror a N ↔ a ≤ threshold := by
    let ratio : ℝ := a / R
    let alpha : ℝ := Real.arccos ratio
    have hratio_nonneg : 0 ≤ ratio := by
      exact div_nonneg ha0 R_pos.le
    have hratio_lt_one : ratio < 1 := by
      exact (div_lt_one R_pos).2 haR
    have hratio_lower : -1 ≤ ratio := by linarith only [hratio_nonneg]
    have halpha_pos : 0 < alpha := by
      exact Real.arccos_pos.mpr hratio_lt_one
    have halpha_half : alpha ≤ Real.pi / 2 := by
      exact Real.arccos_le_pi_div_two.mpr hratio_nonneg
    have hcos_alpha : Real.cos alpha = ratio := by
      exact Real.cos_arccos hratio_lower hratio_lt_one.le
    have hRcos_alpha : R * Real.cos alpha = a := by
      rw [hcos_alpha]
      dsimp [ratio]
      exact mul_div_cancel₀ a (ne_of_gt R_pos)
    have halpha_mem : alpha ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨halpha_pos.le, by linarith only [halpha_half, Real.pi_pos]⟩
    have htheta_mem : theta ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨theta_pos.le, by linarith only [theta_lt_half_pi, Real.pi_pos]⟩
    constructor
    · rintro ⟨count, hcount, hcoordinate, htrace⟩
      have htrace_alpha :
          ExitsAfter mirror (incidentRay (R * Real.cos alpha)) count := by
        rw [hRcos_alpha]
        exact htrace
      have hangles :=
        (incident_exits_iff alpha count halpha_pos halpha_half).1 htrace_alpha
      have hcount_real : (count : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcount
      have hnext_mono : nextAngle alpha count ≤ nextAngle alpha N := by
        dsimp [nextAngle]
        nlinarith only [hcount_real, halpha_pos]
      have hpi_next : Real.pi ≤ nextAngle alpha N :=
        le_trans hangles.2 hnext_mono
      have hpi_scaled : Real.pi ≤ denominator * alpha := by
        simpa [denominator, nextAngle] using hpi_next
      have htheta_le : theta ≤ alpha := by
        dsimp [theta]
        exact (div_le_iff₀ denominator_pos).2
          (by simpa [mul_comm] using hpi_scaled)
      have hcos_le : Real.cos alpha ≤ Real.cos theta :=
        (Real.strictAntiOn_cos.le_iff_ge halpha_mem htheta_mem).2 htheta_le
      have hscaled := mul_le_mul_of_nonneg_left hcos_le R_pos.le
      calc
        a = R * Real.cos alpha := hRcos_alpha.symm
        _ ≤ R * Real.cos theta := hscaled
        _ = threshold := rfl
    · intro habound
      have hscaled : R * Real.cos alpha ≤ R * Real.cos theta := by
        calc
          R * Real.cos alpha = a := hRcos_alpha
          _ ≤ threshold := habound
          _ = R * Real.cos theta := rfl
      have hcos_le : Real.cos alpha ≤ Real.cos theta :=
        le_of_mul_le_mul_left hscaled R_pos
      have htheta_le : theta ≤ alpha :=
        (Real.strictAntiOn_cos.le_iff_ge halpha_mem htheta_mem).1 hcos_le
      have hpi_scaled : Real.pi ≤ denominator * alpha := by
        have hdiv : Real.pi / denominator ≤ alpha := by
          simpa [theta] using htheta_le
        simpa [mul_comm] using (div_le_iff₀ denominator_pos).1 hdiv
      have hpi_next : Real.pi ≤ nextAngle alpha N := by
        simpa [denominator, nextAngle] using hpi_scaled
      let P : ℕ → Prop := fun m => Real.pi ≤ nextAngle alpha m
      have hexists : ∃ m : ℕ, P m := ⟨N, hpi_next⟩
      let count : ℕ := Nat.find hexists
      have hcount_upper : P count := Nat.find_spec hexists
      have hcount_le : count ≤ N := Nat.find_le hpi_next
      have hcount_pos : 0 < count := by
        by_contra hnot
        have hzero : count = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hzero] at hcount_upper
        norm_num [P, nextAngle] at hcount_upper
        have halpha_lt_pi : alpha < Real.pi := by
          linarith only [halpha_half, Real.pi_pos]
        exact (not_le_of_gt halpha_lt_pi) hcount_upper
      have hpred_lt : hitAngle alpha count < Real.pi := by
        have hpred_index : count - 1 < count :=
          Nat.sub_lt hcount_pos (Nat.zero_lt_succ 0)
        have hpred_not : ¬ P (count - 1) :=
          Nat.find_min hexists hpred_index
        have hpred_angle : nextAngle alpha (count - 1) < Real.pi :=
          lt_of_not_ge hpred_not
        have hangle_eq :
            nextAngle alpha (count - 1) = hitAngle alpha count := by
          dsimp [nextAngle, hitAngle]
          rw [Nat.cast_sub hcount_pos]
          push_cast
          ring
        rwa [hangle_eq] at hpred_angle
      have htrace_alpha :
          ExitsAfter mirror (incidentRay (R * Real.cos alpha)) count :=
        (incident_exits_iff alpha count halpha_pos halpha_half).2
          ⟨hpred_lt, hcount_upper⟩
      refine ⟨count, hcount_le, ?_⟩
      refine ⟨⟨by linarith only [ha0, R_pos], haR⟩, ?_⟩
      rw [← hRcos_alpha]
      exact htrace_alpha

  have admissible_eq : AdmissibleDistances mirror N = Set.Icc 0 threshold := by
    apply Set.ext
    intro distance
    constructor
    · rintro ⟨hdistance_nonneg, x, habs, hmost⟩
      rcases hmost with ⟨count, hcount_le, hincident, htrace⟩
      have habs_lt : |x| < R := (abs_lt).2 hincident
      have habs_incident : IsIncidentCoordinate mirror |x| :=
        ⟨by linarith only [R_pos, abs_nonneg x], habs_lt⟩
      have habs_most : HasAtMostReflections mirror |x| N :=
        ⟨count, hcount_le, habs_incident, exits_abs x count htrace⟩
      have habs_le : |x| ≤ threshold :=
        (at_most_nonnegative_iff |x| (abs_nonneg x) habs_lt).1 habs_most
      exact ⟨hdistance_nonneg, by simpa [habs] using habs_le⟩
    · rintro ⟨hdistance_nonneg, hdistance_le⟩
      have hdistance_lt : distance < R :=
        lt_of_le_of_lt hdistance_le threshold_lt_radius
      have hmost : HasAtMostReflections mirror distance N :=
        (at_most_nonnegative_iff distance hdistance_nonneg hdistance_lt).2
          hdistance_le
      exact ⟨hdistance_nonneg, distance, abs_of_nonneg hdistance_nonneg, hmost⟩

  have threshold_is : IsThreshold mirror N threshold := by
    refine ⟨threshold_pos, threshold_lt_radius, ?_, ?_⟩
    · rw [admissible_eq]
      exact ⟨threshold_pos.le, le_rfl⟩
    · rw [admissible_eq]
      exact isLUB_Icc threshold_pos.le
  refine ⟨threshold, threshold_is, ?_⟩
  intro candidate hcandidate
  exact (hcandidate.2.2.2.unique threshold_is.2.2.2)

end Ipho2026Gpt56solBlind.ProblemIPhO2026_2_A_1
