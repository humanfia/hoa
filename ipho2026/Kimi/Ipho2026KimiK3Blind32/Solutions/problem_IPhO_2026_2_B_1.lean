import Mathlib

/- USER: Mandatory formalization repair. Fix the branch/orientation ambiguity
before proving the coefficient theorem. `container_on_axis` places the
container on the source-shown front optical half-axis by the signed vector
identity `containerCenter = origin + (R / 2) • axis`, not merely by an unsigned
distance. The incidence predicate keeps an oriented, signed branch: it uses
the front-illuminated concave-bowl (far) half of the mirror circle, with
`0 < inner ℝ r.d (p - origin)`. The unsigned absolute-value form and the convex
near face both stay excluded. The tangent/extremal bridge is formulated for
that oriented branch. The coefficient values stay answer-free and do not occur
in hypotheses. -/

/-!
# IPhO 2026, Problem 2 (Solar Cooker), Part B.1 — answer-blind formalization

A half-hollow-cylinder mirror of radius `R` faces the sun, and a fully
absorbing cylindrical cooking container of radius `a` sits inside it.  The
axes of the mirror and of the container are parallel, and the center of the
container lies on the symmetry plane of the system, at distance `R / 2` from
the center of the mirror (Figure 2f).  The sunlight has constant, uniform
intensity and its rays are parallel to the optical axis of the mirror.  The
container radius `a` is such that every absorbed ray reflects from the
mirror at most once.  `θ_max` denotes the maximum angle of incidence on the
mirror (measured with respect to the normal drawn at the point of
incidence) among all reflected rays that strike the container, and `P₀`
denotes the power the container would receive if the mirror were not
present (relevant only to the later subquestions).

**Subquestion B.1 (T2-B1, 2 pts):** the container radius is
`a = α * sin θ_max + β * sin (2 θ_max)`; write `α` and `β` in terms of `R`.

The official coefficients are withheld.  The target theorem below states
existence and uniqueness of a coefficient pair `(α, β)` characterised by a
physically meaningful solution predicate — the prescribed identity at every
`θ_max` value realised by the stated geometry — without placing any derived
closed form for `α` or `β` in the signature.
-/

namespace IPhO_2026_2_B_1

open Real

/-- The Euclidean plane in which the cross-sectional ray optics takes place;
the axes of the two cylinders are perpendicular to this plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Geometric data of the solar-cooker cross section (Figure 2f).

- `R` is the radius of the (half-)cylindrical mirror;
- `origin` is the center of the mirror circle;
- `axis` is a unit vector along the optical axis of the mirror (the
  symmetry direction of the system), oriented from the mirror center toward
  the container center (the direction in which the sunlight travels, Fig. 2f);
- `containerCenter` is the center of the absorbing container circle;
- `a` is the container radius.

The statement fixes the container center on the *front* optical half-axis at
signed displacement `R / 2` from the mirror center.  Recording the signed
vector equality, rather than only collinearity plus an unsigned distance,
excludes the reflected back-side configuration. -/
structure Geometry where
  R : ℝ
  origin : Plane
  axis : Plane
  containerCenter : Plane
  a : ℝ
  R_pos : 0 < R
  axis_unit : ‖axis‖ = 1
  container_on_axis : containerCenter = origin + (R / 2) • axis
  container_dist : dist origin containerCenter = R / 2
  a_pos : 0 < a

/-- The mirror circle: points of the cross-sectional plane at distance `R`
from the mirror center `G.origin`.  (The physical mirror is the sun-facing
half of this circle; the half-restriction does not affect incidence angles
and is omitted from this interface.) -/
def mirrorCircle (G : Geometry) : Set Plane := Metric.sphere G.origin G.R

/-- The container disk: the closed disk of radius `G.a` about the container
center (the cross section of the fully absorbing cylinder). -/
def containerDisk (G : Geometry) : Set Plane := Metric.closedBall G.containerCenter G.a

/-- A light ray: a point `X` it passes through and a direction `d` it
travels in, representing the forward path `X + t • d` for `t ≥ 0`. -/
structure LightRay where
  X : Plane
  d : Plane

/-- A ray of the incident sunlight: it *travels* along the optical axis of
the mirror toward the reflecting bowl.  Figure 2f shows the sunlight
descending onto the bowl while the container center sits *below* the mirror
center on the symmetry axis, in the direction the light travels.  Hence the
propagation direction of an incident ray is aligned (not anti-aligned) with
the axis vector `G.axis` that points from the mirror center toward the
container center: `r.d = s • G.axis` with `s > 0`. -/
def LightRay.IsSunlight (r : LightRay) (G : Geometry) : Prop :=
  ∃ s : ℝ, 0 < s ∧ r.d = s • G.axis

/-- Specular reflection on the mirror circle.

`ReflectsAt G r p θ r'` says that the ray `r` reaches the point `p` of the
mirror circle, where its angle of incidence — measured with respect to the
normal drawn at `p`, which for a circle is the radius direction
`p - G.origin` — equals `θ`, and that after reflection the light travels as
the ray `r'` issued from `p`.

The law of reflection is encoded in the standard projection form: with the
surface normal proportional to `p - origin`, the reflected direction is
`d' = d - 2 ⟨d, n⟩ n / ‖n‖²`, which flips the normal component of the
direction and keeps its tangential component. The incidence angle is in
`[0, π / 2]`. On the front-illuminated concave-bowl half of Figure 2f, the
signed branch has `0 < ⟨d, p - origin⟩`; hence its incidence cosine is
`⟨d, p - origin⟩ / (‖d‖ * R)`. This orientation excludes both the unsigned
branch ambiguity and the convex near face. -/
def ReflectsAt (G : Geometry) (r : LightRay) (p : Plane) (θ : ℝ) (r' : LightRay) : Prop :=
  p ∈ mirrorCircle G ∧
  (∃ t : ℝ, t ≥ 0 ∧ p = r.X + t • r.d) ∧
  r'.X = p ∧
  r'.d = r.d - (2 * inner ℝ r.d (p - G.origin) / G.R ^ 2) • (p - G.origin) ∧
  ‖r.d‖ ≠ 0 ∧
  0 < inner ℝ r.d (p - G.origin) ∧
  0 ≤ θ ∧ θ ≤ π / 2 ∧
  Real.cos θ = inner ℝ r.d (p - G.origin) / (‖r.d‖ * G.R)

/-- The ray `r'` issued from the mirror point `p` strikes the container,
which fully absorbs it: some forward point of the ray lies in the container
disk. -/
def HitsContainer (G : Geometry) (p : Plane) (r' : LightRay) : Prop :=
  ∃ t : ℝ, t ≥ 0 ∧ p + t • r'.d ∈ containerDisk G

/-- The regime hypothesis of the problem: the container radius `a` is such
that every absorbed sunlight ray reflects from the mirror at most once.
Equivalently, no sunlight ray can undergo a second mirror reflection and
still end up absorbed by the container. -/
def AtMostOnceRegime (G : Geometry) : Prop :=
  ∀ r r₁ r₂ : LightRay, ∀ p₁ p₂ : Plane, ∀ φ₁ φ₂ : ℝ,
    r.IsSunlight G → ReflectsAt G r p₁ φ₁ r₁ → ReflectsAt G r₁ p₂ φ₂ r₂ →
    ¬ HitsContainer G p₂ r₂

/-- The set of incidence angles realised on the mirror by sunlight rays
that, after exactly one specular reflection, strike (and are absorbed by)
the container.  Under the `AtMostOnceRegime` hypothesis these are all the
reflected-and-captured rays of the system. -/
def capturedIncidenceAngles (G : Geometry) : Set ℝ :=
  {φ : ℝ | ∃ r r' : LightRay, ∃ p : Plane,
    r.IsSunlight G ∧ ReflectsAt G r p φ r' ∧ HitsContainer G p r'}

/-- `θ` is the maximum angle of incidence on the mirror (measured with
respect to the normal drawn at the point of incidence) among all reflected
rays that strike the container — the `θ_max` of the statement. -/
def IsThetaMax (G : Geometry) (θ : ℝ) : Prop := IsGreatest (capturedIncidenceAngles G) θ

/-- **Extremum bridge (global tangent-ray step).**

`MaxCapturedTangentContained G θ` packages the *global extremum fact* that
the largest incidence angle `θ` among captured reflected rays is realised by
a ray whose post-reflection forward path `p + t • r'.d` stays at distance
`≥ G.a` from the container center for every `t ≥ 0`, while meeting the
container disk at some `t₀ ≥ 0`.  Geometrically this is the statement that
the extremal captured ray is *tangent* to the absorbing container: the
perpendicular distance from the container center to the boundary ray's
forward path equals the container radius `G.a` exactly.

This is the single analytic "the maximum is attained by the tangent ray"
step of the problem, isolated from the answer predicate so that the theorem
contract quantifies only over a *local linear* ray (no global optimization).
Producing a witness requires the global analysis of
`capturedIncidenceAngles G`, which is the genuine physical content of the
subquestion and is *not* assumed here. -/
def MaxCapturedTangentContained (G : Geometry) (θ : ℝ) : Prop :=
  ∃ r r' : LightRay, ∃ p : Plane,
    r.IsSunlight G ∧ ReflectsAt G r p θ r' ∧
    (∀ t : ℝ, t ≥ 0 → G.a ≤ dist (p + t • r'.d) G.containerCenter) ∧
    (∃ t₀ : ℝ, t₀ ≥ 0 ∧ p + t₀ • r'.d ∈ containerDisk G)

/-- **Nondegeneracy of the extremal angle.**

The boundary (tangent) ray has nonzero incidence: `0 < θ`.  Together with
`ReflectsAt`'s bound `θ ≤ π / 2` this places `θ ∈ Set.Ioc 0 (π / 2)`, so
both `sin θ ≠ 0` and `sin (2 θ)` range over distinct values as `θ` varies —
the nondegeneracy that makes the two-coefficient system in
`a = α * sin θ + β * sin (2 θ)` solvable and unique. -/
def NondegenerateTheta (θ : ℝ) : Prop := 0 < θ

/-- **Pairwise (fixed-`R`) coefficient-solution predicate (answer-free).**

`CoeffSolutionPairwise R α β` says of a candidate pair `(α, β)` — the
lengths multiplying `sin θ_max` and `sin (2 θ_max)` — that for *every*
configuration `G` of mirror radius `R` whose maximum captured incidence
angle `θ` arises from a nondegenerate tangent boundary ray, the container
radius obeys `G.a = α * sin θ + β * sin (2 θ)`.  The radius `R` is a
parameter (the two physical configurations of Figure 2f share one `R`), so
this is the physically correct habitat for existence *and uniqueness* of the
pair: two admissible configurations with distinct nondegenerate `θ` give a
non-singular `2 × 2` system in `α, β`. -/
def CoeffSolutionPairwise (R α β : ℝ) : Prop :=
  ∀ G : Geometry, G.R = R → AtMostOnceRegime G → ∀ θ : ℝ,
    IsThetaMax G θ → MaxCapturedTangentContained G θ → NondegenerateTheta θ →
    G.a = α * Real.sin θ + β * Real.sin (2 * θ)

/-- A geometric configuration *admits a nondegenerate tangent boundary ray*:
its maximum captured incidence angle exists and is realised by a nondegenerate
tangent boundary ray.  (Existence of a witness for a concrete `Geometry` is
the global-analysis obligation of the problem, not an assumption.) -/
def AdmitsBoundaryRay (G : Geometry) : Prop :=
  ∃ θ : ℝ, IsThetaMax G θ ∧ MaxCapturedTangentContained G θ ∧ NondegenerateTheta θ

namespace PlaneCoords

/-!
### Coordinate helper facts on `EuclideanSpace ℝ (Fin 2)`

The ray-optics derivation below is carried out componentwise: we expand the
inner product and the norm squared in the fixed coordinates of `Plane`, and
reduce every Euclidean identity to real arithmetic via `nlinarith`. -/

lemma inner_eq_plane (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp [Pi.star_apply]; ring

lemma add_coords_plane (u v : Plane) (i : Fin 2) : (u + v) i = u i + v i := rfl

lemma smul_coords_plane (u v : Plane) (i : Fin 2) : (u - v) i = u i - v i := rfl

lemma smul_apply_plane (s : ℝ) (u : Plane) (i : Fin 2) : (s • u) i = s * u i := rfl

lemma norm_sq_plane (u : Plane) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp

/-- Squared Euclidean distance in coordinates. -/
lemma dist_sqd_plane (p c : Plane) :
    dist p c ^ 2 = (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 := by
  rw [dist_eq_norm, norm_sq_plane]
  have h0 : (p - c) 0 = p 0 - c 0 := rfl
  have h1 : (p - c) 1 = p 1 - c 1 := rfl
  rw [h0, h1]

/-- If a nonnegative distance is `≤ a` then it is `= a` as soon as the
corresponding squared coordinate distance equals `a ^ 2` and `0 ≤ a`. -/
lemma dist_eq_of_sqd {p c : Plane} {a : ℝ} (ha : 0 ≤ a)
    (h : (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 = a ^ 2) : dist p c = a := by
  have hnn : 0 ≤ dist p c := dist_nonneg
  have h2 : dist p c ^ 2 = a ^ 2 := by rw [dist_sqd_plane]; exact h
  nlinarith [sq_nonneg (dist p c - a)]

end PlaneCoords

open PlaneCoords

/-- Closed-ball membership used in the tangency step. -/
lemma mem_containerDisk_iff {G : Geometry} {x : Plane} :
    x ∈ containerDisk G ↔ dist x G.containerCenter ≤ G.a := Iff.rfl

/-- The vector `p - origin` when `p` lies on the mirror sphere. -/
lemma mirror_norm_sq (G : Geometry) {p : Plane} (hp : p ∈ mirrorCircle G) :
    ‖p - G.origin‖ ^ 2 = G.R ^ 2 := by
  have h : dist p G.origin = G.R := by
    simpa [mirrorCircle, Metric.sphere, Set.mem_setOf_eq, dist_eq_norm] using hp
  have h' : ‖p - G.origin‖ = G.R := by rwa [← dist_eq_norm]
  rw [h']

/-- **Squared distance along a parametric line (quadratic in `t`).** -/
lemma sqd_along_line_plane (w c d : Plane) (t : ℝ) :
    dist (w + t • d) c ^ 2
      = ‖d‖ ^ 2 * t ^ 2 + 2 * inner ℝ (w - c) d * t + dist w c ^ 2 := by
  rw [dist_sqd_plane, dist_sqd_plane, norm_sq_plane, inner_eq_plane]
  have e : ∀ i : Fin 2, (w + t • d) i = w i + t * d i := fun i => by
    show (w i) + (t • d) i = _
    rw [show (t • d) i = t * d i from rfl]
  rw [show ((w + t • d) 0 - c 0) = (w 0 - c 0) + t * d 0 from by rw [e 0]; ring,
      show ((w + t • d) 1 - c 1) = (w 1 - c 1) + t * d 1 from by rw [e 1]; ring,
      show ((w - c) 0) = w 0 - c 0 from rfl,
      show ((w - c) 1) = w 1 - c 1 from rfl]
  ring

/-- **First-order tangency condition.**  If the starting point `w` of the ray
`t ↦ w + t • d` is at distance `a ≥ 0` from `c`, and every point of the
extended ray stays at distance `≥ a`, then `⟪w - c, d⟫ = 0`. -/
theorem inner_eq_zero_of_min_dist {w c d : Plane} {a : ℝ}
    (ha_nn : 0 ≤ a) (hstart : dist w c = a)
    (hqa : ∀ t : ℝ, a ≤ dist (w + t • d) c) :
    inner ℝ (w - c) d = 0 := by
  classical
  have hquad : ∀ t : ℝ, dist (w + t • d) c ^ 2
      = ‖d‖ ^ 2 * t ^ 2 + 2 * inner ℝ (w - c) d * t + dist w c ^ 2 :=
    fun t => sqd_along_line_plane w c d t
  set A := ‖d‖ ^ 2 with hA
  set F := inner ℝ (w - c) d with hF
  set K := dist w c ^ 2 with hK
  have hsquare : ∀ t : ℝ, a ^ 2 ≤ A * t ^ 2 + 2 * F * t + K := by
    intro t
    have h1 : a ≤ dist (w + t • d) c := hqa t
    have hnn2 : (0:ℝ) ≤ dist (w + t • d) c := dist_nonneg
    have h := (sq_le_sq₀ ha_nn hnn2).mpr h1
    rwa [hquad] at h
  have hst : K = a ^ 2 := by
    rw [hK]
    have hnn : (0:ℝ) ≤ dist w c := dist_nonneg
    nlinarith [hstart, ha_nn, sq_nonneg (dist w c), sq_nonneg a]
  rw [hst] at hsquare
  have hkey : ∀ t : ℝ, 0 ≤ A * t ^ 2 + 2 * F * t := by
    intro t; linarith [hsquare t]
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hp1 := hkey 1
  have hm1 := hkey (-1)
  have hp1' : 0 ≤ A + 2 * F := by nlinarith [hp1]
  have hm1' : 0 ≤ A - 2 * F := by nlinarith [hm1]
  by_cases hAz : A = 0
  · rw [hAz] at hp1' hm1'
    linarith [hp1', hm1']
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
    have hv := hkey (-F / A)
    have hAnz : A ≠ 0 := ne_of_gt hApos
    have hsimp : A * (-F / A) ^ 2 + 2 * F * (-F / A) = -(F^2 / A) := by
      field_simp; ring
    rw [hsimp] at hv
    have hFsq : 0 ≤ F ^ 2 / A := div_nonneg (sq_nonneg _) (le_of_lt hApos)
    have hzero : F ^ 2 / A = 0 := le_antisymm (by nlinarith [hv]) hFsq
    have hFs : F ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hzero with h | h
      · exact h
      · exact absurd h hAnz
    nlinarith [hFs]

set_option maxHeartbeats 1000000

/-- **The marginal-ray (tangent) container-radius law.**  In the physical
configuration of Figure 2f, the captured reflected ray realising the maximum
incidence angle `θ` is tangent to the absorbing container; resolving the
tangency against the specular-reflection geometry yields
`a = R sin θ − (R / 2) sin (2 θ)`.  This is the single geometric input to
the existence half of the B.1 characterization.  Its full componentwise
derivation (via `inner_eq_zero_of_min_dist`) is deferred: see
`task_results/problem_IPhO_2026_2_B_1.md`. -/
theorem tangent_ray_radius_law (G : Geometry) {θ : ℝ}
    (htan : MaxCapturedTangentContained G θ) (hnd : NondegenerateTheta θ) :
    G.a = G.R * Real.sin θ - (G.R / 2) * Real.sin (2 * θ) := by
  classical
  obtain ⟨r, r', p, hsun, hrefl, hge, hhit⟩ := htan
  obtain ⟨hp, _, _, hd', hdnorm, hinc, hθ0, hθpi, hcos⟩ := hrefl
  obtain ⟨s, hs, hd⟩ := hsun
  obtain ⟨t₀, ht₀, htmem⟩ := hhit
  set N : Plane := p - G.origin with hN
  have hdN : r'.d = r.d - (2 * inner ℝ r.d N / G.R ^ 2) • N := by
    simpa [N] using hd'
  have hincN : 0 < inner ℝ r.d N := by simpa [N] using hinc
  have hcosN : Real.cos θ = inner ℝ r.d N / (‖r.d‖ * G.R) := by
    simpa [N] using hcos
  have hRne : G.R ≠ 0 := G.R_pos.ne'
  have hsne : s ≠ 0 := hs.ne'
  have hd_norm : ‖r.d‖ = s := by
    rw [hd, norm_smul, G.axis_unit, Real.norm_eq_abs, abs_of_pos hs, mul_one]
  have hNN : inner ℝ N N = G.R ^ 2 := by
    rw [hN, real_inner_self_eq_norm_sq, mirror_norm_sq G hp]
  have hAA : inner ℝ G.axis G.axis = 1 := by
    rw [real_inner_self_eq_norm_sq, G.axis_unit]
    norm_num
  have hJ : inner ℝ r.d N = s * inner ℝ G.axis N := by
    rw [hd, real_inner_smul_left]
  have hcos_mul : Real.cos θ * (s * G.R) =
      inner ℝ r.d N := by
    rw [hd_norm] at hcosN
    field_simp [hsne, hRne] at hcosN
    nlinarith [hcosN]
  have hM : inner ℝ G.axis N = Real.cos θ * G.R := by
    rw [hJ] at hcos_mul
    apply mul_left_cancel₀ hsne
    nlinarith [hcos_mul]
  have hJval : inner ℝ r.d N = s * (Real.cos θ * G.R) := by
    rw [hJ, hM]
  have hJrev : inner ℝ N r.d = s * (Real.cos θ * G.R) := by
    rw [real_inner_comm, hJval]
  have hMrev : inner ℝ N G.axis = Real.cos θ * G.R := by
    rw [real_inner_comm, hM]
  have hq : p - G.containerCenter =
      N - (G.R / 2) • G.axis := by
    rw [hN, G.container_on_axis]
    module
  have hA2 : ‖r'.d‖ ^ 2 = s ^ 2 := by
    rw [hdN, ← real_inner_self_eq_norm_sq, inner_sub_sub_self,
      real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hd_norm, hNN]
    simp only [hJval, hJrev]
    field_simp [hRne]
    ring
  have hF : inner ℝ (p - G.containerCenter) r'.d =
      s * G.R * (Real.cos θ ^ 2 - Real.cos θ - 1 / 2) := by
    rw [hq, hdN]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_right,
      real_inner_smul_left]
    rw [hNN, hJval, hJrev, hd]
    simp only [real_inner_smul_right, real_inner_smul_left]
    simp only [hAA, hM, hMrev]
    field_simp [hRne]
    ring
  have hcos_pos : 0 < Real.cos θ := by
    rw [hd_norm] at hcosN
    have hden : 0 < s * G.R := mul_pos hs G.R_pos
    rw [hcosN]
    exact div_pos hincN hden
  have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hpoly_neg : Real.cos θ ^ 2 - Real.cos θ - 1 / 2 < 0 := by
    have hcprod : 0 ≤ Real.cos θ * (1 - Real.cos θ) :=
      mul_nonneg hcos_pos.le (sub_nonneg.mpr hcos_le)
    nlinarith [hcprod]
  have hFneg : inner ℝ (p - G.containerCenter) r'.d < 0 := by
    rw [hF]
    exact mul_neg_of_pos_of_neg (mul_pos hs G.R_pos) hpoly_neg
  have hApos : 0 < ‖r'.d‖ ^ 2 := by
    rw [hA2]
    positivity
  have ht_le : dist (p + t₀ • r'.d) G.containerCenter ≤ G.a :=
    mem_containerDisk_iff.mp htmem
  have ht_ge : G.a ≤ dist (p + t₀ • r'.d) G.containerCenter := hge t₀ ht₀
  have ht_eq : dist (p + t₀ • r'.d) G.containerCenter = G.a :=
    le_antisymm ht_le ht_ge
  have ht₀pos : 0 < t₀ := by
    rcases ht₀.eq_or_lt with rfl | htpos
    · have hstart : dist p G.containerCenter = G.a := by simpa using ht_eq
      let u : ℝ := -inner ℝ (p - G.containerCenter) r'.d / ‖r'.d‖ ^ 2
      have hu : 0 < u := div_pos (neg_pos.mpr hFneg) hApos
      have hgu := hge u hu.le
      have hsq : G.a ^ 2 ≤ dist (p + u • r'.d) G.containerCenter ^ 2 :=
        (sq_le_sq₀ G.a_pos.le dist_nonneg).mpr hgu
      rw [sqd_along_line_plane, hstart] at hsq
      have hAne : ‖r'.d‖ ^ 2 ≠ 0 := hApos.ne'
      have hcalc : ‖r'.d‖ ^ 2 *
            (-inner ℝ (p - G.containerCenter) r'.d / ‖r'.d‖ ^ 2) ^ 2 +
          2 * inner ℝ (p - G.containerCenter) r'.d *
            (-inner ℝ (p - G.containerCenter) r'.d / ‖r'.d‖ ^ 2) =
          -(inner ℝ (p - G.containerCenter) r'.d ^ 2 / ‖r'.d‖ ^ 2) := by
        field_simp [hAne]
        ring
      dsimp [u] at hsq
      rw [hcalc] at hsq
      have hquotpos : 0 < inner ℝ (p - G.containerCenter) r'.d ^ 2 /
          ‖r'.d‖ ^ 2 := div_pos (sq_pos_of_neg hFneg) hApos
      linarith
    · exact htpos
  have hlocal : IsLocalMin
      (fun t : ℝ => dist (p + t • r'.d) G.containerCenter ^ 2) t₀ := by
    filter_upwards [Ici_mem_nhds ht₀pos] with t ht
    have hgt := hge t ht
    have hsqt : G.a ^ 2 ≤ dist (p + t • r'.d) G.containerCenter ^ 2 :=
      (sq_le_sq₀ G.a_pos.le dist_nonneg).mpr hgt
    rw [ht_eq]
    exact hsqt
  have hderiv : HasDerivAt
      (fun t : ℝ => dist (p + t • r'.d) G.containerCenter ^ 2)
      (2 * ‖r'.d‖ ^ 2 * t₀ + 2 * inner ℝ (p - G.containerCenter) r'.d) t₀ := by
    have hpoly : HasDerivAt
        (fun t : ℝ => ‖r'.d‖ ^ 2 * t ^ 2 +
          2 * inner ℝ (p - G.containerCenter) r'.d * t +
            dist p G.containerCenter ^ 2)
        (2 * ‖r'.d‖ ^ 2 * t₀ + 2 * inner ℝ (p - G.containerCenter) r'.d) t₀ := by
      convert (((((hasDerivAt_id t₀).pow 2).const_mul (‖r'.d‖ ^ 2)).add
        ((hasDerivAt_id t₀).const_mul
          (2 * inner ℝ (p - G.containerCenter) r'.d))).add_const
            (dist p G.containerCenter ^ 2)) using 1
      all_goals first
        | (ext x; simp)
        | (simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq]; ring)
    exact hpoly.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => sqd_along_line_plane p G.containerCenter r'.d t)
  have hstationary :
      2 * ‖r'.d‖ ^ 2 * t₀ + 2 * inner ℝ (p - G.containerCenter) r'.d = 0 :=
    hlocal.hasDerivAt_eq_zero hderiv
  have hcontact_quad := sqd_along_line_plane p G.containerCenter r'.d t₀
  rw [ht_eq] at hcontact_quad
  have hq2 : dist p G.containerCenter ^ 2 =
      G.R ^ 2 * (5 / 4 - Real.cos θ) := by
    rw [dist_eq_norm, hq, ← real_inner_self_eq_norm_sq,
      inner_sub_sub_self, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, hNN, hAA,
      hM, hMrev]
    ring
  have hprojection : s ^ 2 * G.a ^ 2 =
      s ^ 2 * dist p G.containerCenter ^ 2 -
        (inner ℝ (p - G.containerCenter) r'.d) ^ 2 := by
    rw [hA2] at hstationary hcontact_quad
    have hstat : s ^ 2 * t₀ + inner ℝ (p - G.containerCenter) r'.d = 0 := by
      linarith [hstationary]
    have hstat_sq :
        (s ^ 2 * t₀ + inner ℝ (p - G.containerCenter) r'.d) ^ 2 = 0 := by
      rw [hstat]
      norm_num
    nlinarith [hstat_sq]
  let K : ℝ := G.R * Real.sin θ - (G.R / 2) * Real.sin (2 * θ)
  have hK : K = G.R * Real.sin θ * (1 - Real.cos θ) := by
    dsimp [K]
    rw [Real.sin_two_mul]
    ring
  have hsin_sq : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have halgebra :
      s ^ 2 * (G.R ^ 2 * (5 / 4 - Real.cos θ)) -
          (s * G.R * (Real.cos θ ^ 2 - Real.cos θ - 1 / 2)) ^ 2 =
        s ^ 2 * K ^ 2 := by
    rw [hK]
    calc
      s ^ 2 * (G.R ^ 2 * (5 / 4 - Real.cos θ)) -
            (s * G.R * (Real.cos θ ^ 2 - Real.cos θ - 1 / 2)) ^ 2 =
          s ^ 2 * G.R ^ 2 * (1 - Real.cos θ ^ 2) *
            (1 - Real.cos θ) ^ 2 := by ring
      _ = s ^ 2 * G.R ^ 2 * Real.sin θ ^ 2 *
            (1 - Real.cos θ) ^ 2 := by rw [hsin_sq]
      _ = s ^ 2 * (G.R * Real.sin θ * (1 - Real.cos θ)) ^ 2 := by ring
  have hsquares : G.a ^ 2 = K ^ 2 := by
    have hscaled : s ^ 2 * G.a ^ 2 = s ^ 2 * K ^ 2 := by
      calc
        s ^ 2 * G.a ^ 2 = s ^ 2 * dist p G.containerCenter ^ 2 -
            (inner ℝ (p - G.containerCenter) r'.d) ^ 2 := hprojection
        _ = s ^ 2 * (G.R ^ 2 * (5 / 4 - Real.cos θ)) -
            (s * G.R * (Real.cos θ ^ 2 - Real.cos θ - 1 / 2)) ^ 2 := by
              rw [hq2, hF]
        _ = s ^ 2 * K ^ 2 := halgebra
    exact mul_left_cancel₀ (pow_ne_zero 2 hsne) hscaled
  have hsin_nonneg : 0 ≤ Real.sin θ := by
    exact (Real.sin_pos_of_pos_of_lt_pi hnd
      (lt_of_le_of_lt hθpi (by nlinarith [Real.pi_pos]))).le
  have hKnonneg : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg G.R_pos.le hsin_nonneg)
      (sub_nonneg.mpr hcos_le)
  have haK : G.a = K := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with h | h
    · exact h
    · have : G.a ≤ 0 := by rw [h]; exact neg_nonpos.mpr hKnonneg
      exact (not_le_of_gt G.a_pos this).elim
  exact haK

/-- **Target theorem (answer-free, conditional characterization).**

The subquestion asks to *determine* two lengths `α, β` "in terms of `R`".
Because the official coefficients are withheld, the theorem characterises
them as the **unique pair** satisfying the prescribed identity on every
configuration of radius `R` — *provided* two admissible configurations with
distinct nondegenerate extremal angles exist, which is what forces the
coefficients to specific numbers (rather than an underdetermined continuum).

No closed form for `α` or `β` is placed in the signature: they are
quantified as reals identified uniquely through the identity.  The global
extremum bridge `MaxCapturedTangentContained` is folded into the solution
predicate (not the conclusion), per the redraft directive. -/
theorem problem_IPhO_2026_2_B_1 (R : ℝ) (hR : 0 < R)
    (G₁ G₂ : Geometry)
    (hG₁R : G₁.R = R) (hG₂R : G₂.R = R)
    (hreg₁ : AtMostOnceRegime G₁) (hreg₂ : AtMostOnceRegime G₂)
    (θ₁ θ₂ : ℝ)
    (hmax₁ : IsThetaMax G₁ θ₁) (htan₁ : MaxCapturedTangentContained G₁ θ₁)
    (hnd₁ : NondegenerateTheta θ₁)
    (hmax₂ : IsThetaMax G₂ θ₂) (htan₂ : MaxCapturedTangentContained G₂ θ₂)
    (hnd₂ : NondegenerateTheta θ₂)
    (hdistinct : θ₁ ≠ θ₂) :
    ∃! coeffs : ℝ × ℝ, CoeffSolutionPairwise R coeffs.1 coeffs.2 := by
  classical
  -- The physical candidate, read off the tangent-ray law:
  -- `a = R sin θ - (R/2) sin (2θ)`.
  refine ⟨⟨R, -(R / 2)⟩, ?_, ?_⟩
  · -- Existence: the candidate solves the pairwise identity.
    intro G hGR hreg φ hmax htan hnd
    have hlaw := tangent_ray_radius_law G htan hnd
    rw [hGR] at hlaw
    rw [show ((R, -(R / 2)) : ℝ × ℝ).1 = R from rfl,
        show ((R, -(R / 2)) : ℝ × ℝ).2 = -(R / 2) from rfl]
    linarith [hlaw]
  · -- Uniqueness: any solution equals the candidate.
    rintro ⟨α', β'⟩ hsol
    -- Evaluate the pairwise identity at the two given configurations.
    have heq1 : G₁.a = α' * Real.sin θ₁ + β' * Real.sin (2 * θ₁) :=
      hsol G₁ hG₁R hreg₁ θ₁ hmax₁ htan₁ hnd₁
    have heq2 : G₂.a = α' * Real.sin θ₂ + β' * Real.sin (2 * θ₂) :=
      hsol G₂ hG₂R hreg₂ θ₂ hmax₂ htan₂ hnd₂
    -- The candidate obeys the same two identities.
    have hcan1 : G₁.a = R * Real.sin θ₁ + -(R / 2) * Real.sin (2 * θ₁) := by
      have hlaw := tangent_ray_radius_law G₁ htan₁ hnd₁
      rw [hG₁R] at hlaw
      linarith [hlaw]
    have hcan2 : G₂.a = R * Real.sin θ₂ + -(R / 2) * Real.sin (2 * θ₂) := by
      have hlaw := tangent_ray_radius_law G₂ htan₂ hnd₂
      rw [hG₂R] at hlaw
      linarith [hlaw]
    -- The extremal angles live in (0, π/2]: from the tangent package the ray
    -- is non-grazing (its incidence satisfies 0 < θ ≤ π/2).
    have hθpi1 : θ₁ ≤ π / 2 := by
      obtain ⟨r₁r, r₁r', p₁, _, hrefl1, _, _⟩ := htan₁
      obtain ⟨_, _, _, _, _, hθ0₁, hθpi₁, _⟩ := hrefl1
      nlinarith [hθpi₁]
    have hθpi2 : θ₂ ≤ π / 2 := by
      obtain ⟨r₂r, r₂r', p₂, _, hrefl2, _, _⟩ := htan₂
      obtain ⟨_, _, _, _, _, hθ0₂, hθpi₂, _⟩ := hrefl2
      nlinarith [hθpi₂]
    have hsin1 : Real.sin θ₁ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hnd₁ (by nlinarith [hθpi1, Real.pi_pos]))
    have hsin2 : Real.sin θ₂ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hnd₂ (by nlinarith [hθpi2, Real.pi_pos]))
    -- Linearize: dα sin θᵢ + dβ sin(2θᵢ) = 0 with sin(2θ) = 2 sinθ cosθ.
    -- Below α := R, β := -(R/2) are the candidate components.
    have hlin1 : (α' - R) + 2 * (β' - -(R / 2)) * Real.cos θ₁ = 0 := by
      have e : α' * Real.sin θ₁ + β' * Real.sin (2 * θ₁)
          = R * Real.sin θ₁ + -(R / 2) * Real.sin (2 * θ₁) := by
        linarith [heq1, hcan1]
      rw [Real.sin_two_mul] at e
      have hfact : Real.sin θ₁ * ((α' - R) + 2 * (β' - -(R / 2)) * Real.cos θ₁) = 0 := by
        nlinarith [e]
      exact (mul_eq_zero.mp hfact).resolve_left hsin1
    have hlin2 : (α' - R) + 2 * (β' - -(R / 2)) * Real.cos θ₂ = 0 := by
      have e : α' * Real.sin θ₂ + β' * Real.sin (2 * θ₂)
          = R * Real.sin θ₂ + -(R / 2) * Real.sin (2 * θ₂) := by
        linarith [heq2, hcan2]
      rw [Real.sin_two_mul] at e
      have hfact : Real.sin θ₂ * ((α' - R) + 2 * (β' - -(R / 2)) * Real.cos θ₂) = 0 := by
        nlinarith [e]
      exact (mul_eq_zero.mp hfact).resolve_left hsin2
    -- If dβ ≠ 0 then cos θ₁ = cos θ₂, forcing θ₁ = θ₂ (contradiction);
    -- hence dβ = 0, and then dα = 0.
    have hdβ : β' = -(R / 2) := by
      by_contra hβz
      have hcoseq : Real.cos θ₁ = Real.cos θ₂ := by
        have hβsub : β' - -(R / 2) ≠ 0 := sub_ne_zero.mpr hβz
        have h2b : 2 * (β' - -(R / 2)) ≠ 0 := mul_ne_zero two_ne_zero hβsub
        have e : 2 * (β' - -(R / 2)) * Real.cos θ₁
            = 2 * (β' - -(R / 2)) * Real.cos θ₂ := by
          linarith [hlin1, hlin2]
        exact (mul_right_injective₀ h2b) e
      have hθeq : θ₁ = θ₂ := by
        have hmem1 : θ₁ ∈ Set.Icc 0 π :=
          ⟨le_of_lt hnd₁, by nlinarith [hθpi1, Real.pi_pos]⟩
        have hmem2 : θ₂ ∈ Set.Icc 0 π :=
          ⟨le_of_lt hnd₂, by nlinarith [hθpi2, Real.pi_pos]⟩
        exact Real.injOn_cos hmem1 hmem2 hcoseq
      exact absurd hθeq hdistinct
    have hαeq : α' = R := by
      have hdβ0 : β' - -(R / 2) = 0 := sub_eq_zero.mpr hdβ
      rw [hdβ0] at hlin1
      simp at hlin1
      linarith [hlin1]
    have hβeq2 : β' = -(R / 2) := hdβ
    exact Prod.ext hαeq hβeq2

end IPhO_2026_2_B_1
