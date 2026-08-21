import Mathlib

/-!
# IPhO 2026, Problem T2, Part A.1 — answer-blind formalization (redraft, iter-012)

**Physical setup (Figs. 2a, 2c, 2d, 2e).**

A family of parallel rays strikes the inside of a half-cylindrical mirror of
radius `R`. In the cross-sectional plane (Fig. 2d) the reflective wall is the
open upper semicircle of radius `R` centered at the origin — a dome whose
aperture is the diameter segment between `(−R, 0)` and `(R, 0)`; the optical
axis is the vertical symmetry axis. The incident rays come from a distant
external source and are **parallel to the mirror's optical axis** (Fig. 2a);
they enter through the aperture traveling **upward** along the vertical line
of transverse coordinate `x ∈ (−R, R)` and first touch the wall at
`(x, √(R² − x²))`. This orientation is forced by the geometry: a ray
*descending* onto the upper semicircle from above can only meet its convex
outside — a straight-down line through `(x, √(R² − x²))` continues to the
lower semicircle `(x, −√(R² − x²))`, which is not part of the mirror — so the
concave inner wall of the dome is reachable only from below. The ray is then
specularly reflected by the circular wall, possibly several times, until it
leaves through the aperture (Fig. 2c).

For an incident ray with coordinate `x`, let `N` be the number of reflections
it undergoes on the mirror. As `|x|` varies over `[0, R)`, `N` takes every
natural value `≥ 1` (Fig. 2e: plateaus `1, 2, 3, …` over symmetric intervals
`[−x₁, x₁]`, `±(x₁, x₂]`, … with closed upward steps). The *threshold* `x_N`
is the maximum distance from the optical axis that allows an incident ray to
be reflected by the mirror **at most** `N` times; the geometry is symmetric
about the optical axis, so the count depends only on `|x|`, and
`0 < x_N < R`.

**Question (T2-A1).** Find the general expression for the threshold `x_N`
in terms of `R` and the positive integer `N`.

**Answer-blind statement design.** The official closed form is withheld. We
model the mirror, the specular-reflection dynamics with the incident
direction locked to the optical axis, and the reflection count; define
`IsThreshold R N ξ` as "`ξ` is positive, `< R`, attained at `|x| = ξ` with
at most `N` reflections; every ray with `|x| ≤ ξ` undergoes at most `N`
reflections; every ray with `ξ < |x| < R` undergoes at least `N + 1`"; and
state that for each radius and each positive integer `N` there is a unique
such threshold (`problem_IPhO_2026_2_A_1`). No closed-form witness appears
in any signature.

**Redraft notes (iter-012, fixing the iter-004/iter-011 frozen model).**
Two coupled defects of the previous draft are repaired:

1. **Incident orientation.** `AxisParallelIncident` now requires `0 < v₀.2`
   (ascending through the aperture). The previous draft used `v₀.2 < 0`,
   which is geometrically incompatible with hitting the *inner* wall of the
   upper semicircle from outside.
2. **Reflecting recurrence.** The leg direction now reflects at the *first*
   hit as well: `legDirs v₀ R x 0 = reflectDir (firstHit R x) v₀`, and
   `hits (k+1) = nextHit (hits k) (legDirs k)`. The previous draft stored
   the *unreflected* `v₀` for the first leg, so every second hit landed on
   the lower semicircle, every ray underwent at most one reflection
   (`not_atLeast_of_ge_two`), `OutsideThreshold` was unsatisfiable, and the
   main existence statement was false (`no_threshold_exists`).

With these repairs the dynamics is the standard circular-billiard orbit:
successive hit points sit at circle angles `(2k + 1) · arccos (x / R)`
(`hits_angular_spec`), so the reflection count is characterized by the
arithmetic progression of angles staying inside `(0, π)`
(`threshold_angular_characterization`). Those bridges are stated here with
`sorry` bodies; the closed form itself appears nowhere.

**Counting convention (rims).** A hit exactly on a rim endpoint `(±R, 0)`
has vanishing height and lies outside the open wall `OnMirror`; the physical
ray leaves through the aperture there without reflecting, so the strict
`0 < P.2` clause counts such grazing trajectories correctly on the
"at most `N`" side (this is also Fig. 2e's closed-step convention).
-/

namespace IPhO_2026_2
namespace PartA1

/-- A point of the cross-sectional plane, in Cartesian coordinates
(the coordinate system of Fig. 2d: origin at the mirror center, `y` along
the optical axis). Both coordinates carry units of length. -/
abbrev Point := ℝ × ℝ

/-- Standard dot product of the plane, written with coordinates to keep the
model elementary and self-contained. -/
def dot (u v : Point) : ℝ := u.1 * v.1 + u.2 * v.2

/-- Squared Euclidean norm of a planar vector. -/
def normSq (u : Point) : ℝ := dot u u

/-- Vector subtraction in the plane. -/
def sub (u v : Point) : Point := (u.1 - v.1, u.2 - v.2)

/-- Scalar multiplication in the plane. -/
def smul (c : ℝ) (u : Point) : Point := (c * u.1, c * u.2)

/-- The mirror cross-section: the reflective inner wall is the open upper
semicircle `{(X, Y) : X² + Y² = R², Y > 0}` (Fig. 2d). The rim endpoints
`(±R, 0)` belong to the aperture, not to the wall: a trajectory reaching
height `0` leaves the mirror region through the open diameter. -/
def OnMirror (R : ℝ) (P : Point) : Prop :=
  normSq P = R ^ 2 ∧ 0 < P.2

/-- A ray with coordinate `x` first touches the wall at
`(x, √(R² − x²))`, the upper-semicircle point of transverse coordinate `x`
(Fig. 2d). -/
noncomputable def firstHit (R x : ℝ) : Point := (x, Real.sqrt (R ^ 2 - x ^ 2))

/-- A ray is a valid incident configuration when it enters through the
aperture: `|x| < R`, so that its vertical line meets the wall in the open
upper half-plane. -/
def ValidIncident (R x : ℝ) : Prop := |x| < R

/-- **The incident family is parallel to the optical axis** (Fig. 2a: "the
incident rays come from a distant external light source and are parallel to
the mirror's optical axis") and **ascends through the aperture** (the only
orientation that can illuminate the concave inside of the upper semicircle):
`v₀ ≠ 0` is vertical with positive height component.

This predicate (not an arbitrary nonzero vector, and not the descending
orientation) is the correct domain for the threshold question: first hits
land on the upper semicircle only for the ascending family, and the
reflection counts of Fig. 2e climb without bound as `|x| → R` only for it. -/
def AxisParallelIncident (v₀ : Point) : Prop :=
  v₀ ≠ 0 ∧ v₀.1 = 0 ∧ 0 < v₀.2

/-- Specular reflection of the propagation direction `v` at a hit point `P`
of a circular mirror: the reflected direction is the mirror image of `v`
across the radius line, `v' = v − 2 ⟨v, P⟩ P / ⟨P, P⟩`. This is the law of
reflection (angle of incidence equals angle of departure) applied to a
circular wall whose outward normal at `P` is the radius `P`; it reverses
the radial component and preserves the tangential component of `v`. -/
noncomputable def reflectDir (P v : Point) : Point :=
  sub v (smul (2 * dot v P / normSq P) P)

/-- Second intersection with the `R`-circle of the line through `P` in
direction `v`: for `P` on the circle and `v ≠ 0` pointing into the disk
(`⟨P, v⟩ < 0`), the chord from `P` meets the circle again at
`P − 2 ⟨P, v⟩ / ⟨v, v⟩ • v`. -/
noncomputable def nextHit (P v : Point) : Point :=
  sub P (smul (2 * dot P v / normSq v) v)

mutual

/-- The sequence of successive hit points of a ray inside the cylindrical
mirror: `hits v₀ R x k` is the `k`-th point at which the ray of incident
coordinate `x` and incident direction `v₀` meets the mirror circle
(`hits v₀ R x 0` is the first hit, Fig. 2d). The travel direction on the
leg leaving each hit is the specular reflection of the previous leg
(`legDirs`), so the orbit is exactly the circular billiard inside the
`R`-circle; only hits lying in `OnMirror` are physical reflections, the
others sit below the aperture where the real ray has already escaped. -/
noncomputable def hits (v₀ : Point) (R x : ℝ) : ℕ → Point
  | 0 => firstHit R x
  | k + 1 => nextHit (hits v₀ R x k) (legDirs v₀ R x k)

/-- The propagation direction on the leg that **leaves** the `k`-th hit
point: the direction arriving at hit `k` specularly reflected in the wall
normal at that hit. In particular the leg leaving the first hit is
`reflectDir (firstHit R x) v₀` — the reflection at the first hit is part of
the dynamics (this is the iter-012 repair of the frozen recurrence). -/
noncomputable def legDirs (v₀ : Point) (R x : ℝ) : ℕ → Point
  | 0 => reflectDir (firstHit R x) v₀
  | k + 1 => reflectDir (hits v₀ R x (k + 1)) (legDirs v₀ R x k)

end

/-- The ray with incident coordinate `x` undergoes **at least `n`**
reflections on the mirror: its first `n` hit points all lie on the
reflective wall (the open upper semicircle). Reflections `1, …, n` are the
hits indexed `0, …, n − 1`. Once a hit lands at height `≤ 0` the physical
ray has left through the aperture, and all later hits of the underlying
circle orbit are immaterial: the predicate correctly fails from that index
onward, because a first crossing below height `0` occurs strictly before
the orbit angle can wind past `2π` (successive hit angles advance by
`2 · arccos (x / R) < π`). -/
def AtLeastNReflections (v₀ : Point) (R x : ℝ) (n : ℕ) : Prop :=
  ∀ k : ℕ, k < n → OnMirror R (hits v₀ R x k)

/-- The ray with incident coordinate `x` undergoes **at most `N`**
reflections: it does not undergo `N + 1` or more, i.e. one of its first
`N + 1` hit points fails to lie on the reflective wall. This matches the
counting used in the statement and in Fig. 2e, where `N` counts every
natural number `≥ 1` and every incident ray is reflected at least once
(the first hit always lies on the wall by `ValidIncident`). -/
def AtMostNReflections (v₀ : Point) (R x : ℝ) (N : ℕ) : Prop :=
  ¬ AtLeastNReflections v₀ R x (N + 1)

/-- The mirror is reflection-symmetric about the optical axis, so the
incident coordinate enters the reflection count only through `|x|`
(Fig. 2e shows even plateaus `±x₁, ±x₂, ±x₃`). Factoring this symmetry out
as a hypothesis keeps the model faithful to the figure without deciding
the dynamics; it also follows from `hits_angular_spec` together with
`sin ((2k+1) arccos (x/R)) = sin ((2k+1) arccos (−x/R))`, a consequence of
`arccos (−t) = π − arccos t` and the odd step `(2k + 1)`. -/
def CountSymmetric (v₀ : Point) (R : ℝ) : Prop :=
  ∀ x : ℝ, ValidIncident R x →
    ∀ n : ℕ, (AtLeastNReflections v₀ R x n ↔ AtLeastNReflections v₀ R (-x) n)

/-- **`x` lies inside the threshold `ξ`**: the ray with distance `|x|` from
the optical axis not exceeding `ξ` undergoes at most `N` reflections. -/
def InsideThreshold (v₀ : Point) (R ξ : ℝ) (N : ℕ) (x : ℝ) : Prop :=
  ValidIncident R x → |x| ≤ ξ → AtMostNReflections v₀ R x N

/-- **`x` lies strictly outside the threshold `ξ`**: any valid incident ray
farther than `ξ` from the optical axis undergoes more than `N` reflections,
i.e. at least `N + 1`. -/
def OutsideThreshold (v₀ : Point) (R ξ : ℝ) (N : ℕ) (x : ℝ) : Prop :=
  ValidIncident R x → ξ < |x| → AtLeastNReflections v₀ R x (N + 1)

/-- **Solution predicate (answer-free).**
`ξ` is the threshold `x_N` for the mirror of radius `R` and the allowed
reflection count `N`:

* `ξ` is positive and lies strictly below the mirror radius
  (Fig. 2e: `x_N` sits inside the open interval `(−R, R)`);
* every incident ray with `|x| ≤ ξ` undergoes at most `N` reflections;
* every incident ray with `ξ < |x| < R` undergoes at least `N + 1`
  reflections;
* the threshold is attained: the ray with `|x| = ξ` itself undergoes at
  most `N` reflections (Fig. 2e draws the steps closed at `±x_N`).

This is precisely "the **maximum** distance from the optical axis that
allows an incident ray to be reflected by the mirror at most `N` times":
the strict bound `ξ < R` keeps the outside pre-image nonempty, and the
attainment clause makes `ξ` a maximum, not merely a supremum.
No closed-form value of `ξ` is asserted here. -/
structure IsThreshold (v₀ : Point) (R ξ : ℝ) (N : ℕ) : Prop where
  /-- The threshold is a positive distance (Fig. 2e: `x_N > 0`). -/
  pos : 0 < ξ
  /-- The threshold lies strictly inside the mirror aperture
  (Fig. 2e: `x_N < R`; this also keeps the outside regime nonempty). -/
  lt_radius : ξ < R
  /-- Rays inside the threshold undergo at most `N` reflections. -/
  inside : ∀ x : ℝ, InsideThreshold v₀ R ξ N x
  /-- Rays beyond the threshold undergo at least `N + 1` reflections. -/
  outside : ∀ x : ℝ, OutsideThreshold v₀ R ξ N x
  /-- The threshold distance itself is attained: the ray at `|x| = ξ`
  still undergoes at most `N` reflections (closed step in Fig. 2e). -/
  attained : ∃ x : ℝ, ValidIncident R x ∧ |x| = ξ ∧ AtMostNReflections v₀ R x N

/-! ## Derivability bridges (spec-level facts about the model, to be proved)

The three lemmas below carry every nontrivial step from the geometric model
to the final existence-and-uniqueness statement. They are part of the
formalization surface (with `sorry` bodies) so that the later proving stage
can discharge them from the definitions without re-deriving the physics. -/


private lemma reflectDir_circle (c R θ φ : ℝ) (hR : R ≠ 0) :
    reflectDir (R * Real.cos θ, R * Real.sin θ)
        (c * Real.cos φ, c * Real.sin φ) =
      (c * Real.cos (2 * θ - φ + Real.pi), c * Real.sin (2 * θ - φ + Real.pi)) := by
  have hPR : dot (c * Real.cos φ, c * Real.sin φ) (R * Real.cos θ, R * Real.sin θ)
      = c * R * (Real.cos φ * Real.cos θ + Real.sin φ * Real.sin θ) := by
    simp [dot]; ring
  have hn : normSq (R * Real.cos θ, R * Real.sin θ) = R ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    simp [normSq, dot]; nlinarith
  have e1 : Real.cos (2 * θ - φ + Real.pi) =
      Real.cos φ - 2 * Real.cos θ * (Real.cos φ * Real.cos θ + Real.sin φ * Real.sin θ) := by
    have hpi : Real.cos (2 * θ - φ + Real.pi) = -Real.cos (2 * θ - φ) := Real.cos_add_pi _
    have h2c := Real.cos_two_mul θ
    have h2s := Real.sin_two_mul θ
    rw [hpi, Real.cos_sub, h2c, h2s]; ring
  have e2 : Real.sin (2 * θ - φ + Real.pi) =
      Real.sin φ - 2 * Real.sin θ * (Real.cos φ * Real.cos θ + Real.sin φ * Real.sin θ) := by
    have hpi : Real.sin (2 * θ - φ + Real.pi) = -Real.sin (2 * θ - φ) := Real.sin_add_pi _
    have h2c := Real.cos_two_mul θ
    have h2s := Real.sin_two_mul θ
    rw [hpi, Real.sin_sub, h2c, h2s]
    have h1 := Real.sin_sq_add_cos_sq θ
    have h3 : Real.cos θ ^ 2 * Real.sin φ = (1 - Real.sin θ ^ 2) * Real.sin φ := by
      have hh : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [h1]
      rw [hh]
    nlinarith [h1, h3]
  rw [reflectDir, sub, smul]
  apply Prod.ext
  · change c * Real.cos φ - (2 * dot (c * Real.cos φ, c * Real.sin φ)
        (R * Real.cos θ, R * Real.sin θ) / normSq (R * Real.cos θ, R * Real.sin θ)) *
        (R * Real.cos θ) = c * Real.cos (2 * θ - φ + Real.pi)
    rw [hPR, hn]
    have hrw : 2 * (c * R * (Real.cos φ * Real.cos θ + Real.sin φ * Real.sin θ)) / R ^ 2 *
        (R * Real.cos θ)
        = c * (2 * Real.cos θ * (Real.cos φ * Real.cos θ + Real.sin φ * Real.sin θ)) := by
      field_simp
    rw [hrw]
    linear_combination (-c) * e1
  · change c * Real.sin φ - (2 * dot (c * Real.cos φ, c * Real.sin φ)
        (R * Real.cos θ, R * Real.sin θ) / normSq (R * Real.cos θ, R * Real.sin θ)) *
        (R * Real.sin θ) = c * Real.sin (2 * θ - φ + Real.pi)
    rw [hPR, hn]
    have hrw : 2 * (c * R * (Real.cos φ * Real.cos θ + Real.sin φ * Real.sin θ)) / R ^ 2 *
        (R * Real.sin θ)
        = c * (2 * Real.sin θ * (Real.cos φ * Real.cos θ + Real.sin φ * Real.sin θ)) := by
      field_simp
    rw [hrw]
    linear_combination (-c) * e2

private lemma nextHit_circle (c R θ φ : ℝ) (hc : c ≠ 0) :
    nextHit (R * Real.cos θ, R * Real.sin θ)
        (c * Real.cos φ, c * Real.sin φ) =
      (R * Real.cos (2 * φ - θ + Real.pi), R * Real.sin (2 * φ - θ + Real.pi)) := by
  have hPv : dot (R * Real.cos θ, R * Real.sin θ) (c * Real.cos φ, c * Real.sin φ)
      = R * c * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ) := by
    simp [dot]; ring
  have hnv : normSq (c * Real.cos φ, c * Real.sin φ) = c ^ 2 := by
    have h := Real.sin_sq_add_cos_sq φ
    simp [normSq, dot]; nlinarith
  have e1 : Real.cos (2 * φ - θ + Real.pi) =
      Real.cos θ - 2 * Real.cos φ * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ) := by
    have hpi : Real.cos (2 * φ - θ + Real.pi) = -Real.cos (2 * φ - θ) := Real.cos_add_pi _
    have h2c := Real.cos_two_mul φ
    have h2s := Real.sin_two_mul φ
    rw [hpi, Real.cos_sub, h2c, h2s]
    have h1 := Real.sin_sq_add_cos_sq φ
    have h3 : Real.cos φ ^ 2 * Real.cos θ = (1 - Real.sin φ ^ 2) * Real.cos θ := by
      have hh : Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 := by linarith [h1]
      rw [hh]
    nlinarith [h1, h3]
  have e2 : Real.sin (2 * φ - θ + Real.pi) =
      Real.sin θ - 2 * Real.sin φ * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ) := by
    have hpi : Real.sin (2 * φ - θ + Real.pi) = -Real.sin (2 * φ - θ) := Real.sin_add_pi _
    have h2c := Real.cos_two_mul φ
    have h2s := Real.sin_two_mul φ
    rw [hpi, Real.sin_sub, h2c, h2s]
    have h1 := Real.sin_sq_add_cos_sq φ
    have h3 : Real.cos φ ^ 2 * Real.sin θ = (1 - Real.sin φ ^ 2) * Real.sin θ := by
      have hh : Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 := by linarith [h1]
      rw [hh]
    nlinarith [h1, h3]
  rw [nextHit, sub, smul]
  apply Prod.ext
  · change R * Real.cos θ - (2 * dot (R * Real.cos θ, R * Real.sin θ)
        (c * Real.cos φ, c * Real.sin φ) / normSq (c * Real.cos φ, c * Real.sin φ)) *
        (c * Real.cos φ) = R * Real.cos (2 * φ - θ + Real.pi)
    rw [hPv, hnv]
    have hrw : 2 * (R * c * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ)) / c ^ 2 *
        (c * Real.cos φ)
        = R * (2 * Real.cos φ * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ)) := by
      field_simp
    rw [hrw]
    linear_combination (-R) * e1
  · change R * Real.sin θ - (2 * dot (R * Real.cos θ, R * Real.sin θ)
        (c * Real.cos φ, c * Real.sin φ) / normSq (c * Real.cos φ, c * Real.sin φ)) *
        (c * Real.sin φ) = R * Real.sin (2 * φ - θ + Real.pi)
    rw [hPv, hnv]
    have hrw : 2 * (R * c * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ)) / c ^ 2 *
        (c * Real.sin φ)
        = R * (2 * Real.sin φ * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ)) := by
      field_simp
    rw [hrw]
    linear_combination (-R) * e2

/-- Joint induction companion of Bridges 1 and 2: the `k`-th hit sits at circle
angle `(2k + 1)·arccos (x/R)`, and the leg leaving it has direction angle
`π/2 + 2(k + 1)·arccos (x/R)`. `hits_angular_spec` resp.
`legDirs_angular_spec` project the two components. -/
private lemma orbit_spec
    (v₀ : Point) (hv₀ : AxisParallelIncident v₀) (R : ℝ) (hR : 0 < R)
    (x : ℝ) (hx : ValidIncident R x) (k : ℕ) :
    hits v₀ R x k =
      (R * Real.cos ((2 * (k : ℝ) + 1) * Real.arccos (x / R)),
       R * Real.sin ((2 * (k : ℝ) + 1) * Real.arccos (x / R))) ∧
    legDirs v₀ R x k =
      (v₀.2 * Real.cos (Real.pi / 2 + 2 * ((k : ℝ) + 1) * Real.arccos (x / R)),
       v₀.2 * Real.sin (Real.pi / 2 + 2 * ((k : ℝ) + 1) * Real.arccos (x / R))) := by
  obtain ⟨-, h1, h2⟩ := hv₀
  set c : ℝ := v₀.2 with hc
  have hcpos : 0 < c := h2
  have hcneq : c ≠ 0 := ne_of_gt hcpos
  have hv : v₀ = (c * Real.cos (Real.pi / 2), c * Real.sin (Real.pi / 2)) := by
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
    apply Prod.ext
    · change v₀.1 = c * 0
      rw [h1]; ring
    · change v₀.2 = c * 1
      rw [hc]; ring
  have hxR : x / R ∈ Set.Icc (-1) 1 := by
    rw [Set.mem_Icc]
    rw [ValidIncident] at hx
    have h1l : -1 * R ≤ x := by
      have := abs_le.mp (le_of_lt hx)
      linarith [this.1]
    have h1r : x ≤ 1 * R := by
      have := abs_le.mp (le_of_lt hx)
      linarith [this.2]
    constructor
    · rw [le_div_iff₀ hR]; exact h1l
    · rw [div_le_iff₀ hR]; exact h1r
  set α : ℝ := Real.arccos (x / R) with hα
  have hfh : firstHit R x = (R * Real.cos α, R * Real.sin α) := by
    apply Prod.ext
    · change x = R * Real.cos α
      rw [hα, Real.cos_arccos hxR.1 hxR.2]; field_simp
    · change Real.sqrt (R ^ 2 - x ^ 2) = R * Real.sin α
      rw [hα, Real.sin_arccos]
      rw [ValidIncident] at hx
      have hsq : R * Real.sqrt (1 - (x / R) ^ 2) = Real.sqrt (R ^ 2 - x ^ 2) := by
        have h2 : Real.sqrt (R ^ 2) = R := Real.sqrt_sq (le_of_lt hR)
        calc R * Real.sqrt (1 - (x / R) ^ 2)
            = Real.sqrt (R ^ 2) * Real.sqrt (1 - (x / R) ^ 2) := by rw [h2]
          _ = Real.sqrt (R ^ 2 * (1 - (x / R) ^ 2)) := by
              rw [Real.sqrt_mul (show (0:ℝ) ≤ R ^ 2 from sq_nonneg R)]
          _ = Real.sqrt (R ^ 2 - x ^ 2) := by
              congr 1
              field_simp
      rw [hsq]
  induction k with
  | zero =>
    constructor
    · show hits v₀ R x 0 = _
      rw [hits]
      rw [hfh]
      have e : (2 * ((0 : ℕ) : ℝ) + 1) * α = α := by norm_num
      rw [e]
    · show legDirs v₀ R x 0 = _
      rw [legDirs]
      rw [hv, hfh, reflectDir_circle c R α (Real.pi / 2) (ne_of_gt hR)]
      have e2 : Real.pi / 2 + 2 * (((0 : ℕ) : ℝ) + 1) * α =
          2 * α - Real.pi / 2 + Real.pi := by
        norm_num
        ring
      rw [e2]
  | succ k ih =>
    obtain ⟨ihh, ihl⟩ := ih
    have hstep : hits v₀ R x (k + 1) =
        (R * Real.cos (2 * (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) -
            ((2 * (k : ℝ) + 1) * α) + Real.pi),
         R * Real.sin (2 * (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) -
            ((2 * (k : ℝ) + 1) * α) + Real.pi)) := by
      rw [hits]
      rw [ihh, ihl, nextHit_circle c R _ _ hcneq]
    constructor
    · rw [hstep]
      have ecos : Real.cos ((2 * ((k + 1 : ℕ) : ℝ) + 1) * α) =
          Real.cos (2 * (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) - ((2 * (k : ℝ) + 1) * α) +
            Real.pi) := by
        have h2pi : 2 * (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) - ((2 * (k : ℝ) + 1) * α) + Real.pi =
            (2 * ((k + 1 : ℕ) : ℝ) + 1) * α + 2 * Real.pi := by
          have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [this]; ring
        rw [h2pi, Real.cos_add_two_pi]
      have esin : Real.sin ((2 * ((k + 1 : ℕ) : ℝ) + 1) * α) =
          Real.sin (2 * (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) - ((2 * (k : ℝ) + 1) * α) +
            Real.pi) := by
        have h2pi : 2 * (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) - ((2 * (k : ℝ) + 1) * α) + Real.pi =
            (2 * ((k + 1 : ℕ) : ℝ) + 1) * α + 2 * Real.pi := by
          have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [this]; ring
        rw [h2pi, Real.sin_add_two_pi]
      rw [ecos, esin]
    · rw [legDirs]
      conv_lhs => rw [hstep]
      rw [ihl, reflectDir_circle c R _ _ (ne_of_gt hR)]
      have ecos : Real.cos (Real.pi / 2 + 2 * ((((k + 1 : ℕ)) : ℝ) + 1) * α) =
          Real.cos (2 * (2 * (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) - ((2 * (k : ℝ) + 1) * α) +
            Real.pi) - (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) + Real.pi) := by
        have h2pi : 2 * (2 * (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) - ((2 * (k : ℝ) + 1) * α) +
              Real.pi) - (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) + Real.pi =
            Real.pi / 2 + 2 * ((((k + 1 : ℕ)) : ℝ) + 1) * α + (2 * Real.pi + 2 * Real.pi) := by
          have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [this]; ring
        rw [h2pi, ← add_assoc, Real.cos_add_two_pi, Real.cos_add_two_pi]
      have esin : Real.sin (Real.pi / 2 + 2 * ((((k + 1 : ℕ)) : ℝ) + 1) * α) =
          Real.sin (2 * (2 * (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) - ((2 * (k : ℝ) + 1) * α) +
            Real.pi) - (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) + Real.pi) := by
        have h2pi : 2 * (2 * (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) - ((2 * (k : ℝ) + 1) * α) +
              Real.pi) - (Real.pi / 2 + 2 * ((k : ℝ) + 1) * α) + Real.pi =
            Real.pi / 2 + 2 * ((((k + 1 : ℕ)) : ℝ) + 1) * α + (2 * Real.pi + 2 * Real.pi) := by
          have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [this]; ring
        rw [h2pi, ← add_assoc, Real.sin_add_two_pi, Real.sin_add_two_pi]
      rw [ecos, esin]

/-- **Bridge 1 — angular hit sequence.** Successive hit points advance along
the circle by the constant central angle `2 · arccos (x / R)`: the chord
between consecutive hits and the wall normal enclose the incidence angle
`arccos (x / R)`, so hit `k` sits at circle angle
`(2k + 1) · arccos (x / R)` measured from the `(R, 0)` rim direction.
For `k = 0` this is `firstHit`: `R (cos θ, sin θ)` with
`θ = arccos (x / R)` is `(x, √(R² − x²))` by `Real.cos_arccos` and
`Real.sin_arccos`; the induction step is the specular law `reflectDir`
composed with the chord intersection `nextHit`. -/
theorem hits_angular_spec
    (v₀ : Point) (hv₀ : AxisParallelIncident v₀) (R : ℝ) (hR : 0 < R)
    (x : ℝ) (hx : ValidIncident R x) (k : ℕ) :
    hits v₀ R x k =
      (R * Real.cos ((2 * (k : ℝ) + 1) * Real.arccos (x / R)),
       R * Real.sin ((2 * (k : ℝ) + 1) * Real.arccos (x / R))) := by
  exact (orbit_spec v₀ hv₀ R hR x hx k).1

/-- **Bridge 2 — reflected leg directions.** The leg leaving hit `k` has
constant length `v₀.2` (specular reflection is a linear isometry) and
direction angle `π / 2 + 2 (k + 1) · arccos (x / R)`. Together with
Bridge 1 this pins down the entire orbit: `hits_angular_spec` and
`legDirs_angular_spec` are mutual induction companions. -/
theorem legDirs_angular_spec
    (v₀ : Point) (hv₀ : AxisParallelIncident v₀) (R : ℝ) (hR : 0 < R)
    (x : ℝ) (hx : ValidIncident R x) (k : ℕ) :
    legDirs v₀ R x k =
      (v₀.2 * Real.cos (Real.pi / 2 + 2 * ((k : ℝ) + 1) * Real.arccos (x / R)),
       v₀.2 * Real.sin (Real.pi / 2 + 2 * ((k : ℝ) + 1) * Real.arccos (x / R))) := by
  exact (orbit_spec v₀ hv₀ R hR x hx k).2

/-- **Bridge 3 — wall membership is sine positivity.** Hit `k` lies on the
reflective wall exactly when its circle angle has positive sine:
`OnMirror R (hits … k) ↔ 0 < sin ((2k + 1) · arccos (x / R))`. This is the
harmless unfolding of `OnMirror` along Bridge 1
(`Real.cos_sq_add_sin_sq` supplies the radius equation), and it converts
the geometric counting predicates into arithmetic statements about the
angle arithmetic progression. -/
theorem hits_onMirror_iff
    (v₀ : Point) (hv₀ : AxisParallelIncident v₀) (R : ℝ) (hR : 0 < R)
    (x : ℝ) (hx : ValidIncident R x) (k : ℕ) :
    OnMirror R (hits v₀ R x k) ↔
      0 < Real.sin ((2 * (k : ℝ) + 1) * Real.arccos (x / R)) := by
  rw [hits_angular_spec v₀ hv₀ R hR x hx k]
  constructor
  · intro h
    have h2 := h.2
    change 0 < R * Real.sin ((2 * (k : ℝ) + 1) * Real.arccos (x / R)) at h2
    exact (mul_pos_iff_of_pos_left hR).mp h2
  · intro h
    refine ⟨?_, ?_⟩
    · show normSq (R * Real.cos ((2 * (k : ℝ) + 1) * Real.arccos (x / R)),
          R * Real.sin ((2 * (k : ℝ) + 1) * Real.arccos (x / R))) = R ^ 2
      have h1 := Real.sin_sq_add_cos_sq ((2 * (k : ℝ) + 1) * Real.arccos (x / R))
      simp [normSq, dot]
      nlinarith [h1]
    · show 0 < (R * Real.cos ((2 * (k : ℝ) + 1) * Real.arccos (x / R)),
          R * Real.sin ((2 * (k : ℝ) + 1) * Real.arccos (x / R))).2
      change 0 < R * Real.sin ((2 * (k : ℝ) + 1) * Real.arccos (x / R))
      exact mul_pos hR h

/-- **Bridge 4 — angular characterization of the reflection count.**
"At most `N` reflections" is equivalent to the threshold-angle inequality
`π / (2N + 1) ≤ arccos (|x| / R)`.

*Proof route carried by this contract.* By symmetry (`CountSymmetric`, or
`arccos (−t) = π − arccos t` with the odd progression step) take `x ≥ 0`
and set `α = arccos (x / R) ∈ (0, π/2]`. By Bridge 3,
`AtLeastNReflections v₀ R x (N + 1)` says `sin ((2k + 1) α) > 0` for all
`k ≤ N`; since the angles `(2k + 1) α` are positive, increasing, and spaced
`2α < π` apart, that happens iff `(2N + 1) α < π`: if `(2N + 1) α ≥ π` then
the *first* index `j ≤ N` with `(2j + 1) α ≥ π` still has
`(2j + 1) α < π + 2α ≤ 2π`, so its sine is `≤ 0`
(`Real.sin_nonpos_of_nonnpos_of_neg_pi_le`, `Real.sin_pos_of_pos_of_lt_pi`
are the Mathlib carriers). Negating both sides gives the `AtMost` form.

This lemma is the entire combinatorial content of the problem; the closed
form itself is still nowhere asserted — extracting the witness only uses
strict antitonicity of `Real.arccos` on `Set.Icc (-1) 1`
(`Real.strictAntiOn_arccos`) applied to the endpoint
`arccos (|x| / R) = π / (2N + 1)`. -/
theorem threshold_angular_characterization
    (v₀ : Point) (hv₀ : AxisParallelIncident v₀) (R : ℝ) (hR : 0 < R)
    (hsymm : CountSymmetric v₀ R)
    (N : ℕ) (x : ℝ) (hx : ValidIncident R x) :
    AtMostNReflections v₀ R x N ↔
      Real.pi / (2 * (N : ℝ) + 1) ≤ Real.arccos (|x| / R) := by
  -- Reduce to the nonnegative coordinate `y = |x|` via the mirror symmetry.
  have hN1 : 0 < (N : ℝ) + 1 := by positivity
  have hs : AtLeastNReflections v₀ R x (N + 1) ↔
      AtLeastNReflections v₀ R |x| (N + 1) := by
    rcases lt_or_ge x 0 with hxn | hxp
    · have h := hsymm x hx (N + 1)
      rw [abs_of_neg hxn]
      exact h
    · rw [abs_of_nonneg hxp]
  have hyv : ValidIncident R |x| := by
    unfold ValidIncident
    rwa [abs_abs]
  have hyv2 : |x| < R := by
    unfold ValidIncident at hyv
    rwa [abs_abs] at hyv
  -- The aperture angle `α = arccos (|x| / R)` of the chord midpoint.
  set α : ℝ := Real.arccos (|x| / R) with hα
  have hyR : |x| / R ∈ Set.Icc (-1) 1 := by
    rw [Set.mem_Icc]
    have hnn : 0 ≤ |x| / R := div_nonneg (abs_nonneg x) (le_of_lt hR)
    refine ⟨le_trans (by norm_num : (-1:ℝ) ≤ 0) hnn, ?_⟩
    rw [div_le_one hR]
    exact le_of_lt hyv2
  have hα0 : 0 < α := by
    have hlt : |x| / R < 1 := by
      rw [div_lt_one hR]
      exact hyv2
    have hanti := Real.strictAntiOn_arccos
    have hm := hanti hyR (Set.mem_Icc.mpr ⟨by norm_num, le_refl 1⟩) hlt
    rw [Real.arccos_one] at hm
    exact hm
  have hα0' : 0 ≤ α := le_of_lt hα0
  have hα2 : α ≤ Real.pi / 2 := by
    rw [Real.arccos_le_pi_div_two]
    exact (div_nonneg (abs_nonneg x) (le_of_lt hR))
  have hαlt : α < Real.pi := lt_of_le_of_lt hα2 (by
    have := Real.pi_pos
    linarith [Real.pi_pos])
  have h2α : 2 * α ≤ Real.pi := by linarith [hα2]
  have hstep_pos : ∀ j : ℕ, (0:ℝ) < (2 * (j : ℝ) + 1) * α := by
    intro j
    have h1r : (0:ℝ) < 2 * (j : ℝ) + 1 := by positivity
    exact mul_pos h1r hα0
  have hmono : StrictMono (fun j : ℕ => (2 * (j : ℝ) + 1) * α) := by
    intro a b hab
    have : (2:ℝ) * (a : ℝ) + 1 < 2 * (b : ℝ) + 1 := by
      have := mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hab) (by norm_num : (0:ℝ) < 2)
      linarith
    exact mul_lt_mul_of_pos_right this hα0
  -- The counting characterization: at least N+1 reflections ↔ (2N+1)α < π.
  have hkey : AtLeastNReflections v₀ R |x| (N + 1) ↔
      (2 * (N : ℝ) + 1) * α < Real.pi := by
    constructor
    · intro hcount
      by_contra hbad
      push Not at hbad
      -- Minimal index whose angle reaches π; supplied by the endpoint bound.
      have h_cross_ex : ∃ j : ℕ, j ≤ N ∧ Real.pi ≤ (2 * (j : ℝ) + 1) * α :=
        ⟨N, le_refl N, hbad⟩
      have hex : ∃ j : ℕ, j ≤ N ∧ Real.sin ((2 * (j : ℝ) + 1) * α) ≤ 0 := by
        have hj₀spec := Nat.find_spec h_cross_ex
        set j₀ := Nat.find h_cross_ex with hj₀
        obtain ⟨hj₀N, hj₀pi⟩ := hj₀spec
        refine ⟨j₀, hj₀N, ?_⟩
        -- the crossing happens strictly between π and 2π.
        have hj0pos : j₀ ≠ 0 := by
          intro h0
          rw [h0] at hj₀pi
          have hsimp : (2 * ((0:ℕ) : ℝ) + 1) * α = α := by norm_num
          rw [hsimp] at hj₀pi
          exact not_lt.mpr hj₀pi hαlt
        obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero hj0pos
        have hprev : ¬ (j' ≤ N ∧ Real.pi ≤ (2 * (j' : ℝ) + 1) * α) :=
          Nat.find_min h_cross_ex (by omega : j' < j₀)
        have hplt : (2 * (j' : ℝ) + 1) * α < Real.pi := by
          by_contra hnn2
          push Not at hnn2
          have hle : j' ≤ N := by omega
          exact hprev ⟨hle, hnn2⟩
        -- (2j₀+1)α = (2j'+1)α + 2α < π + π = 2π, while ≥ π.
        have hθge : Real.pi ≤ (2 * (j₀ : ℝ) + 1) * α := hj₀pi
        have hθlt : (2 * (j₀ : ℝ) + 1) * α < 2 * Real.pi := by
          have hsplit : (2 * (j₀ : ℝ) + 1) * α = (2 * (j' : ℝ) + 1) * α + 2 * α := by
            rw [hj']; push_cast; ring
          rw [hsplit]
          linarith [hplt, h2α]
        have hθpos : 0 < (2 * (j₀ : ℝ) + 1) * α := hstep_pos j₀
        -- sin(θ) = -sin(2π - θ) ≤ 0 as 0 < 2π - θ < π.
        have hsineq : Real.sin ((2 * (j₀ : ℝ) + 1) * α) =
            -Real.sin (2 * Real.pi - (2 * (j₀ : ℝ) + 1) * α) := by
          have h1 : Real.sin ((2 * (j₀ : ℝ) + 1) * α) =
              Real.sin ((2 * (j₀ : ℝ) + 1) * α - 2 * Real.pi) := by
            rw [← Real.sin_add_two_pi ((2 * (j₀ : ℝ) + 1) * α - 2 * Real.pi)]
            ring_nf
          have h2 : Real.sin ((2 * (j₀ : ℝ) + 1) * α - 2 * Real.pi) =
              -Real.sin (2 * Real.pi - (2 * (j₀ : ℝ) + 1) * α) := by
            rw [← Real.sin_neg]
            ring_nf
          rw [h1, h2]
        rw [hsineq]
        have hpos : 0 ≤ Real.sin (2 * Real.pi - (2 * (j₀ : ℝ) + 1) * α) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr (le_of_lt hθlt))
            (by linarith [hj₀pi, Real.pi_pos])
        linarith [hpos]
      obtain ⟨j, hjN, hjsin⟩ := hex
      have hbad2 := hcount j (Nat.lt_succ_of_le hjN)
      rw [hits_onMirror_iff v₀ hv₀ R hR |x| hyv j] at hbad2
      exact (not_le.mpr hbad2) hjsin
    · intro hpi k hkN
      rw [hits_onMirror_iff v₀ hv₀ R hR |x| hyv k]
      have hlt : (2 * (k : ℝ) + 1) * α < Real.pi :=
        calc (2 * (k : ℝ) + 1) * α
            ≤ (2 * (N : ℝ) + 1) * α := by
              apply mul_le_mul_of_nonneg_right _ hα0'
              have hle : k ≤ N := Nat.lt_succ_iff.mp hkN
              have hkr : (k : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hle
              linarith [hkr]
          _ < Real.pi := hpi
      exact Real.sin_pos_of_pos_of_lt_pi (hstep_pos k) hlt
  -- Negation: at most N reflections ↔ (2N+1)α ≥ π.
  rw [AtMostNReflections, hs]
  constructor
  · intro h
    by_contra hb
    push Not at hb
    have hpos : (0:ℝ) < 2 * (N : ℝ) + 1 := by positivity
    have hb' : (2 * (N : ℝ) + 1) * α < Real.pi := by
      have hb2 := (lt_div_iff₀ hpos).mp hb
      linarith [hb2]
    exact h (hkey.mpr hb')
  · intro h hc
    have := hkey.mp hc
    have hpos : (0:ℝ) < 2 * (N : ℝ) + 1 := by positivity
    have hge : Real.pi ≤ (2 * (N : ℝ) + 1) * α := by
      have hg2 := (div_le_iff₀ hpos).mp h
      linarith [hg2]
    linarith [this, hge]

/-- **IPhO 2026, T2-A1 (answer-blind).**
For a half-cylindrical mirror of positive radius `R` illuminated by
parallel rays traveling along the optical axis and entering through the
aperture (Fig. 2a), and for every positive integer `N`, there exists a
unique positive distance `x_N < R` which is the largest transverse
coordinate for which an incident ray undergoes at most `N` specular
reflections on the mirror (Fig. 2e).

The theorem only asserts the existence and uniqueness of this threshold:
the requested general expression for `x_N` in terms of `R` and `N` is the
unique witness, to be constructed by the prover — the natural route is
Bridge 4 plus strict antitonicity of `Real.arccos` on `[−1, 1]`, with the
boundary ray `|x| = x_N` reflecting exactly `N` times and exiting through
the rim (sin `= 0` at index `N`). The value `x_N` itself appears in no
signature. -/
theorem problem_IPhO_2026_2_A_1
    (v₀ : Point) (hv₀ : AxisParallelIncident v₀) (R : ℝ) (hR : 0 < R)
    (hsymm : CountSymmetric v₀ R)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃! ξ : ℝ, IsThreshold v₀ R ξ N := by
    -- The candidate threshold distance `ξ = R · cos β` with `β = π / (2N + 1)`.
    have hNpos : (0:ℝ) < 2 * (N : ℝ) + 1 := by
      have h1 : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      nlinarith
    set β : ℝ := Real.pi / (2 * (N : ℝ) + 1) with hβ
    have hβpos : 0 < β := div_pos Real.pi_pos hNpos
    have hβlt : β < Real.pi / 2 := by
      have hN3 : (2:ℝ) ≤ 2 * (N : ℝ) + 1 := by
        have h1 : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        nlinarith
      have hN3s : (3:ℝ) ≤ 2 * (N : ℝ) + 1 := by
        have h1 : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        nlinarith
      rw [hβ, div_lt_iff₀ hNpos]
      nlinarith [Real.pi_pos, hN3s]
    have hβle : β ≤ Real.pi / 2 := le_of_lt hβlt
    have hβmem : β ∈ Set.Icc 0 Real.pi :=
      ⟨le_of_lt hβpos, by nlinarith [Real.pi_pos, hβle]⟩
    have hcos_pos : 0 < Real.cos β :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, hβpos], hβlt⟩
    have hcos_lt_one : Real.cos β < 1 := by
      have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ) ≤ 0 from le_refl 0)
        (le_trans hβle (by nlinarith [Real.pi_pos])) hβpos
      rwa [Real.cos_zero] at h2
    set ξ : ℝ := R * Real.cos β with hξ
    have hξpos : 0 < ξ := mul_pos hR hcos_pos
    have hξlt : ξ < R := by
      have h2 := mul_lt_mul_of_pos_left hcos_lt_one hR
      rwa [mul_one] at h2
    have harccos_cos : Real.arccos (Real.cos β) = β :=
      Real.arccos_cos hβmem.1 hβmem.2
    have hξth : IsThreshold v₀ R ξ N := by
      refine ⟨hξpos, hξlt, ?_, ?_, ?_⟩
      · -- inside: rays with |x| ≤ ξ undergo at most N reflections
        intro x hxv hxξ
        rw [threshold_angular_characterization v₀ hv₀ R hR hsymm N x hxv]
        have hxR : |x| / R ≤ Real.cos β := by
          rw [div_le_iff₀ hR]
          calc |x| ≤ ξ := hxξ
            _ = Real.cos β * R := by ring
        have h2 := Real.arccos_le_arccos (show |x| / R ≤ Real.cos β from hxR)
        rwa [harccos_cos] at h2
      · -- outside: rays with ξ < |x| < R undergo at least N + 1 reflections
        intro x hxv hξx
        by_contra hcontra
        have ham : AtMostNReflections v₀ R x N := hcontra
        rw [threshold_angular_characterization v₀ hv₀ R hR hsymm N x hxv] at ham
        have hlt : Real.arccos (|x| / R) < β := by
          have hxr : Real.cos β < |x| / R := by
            rw [lt_div_iff₀ hR]
            calc Real.cos β * R = ξ := by ring
              _ < |x| := hξx
          have hxv2 : |x| < R := hxv
          have hb1 : |x| / R ≤ 1 := by
            rw [div_le_one hR]; exact le_of_lt hxv2
          have hb2 : -1 ≤ |x| / R :=
            le_trans (by norm_num : (-1:ℝ) ≤ 0) (div_nonneg (abs_nonneg x) (le_of_lt hR))
          have h2 := Real.strictAntiOn_arccos ⟨Real.neg_one_le_cos β, le_of_lt hcos_lt_one⟩
            ⟨hb2, hb1⟩ hxr
          rwa [harccos_cos] at h2
        exact not_lt.mpr ham hlt
      · -- attained at x = ξ
        refine ⟨ξ, ?_, ?_, ?_⟩
        · change |ξ| < R
          rw [abs_of_pos hξpos]; exact hξlt
        · rw [abs_of_pos hξpos]
        · have hξv : ValidIncident R ξ := by
            change |ξ| < R
            rw [abs_of_pos hξpos]; exact hξlt
          rw [threshold_angular_characterization v₀ hv₀ R hR hsymm N ξ hξv]
          have her : |ξ| / R = Real.cos β := by
            rw [abs_of_pos hξpos, hξ]
            field_simp
          rw [her, harccos_cos]
    refine ⟨ξ, hξth, ?_⟩
    · -- uniqueness: any other threshold equals ξ
      intro ξ' hξ'
      rcases lt_trichotomy ξ ξ' with hlt | heq | hgt
      · have h1 : ValidIncident R ξ' := by
          change |ξ'| < R
          rw [abs_of_pos hξ'.pos]; exact hξ'.lt_radius
        have hAtMost := hξ'.inside ξ' h1 (by rw [abs_of_pos hξ'.pos])
        have hAtLeast := hξth.outside ξ' h1 (by rw [abs_of_pos hξ'.pos]; exact hlt)
        exact (hAtMost hAtLeast).elim
      · exact heq.symm
      · have h1 : ValidIncident R ξ := by
          change |ξ| < R
          rw [abs_of_pos hξpos]; exact hξlt
        have hAtMost := hξth.inside ξ h1 (by rw [abs_of_pos hξpos])
        have hAtLeast := hξ'.outside ξ h1 (by rw [abs_of_pos hξpos]; exact hgt)
        exact (hAtMost hAtLeast).elim


end PartA1
end IPhO_2026_2
