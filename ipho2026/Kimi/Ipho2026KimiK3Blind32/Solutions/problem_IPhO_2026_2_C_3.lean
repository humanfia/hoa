import Mathlib

/-!
# IPhO 2026, Problem 2 (T2), Part C.3 — Caustics and Cusp

Answer-blind formalization of subquestion T2-C3 (1.0 pts):

> Find the coordinates of the point of intersection `(X_c, Y_c)` between the
> reflected rays of `A` and `B` (as `B` neighboring `A`).  Write your answer
> in terms of `R` and `θ`.

## Physical setting (from Figure 2g and parts C.1–C.2 of the statement)

* The mirror is the upper half of the circle of radius `R` centred at the
  origin; its diameter endpoints are labelled `−R` and `R` on the `x`-axis.
* Ray `A` is vertical (parallel to the `y`-axis), travelling downward
  (`dir = (0, −1)`), and strikes the mirror at the point
  `P_A = (R sin θ, R cos θ)`, where `θ ∈ (0, π/2)` is the incidence angle
  measured from the radial outward normal `P_A` (dashed in Figure 2g).
* After specular reflection the ray `A` travels along the line
  `y = m_A x + b_A` (part C.1).  A neighbouring vertical ray `B`, parallel to
  `A`, strikes the mirror at incidence angle `θ + Δθ` with `Δθ ≪ θ`, and its
  reflected line is `y = m_B x + b_B`, with `m_B, b_B` given to first order
  in `Δθ` (part C.2).
* Part C.3 asks for the *limiting* intersection point `(X_c, Y_c)` of the
  reflected lines of `A` and `B` as the angular separation `Δθ → 0`; the
  collection of these limiting points over `θ` is the **caustic** of the
  mirror.

## Answer-blind policy

The official answer `(X_c, Y_c) = (…, …)` in terms of `R` and `θ` is
withheld.  Following the project policy, the requested closed form is kept
out of the theorem signature: we define a physically meaningful solution
predicate — the *limiting intersection point* of the reflected lines of the
neighbouring rays as their angular separation tends to zero — and state the
problem as the existence and uniqueness of such a point.  The concrete
witness (the closed form in terms of `R` and `θ`) will be constructed by the
prover stage as the witness of the `∃!`.

## The limiting-intersection characterization used here

Two distinct reflected lines `y = m_A x + b_A` and `y = m_B x + b_B` meet at
`x = (b_B − b_A)/(m_A − m_B)`.  As `Δθ → 0`, both `m_B → m_A` and `b_B → b_A`
(smoothness of the reflection law), so naively this is `0/0`; the meaningful
limit is the quotient of first-order increments,

    X_c = −(d b/dθ)/(d m/dθ)  at θ,     Y_c = m_A · X_c + b_A,

i.e. the unique point of the reflected line of `A` at which the directional
derivative of the line's height function `θ ↦ m(θ) · x + b(θ)` vanishes.
This is precisely the caustic/envelope characterization: the reflected ray is
tangent to the caustic at `(X_c, Y_c)`.  We formalize the limiting
intersection as the unique point of the reflected line of `A` where the
θ-derivative of the line height `x ↦ m(θ) x + b(θ)` vanishes — the
`deriv`-equalizing intersection — and state the problem as existence and
uniqueness of that point.  The concrete witness `(X_c, Y_c)(R, θ)` is kept
out of every signature; the prover stage constructs it.

The first-order content of part C.2 is injected answer-blind as the
hypothesis that the reflected slope/intercept law is differentiable in θ
(`ReflectedRayLawSmooth`), which is exactly the content of C.2 used by C.3.
-/

noncomputable section

namespace IPhO2026P2C3

open Real Set Filter

/-- The plane of Figure 2g, with origin at the centre of the half-cylinder,
the `x`-axis along the diameter labelled `−R, R`, and the `y`-axis upward. -/
abbrev MirrorPlane := Fin 2 → ℝ

/-- A half-cylindrical mirror of Figure 2g: radius `R > 0`, centre at the
origin, reflecting arc `{(x, y) : x² + y² = R², y > 0}`. -/
structure HalfCylindricalMirror where
  /-- Radius `R` of the mirror. -/
  R : ℝ
  /-- A physical mirror has positive radius. -/
  R_pos : 0 < R

/-- The incidence/reflection point of a ray incident at angle `θ` from the
radial normal, as read from Figure 2g: `(R sin θ, R cos θ)`. -/
def incidencePoint (G : HalfCylindricalMirror) (θ : ℝ) : MirrorPlane :=
  ![G.R * Real.sin θ, G.R * Real.cos θ]

/-- The radial outward unit normal to the mirror at incidence angle `θ`:
the direction of `incidencePoint G θ` itself, `(sin θ, cos θ)`. -/
def outwardNormal (_G : HalfCylindricalMirror) (θ : ℝ) : MirrorPlane :=
  ![Real.sin θ, Real.cos θ]

/-- Specular reflection at the mirror: the incident direction `i` and the
reflected direction `r` make equal angles with the normal `n` with reversed
normal component; with `i` pointing into the surface and `r` away, equal
angles about `n` give `⟨r − i, n⟩ = 2 ⟨r, n⟩` componentwise, and reflection
preserves `‖·‖²` (speed of light). -/
def IsSpecularReflection (n i r : MirrorPlane) : Prop :=
  (∑ j : Fin 2, (r - i) j * n j = 2 * ∑ j : Fin 2, r j * n j) ∧
    ∑ j : Fin 2, r j * r j = ∑ j : Fin 2, i j * i j

/-- A concrete law-of-reflection model for Figure 2g: for every incidence
angle `θ` in the physical range `(0, π/2)`, the reflected line of the
vertical incident ray is the graph `y = m θ · x + b θ` through the incidence
point, with `m θ, b θ` delivered by the law.  This is the C.1 data, kept
answer-blind: `slopeIntercept θ` is *some* pair for which specular reflection
holds; its closed form is the withheld answer of C.1. -/
structure ReflectedRayLaw (G : HalfCylindricalMirror) where
  /-- Reflected slope–intercept data as a function of the incidence angle. -/
  slopeIntercept : ℝ → ℝ × ℝ
  /-- Specular-reflection content: at every physical incidence angle the
  delivered line passes through the incidence point and its direction
  `![1, m]` is the specular reflection of the downward vertical `![0, −1]`
  about the outward normal. -/
  reflected_isSpecular :
    ∀ θ ∈ Ioo 0 (Real.pi / 2),
      (incidencePoint G θ 1 =
          (slopeIntercept θ).1 * incidencePoint G θ 0 + (slopeIntercept θ).2) ∧
        IsSpecularReflection (outwardNormal G θ) ![0, -1] ![1, (slopeIntercept θ).1]

namespace ReflectedRayLaw

variable {G : HalfCylindricalMirror} (law : ReflectedRayLaw G)

/-- Slope `m θ` of the reflected ray at incidence angle `θ`. -/
def slope (θ : ℝ) : ℝ := (law.slopeIntercept θ).1

/-- Intercept `b θ` of the reflected ray at incidence angle `θ`. -/
def intercept (θ : ℝ) : ℝ := (law.slopeIntercept θ).2

/-- The reflected line at incidence angle `θ`, as the height function
`x ↦ m θ · x + b θ`. -/
def lineHeight (θ x : ℝ) : ℝ := law.slope θ * x + law.intercept θ

/-- A point `(x, y)` lies on the reflected line at incidence angle `θ`. -/
def OnReflectedLine (θ x y : ℝ) : Prop := y = law.lineHeight θ x

end ReflectedRayLaw

/-- The physical smoothness of the reflection law underlying parts C.1–C.2
(the content of C.1–C.2 used by C.3): the reflected slope and intercept are
differentiable in the incidence angle on the physical range.  This is the
answer-blind stand-in for the C.1 closed form and the C.2 first-order
expansion; its witnesses are exactly the derivatives that appear in the C.3
limiting intersection. -/
structure ReflectedRayLawSmooth (G : HalfCylindricalMirror)
    (law : ReflectedRayLaw G) where
  /-- `θ ↦ m θ` is differentiable on `(0, π/2)`. -/
  slope_differentiable :
    ∀ θ ∈ Ioo 0 (Real.pi / 2), DifferentiableAt ℝ law.slope θ
  /-- `θ ↦ b θ` is differentiable on `(0, π/2)`. -/
  intercept_differentiable :
    ∀ θ ∈ Ioo 0 (Real.pi / 2), DifferentiableAt ℝ law.intercept θ
  /-- The reflected slope is strictly monotone on the physical band — the
  reflected rays fan out (`m` strictly decreasing here, as in Figure 2g).
  Equivalently the derivative of the slope does not vanish on `(0, π/2)`,
  which is what makes the limiting intersection well-defined and finite. -/
  slope_deriv_ne_zero :
    ∀ θ ∈ Ioo 0 (Real.pi / 2), deriv law.slope θ ≠ 0

/-- **Set-up for T2-C3.**  The full physical context: a half-cylindrical
mirror `G` with reflection law `law` (C.1 data) that is differentiable in the
incidence angle (C.2 content), the incidence angle `θ` of ray `A` in the
physical range, and the reflected line `y = m_A x + b_A` of ray `A`. -/
structure CausticContext where
  /-- The half-cylindrical mirror. -/
  G : HalfCylindricalMirror
  /-- Reflection law (C.1 data), answer-blind. -/
  law : ReflectedRayLaw G
  /-- Smoothness/first-order content (C.2), answer-blind. -/
  law_smooth : ReflectedRayLawSmooth G law
  /-- Incidence angle `θ` of ray `A`. -/
  θ : ℝ
  /-- Physical range of `θ` (Figure 2g regime). -/
  θ_mem : θ ∈ Ioo 0 (Real.pi / 2)

namespace CausticContext

variable (C : CausticContext)

/-- Slope `m_A` of the reflected ray of `A`. -/
def mA : ℝ := C.law.slope C.θ

/-- Intercept `b_A` of the reflected ray of `A`. -/
def bA : ℝ := C.law.intercept C.θ

/-- A point `(x, y)` lies on the reflected line of ray `A`. -/
def OnLineA (x y : ℝ) : Prop := C.law.OnReflectedLine C.θ x y

/-- **Limiting-intersection predicate.**  A point `(X_c, Y_c)` of the plane
is the limiting intersection of the reflected rays of `A` and `B` as the
angular separation `Δθ → 0` iff

* it lies on the reflected line of `A`, `Y_c = m_A X_c + b_A`, and
* at `x = X_c` the θ-derivative of the reflected-line height vanishes,
  `deriv (fun φ ↦ lineHeight φ X_c) θ = 0`.

The second condition is exactly the statement that `X_c` is the limit of the
intersection abscissa `(b(θ + Δθ) − b θ)/(m θ − m(θ + Δθ))` as `Δθ → 0`: both
numerator and denominator are `O(Δθ)`, and l'Hôpital/difference-quotient
limit is `−b'(θ)/m'(θ)`, which is the unique solution `x` of
`deriv (fun φ ↦ lineHeight φ x) θ = 0` (a finite limit since `m'(θ) ≠ 0` by
`ReflectedRayLawSmooth.slope_deriv_ne_zero`).  Physically this is the point
where the reflected ray of `A` touches the caustic. -/
def IsLimitingIntersection (Xc Yc : ℝ) : Prop :=
  C.OnLineA Xc Yc ∧
    deriv (fun φ ↦ C.law.lineHeight φ Xc) C.θ = 0

/-- **Solution predicate for T2-C3**, answer-blind: `(X_c, Y_c)` are the
coordinates of the limiting intersection point of the reflected rays of `A`
and of the neighbouring ray `B` as the angular separation `Δθ` tends to `0`,
where `A` is incident at angle `θ` on the half-cylindrical mirror `G` and
`B`, parallel to `A`, is incident at `θ + Δθ`. -/
def SolutionC3 (Xc Yc : ℝ) : Prop := C.IsLimitingIntersection Xc Yc

/-- **T2-C3, formalized target (existence and uniqueness).**  There is a
unique point `(X_c, Y_c)` of the plane that is the limiting intersection of
the reflected rays of `A` and of the neighbouring parallel ray `B` as the
angular separation tends to zero.  The concrete coordinates `(X_c, Y_c)` in
terms of `R` and `θ` are *not* in the signature; the prover stage constructs
the witness `X_c = −(deriv b θ)/(deriv m θ)`, `Y_c = m_A X_c + b_A`, whose
existence is guaranteed by `m'(θ) ≠ 0` and uniqueness by the affinity of the
line height in `x`. -/
theorem exists_unique_limiting_intersection :
    ∃! p : MirrorPlane, C.SolutionC3 (p 0) (p 1) := by
  -- The slope θ-derivative is nonzero by the smoothness content of C.2,
  -- so the derivative ratio below is a genuine real number.
  have hm' : deriv C.law.slope C.θ ≠ 0 :=
    C.law_smooth.slope_deriv_ne_zero C.θ C.θ_mem
  -- Both slope and intercept are differentiable at θ (content of C.1–C.2).
  have hdm : DifferentiableAt ℝ C.law.slope C.θ :=
    C.law_smooth.slope_differentiable C.θ C.θ_mem
  have hdb : DifferentiableAt ℝ C.law.intercept C.θ :=
    C.law_smooth.intercept_differentiable C.θ C.θ_mem
  -- The witness: the derivative-ratio abscissa `X_c = −b'(θ)/m'(θ)` and the
  -- reflected-line ordinate `Y_c = m_A X_c + b_A`.
  refine ⟨![-(deriv C.law.intercept C.θ) / deriv C.law.slope C.θ,
      C.law.slope C.θ * (-(deriv C.law.intercept C.θ) / deriv C.law.slope C.θ)
        + C.law.intercept C.θ], ?_, ?_⟩
  · -- The witness is a limiting intersection: it lies on the reflected line
    -- of `A`, and the θ-derivative of the line height vanishes at `X_c`.
    refine ⟨rfl, ?_⟩
    -- Reduce the vector application `![Xc, Yc] 0` to `Xc`.
    change deriv (fun φ ↦ C.law.lineHeight φ
          (-(deriv C.law.intercept C.θ) / deriv C.law.slope C.θ)) C.θ = 0
    -- The derivative of the affine-in-x line height is `m'(θ) x + b'(θ)`.
    have hder :
        deriv (fun φ ↦ C.law.lineHeight φ
          (-(deriv C.law.intercept C.θ) / deriv C.law.slope C.θ)) C.θ =
          deriv C.law.slope C.θ *
              (-(deriv C.law.intercept C.θ) / deriv C.law.slope C.θ)
            + deriv C.law.intercept C.θ := by
      have hd :
          deriv ((fun φ ↦ C.law.slope φ *
              (-(deriv C.law.intercept C.θ) / deriv C.law.slope C.θ))
            + C.law.intercept) C.θ =
          deriv C.law.slope C.θ *
              (-(deriv C.law.intercept C.θ) / deriv C.law.slope C.θ)
            + deriv C.law.intercept C.θ := by
        rw [deriv_add (hdm.mul_const _) hdb, deriv_mul_const hdm]
      exact hd
    rw [hder]
    field_simp
    ring
  · -- Uniqueness: any limiting intersection has the derivative-ratio
    -- abscissa and lies on the reflected line of `A`.
    intro q hq
    obtain ⟨hqline, hqderiv⟩ := hq
    have hder :
        deriv (fun φ ↦ C.law.lineHeight φ (q 0)) C.θ =
          deriv C.law.slope C.θ * q 0 + deriv C.law.intercept C.θ := by
      have hd :
          deriv ((fun φ ↦ C.law.slope φ * q 0) + C.law.intercept) C.θ =
            deriv C.law.slope C.θ * q 0 + deriv C.law.intercept C.θ := by
        rw [deriv_add (hdm.mul_const _) hdb, deriv_mul_const hdm]
      exact hd
    rw [hder] at hqderiv
    -- From `m'(θ) q₀ + b'(θ) = 0` and `m'(θ) ≠ 0`, `q₀ = −b'(θ)/m'(θ)`.
    have hq00 : q 0 * deriv C.law.slope C.θ = -deriv C.law.intercept C.θ := by
      linear_combination hqderiv
    have hq0 : q 0 = -(deriv C.law.intercept C.θ) / deriv C.law.slope C.θ := by
      field_simp
      linear_combination hq00
    -- `q` and the witness are points of `Fin 2 → ℝ`; compare them componentwise.
    apply funext_iff.mpr
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hq0
    · intro j
      -- `Fin 1` is a subsingleton, so `j = 0`; the remaining component is 1.
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      change q 1 =
        C.law.slope C.θ *
            (-(deriv C.law.intercept C.θ) / deriv C.law.slope C.θ)
          + C.law.intercept C.θ
      -- `hqline : q 1 = lineHeight θ (q 0) = slope θ * q 0 + intercept θ`.
      have hqline' : q 1 =
          C.law.slope C.θ * q 0 + C.law.intercept C.θ := hqline
      rw [hqline', hq0]

/-- The limiting intersection lies on the reflected line of `A`, as a point
of the plane. -/
theorem limitingIntersection_onLineA {Xc Yc : ℝ} (h : C.SolutionC3 Xc Yc) :
    C.OnLineA Xc Yc := by
  exact h.1

/-- **Uniqueness, coordinate form.**  Two limiting-intersection points for the
same mirror, ray `A` incidence angle `θ`, and reflection law coincide.  This
is the coordinate-shadow form of the uniqueness half of
`exists_unique_limiting_intersection`, stated separately so that the prover
can use it componentwise. -/
theorem limitingIntersection_unique {Xc₁ Yc₁ Xc₂ Yc₂ : ℝ}
    (h₁ : C.SolutionC3 Xc₁ Yc₁) (h₂ : C.SolutionC3 Xc₂ Yc₂) :
    Xc₁ = Xc₂ ∧ Yc₁ = Yc₂ := by
  -- The slope θ-derivative is nonzero and both slope and intercept are
  -- differentiable at θ (content of C.1–C.2).
  have hm' : deriv C.law.slope C.θ ≠ 0 :=
    C.law_smooth.slope_deriv_ne_zero C.θ C.θ_mem
  have hdm : DifferentiableAt ℝ C.law.slope C.θ :=
    C.law_smooth.slope_differentiable C.θ C.θ_mem
  have hdb : DifferentiableAt ℝ C.law.intercept C.θ :=
    C.law_smooth.intercept_differentiable C.θ C.θ_mem
  -- At any limiting abscissa `x`, the θ-derivative of the line height is
  -- `m'(θ) x + b'(θ)`, so `m'(θ) ≠ 0` pins it to `−b'(θ)/m'(θ)`.
  have key : ∀ {x : ℝ},
      deriv (fun φ ↦ C.law.lineHeight φ x) C.θ = 0 →
        x * deriv C.law.slope C.θ + deriv C.law.intercept C.θ = 0 := by
    intro x hx
    have hder :
        deriv (fun φ ↦ C.law.lineHeight φ x) C.θ =
          deriv C.law.slope C.θ * x + deriv C.law.intercept C.θ := by
      have hd :
          deriv ((fun φ ↦ C.law.slope φ * x) + C.law.intercept) C.θ =
            deriv C.law.slope C.θ * x + deriv C.law.intercept C.θ := by
        rw [deriv_add (hdm.mul_const _) hdb, deriv_mul_const hdm]
      exact hd
    rw [hder] at hx
    linear_combination hx
  have e1 : Xc₁ * deriv C.law.slope C.θ + deriv C.law.intercept C.θ = 0 := key h₁.2
  have e2 : Xc₂ * deriv C.law.slope C.θ + deriv C.law.intercept C.θ = 0 := key h₂.2
  have hX : Xc₁ = Xc₂ := by
    have h : (Xc₁ - Xc₂) * deriv C.law.slope C.θ = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp h with hsub | hzero
    · linear_combination hsub
    · exact absurd hzero hm'
  refine ⟨hX, ?_⟩
  -- Both ordinates are the reflected-line height at the common abscissa.
  have o₁ : Yc₁ = C.law.slope C.θ * Xc₁ + C.law.intercept C.θ := h₁.1
  have o₂ : Yc₂ = C.law.slope C.θ * Xc₂ + C.law.intercept C.θ := h₂.1
  rw [o₁, o₂, hX]

/-- **Difference-quotient form of the limiting intersection.**  The abscissa
`x_c` of the limiting intersection equals the derivative ratio
`−(deriv b θ)/(deriv m θ)`: the limit of the intersection abscissa
`(b(θ+Δθ) − b θ)/(m θ − m(θ+Δθ))` of the two reflected lines as `Δθ → 0`.
This records the *limiting-intersection* reading of T2-C3 in Lean terms and
is the equation the prover uses to construct the witness.  It is stated
answer-blind: no closed form of the derivatives appears. -/
theorem limitingIntersection_eq_deriv_ratio {Xc Yc : ℝ} (h : C.SolutionC3 Xc Yc) :
    Xc = -(deriv C.law.intercept C.θ) / (deriv C.law.slope C.θ) := by
  obtain ⟨_hqline, hqderiv⟩ := h
  have hm' : deriv C.law.slope C.θ ≠ 0 :=
    C.law_smooth.slope_deriv_ne_zero C.θ C.θ_mem
  have hdm : DifferentiableAt ℝ C.law.slope C.θ :=
    C.law_smooth.slope_differentiable C.θ C.θ_mem
  have hdb : DifferentiableAt ℝ C.law.intercept C.θ :=
    C.law_smooth.intercept_differentiable C.θ C.θ_mem
  -- The θ-derivative of the affine-in-x line height is `m'(θ) x + b'(θ)`.
  have hder :
      deriv (fun φ ↦ C.law.lineHeight φ Xc) C.θ =
        deriv C.law.slope C.θ * Xc + deriv C.law.intercept C.θ := by
    have hd :
        deriv ((fun φ ↦ C.law.slope φ * Xc) + C.law.intercept) C.θ =
          deriv C.law.slope C.θ * Xc + deriv C.law.intercept C.θ := by
      rw [deriv_add (hdm.mul_const _) hdb, deriv_mul_const hdm]
    exact hd
  rw [hder] at hqderiv
  have hXC : Xc * deriv C.law.slope C.θ = -deriv C.law.intercept C.θ := by
    linear_combination hqderiv
  field_simp
  linear_combination hXC

/-- The ordinate of the limiting intersection is the reflected-line height at
its abscissa, `Y_c = m_A X_c + b_A`, i.e. the limiting intersection lies on
the reflected ray of `A`. -/
theorem limitingIntersection_ordinate {Xc Yc : ℝ} (h : C.SolutionC3 Xc Yc) :
    Yc = C.mA * Xc + C.bA := by
  exact h.1

end CausticContext

/-- **Physical caustic characterization (tangency).**  The limiting
intersection of the neighbouring reflected rays is where the reflected ray of
`A` is tangent to the caustic curve; in particular the θ-derivative of the
reflected-line height at the limiting abscissa vanishes.  This theorem
restates the `IsLimitingIntersection` condition in derivative form, so that
the prover can unfold it directly into the `deriv = 0` goal. -/
theorem limitingIntersection_deriv_eq_zero (C : CausticContext) {Xc Yc : ℝ}
    (h : C.SolutionC3 Xc Yc) :
    deriv (fun φ ↦ C.law.lineHeight φ Xc) C.θ = 0 := by
  exact h.2

end IPhO2026P2C3

end
