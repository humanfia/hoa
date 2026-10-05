import Mathlib
import Physlib

namespace Ipho2026Gpt56solBlind

/-!
# IPhO 2026, Problem 2, part C.1

This file models the cross-section in Figure 2g.  Coordinates and the radius
are represented by real numbers measured in one common length unit; vector
components use the corresponding coordinate basis.  A line's slope is
dimensionless, while its intercept has the same length dimension as `R`.

The requested coefficients are deliberately not built into the statement.
Instead, `IsReflectedRayASolution` says that they describe the unique
nonvertical line selected by the mirror geometry and the law of specular
reflection.
-/

namespace ProblemIPhO2026_2_C_1

/-- A point in the two-dimensional cross-section shown in Figure 2g. -/
structure PlanePoint where
  x : ℝ
  y : ℝ

/-- A vector expressed in the positive-`x`, positive-`y` axes of Figure 2g. -/
structure PlaneVector where
  x : ℝ
  y : ℝ

/-- Euclidean scalar product in the coordinate system of Figure 2g. -/
def dot (u v : PlaneVector) : ℝ := u.x * v.x + u.y * v.y

/-- A vector is unit length in the Euclidean cross-section. -/
def IsUnitVector (v : PlaneVector) : Prop := dot v v = 1

/--
The half-cylindrical mirror, viewed in cross-section: a point lies on the
circle of radius `R` centred at the origin and on its upper semicircle.
-/
def OnUpperSemicircularMirror (R : ℝ) (P : PlanePoint) : Prop :=
  P.x ^ 2 + P.y ^ 2 = R ^ 2 ∧ 0 ≤ P.y

/--
The vector form of the specular-reflection law.  `incoming` points in the
direction in which the light travels toward the mirror, `normal` is a unit
radial normal, and `outgoing` points away from the reflection point.

Changing the sign of the chosen unit normal leaves these equations unchanged,
so this convention also describes reflection from the inner surface of the
half-cylinder.
-/
def ObeysSpecularReflection
    (incoming normal outgoing : PlaneVector) : Prop :=
  IsUnitVector normal ∧
    outgoing.x = incoming.x - 2 * dot incoming normal * normal.x ∧
    outgoing.y = incoming.y - 2 * dot incoming normal * normal.y

/--
All geometric data for ray `A` in Figure 2g.

The incidence point is on the right-hand half of the upper mirror.  The angle
`θ` is measured from the positive `y`-axis to its radial normal.  Ray `A`
travels vertically upward before reflection.
-/
def Figure2gRayASetup
    (R θ : ℝ) (P : PlanePoint)
    (normal incoming outgoing : PlaneVector) : Prop :=
  OnUpperSemicircularMirror R P ∧
    0 ≤ P.x ∧
    P.x = R * Real.sin θ ∧
    P.y = R * Real.cos θ ∧
    normal.x = Real.sin θ ∧
    normal.y = Real.cos θ ∧
    incoming.x = 0 ∧
    incoming.y = 1 ∧
    ObeysSpecularReflection incoming normal outgoing

/--
The two requested coefficients.  `slope` is dimensionless and `intercept` is
a signed `y`-coordinate, hence has the same length dimension as `R`.
-/
structure ReflectedLineCoefficients where
  slope : ℝ
  intercept : ℝ

/--
A nonvertical directed line through `P`, written in the requested form
`y = slope * x + intercept`.  The equation involving `direction` fixes its
slope without dividing by a possibly zero horizontal component.
-/
def DescribesNonverticalLine
    (P : PlanePoint) (direction : PlaneVector)
    (coeff : ReflectedLineCoefficients) : Prop :=
  direction.x ≠ 0 ∧
    direction.y = coeff.slope * direction.x ∧
    P.y = coeff.slope * P.x + coeff.intercept

/--
Answer-free solution predicate for part C.1: the coefficients describe the
line containing the specularly reflected ray `A` in Figure 2g.
-/
def IsReflectedRayASolution
    (R θ : ℝ) (coeff : ReflectedLineCoefficients) : Prop :=
  ∃ P normal incoming outgoing,
    Figure2gRayASetup R θ P normal incoming outgoing ∧
      DescribesNonverticalLine P outgoing coeff

/--
For a positive mirror radius and an incidence point strictly inside the
right-hand quadrant of the upper semicircle, the governing geometry and the
law of reflection select exactly one slope/intercept pair for ray `A`.
-/
theorem problem_IPhO_2026_2_C_1
    (R θ : ℝ)
    (hR : 0 < R)
    (hθ_pos : 0 < θ)
    (hθ_acute : θ < Real.pi / 2) :
    ∃! coeff : ReflectedLineCoefficients,
      IsReflectedRayASolution R θ coeff := by
  have hθ_pi : θ < Real.pi := by
    linarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_pi
  have hcos_pos : 0 < Real.cos θ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ_acute⟩
  have htrig : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq θ

  let P : PlanePoint := ⟨R * Real.sin θ, R * Real.cos θ⟩
  let normal : PlaneVector := ⟨Real.sin θ, Real.cos θ⟩
  let incoming : PlaneVector := ⟨0, 1⟩
  let outgoing : PlaneVector :=
    ⟨-2 * Real.cos θ * Real.sin θ,
      1 - 2 * Real.cos θ * Real.cos θ⟩

  have hmirror : OnUpperSemicircularMirror R P := by
    constructor
    · dsimp [P]
      calc
        (R * Real.sin θ) ^ 2 + (R * Real.cos θ) ^ 2 =
            R ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
        _ = R ^ 2 := by rw [htrig]; ring
    · dsimp [P]
      exact (mul_pos hR hcos_pos).le

  have hreflection :
      ObeysSpecularReflection incoming normal outgoing := by
    change
      (normal.x * normal.x + normal.y * normal.y = 1) ∧
        outgoing.x = incoming.x -
          2 * (incoming.x * normal.x + incoming.y * normal.y) * normal.x ∧
        outgoing.y = incoming.y -
          2 * (incoming.x * normal.x + incoming.y * normal.y) * normal.y
    refine ⟨?_, ?_, ?_⟩
    · dsimp [normal]
      nlinarith [htrig]
    · dsimp [outgoing, incoming, normal]
      ring
    · dsimp [outgoing, incoming, normal]
      ring

  have hsetup : Figure2gRayASetup R θ P normal incoming outgoing := by
    refine ⟨hmirror, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hreflection⟩
    dsimp [P]
    exact (mul_pos hR hsin_pos).le

  have houtgoing_x : outgoing.x ≠ 0 := by
    dsimp [outgoing]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (ne_of_gt hcos_pos))
      (ne_of_gt hsin_pos)

  let coeff : ReflectedLineCoefficients :=
    ⟨outgoing.y / outgoing.x,
      P.y - (outgoing.y / outgoing.x) * P.x⟩

  have hline : DescribesNonverticalLine P outgoing coeff := by
    refine ⟨houtgoing_x, ?_, ?_⟩
    · dsimp [coeff]
      exact (div_mul_cancel₀ outgoing.y houtgoing_x).symm
    · dsimp [coeff]
      ring

  refine ⟨coeff, ?_, ?_⟩
  · exact ⟨P, normal, incoming, outgoing, hsetup, hline⟩
  · intro coeff' hcoeff'
    rcases hcoeff' with
      ⟨P', normal', incoming', outgoing', hsetup', hline'⟩
    rcases hsetup' with
      ⟨_, _, hP'x, hP'y, hnormal'x, hnormal'y,
        hincoming'x, hincoming'y, hreflection'⟩
    change
      (normal'.x * normal'.x + normal'.y * normal'.y = 1) ∧
        outgoing'.x = incoming'.x -
          2 * (incoming'.x * normal'.x + incoming'.y * normal'.y) * normal'.x ∧
        outgoing'.y = incoming'.y -
          2 * (incoming'.x * normal'.x + incoming'.y * normal'.y) * normal'.y
      at hreflection'
    rcases hreflection' with ⟨_, houtgoing'x, houtgoing'y⟩
    rcases hline' with ⟨_, hline_slope', hline_point'⟩

    have houtgoing_x_eq : outgoing'.x = outgoing.x := by
      rw [houtgoing'x]
      dsimp [outgoing]
      rw [hincoming'x, hincoming'y, hnormal'x, hnormal'y]
      ring
    have houtgoing_y_eq : outgoing'.y = outgoing.y := by
      rw [houtgoing'y]
      dsimp [outgoing]
      rw [hincoming'x, hincoming'y, hnormal'x, hnormal'y]
      ring

    have hslope : coeff'.slope = coeff.slope := by
      apply mul_right_cancel₀ houtgoing_x
      calc
        coeff'.slope * outgoing.x = coeff'.slope * outgoing'.x := by
          rw [houtgoing_x_eq]
        _ = outgoing'.y := hline_slope'.symm
        _ = outgoing.y := houtgoing_y_eq
        _ = coeff.slope * outgoing.x := hline.2.1

    have hintercept : coeff'.intercept = coeff.intercept := by
      dsimp [coeff, P]
      rw [hP'x, hP'y] at hline_point'
      dsimp [coeff] at hslope
      rw [hslope] at hline_point'
      linarith

    calc
      coeff' = ⟨coeff'.slope, coeff'.intercept⟩ := by rfl
      _ = ⟨coeff.slope, coeff.intercept⟩ := by
        rw [hslope, hintercept]
      _ = coeff := by rfl

end ProblemIPhO2026_2_C_1

end Ipho2026Gpt56solBlind
