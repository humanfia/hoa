import Mathlib
set_option backward.isDefEq.respectTransparency false

open EuclideanGeometry

-- We work in the Euclidean plane `ℝ²` with the standard `L²` (Euclidean) norm.
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A point `P` lies in the open interior of the triangle `X Y Z`: it is a
strictly convex combination `P = α • X + β • Y + γ • Z` with `α, β, γ > 0` and
`α + β + γ = 1`. -/
def InsideTriangle (X Y Z P : Plane) : Prop :=
  ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    P = α • X + β • Y + γ • Z

/-- A point `P` lies inside the (proper) angle at vertex `Y` spanned by the rays
`Y X` and `Y Z`: writing `P - Y = s • (X - Y) + t • (Z - Y)`, one has `s > 0`
and `t > 0`. -/
def InsideAngle (X Y Z P : Plane) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ P - Y = s • (X - Y) + t • (Z - Y)

/-- `O` is the circumcentre of triangle `A K L`: it is equidistant from the three
vertices. (For a nondegenerate triangle such a point exists and is unique.) -/
def IsCircumcentre (A K L O : Plane) : Prop :=
  dist O A = dist O K ∧ dist O A = dist O L

/-- With the configuration described above, the circumcentre
`O` of triangle `AKL` satisfies `OM = ON`, where `M`, `N` are the midpoints of
`AB`, `AC`. -/
theorem main_theorem
    (A B C K L O : Plane)
    -- `ABC` is a nondegenerate triangle.
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    -- `M`, `N` are the midpoints of `AB`, `AC`.
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    -- `K` is inside triangle `BMC`; `L` is inside triangle `BNC`.
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    -- `K` inside angle `∠ L B A`; `L` inside angle `∠ A C K`.
    (hKangle : InsideAngle L B A K)
    (hLangle : InsideAngle A C K L)
    -- The three angle equalities.
    (h1 : ∠ K B A = ∠ A C L)
    (h2 : ∠ L B K = ∠ L N C)
    (h3 : ∠ L C K = ∠ B M K)
    -- `O` is the circumcentre of triangle `AKL`.
    (hO : IsCircumcentre A K L O) :
    dist O M = dist O N := by
  sorry
