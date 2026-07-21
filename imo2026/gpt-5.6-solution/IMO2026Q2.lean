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
  exact (set_option maxHeartbeats 2000000 in by
    subst M
    subst N
    rcases hK with ⟨aK, bK, cK, haK, hbK, hcK, hsumK, hKeq⟩
    rcases hL with ⟨aL, bL, cL, haL, hbL, hcL, hsumL, hLeq⟩
    rcases hKangle with ⟨s, t, hs, ht, hKangleEq⟩
    rcases hLangle with ⟨u, v, hu, hv, hLangleEq⟩
    letI : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩
    letI : Module.Oriented ℝ Plane (Fin 2) :=
      ⟨(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation⟩
    let o : Orientation ℝ Plane (Fin 2) := Module.Oriented.positiveOrientation
    have areaForm_eq_norm_mul_norm_mul_sin_oangle
        (o : Orientation ℝ Plane (Fin 2)) (w z : Plane) :
        o.areaForm w z = ‖w‖ * ‖z‖ * Real.Angle.sin (o.oangle w z) := by
      rw [Orientation.oangle, Real.Angle.sin_coe, ← o.norm_kahler]
      simpa [Orientation.kahler_apply_apply, mul_comm] using
        (Complex.norm_mul_sin_arg (o.kahler w z)).symm
    have inner_mul_areaForm_eq_of_oangle_eq
        (o : Orientation ℝ Plane (Fin 2)) (w x y z : Plane)
        (h : o.oangle w x = o.oangle y z) :
        inner ℝ w x * o.areaForm y z = inner ℝ y z * o.areaForm w x := by
      rw [o.inner_eq_norm_mul_norm_mul_cos_oangle,
        areaForm_eq_norm_mul_norm_mul_sin_oangle,
        o.inner_eq_norm_mul_norm_mul_cos_oangle,
        areaForm_eq_norm_mul_norm_mul_sin_oangle, h]
      ring
    let a : Plane := A - B
    let c : Plane := C - B
    let z0 : Plane := O - B
    let x : ℝ := bK / 2
    let y : ℝ := cK
    let p : ℝ := bL / 2
    let q : ℝ := bL / 2 + cL
    have hx : 0 < x := by dsimp [x]; positivity
    have hy : 0 < y := by exact hcK
    have hp : 0 < p := by dsimp [p]; positivity
    have hq : 0 < q := by dsimp [q]; positivity
    have hxy : x + y < 1 := by
      dsimp [x, y]
      nlinarith only [haK, hbK, hcK, hsumK]
    have hpq : p + q < 1 := by
      dsimp [p, q]
      nlinarith only [haL, hbL, hcL, hsumL]
    have hq1 : q < 1 := lt_trans (lt_add_of_pos_left q hp) hpq
    have hp1 : p < 1 := lt_trans (lt_add_of_pos_right p hq) hpq
    have hdet1a : x * 0 - y * 1 < 0 := by nlinarith only [hy]
    have hdet1b : 1 * (q - 1) - (-1) * p < 0 := by nlinarith only [hpq]
    have hdet2a : p * 0 - q * 1 < 0 := by nlinarith only [hq]
    have hdet2b : (p - 1 / 2) * (1 / 2) - (q - 1 / 2) * (-1 / 2) < 0 := by
      nlinarith only [hpq]
    have hdet3a : 1 * (y - 1) - (-1) * x < 0 := by nlinarith only [hxy]
    have hdet3b : (-1 / 2 : ℝ) * y - 0 * (x - 1 / 2) < 0 := by
      nlinarith only [hy]
    have haKeq : aK = 1 - bK - cK := by linarith only [hsumK]
    have haLeq : aL = 1 - bL - cL := by linarith only [hsumL]
    have hKvec : K - B = x • a + y • c := by
      rw [hKeq]
      rw [haKeq]
      simp only [a, c, x, y, midpoint_eq_smul_add, invOf_eq_inv]
      module
    have hLvec : L - B = p • a + q • c := by
      rw [hLeq]
      rw [haLeq]
      simp only [a, c, p, q, midpoint_eq_smul_add, invOf_eq_inv]
      module
    have hOAvec : O - A = z0 - a := by simp [z0, a]
    have hOKvec : O - K = z0 - (x • a + y • c) := by
      calc
        O - K = (O - B) - (K - B) := by abel
        _ = z0 - (x • a + y • c) := by rw [hKvec]
    have hOLvec : O - L = z0 - (p • a + q • c) := by
      calc
        O - L = (O - B) - (L - B) := by abel
        _ = z0 - (p • a + q • c) := by rw [hLvec]
    have hAvec : A - B = a := rfl
    have hCvec : C - B = c := rfl
    have hACvec : A - C = a - c := by simp [a, c]
    have hLCvec : L - C = p • a + (q - 1) • c := by
      calc
        L - C = (L - B) - (C - B) := by abel
        _ = p • a + (q - 1) • c := by rw [hLvec, hCvec]; module
    have hKCvec : K - C = x • a + (y - 1) • c := by
      calc
        K - C = (K - B) - (C - B) := by abel
        _ = x • a + (y - 1) • c := by rw [hKvec, hCvec]; module
    have hLNvec : L - midpoint ℝ A C = (p - 1 / 2) • a + (q - 1 / 2) • c := by
      rw [← sub_add_sub_cancel L B (midpoint ℝ A C), hLvec]
      simp only [a, c, midpoint_eq_smul_add, invOf_eq_inv]
      module
    have hCNvec : C - midpoint ℝ A C = (-1 / 2 : ℝ) • a + (1 / 2 : ℝ) • c := by
      simp only [a, c, midpoint_eq_smul_add, invOf_eq_inv]
      module
    have hBMvec : B - midpoint ℝ A B = (-1 / 2 : ℝ) • a := by
      simp only [a, midpoint_eq_smul_add, invOf_eq_inv]
      module
    have hKMvec : K - midpoint ℝ A B = (x - 1 / 2) • a + y • c := by
      rw [← sub_add_sub_cancel K B (midpoint ℝ A B), hKvec]
      simp only [a, midpoint_eq_smul_add, invOf_eq_inv]
      module
    have hBNvec : B - midpoint ℝ A C = (-1 / 2 : ℝ) • a + (-1 / 2 : ℝ) • c := by
      simp only [a, c, midpoint_eq_smul_add, invOf_eq_inv]
      module
    have hOMvec : O - midpoint ℝ A B = z0 - (1 / 2 : ℝ) • a := by
      calc
        O - midpoint ℝ A B = (O - B) + (B - midpoint ℝ A B) := by abel
        _ = z0 - (1 / 2 : ℝ) • a := by rw [hBMvec]; module
    have hONvec : O - midpoint ℝ A C = z0 - (1 / 2 : ℝ) • a - (1 / 2 : ℝ) • c := by
      calc
        O - midpoint ℝ A C = (O - B) + (B - midpoint ℝ A C) := by abel
        _ = z0 - (1 / 2 : ℝ) • a - (1 / 2 : ℝ) • c := by rw [hBNvec]; module
    have hKangleVec : x • a + y • c = s • (p • a + q • c) + t • a := by
      simpa [hKvec, hLvec, hAvec] using hKangleEq
    have hLangleVec : p • a + (q - 1) • c =
        u • (a - c) + v • (x • a + (y - 1) • c) := by
      simpa [hLCvec, hACvec, hKCvec] using hLangleEq
    change InnerProductGeometry.angle (K - B) (A - B) =
      InnerProductGeometry.angle (A - C) (L - C) at h1
    change InnerProductGeometry.angle (L - B) (K - B) =
      InnerProductGeometry.angle (L - midpoint ℝ A C) (C - midpoint ℝ A C) at h2
    change InnerProductGeometry.angle (L - C) (K - C) =
      InnerProductGeometry.angle (B - midpoint ℝ A B) (K - midpoint ℝ A B) at h3
    rw [hKvec, hAvec, hACvec, hLCvec] at h1
    rw [hLvec, hKvec, hLNvec, hCNvec] at h2
    rw [hLCvec, hKCvec, hBMvec, hKMvec] at h3
    have hsign1 :
        (o.oangle (x • a + y • c) a).sign =
          (o.oangle (a - c) (p • a + (q - 1) • c)).sign := by
      calc
        (o.oangle (x • a + y • c) a).sign =
            SignType.sign (x * 0 - y * 1) * (o.oangle a c).sign := by
              simpa using o.oangle_sign_smul_add_smul_smul_add_smul a c x y 1 0
        _ = -(o.oangle a c).sign := by rw [sign_neg hdet1a]; simp
        _ = SignType.sign (1 * (q - 1) - (-1) * p) * (o.oangle a c).sign := by
          rw [sign_neg hdet1b]; simp
        _ = (o.oangle (a - c) (p • a + (q - 1) • c)).sign := by
          simpa [sub_eq_add_neg] using
            (o.oangle_sign_smul_add_smul_smul_add_smul a c 1 (-1) p (q - 1)).symm
    have hsign2 :
        (o.oangle (p • a + q • c) (x • a + y • c)).sign =
          (o.oangle ((p - 1 / 2) • a + (q - 1 / 2) • c)
            ((-1 / 2 : ℝ) • a + (1 / 2 : ℝ) • c)).sign := by
      calc
        (o.oangle (p • a + q • c) (x • a + y • c)).sign =
            (o.oangle (p • a + q • c) (s • (p • a + q • c) + t • a)).sign := by
              rw [hKangleVec]
        _ = SignType.sign t * (o.oangle (p • a + q • c) a).sign := by
              exact o.oangle_sign_smul_add_smul_right _ _ s t
        _ = -(o.oangle a c).sign := by
              rw [sign_pos ht, one_mul]
              calc
                (o.oangle (p • a + q • c) a).sign =
                    SignType.sign (p * 0 - q * 1) * (o.oangle a c).sign := by
                      simpa using o.oangle_sign_smul_add_smul_smul_add_smul a c p q 1 0
                _ = -(o.oangle a c).sign := by rw [sign_neg hdet2a]; simp
        _ = SignType.sign ((p - 1 / 2) * (1 / 2) - (q - 1 / 2) * (-1 / 2)) *
            (o.oangle a c).sign := by
              rw [sign_neg hdet2b]; simp
        _ = (o.oangle ((p - 1 / 2) • a + (q - 1 / 2) • c)
            ((-1 / 2 : ℝ) • a + (1 / 2 : ℝ) • c)).sign := by
              simpa using (o.oangle_sign_smul_add_smul_smul_add_smul a c
                (p - 1 / 2) (q - 1 / 2) (-1 / 2) (1 / 2)).symm
    have hsign3 :
        (o.oangle (p • a + (q - 1) • c) (x • a + (y - 1) • c)).sign =
          (o.oangle ((-1 / 2 : ℝ) • a) ((x - 1 / 2) • a + y • c)).sign := by
      calc
        (o.oangle (p • a + (q - 1) • c) (x • a + (y - 1) • c)).sign =
            (o.oangle (u • (a - c) + v • (x • a + (y - 1) • c))
              (x • a + (y - 1) • c)).sign := by rw [hLangleVec]
        _ = SignType.sign u * (o.oangle (a - c) (x • a + (y - 1) • c)).sign := by
              exact o.oangle_sign_smul_add_smul_left _ _ u v
        _ = -(o.oangle a c).sign := by
              rw [sign_pos hu, one_mul]
              calc
                (o.oangle (a - c) (x • a + (y - 1) • c)).sign =
                    SignType.sign (1 * (y - 1) - (-1) * x) * (o.oangle a c).sign := by
                      simpa [sub_eq_add_neg] using
                        o.oangle_sign_smul_add_smul_smul_add_smul a c 1 (-1) x (y - 1)
                _ = -(o.oangle a c).sign := by rw [sign_neg hdet3a]; simp
        _ = SignType.sign ((-1 / 2 : ℝ) * y - 0 * (x - 1 / 2)) *
            (o.oangle a c).sign := by rw [sign_neg hdet3b]; simp
        _ = (o.oangle ((-1 / 2 : ℝ) • a) ((x - 1 / 2) • a + y • c)).sign := by
              simpa using (o.oangle_sign_smul_add_smul_smul_add_smul a c
                (-1 / 2) 0 (x - 1 / 2) y).symm
    have ho1 := o.oangle_eq_of_angle_eq_of_sign_eq h1 hsign1
    have ho2 := o.oangle_eq_of_angle_eq_of_sign_eq h2 hsign2
    have ho3 := o.oangle_eq_of_angle_eq_of_sign_eq h3 hsign3
    clear h1 h2 h3
    have hc1 := inner_mul_areaForm_eq_of_oangle_eq o _ _ _ _ ho1
    have hc2 := inner_mul_areaForm_eq_of_oangle_eq o _ _ _ _ ho2
    have hc3 := inner_mul_areaForm_eq_of_oangle_eq o _ _ _ _ ho3
    have hbaseSign : (o.oangle a c).sign ≠ 0 := by
      intro hzero
      apply hABC
      apply (EuclideanGeometry.oangle_sign_eq_zero_iff_collinear).mp
      change (o.oangle (A - B) (C - B)).sign = 0
      simpa [a, c] using hzero
    have ha0 : a ≠ 0 := o.left_ne_zero_of_oangle_sign_ne_zero hbaseSign
    have hc0 : c ≠ 0 := o.right_ne_zero_of_oangle_sign_ne_zero hbaseSign
    have harea : o.areaForm a c ≠ 0 := by
      intro hzero
      have hnorm : ‖a‖ * ‖c‖ ≠ 0 :=
        mul_ne_zero (norm_ne_zero_iff.mpr ha0) (norm_ne_zero_iff.mpr hc0)
      have hsine : Real.Angle.sin (o.oangle a c) = 0 := by
        have h := areaForm_eq_norm_mul_norm_mul_sin_oangle o a c
        rw [hzero] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hnorm
      exact hbaseSign (by simp [Real.Angle.sign, hsine])
    simp only [inner_add_left, inner_add_right, inner_sub_left,
      real_inner_smul_left, real_inner_smul_right, map_add, map_sub, map_smul,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      o.areaForm_apply_self, neg_mul, zero_mul, mul_zero,
      add_zero, zero_add, sub_zero] at hc1 hc2 hc3
    rw [o.areaForm_swap c a] at hc1 hc2 hc3
    rw [real_inner_comm a c] at hc1 hc2 hc3
    ring_nf at hc1 hc2 hc3
    let X : ℝ := inner ℝ a a
    let Y : ℝ := inner ℝ a c
    let Z : ℝ := inner ℝ c c
    let W : ℝ := o.areaForm a c
    let e1a : ℝ := x * p + y * p + x * q - x
    let e1b : ℝ := 2 * y * q - 2 * y
    let e1c : ℝ := -y * q + y
    let e2a : ℝ := x * p ^ 2 + y * p ^ 2 - x * p - y * p / 2 + x * q / 2
    let e2b : ℝ := 2 * x * p * q + 2 * y * p * q - y * p - x * q
    let e2c : ℝ := x * q ^ 2 + y * q ^ 2 + y * p / 2 - x * q / 2 - y * q
    let e3a : ℝ := -x ^ 2 * q + x ^ 2 - x * p - y * p / 2 + x * q / 2 - x / 2 + p / 2
    let e3b : ℝ := -2 * x * y * q + 2 * x * y
    let e3c : ℝ := -y ^ 2 * q + y ^ 2 + y * q - y
    have he1W : (e1a * X + e1b * Y + e1c * Z) * W = 0 := by
      dsimp [e1a, e1b, e1c, X, Y, Z, W]
      linear_combination hc1
    have he2W : (e2a * X + e2b * Y + e2c * Z) * W = 0 := by
      change ((x * p ^ 2 + y * p ^ 2 - x * p - y * p / 2 + x * q / 2) * inner ℝ a a +
        (2 * x * p * q + 2 * y * p * q - y * p - x * q) * inner ℝ a c +
        (x * q ^ 2 + y * q ^ 2 + y * p / 2 - x * q / 2 - y * q) * inner ℝ c c) *
          o.areaForm a c = 0
      linear_combination 2 * hc2
    have he3W : (e3a * X + e3b * Y + e3c * Z) * W = 0 := by
      change ((-x ^ 2 * q + x ^ 2 - x * p - y * p / 2 + x * q / 2 - x / 2 + p / 2) *
          inner ℝ a a + (-2 * x * y * q + 2 * x * y) * inner ℝ a c +
        (-y ^ 2 * q + y ^ 2 + y * q - y) * inner ℝ c c) * o.areaForm a c = 0
      linear_combination 2 * hc3
    have hW : W ≠ 0 := by exact harea
    have he1 : e1a * X + e1b * Y + e1c * Z = 0 :=
      (mul_eq_zero.mp he1W).resolve_right hW
    have he2 : e2a * X + e2b * Y + e2c * Z = 0 :=
      (mul_eq_zero.mp he2W).resolve_right hW
    have he3 : e3a * X + e3b * Y + e3c * Z = 0 :=
      (mul_eq_zero.mp he3W).resolve_right hW
    have hX : 0 < X := by
      dsimp [X]
      exact real_inner_self_pos.mpr ha0
    let det123 : ℝ := e1a * (e2b * e3c - e2c * e3b) -
      e1b * (e2a * e3c - e2c * e3a) + e1c * (e2a * e3b - e2b * e3a)
    have hdet123X : det123 * X = 0 := by
      dsimp [det123]
      linear_combination
        (e2b * e3c - e2c * e3b) * he1 +
        (e1c * e3b - e1b * e3c) * he2 +
        (e1b * e2c - e1c * e2b) * he3
    have hdet123 : det123 = 0 :=
      (mul_eq_zero.mp hdet123X).resolve_right (ne_of_gt hX)
    let H : ℝ := -x ^ 2 * q + x * y * p - x * y * q - x * q ^ 2 +
      y ^ 2 * p + y * p * q + 2 * x * q - y * p - p * q
    have hdet123Factor : det123 = y * (p + q - 1) * (1 - q) * (x + y) * H := by
      dsimp [det123, H, e1a, e1b, e1c, e2a, e2b, e2c, e3a, e3b, e3c]
      ring
    have hpqne : p + q - 1 ≠ 0 := by nlinarith only [hpq]
    have hqne : 1 - q ≠ 0 := by nlinarith only [hq1]
    have hxyne : x + y ≠ 0 := by nlinarith only [hx, hy]
    have hpref : y * (p + q - 1) * (1 - q) * (x + y) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt hy) hpqne) hqne) hxyne
    have hHprod : y * (p + q - 1) * (1 - q) * (x + y) * H = 0 := by
      rw [← hdet123Factor]
      exact hdet123
    have hH : H = 0 := (mul_eq_zero.mp hHprod).resolve_left hpref
    let t1 : ℝ := -2 * x ^ 2 * p + 2 * x * p ^ 2 + 2 * x ^ 2 - 2 * p ^ 2 - 2 * x + 2 * p
    let t2 : ℝ := -4 * x * y * p + 4 * x * p * q + 4 * x * y + 2 * y * p -
      2 * x * q - 4 * p * q - 2 * y + 2 * q
    let t3 : ℝ := -2 * y ^ 2 * p + 2 * x * q ^ 2 + 2 * y ^ 2 + y * p -
      x * q - 2 * q ^ 2 - y + q
    let det12t : ℝ := e1a * (e2b * t3 - e2c * t2) -
      e1b * (e2a * t3 - e2c * t1) + e1c * (e2a * t2 - e2b * t1)
    have hdet12tFactor :
        det12t = 2 * y * (x + y) * (1 - p) * (p + q - 1) * H := by
      dsimp [det12t, H, t1, t2, t3, e1a, e1b, e1c, e2a, e2b, e2c]
      ring
    have hdet12t : det12t = 0 := by
      rw [hdet12tFactor, hH]
      ring
    let minor : ℝ := e1b * e2c - e1c * e2b
    have hminorFactor :
        minor = -2 * q * y * (1 - q) * (p + q - 1) * (x + y) := by
      dsimp [minor, e1b, e1c, e2b, e2c]
      ring
    have hminor : minor ≠ 0 := by
      rw [hminorFactor]
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hq))
          (ne_of_gt hy)) hqne) hpqne) hxyne
    let T : ℝ := t1 * X + t2 * Y + t3 * Z
    have hminorT : minor * T = 0 := by
      dsimp [minor, T, det12t]
      linear_combination
        (t2 * e2c - e2b * t3) * he1 +
        (e1b * t3 - e1c * t2) * he2 + X * hdet12t
    have hT : T = 0 := (mul_eq_zero.mp hminorT).resolve_left hminor
    let D : ℝ := (x - 1) * q - y * (p - 1)
    have hD : D ≠ 0 := by
      intro hDz
      have hresultant : (1 - x - y) * (q - y) * (q + y) = 0 := by
        dsimp [D, H] at hDz hH ⊢
        linear_combination y * hH + (y * (x + y + q - 1) - q) * hDz
      have hleft : 1 - x - y ≠ 0 := by nlinarith only [hxy]
      have hright : q + y ≠ 0 := by nlinarith only [hq, hy]
      have hmiddle : q - y = 0 := by
        have hreordered : ((1 - x - y) * (q + y)) * (q - y) = 0 := by
          linear_combination hresultant
        exact (mul_eq_zero.mp hreordered).resolve_left (mul_ne_zero hleft hright)
      have hqy : q = y := sub_eq_zero.mp hmiddle
      have hpxprod : y * (x - p) = 0 := by
        dsimp [D] at hDz
        rw [hqy] at hDz
        linear_combination hDz
      have hpx : p = x := by
        have hxp := (mul_eq_zero.mp hpxprod).resolve_left (ne_of_gt hy)
        exact (sub_eq_zero.mp hxp).symm
      have hkself : x • a + y • c = s • (x • a + y • c) + t • a := by
        simpa [hpx, hqy] using hKangleVec
      have hkarea := congrArg (fun z : Plane => o.areaForm (x • a + y • c) z) hkself
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, o.areaForm_apply_self, mul_zero, add_zero] at hkarea
      rw [o.areaForm_swap c a] at hkarea
      have htyW : t * y * W = 0 := by
        dsimp [W]
        linear_combination hkarea
      exact (mul_ne_zero (mul_ne_zero (ne_of_gt ht) (ne_of_gt hy)) hW) htyW
    let U : ℝ := inner ℝ z0 a
    let V : ℝ := inner ℝ z0 c
    let R1 : ℝ := (x ^ 2 - 1) * X + 2 * x * y * Y + y ^ 2 * Z
    let R2 : ℝ := (p ^ 2 - 1) * X + 2 * p * q * Y + q ^ 2 * Z
    rcases hO with ⟨hOAK, hOAL⟩
    have hsq1 := congrArg (fun r : ℝ => r ^ 2) hOAK
    have hsq2 := congrArg (fun r : ℝ => r ^ 2) hOAL
    simp only [dist_eq_norm] at hsq1 hsq2
    rw [hOAvec, hOKvec, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq] at hsq1
    rw [hOAvec, hOLvec, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq] at hsq2
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right] at hsq1 hsq2
    rw [real_inner_comm z0 a, real_inner_comm z0 c, real_inner_comm a c] at hsq1 hsq2
    ring_nf at hsq1 hsq2
    have heO1 : 2 * (x - 1) * U + 2 * y * V - R1 = 0 := by
      dsimp [U, V, R1, X, Y, Z]
      linear_combination hsq1
    have heO2 : 2 * (p - 1) * U + 2 * q * V - R2 = 0 := by
      dsimp [U, V, R2, X, Y, Z]
      linear_combination hsq2
    have hTform :
        (p - 1) * (y * (2 * Y + Z) - 2 * R1) -
          (x - 1) * (q * (2 * Y + Z) - 2 * R2) = 0 := by
      dsimp [T, t1, t2, t3, R1, R2] at hT ⊢
      linear_combination hT
    have hDV : D * (4 * V - 2 * Y - Z) = 0 := by
      dsimp [D]
      linear_combination hTform - 2 * (p - 1) * heO1 + 2 * (x - 1) * heO2
    have hV : 4 * V - 2 * Y - Z = 0 :=
      (mul_eq_zero.mp hDV).resolve_left hD
    refine (sq_eq_sq₀ (dist_nonneg) (dist_nonneg)).mp ?_
    simp only [dist_eq_norm]
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hOMvec, hONvec]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm z0 a, real_inner_comm z0 c, real_inner_comm a c]
    dsimp [U, V, X, Y, Z] at hV ⊢
    linear_combination (1 / 4) * hV)
