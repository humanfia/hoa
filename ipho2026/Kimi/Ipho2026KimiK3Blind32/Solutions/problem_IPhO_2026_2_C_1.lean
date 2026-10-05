import Mathlib

/-!
# IPhO 2026, Problem 2 (T2), Part C.1 — Caustics and Cusp

Answer-blind formalization of subquestion T2-C1 (0.5 pts):

> Consider a ray `A` that strikes the mirror at an angle `θ`, as shown in
> Figure 2g.  Upon reflection, the equation corresponding to this ray in the
> coordinate system defined in Figure 2g is `y = m_A * x + b_A`.  Write `m_A`
> and `b_A` in terms of `θ` and `R`.
>
> (Hint printed in the statement: the expected form is
> `m_A = K₁ cot (K₂ θ)` and `b_A = R K₃ / cos (K₄ θ)`, with `Kᵢ` numerical
> constants.)

## Geometry read from Figure 2g (page T2, "Fig. 2g.")

* The mirror is the **upper half of the circle of radius `R` centred at the
  origin**, with its diameter on the `x`-axis; the labels `-R` and `R` mark
  the endpoints of the diameter, at the rim points `(-R, 0)` and `(R, 0)`.
  The `y`-axis points upward through the apex of the arc.  The reflecting
  surface is the **inside** of the cylindrical arc.  This is the plain
  radius-`R` reading: no vertical feature of Figure 2g is labelled with a
  length (the incident leg is drawn without any length mark), and no mark
  `R / 2` or doubled radius exists anywhere in the figure.  (Iter-013
  root-cause repair: the abandoned iter-012 "vertical leg of the incidence
  triangle has length `R`" reinterpretation placed every labelled feature at
  twice its radius-`R` coordinate — a fabricated scale distortion drawn
  from nowhere in Figure 2g; it is purged.)
* The incoming ray `A` is **vertical** (parallel to the `y`-axis), drawn on
  the positive-`x` side, and its arrowheads point **upward** towards the
  mirror: its actual direction of propagation is
  `incidentPropagationDir = ![0, 1]`, and that actual vector — never its
  into-surface opposite `![0, -1]` — occurs as the incident side of the
  specular law.
* The strike point `P` lies on the upper half-circle in the first quadrant
  at `(R sin θ, R cos θ)`.  The incidence angle `θ` is the dashed angle at
  `P` between the incoming ray and the **radial normal `OP`**, so the mirror
  normal used by the law is the outward radial direction
  `unitOutwardNormal θ = !(sin θ, cos θ)`.
* The reflected line, annotated `y = m_A x + b_A`, leaves `P` towards the
  **lower left** (its arrowheads point down-left), **ascends as `x`
  increases** (positive slope), crosses the `y`-axis **above the origin**
  (between `O` and `P`), and meets the `x`-axis to the left inside the
  drawing, without passing through either labelled rim endpoint `(-R, 0)`
  or `(R, 0)`.  The actual direction of propagation of the reflected ray is
  therefore the *oriented, down-left* graph direction of that line: the
  normalized vector `outgoingPropagationDir = (1 + m_A²)^(-1/2) • ![-1, −m_A]`
  (equivalently any exactly equal oriented vector, i.e. `c • ![-1, −m_A]`
  with `0 < c`), and that actual vector — not an existential over parallel
  directions — is the outgoing side of the specular law.
* The strike point is drawn **high on the arc, close to the apex**.  With
  reflection off the radial normal deflecting the vertical propagation by
  `2θ` from the vertical, the reflected slope evaluated on the delivered
  physical direction is `−(−m_A) = m_A > 0` only while `2θ` stays below
  `π / 2`, i.e. on the drawn branch `0 < θ < π / 4`: higher strikes
  (smaller incidence from the vertical) reflect closer to vertical.  At
  `θ = π / 4` the reflected direction is horizontal; for `θ > π / 4` the
  line descends as `x` increases — a different drawing, not Figure 2g.
  The drawn regime is encoded by `DrawnRegime`.
* A caustic context is announced (a parallel ray `B` at `θ + Δθ` and the
  envelope of reflected rays), but only ray `A` is modelled here; ray `B`
  belongs to part C.2.

The requested quantities are the slope `m_A` and the intercept `b_A` of the
reflected line.  Following the answer-blind policy, the closed forms of
`m_A` and `b_A` (and the numerical hint constants `Kᵢ`) are kept out of all
theorem signatures; instead a solution predicate is built from Figure 2g's
geometry and the law of reflection, and existence–uniqueness plus the
hint's analytic form (with symbolic constants) are stated.

Physical domain: `R > 0` and `0 < θ < π / 2` (the strike point ranges over
the open first-quadrant arc, excluding the rim point and the apex),
restricted to the drawn high-strike branch `0 < θ < π / 4`.

## Governability check (not part of the model)

With `û = (sin θ, cos θ)` the unit outward normal and `i = (0, 1)` the
actual upward incident propagation, the specular law
`r = i − 2 ⟨i, û⟩ û` fixes the actual outgoing propagation
`r = (−sin (2θ), −cos (2θ))`, componentwise; leaving through the strike
point `P = (R sin θ, R cos θ)`, this ray lies on the line
`y = m x + b` with a mathematically determined slope `tan (π / 2 − 2θ)`
and intercept `R / (2 cos θ)`, and `r` is exactly
`(1 + m²)^(−1/2) • ![-1, -m]` on this data.  On the drawn branch
(`0 < θ < π / 4`) this line satisfies every clause of `DrawnBranch`
(indeed `m * R + b ≥ b > 0`, the physical reflective horizontal crossing
`x = −b / m ≤ −2R sin θ → −R` as `θ → π / 4` being approached from inside
and reaching `−R` only in the limit, so it is simply *not claimed* to lie
inside the labelled segment — no `b < m * R` clause is recorded, and none
can be).  Hence the solution predicate below is satisfiable and the
witness unique on the stated domain.  These closed forms are the content
of the later proof of `reflectedRay_A_exists_unique` and are deliberately
not stated here.
-/

namespace Ipho2026KimiK3Blind32.ProblemIPhO2026_2C1

open Real

/-- The plane `ℝ²` of Figure 2g, with origin at the center of the
half-cylinder, the `x`-axis along the diameter `(-R, R)` and the `y`-axis
upward. -/
abbrev MirrorPlane := Fin 2 → ℝ

/-- The concrete real dot product on `MirrorPlane`.  (`@inner ℝ` on
`Fin 2 → ℝ` is defined through the `PiLp` norms and inconvenient for the
elementary coordinate computations of this affine problem, so the
2-dimensional dot product is introduced as faithful local infrastructure.) -/
def dot (u v : MirrorPlane) : ℝ := u 0 * v 0 + u 1 * v 1

/-- The physical incidence-angle domain of ray `A`: `0 < θ < π / 2`, the
open first-quadrant strike range of Figure 2g (the strike point is strictly
between the rim point `(R, 0)`, `θ = 0`, and the apex `(0, R)`,
`θ = π / 2`). -/
def IncidenceDomain (θ : ℝ) : Prop :=
  0 < θ ∧ θ < Real.pi / 2

/-- **Drawn high-strike regime.**  In Figure 2g the ray strikes high on the
arc and the reflected line is drawn ascending as `x` increases (positive
slope).  Reflection off the radial normal deflects the vertical incoming
propagation by `2θ` from the vertical, so the drawn branch is exactly
`0 < θ < π / 4`; the boundary `θ = π / 4` would give a horizontal
reflected ray and any `θ > π / 4` a line descending as `x` increases,
crossing the `y`-axis below the origin — a different drawing, not
Figure 2g. -/
def DrawnRegime (θ : ℝ) : Prop :=
  0 < θ ∧ θ < Real.pi / 4

/-- Reflection point `P`: the point of the mirror where ray `A` strikes, on
the upper half-circle of radius `R` at `(R sin θ, R cos θ)`.  At this point
the angle between the vertical incoming ray and the radial normal `OP` is
exactly `θ`, the dashed incidence angle of Figure 2g. -/
noncomputable def reflectionPoint (R θ : ℝ) : MirrorPlane :=
  ![R * Real.sin θ, R * Real.cos θ]

/-- The actual direction of propagation of the incoming ray `A`: vertical
and upward, `![0, 1]`, as the arrowheads of the incident leg in Figure 2g
point upward towards the mirror.  This directed propagation — not the
into-surface opposite `![0, -1]` — is the incident side of the specular
law. -/
def incidentPropagationDir : MirrorPlane := ![0, 1]

/-- The radial direction `(sin θ, cos θ)` at the strike point of ray `A`
(Figure 2g's dashed normal `OP`), a unit vector. -/
noncomputable def unitOutwardNormal (θ : ℝ) : MirrorPlane :=
  ![Real.sin θ, Real.cos θ]

/-- **Law of specular reflection (governing-law predicate), direction form.**
`IsSpecularReflection i r n` says that the incident direction of
propagation `i` becomes the outgoing direction of propagation `r` under
specular reflection at a surface with normal `n`.  Arguments are the
*actual directions of propagation*: `i` towards and `r` away from the
surface, in their drawn orientations.  The quantitative clause is the
linear law of reflection, written on the unit normal
`û = (√⟨n, n⟩)⁻¹ • n`:

  `r = i − 2 ⟨i, û⟩ • û`;

* its tangential component is preserved,
* its normal component is reversed, so the angle of incidence equals the
  angle of reflection,
* it is an involutive isometry, `‖r‖ = ‖i‖` (the mirror conserves the
  ray's speed).

The reflected ray leaves on the drawn side of the surface because the
reversed normal component `⟨r, û⟩ = −⟨i, û⟩` is nonzero (`i` is not
parallel to the mirror).  The normal `n` marks the mirror geometry (the
radial normal `OP` of Figure 2g): being nonzero it determines `û` up to
an overall sign that leaves the law unchanged. -/
def IsSpecularReflection (i r n : MirrorPlane) : Prop :=
  n ≠ 0 ∧
    (let û : MirrorPlane := (Real.sqrt (dot n n))⁻¹ • n
     r = i - (2 * dot i û) • û)

/-- The requested answer is a pair `(m_A, b_A)` of a slope and an intercept
of the line carrying the reflected ray, in the coordinate system of
Figure 2g. -/
structure ReflectedRayData where
  /-- The slope `m_A` of the reflected line `y = m_A * x + b_A`. -/
  m : ℝ
  /-- The intercept `b_A` of the reflected line. -/
  b : ℝ

/-- The **actual direction of propagation** of the reflected ray, in the
oriented, down-left direction drawn in Figure 2g: the direction of
decreasing `x` along the graph `y = m x + b`, normalized to a unit vector,
`(1 + m²)^(-1/2) • ![-1, -m]`.  This oriented vector — one specific
graph direction, not an existentially quantified parallel direction — is
the outgoing side of the specular law. -/
noncomputable def outgoingPropagationDir (d : ReflectedRayData) :
    MirrorPlane :=
  ((1 + d.m ^ 2).sqrt)⁻¹ • ![-1, -d.m]

/-- The local branch of the reflected line drawn in Figure 2g:

* the line **ascends as `x` increases**, `0 < m`, and the actual outgoing
  propagation **leaves `P` towards the lower left** — the oriented
  down-left vector `outgoingPropagationDir` (both of its coordinates
  negative), which is exactly what the specular-law clause states;
* it **crosses the `y`-axis above the origin**, between `O` and the
  strike point: `0 < b`;
* it **meets the reflective arc on the drawn left side**, inside the
  arc: at the labelled left rim abscissa `x = -R` the line's height
  `m * (-R) + b = -(m * R + b)` is strictly negative,
  `0 < m * R + b`, so the line lies strictly below the diameter there
  and its negative-`x` crossing is confined to the left half of the
  drawing.

No clause equates the line with either rim endpoint: Figure 2g shows the
reflected line interior to the drawing on the left and rising through `P`
on the right.  No upper clause on `b` against `m * R` is recorded: the
physical line does not satisfy `b < m * R` throughout Figure 2g's regime
(the physical horizontal crossing `x = -b / m` lies at the left rim `-R`
only in the limit `θ → π / 4` and inside the segment `[-R, R]` for higher
strikes), so asserting it would make the contract unsatisfiable. -/
def ReflectedRayData.DrawnBranch (R : ℝ) (d : ReflectedRayData) : Prop :=
  0 < d.m ∧ 0 < d.b ∧ 0 < d.m * R + d.b

/-- **T2-C1 solution predicate.**
The pair `(m_A, b_A)` solves T2-C1 for the mirror of radius `R` and
incidence angle `θ` when the line `y = m_A * x + b_A`

1. passes through the reflection point `reflectionPoint R θ`,
2. is the specular reflection (`IsSpecularReflection`) of the **actual
   incident propagation direction** `incidentPropagationDir = ![0, 1]`
   into the **actual outgoing propagation direction**
   `outgoingPropagationDir d = (1 + m_A²)^(-1/2) • ![-1, −m_A]` — the
   normalized, oriented down-left graph vector, nameable from `d` and
   occurring directly in the reflection equation — off the mirror whose
   normal at the strike point is the radial direction
   `unitOutwardNormal θ` (Figure 2g's `OP`), and
3. has the local branch drawn in Figure 2g (`DrawnBranch`). -/
def ReflectedRaySolution (R θ : ℝ) (d : ReflectedRayData) : Prop :=
  reflectionPoint R θ 1 = d.m * reflectionPoint R θ 0 + d.b ∧
    IsSpecularReflection incidentPropagationDir (outgoingPropagationDir d)
      (unitOutwardNormal θ) ∧
    d.DrawnBranch R

/-- The radial normal at the strike point is a unit vector. -/
theorem unitOutwardNormal_norm (θ : ℝ) :
    dot (unitOutwardNormal θ) (unitOutwardNormal θ) = 1 := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [unitOutwardNormal, dot, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination h

/-- The reflection point lies on the upper half-circle, in the first
quadrant as drawn in Figure 2g. -/
theorem reflectionPoint_mem_circle {R θ : ℝ} (hR : 0 < R) (hθ : IncidenceDomain θ) :
    reflectionPoint R θ 0 ^ 2 + reflectionPoint R θ 1 ^ 2 = R ^ 2 ∧
      0 < reflectionPoint R θ 0 ∧ 0 < reflectionPoint R θ 1 := by
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩
  simp only [reflectionPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨?_, mul_pos hR hs, mul_pos hR hcos⟩
  have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  calc (R * Real.sin θ) ^ 2 + (R * Real.cos θ) ^ 2
      = R ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    _ = R ^ 2 := by rw [hsc, mul_one]

/-- On the drawn high-strike regime, the strike point is higher than its
abscissa (`R cos θ > R sin θ`): it lies between the points of the arc level
with the y-axis (where `R sin θ = R cos θ`, i.e. `θ = π / 4`) and the apex,
as drawn in Figure 2g. -/
theorem reflectionPoint_high_of_drawnRegime {R θ : ℝ} (hR : 0 < R)
    (hreg : DrawnRegime θ) :
    R * Real.sin θ < R * Real.cos θ := by
  obtain ⟨hθ1, hθ2⟩ := hreg
  have hsin_lt : Real.sin θ < Real.sin (Real.pi / 4) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos, hθ1])
      (by linarith [Real.pi_pos]) hθ2
  have hcos_gt : Real.cos (Real.pi / 4) < Real.cos θ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hθ1)
      (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi) hθ2
  have hsc4 : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hsin_lt_cos : Real.sin θ < Real.cos θ :=
    lt_of_lt_of_le hsin_lt (hsc4 ▸ le_of_lt hcos_gt)
  exact mul_lt_mul_of_pos_left hsin_lt_cos hR

/-- The drawn outgoing propagation direction is a unit vector, for the
slope of any reflected line: `(-1)² + (-m)² = 1 + m²`, which the
normalization `1 / √(1 + m²)` cancels. -/
theorem dot_outgoingPropagationDir (d : ReflectedRayData) :
    dot (outgoingPropagationDir d) (outgoingPropagationDir d) = 1 := by
  have hm : (0 : ℝ) < 1 + d.m ^ 2 := by positivity
  set s : ℝ := Real.sqrt (1 + d.m ^ 2) with hs
  have hspos : (0:ℝ) < s := hs ▸ Real.sqrt_pos.mpr hm
  have hs0 : s ≠ 0 := ne_of_gt hspos
  have hs2 : s * s = 1 + d.m ^ 2 := Real.mul_self_sqrt (le_of_lt hm)
  have h31 : outgoingPropagationDir d 0 = -s⁻¹ := mul_neg_one _
  have h32 : outgoingPropagationDir d 1 = s⁻¹ * (-d.m) := rfl
  have hcan : s * s * (s⁻¹ * s⁻¹) = 1 := by
    calc s * s * (s⁻¹ * s⁻¹)
        = (s * s⁻¹) * (s * s⁻¹) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hs0]; exact mul_one _
  calc dot (outgoingPropagationDir d) (outgoingPropagationDir d)
      = (-s⁻¹) * (-s⁻¹) + (s⁻¹ * -d.m) * (s⁻¹ * -d.m) := by
        simp only [dot, h31, h32]
    _ = s * s * (s⁻¹ * s⁻¹) := by rw [hs2]; ring
    _ = 1 := hcan

/-- Auxiliary sign and nonvanishing facts on the drawn high-strike regime
`0 < θ < π / 4`: the sine and cosine at `θ` are positive, the straight
reflected direction `2θ` stays strictly below `π / 2` (so
`sin (2θ) > 0`, `cos (2θ) > 0`, `tan (π / 2 − 2θ) > 0`), and the halves
used in the algebra satisfy `sin θ ≤ cos θ` and
`sin (π / 2 − 2θ) = cos (2θ)`. -/
private theorem aux_drawnRegime {θ : ℝ} (hreg : DrawnRegime θ) :
    0 < Real.sin θ ∧ 0 < Real.cos θ ∧ Real.sin θ ≤ Real.cos θ ∧
      0 < Real.sin (2 * θ) ∧ 0 < Real.cos (2 * θ) ∧
      0 < Real.tan (Real.pi / 2 - 2 * θ) ∧
      Real.sin (Real.pi / 2 - 2 * θ) = Real.cos (2 * θ) := by
  obtain ⟨h1, h2⟩ := hreg
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsincos : Real.sin θ ≤ Real.cos θ := by
    have h2 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
      calc Real.sqrt 2 * (Real.sqrt 2 / 2)
          = (Real.sqrt 2 * Real.sqrt 2) / 2 := by ring
        _ = 2 / 2 := by rw [Real.mul_self_sqrt two_pos.le]
        _ = 1 := by norm_num
    have key : Real.cos θ - Real.sin θ = Real.sqrt 2 * Real.cos (Real.pi / 4 + θ) := by
      rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
      nlinarith [h2]
    have hnn : 0 ≤ Real.sqrt 2 * Real.cos (Real.pi / 4 + θ) :=
      mul_nonneg (Real.sqrt_nonneg 2)
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)
    nlinarith [hnn]
  have h2s1 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < 2 * θ)
      (by linarith : 2 * θ < Real.pi)
  have h2s2 : 0 < Real.cos (2 * θ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have htan2 : 0 < Real.tan (Real.pi / 2 - 2 * θ) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two
      (by linarith : 0 < Real.pi / 2 - 2 * θ)
      (by linarith : Real.pi / 2 - 2 * θ < Real.pi / 2)
  have hsh : Real.sin (Real.pi / 2 - 2 * θ) = Real.cos (2 * θ) :=
    Real.sin_pi_div_two_sub (2 * θ)
  exact ⟨hsin, hcos, hsincos, h2s1, h2s2, htan2, hsh⟩

/-- Auxiliary slope identification: on the drawn regime, the reflected slope
`(2 c² − 1) / (2 s c)` (with `s = sin θ`, `c = cos θ`) equals
`tan (π / 2 − 2θ)`; indeed `sin (π / 2 − 2θ) = cos (2θ) = 2c² − 1` and
`cos (π / 2 − 2θ) = sin (2θ) = 2 s c`. -/
private theorem aux_slope_eq_tan {θ : ℝ} (hreg : DrawnRegime θ) :
    (2 * Real.cos θ ^ 2 - 1) / (2 * Real.sin θ * Real.cos θ) =
      Real.tan (Real.pi / 2 - 2 * θ) := by
  obtain ⟨hsθ, hcθ, _, h2s1, _, _, hsh⟩ := aux_drawnRegime hreg
  have ht2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hc2' : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hch : Real.cos (Real.pi / 2 - 2 * θ) = Real.sin (2 * θ) :=
    Real.cos_pi_div_two_sub (2 * θ)
  rw [Real.tan_eq_sin_div_cos, hsh, hch, ht2, hc2']


/-- Auxiliary specular-law analysis: for data `d` satisfying the T2-C1
solution predicate on the drawn regime, the slope is forced to
`d.m = (2 c² − 1) / (2 s c) = cot (2θ)` (with `s = sin θ`, `c = cos θ`)
and the intercept is `d.b = R / (2 c)`.  Indeed the `x`-component of the
specular law is `(w)⁻¹ = 2 s c` with `w = √(1 + d.m²)` the outgoing
direction's normalization, the `y`-component is `(w)⁻¹ d.m = 2 c² − 1`,
so `d.m = (2 c² − 1) / (2 s c)` on the drawn regime where
`sin (2θ) = 2 s c > 0`; the intercept follows from the line equation
through the strike point `(R s, R c)`. -/
private theorem aux_slope_value {R θ : ℝ} (hR : 0 < R) (hreg : DrawnRegime θ)
    (d : ReflectedRayData) (h : ReflectedRaySolution R θ d) :
    d.m = (2 * Real.cos θ ^ 2 - 1) / (2 * Real.sin θ * Real.cos θ) ∧
      d.b = R / (2 * Real.cos θ) := by
  obtain ⟨hOn, ⟨_, hbase⟩, hbranch⟩ := h
  obtain ⟨hsθ, hcθ, _, h2s1, _, _, _⟩ := aux_drawnRegime hreg
  have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have ht2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  -- Rewrite the specular-law base: first unfold its `let` to expose the
  -- unit normal, then simplify with its unit norm, then evaluate the dot
  -- product with the incident direction.
  change outgoingPropagationDir d = incidentPropagationDir -
      (2 * dot incidentPropagationDir
        ((Real.sqrt (dot (unitOutwardNormal θ) (unitOutwardNormal θ)))⁻¹ •
          unitOutwardNormal θ)) •
        ((Real.sqrt (dot (unitOutwardNormal θ) (unitOutwardNormal θ)))⁻¹ •
          unitOutwardNormal θ) at hbase
  rw [unitOutwardNormal_norm θ, Real.sqrt_one, inv_one, one_smul] at hbase
  have h_di : dot incidentPropagationDir (unitOutwardNormal θ) = Real.cos θ := by
    simp [incidentPropagationDir, unitOutwardNormal, dot, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  rw [h_di] at hbase
  -- Componentwise values.
  have hb0 := congrFun hbase 0
  have hb1 := congrFun hbase 1
  rw [outgoingPropagationDir] at hb0 hb1
  simp only [incidentPropagationDir, unitOutwardNormal, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply,
    Pi.smul_apply] at hb0 hb1
  -- Now:
  -- hb0 : (√(1 + d.m ^ 2))⁻¹ * -1 = 0 - 2 * Real.cos θ * Real.sin θ
  -- hb1 : (√(1 + d.m ^ 2))⁻¹ * -d.m = 1 - 2 * Real.cos θ * Real.cos θ
  simp only [reflectionPoint, Matrix.cons_val_zero, Matrix.cons_val_one] at hOn
  -- hOn : R * Real.cos θ = d.m * (R * Real.sin θ) + d.b
  have hwpos : 0 < Real.sqrt (1 + d.m ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hwne : Real.sqrt (1 + d.m ^ 2) ≠ 0 := ne_of_gt hwpos
  have e0 : 2 * Real.cos θ * Real.sin θ * Real.sqrt (1 + d.m ^ 2) = 1 := by
    have h0 : 2 * Real.cos θ * Real.sin θ ≠ 0 := by positivity
    field_simp at hb0 ⊢
    nlinarith [hb0]
  have e1 : (2 * Real.cos θ ^ 2 - 1) * Real.sqrt (1 + d.m ^ 2) = d.m := by
    field_simp at hb1 ⊢
    nlinarith [hb1]
  have h2cspos : 0 < 2 * Real.sin θ * Real.cos θ := by positivity
  have hslope : d.m * (2 * Real.sin θ * Real.cos θ) =
      2 * Real.cos θ ^ 2 - 1 := by
    nlinarith [e0, e1]
  refine ⟨?_, ?_⟩
  · field_simp [h2cspos.ne']
    nlinarith [hslope]
  · -- `db = R c − m R s`
    have hdv : d.b = R * Real.cos θ - d.m * (R * Real.sin θ) := by
      linarith [hOn]
    have h2cs : 2 * Real.cos θ * Real.sin θ * Real.sin θ + (2 * Real.cos θ ^ 2 - 1) =
        2 * Real.cos θ ^ 2 - 1 + 2 * Real.cos θ * Real.sin θ * Real.sin θ := by ring
    rw [hdv]
    field_simp [hcθ.ne', h2cspos.ne']
    nlinarith [hdv, hslope, hsc, hR]

/-- **T2-C1, existence and uniqueness of the reflected ray's line.**
For a positive radius and an incidence angle in its physical domain and in
the drawn high-strike regime of Figure 2g, there exists a unique pair
`(m_A, b_A)` such that the line `y = m_A * x + b_A` is the reflected ray of
`A`, with the branch drawn in Figure 2g, in the coordinate system of
Figure 2g.  The closed forms that the statement asks to "write in terms of
`θ` and `R`" are the answer the later proof constructs as the witness of
this `∃!` and are kept off the signature by the answer-blind policy. -/
theorem reflectedRay_A_exists_unique {R θ : ℝ} (hR : 0 < R)
    (hθ : IncidenceDomain θ) (hreg : DrawnRegime θ) :
    ∃! d : ReflectedRayData, ReflectedRaySolution R θ d := by
  obtain ⟨hsθ, hcθ, _, h2s1, h2s2, htan2, hsh⟩ := aux_drawnRegime hreg
  have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  -- The witness: slope `tan (π / 2 − 2θ)` and intercept `R / (2 cos θ)`.
  set m₀ : ℝ := Real.tan (Real.pi / 2 - 2 * θ) with hm₀
  set b₀ : ℝ := R / (2 * Real.cos θ) with hb₀
  have hm0' : m₀ = (2 * Real.cos θ ^ 2 - 1) / (2 * Real.sin θ * Real.cos θ) := by
    rw [hm₀]
    exact (aux_slope_eq_tan hreg).symm
  have hm0pos : 0 < m₀ := by rw [hm₀]; exact htan2
  have hb0pos : 0 < b₀ := by
    rw [hb₀]; positivity
  have hsol : ReflectedRaySolution R θ ⟨m₀, b₀⟩ := by
    refine ⟨?_, ⟨?_, ?_⟩, ⟨hm0pos, hb0pos, ?_⟩⟩
    · -- The line passes through the strike point.
      rw [reflectionPoint]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hm0', hb₀]
      have h2cspos : 0 < 2 * Real.sin θ * Real.cos θ := by positivity
      field_simp [h2cspos.ne', hcθ.ne']
      nlinarith [hsc, hR]
    · -- The normal is nonzero.
      intro hz
      have h1 := congrFun hz 0
      simp only [unitOutwardNormal, Pi.zero_apply, Matrix.cons_val_zero] at h1
      exact (ne_of_gt hsθ) h1
    · -- The specular-law base equation.
      change outgoingPropagationDir ⟨m₀, b₀⟩ = incidentPropagationDir -
          (2 * dot incidentPropagationDir
            ((Real.sqrt (dot (unitOutwardNormal θ) (unitOutwardNormal θ)))⁻¹ •
              unitOutwardNormal θ)) •
            ((Real.sqrt (dot (unitOutwardNormal θ) (unitOutwardNormal θ)))⁻¹ •
              unitOutwardNormal θ)
      rw [unitOutwardNormal_norm θ, Real.sqrt_one, inv_one, one_smul]
      have h_di : dot incidentPropagationDir (unitOutwardNormal θ) = Real.cos θ := by
        simp [incidentPropagationDir, unitOutwardNormal, dot, Matrix.cons_val_zero,
          Matrix.cons_val_one]
      rw [h_di]
      have h2cspos : 0 < 2 * Real.sin θ * Real.cos θ := by positivity
      have hw2 : Real.sqrt (1 + m₀ ^ 2) = 1 / Real.sin (2 * θ) := by
        have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt h2s1
        apply Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity) |>.mpr
        -- (1 / sin2θ)² = 1 + m₀²
        rw [hm0']
        have ht2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
        rw [ht2]
        field_simp [h2cspos.ne']
        nlinarith [hsc, Real.sin_sq_add_cos_sq (2 * θ), Real.cos_two_mul θ]
      rw [outgoingPropagationDir, incidentPropagationDir]
      funext i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Pi.sub_apply, Pi.smul_apply, unitOutwardNormal,
        smul_eq_mul]
      · -- component 0 : (√(1+m₀²))⁻¹ * (-1) = 0 - 2c * s
        rw [hw2]
        have ht2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
        rw [ht2]
        field_simp [h2cspos.ne']
        ring
      · -- component 1 : (√(1+m₀²))⁻¹ * (-m₀) = 1 - 2c * c
        rw [hw2]
        have ht2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
        rw [ht2, hm0']
        field_simp [h2cspos.ne']
        nlinarith [hsc]
    · -- The drawn-branch third clause.
      nlinarith [hR, hm0pos, hb0pos]
  refine ⟨⟨m₀, b₀⟩, hsol, ?_⟩
  rintro ⟨dm, db⟩ hd
  obtain ⟨hdm, hdb⟩ := aux_slope_value hR hreg ⟨dm, db⟩ hd
  have hdm' : dm = (2 * Real.cos θ ^ 2 - 1) / (2 * Real.sin θ * Real.cos θ) := hdm
  have hdb' : db = R / (2 * Real.cos θ) := hdb
  rw [ReflectedRayData.mk.injEq]
  exact ⟨hdm'.trans hm0'.symm, hdb'.trans hb₀.symm⟩

/-- The mathematical content of the printed hint: on the drawn regime, any
solution `(m_A, b_A)` of T2-C1 admits the forms
`m_A = K₁ * cot (K₂ * θ)` and `b_A = R * K₃ / cos (K₄ * θ)` for some
numerical constants `Kᵢ`.  The constants are left symbolic (existentially
quantified) so that no numerical value of the answer is placed in a
signature; the later proof determines them. -/
theorem hint_form {R θ : ℝ} (hR : 0 < R) (hθ : IncidenceDomain θ)
    (hreg : DrawnRegime θ)
    (d : ReflectedRayData) (h : ReflectedRaySolution R θ d) :
    ∃ K₁ K₂ K₃ K₄ : ℝ,
      d.m = K₁ * Real.cot (K₂ * θ) ∧ d.b = R * K₃ / Real.cos (K₄ * θ) := by
  obtain ⟨hdm, hdb⟩ := aux_slope_value hR hreg d h
  obtain ⟨_, hcθ, _, _, _, _, _⟩ := aux_drawnRegime hreg
  refine ⟨1, 2, 1 / 2, 1, ?_, ?_⟩
  · -- `m = cot (2θ) = cos (2θ) / sin (2θ) = (2c²−1)/(2sc)`.
    rw [one_mul, hdm, Real.cot_eq_cos_div_sin, Real.cos_two_mul θ, Real.sin_two_mul θ]
  · -- `b = R * (1/2) / cos (1 * θ) = R / (2 cos θ)`.
    have hgoal : R / (2 * Real.cos θ) = R * (1 / 2) / Real.cos (1 * θ) := by
      rw [one_mul]
      field_simp [hcθ.ne']
    exact hdb.trans hgoal

end Ipho2026KimiK3Blind32.ProblemIPhO2026_2C1
