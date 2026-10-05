import Mathlib

/- USER: Mandatory contract repair. Keep exactly one namespace/document and compile it. Characterize an unknown coefficient `c` answer-free by `(fun δ => law.slope (θ + δ) - law.slope θ - c * δ) =o[nhds 0] (fun δ => δ)` (and analogously for intercept), prove its existence and uniqueness from differentiability, and expose the fixed first-order correction terms `c_m * Δθ`, `c_b * Δθ`. CRITICAL: do not assert either correction equals the full finite increment `mB-mA` or `bB-bA`; differentiability only supplies an `o(Δθ)` remainder, and the exact equality is refuted by `f(x)=x^2`. Do not define a candidate using `deriv ... * Δθ` or a deviation from it. Keep dummy `δ` distinct from fixed nonzero `Δθ`. -/

/-!
# IPhO 2026, Problem 2 (T2), Part C.2 — Caustics and Cusp

Answer-blind formalization of subquestion T2-C2:

> Ray `A` is reflected by the half-cylindrical mirror into the line
> `y = m_A * x + b_A` (part C.1).  A neighboring ray `B`, parallel to `A`,
> strikes the mirror at incidence angle `θ + Δθ`, with `Δθ ≪ θ`, and its
> reflected line is `y = m_B * x + b_B`.
>
> **Expand `m_B` and `b_B` to first order in `Δθ`.**

## Geometry read from Figure 2g and the statement text (radius-is-`R`)

* The mirror is the upper half of the circle of radius `R` centred at the
  origin of the `(x, y)` system of Figure 2g; the `x`-axis runs along the
  flat face and the endpoints of the half-circle are labelled `−R` and `R`.
* Both incoming rays are vertical (parallel to the `y`-axis), their
  arrowheads pointing upward toward the mirror; the *downward* vertical
  direction `!(0, −1)` is the into-surface incident direction used by the
  specular law.
* A ray incident at angle `θ` from the radial outward normal strikes the
  mirror at the point `P = (R sin θ, R cos θ)` of Figure 2g; the incidence
  angle is measured between the incoming ray and the radial normal `OP`
  (dashed).  Reflecting the downward vertical direction in the `OP` normal
  gives the outgoing propagation direction, which on the C.1 law
  `m (θ) = −tan (2 θ)` (equivalently `cot (2 θ)` on the `θ < π / 4`
  down-left / positive-slope branch shown in the figure) points down-left,
  and the reflected line crosses the `y`-axis.
* A neighboring ray `B`, parallel to `A` (hence also vertical), strikes at
  incidence angle `θ + Δθ` with `Δθ ≪ θ`; both rays obey the same law of
  specular reflection, only at shifted incidence angles.

## Previous part (C.1, statement of law — conclusions not imported)

Part C.1 asked for the slope `m_A` and intercept `b_A` of the reflected ray
`A` in terms of `θ` and `R`, expected in the form `m_A = K₁ cot (K₂ θ)`,
`b_A = R K₃ / cos (K₄ θ)` with numerical constants `Kᵢ`.  Being closed-form
expressions built from `tan` and `cos`, the assignment `θ ↦ (m, b)`
delivered by the reflection law is a differentiable function of `θ` on
`(0, π/2)`.  We record this as the hypothesis structure
`SlopeInterceptDifferentiability`, so the present file does not depend on
the C.1 closed form; the prover stage may supply the C.1 witness
`θ ↦ (-tan (2 θ), R / cos (2 θ))` from the sibling file.

## Current part (C.2) — answer-blind formulation (iteration-016 redraft)

"Expand `m_B` and `b_B` to first order in `Δθ`" is the **Taylor expansion
of the law in the perturbation variable** `δ → 0`:

    m (θ + δ) = m (θ) + c_m * δ + o (δ),    b (θ + δ) = b (θ) + c_b * δ + o (δ),

for a *unique* pair of linear coefficients `(c_m, c_b)` — a coefficient is
determined as soon as the residual `(m (θ + δ) − m θ − c * δ) / δ → 0` on
a punctured neighborhood of `0`, and differentiability of the law then
identifies it with `deriv m θ`, resp. `deriv b θ`.  The fixed, *nonzero*
separation `Δθ` of the physical rays `A` and `B` is **kept strictly
separate** from the dummy asymptotic variable `δ`: `Δθ` appears only
*evaluated*, in the two-ray corrections `c_m * Δθ`, `c_b * Δθ` whose
exhaustion (all first-order corrections have this shape) and uniqueness are
the last two clauses of the target.  `(c_m, c_b)` are answer-blind: the
signature carries only the existence-uniqueness of the little-`o`
approximation, never the closed-form `deriv` of any C.1 expression.

This repairs the iter-014/015 contract defect: a standalone constant placed
inside a `=O[𝓝[≠] 0] (· ^ 2)` clause is forced to `0` by continuity at
`δ = 0`, which then forces `deriv slope θ = 0` — false for the C.1 law
(e.g. `slope θ = −tan (2 θ)` on `(0, π/2)`).  No standalone constant occurs
inside any neighborhood clause here: the only quantities under `=o[𝓝 0]`
are the law increments and the candidate linear term `c * δ`.
-/

namespace Ipho2026KimiK3Blind32.ProblemIPhO2026_2C2

open Real Set Filter Asymptotics
open scoped Topology

/-- The Euclidean plane of Figure 2g, with origin at the center of the
half-cylindrical mirror, the `x`-axis along the flat face (diameter) from
`−R` to `R`, and the `y`-axis vertical.  The `2`-dimensional dot product on
this space is introduced below, since the generic `inner` of
`EuclideanSpace ℝ (Fin 2)` is still `1`-generic in the current Mathlib. -/
abbrev MirrorPlane := EuclideanSpace ℝ (Fin 2)

/-- The concrete real dot product on `MirrorPlane`. -/
noncomputable def dot (u v : MirrorPlane) : ℝ := u 0 * v 0 + u 1 * v 1

@[simp] lemma dot_apply (u v : MirrorPlane) :
    dot u v = u 0 * v 0 + u 1 * v 1 := rfl

/-- A configuration of the half-cylindrical mirror of Figure 2g: its radius
`R`, with the physical condition `R > 0`.  The reflecting half-circle is
`x² + y² = R², y > 0`, with center at the origin. -/
structure HalfCylindricalMirror where
  /-- Radius `R` of the cylindrical mirror. -/
  R : ℝ
  /-- A physical mirror has positive radius. -/
  R_pos : 0 < R

/-- The reflecting arc of the half-cylindrical mirror: the half-circle
`{(x, y) : x² + y² = R², y > 0}` of Figure 2g. -/
def mirrorArc (G : HalfCylindricalMirror) : Set MirrorPlane :=
  {p | ‖p‖ = G.R ∧ p 1 > 0}

/-- Parametrization of the incidence point of Figure 2g: a ray incident at
angle `θ` from the outward radial normal hits the mirror at
`P = (R sin θ, R cos θ)`. -/
noncomputable def incidencePoint (G : HalfCylindricalMirror) (θ : ℝ) : MirrorPlane :=
  WithLp.toLp 2 ![G.R * Real.sin θ, G.R * Real.cos θ]

@[simp] lemma incidencePoint_zero (G : HalfCylindricalMirror) (θ : ℝ) :
    incidencePoint G θ 0 = G.R * Real.sin θ := rfl

@[simp] lemma incidencePoint_one (G : HalfCylindricalMirror) (θ : ℝ) :
    incidencePoint G θ 1 = G.R * Real.cos θ := rfl

/-- The outward unit normal to the mirror at a point of the arc is the radial
direction: at incidence angle `θ` from the normal, the outward unit normal is
`(sin θ, cos θ)`. -/
noncomputable def outwardNormal (_G : HalfCylindricalMirror) (θ : ℝ) : MirrorPlane :=
  WithLp.toLp 2 ![Real.sin θ, Real.cos θ]

/-- The outward radial normal is a unit vector. -/
theorem norm_outwardNormal (G : HalfCylindricalMirror) (θ : ℝ) :
    ‖outwardNormal G θ‖ = 1 := by
  have hsq : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := Real.sin_sq_add_cos_sq θ
  have h2 : ‖outwardNormal G θ‖ ^ 2 = 1 := by
    have hsq2 : ‖outwardNormal G θ‖ ^ 2 = (Real.sin θ)^2 + (Real.cos θ)^2 := by
      have hSnn : (0:ℝ) ≤ ∑ i, ‖(outwardNormal G θ) i‖^2 := by positivity
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt hSnn, Fin.sum_univ_two,
          Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      simp [outwardNormal]
    rw [hsq2, hsq]
  have hnn : (0:ℝ) ≤ ‖outwardNormal G θ‖ := norm_nonneg _
  nlinarith [h2, hnn]

/-- The outward normal at `incidencePoint G θ` is the radial direction of
that point: `outwardNormal G θ = G.R⁻¹ • incidencePoint G θ`. -/
theorem outwardNormal_eq_radial (G : HalfCylindricalMirror) (θ : ℝ) :
    outwardNormal G θ = (G.R)⁻¹ • incidencePoint G θ := by
  have hsin : (G.R)⁻¹ * (G.R * Real.sin θ) = Real.sin θ := by
    exact inv_mul_cancel_left₀ (ne_of_gt G.R_pos) _
  have hcos : (G.R)⁻¹ * (G.R * Real.cos θ) = Real.cos θ := by
    exact inv_mul_cancel_left₀ (ne_of_gt G.R_pos) _
  have h0 : ((G.R)⁻¹ • incidencePoint G θ) 0 = Real.sin θ := by
    show (G.R)⁻¹ * (incidencePoint G θ 0) = Real.sin θ
    rw [incidencePoint_zero]; exact hsin
  have h1 : ((G.R)⁻¹ • incidencePoint G θ) 1 = Real.cos θ := by
    show (G.R)⁻¹ * (incidencePoint G θ 1) = Real.cos θ
    rw [incidencePoint_one]; exact hcos
  ext i
  fin_cases i
  · show Real.sin θ = ((G.R)⁻¹ • incidencePoint G θ) 0
    rw [h0]
  · show Real.cos θ = ((G.R)⁻¹ • incidencePoint G θ) 1
    rw [h1]

/-- The incidence point of a ray meeting the mirror at angle `θ ∈ (0, π/2)`
lies on the reflecting arc. -/
theorem incidencePoint_mem_mirrorArc (G : HalfCylindricalMirror) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) : incidencePoint G θ ∈ mirrorArc G := by
  obtain ⟨h0, htop⟩ := hθ
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  constructor
  · have h2 : ‖incidencePoint G θ‖ ^ 2 = (G.R) ^ 2 := by
      have hsq : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := Real.sin_sq_add_cos_sq θ
      have hsq2 : ‖incidencePoint G θ‖ ^ 2 = (G.R * Real.sin θ)^2 + (G.R * Real.cos θ)^2 := by
        have hSnn : (0:ℝ) ≤ ∑ i, ‖(incidencePoint G θ) i‖^2 := by positivity
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt hSnn, Fin.sum_univ_two,
            Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
        simp [incidencePoint]
      nlinarith [hsq, sq_nonneg G.R, sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]
    have hnn : (0:ℝ) ≤ ‖incidencePoint G θ‖ := norm_nonneg _
    nlinarith [h2, hnn, G.R_pos, sq_nonneg G.R]
  · have hy : incidencePoint G θ 1 = G.R * Real.cos θ := rfl
    rw [hy]
    exact mul_pos G.R_pos hcos_pos

/-- **Law of specular reflection (unit-direction form).**  Three unit vectors
`n, i, r` of the plane — the surface normal, the incident direction of
propagation into the mirror face, and the reflected direction of propagation
away from it — obey the law of reflection when

* `n` and `i` are not collinear (the incidence point is well defined), and
* `i` and `r` are antisymmetric about the normal axis: their normal
  components are opposite and their tangential components equal;
  equivalently, the angles each makes with the normal sum to `π`.

Because all three vectors are units, the angle condition is expressed through
dot products.  This is the physical governing law of parts C.1–C.4; it is
satisfiable (the mirror reflection of the incoming direction in the normal
is a witness) and is recorded from the statement of Figure 2g. -/
structure IsSpecular (n i r : MirrorPlane) : Prop where
  /-- The normal is a unit vector. -/
  hn : ‖n‖ = 1
  /-- The incident direction of propagation is a unit vector. -/
  hi : ‖i‖ = 1
  /-- The reflected direction of propagation is a unit vector. -/
  hr : ‖r‖ = 1
  /-- The incidence is not along the normal: normal and incidence directions
  are linearly independent, so the reflection point and the two propagation
  half-lines are well defined (`0 < incidence angle < π/2 < π`). -/
  hli : n ≠ i ∧ n ≠ -i
  /-- The angles with the unit normal sum to `π`: the reflected direction
  leaves the surface on the opposite side of the normal from where the
  incident direction arrives. -/
  hangle : Real.arccos (dot n i) + Real.arccos (dot n r) = Real.pi
  /-- The components of `i` and `r` perpendicular to the normal axis are
  equal and opposite (mirror antisymmetry). -/
  hperp : i - dot n i • n = -(r - dot n r • n)

/-- The half-cylindrical mirror of Figure 2g reflects a downward vertical ray
incident at angle `θ ∈ (0, π/2)` into a line having a slope–intercept
equation `y = m x + b`; part C.1 determines `m` and `b` in terms of `θ` and
`R`.  This structure records the reflection *law* as an abstract assignment
`θ ↦ (m, b)` together with the physical constraints it must obey: the law
of reflection holds at every incidence angle of the domain, and the
reflected line passes through the incidence point.

Since the reflected direction of propagation is a positive multiple of
`!(-1, -m)` (the direction of decreasing `x` along the graph
`y = m x + b`), the unit reflected direction of propagation is
`!(-1, -m) / √(1 + m²)`. -/
structure ReflectedRayLaw (G : HalfCylindricalMirror) where
  /-- The reflected slope–intercept data `(m, b)` as a function of the
  incidence angle `θ`; part C.1 asks for its closed form in terms of `θ`
  and `R`. -/
  slopeIntercept : ℝ → ℝ × ℝ
  /-- The incidence-angle domain of the law: for `0 < θ < π/2`, the outward
  radial unit normal, the incident downward vertical unit direction, and the
  reflected unit direction of propagation obey the law of reflection, and
  the reflected line passes through the incidence point with the delivered
  intercept (so it is exactly the graph of `y = m x + b`). -/
  domain : ∀ θ, θ ∈ Ioo 0 (Real.pi / 2) →
    IsSpecular (outwardNormal G θ) (WithLp.toLp 2 ![(0 : ℝ), -1])
      (((1 + (slopeIntercept θ).1 ^ 2).sqrt)⁻¹ •
        WithLp.toLp 2 ![-1, -(slopeIntercept θ).1]) ∧
    (incidencePoint G θ 1 =
      (slopeIntercept θ).1 * incidencePoint G θ 0 + (slopeIntercept θ).2)

/-- The slope `m` of the reflected ray at incidence angle `θ`. -/
def ReflectedRayLaw.slope {G : HalfCylindricalMirror} (law : ReflectedRayLaw G)
    (θ : ℝ) : ℝ :=
  (law.slopeIntercept θ).1

/-- The intercept `b` of the reflected ray at incidence angle `θ`. -/
def ReflectedRayLaw.intercept {G : HalfCylindricalMirror} (law : ReflectedRayLaw G)
    (θ : ℝ) : ℝ :=
  (law.slopeIntercept θ).2

/-- The outgoing unit direction of propagation of the reflected ray at
incidence angle `θ`: the normalized direction of decreasing `x` along
`y = m x + b`. -/
noncomputable def ReflectedRayLaw.outgoingDir {G : HalfCylindricalMirror}
    (law : ReflectedRayLaw G) (θ : ℝ) : MirrorPlane :=
  ((1 + law.slope θ ^ 2).sqrt)⁻¹ • WithLp.toLp 2 ![-1, -law.slope θ]

/-- The specular law at incidence angle `θ`, with the reflected unit
direction of propagation built from the delivered slope (the outgoing
direction of decreasing `x` along `y = m x + b`). -/
theorem ReflectedRayLaw.specular {G : HalfCylindricalMirror}
    (law : ReflectedRayLaw G) {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    IsSpecular (outwardNormal G θ) (WithLp.toLp 2 ![(0 : ℝ), -1])
      (law.outgoingDir θ) :=
  (law.domain θ hθ).1

/-- Unfolding of the line-incidence clause: the reflected line
`y = slope θ · x + intercept θ` passes through `incidencePoint G θ`. -/
theorem ReflectedRayLaw.line_through_incidencePoint {G : HalfCylindricalMirror}
    (law : ReflectedRayLaw G) {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    incidencePoint G θ 1 =
      law.slope θ * incidencePoint G θ 0 + law.intercept θ :=
  (law.domain θ hθ).2

/-- **Statement of the C.1 regularity used by C.2, kept answer-blind.**  The
reflected slope–intercept law is a differentiable function of the incidence
angle — as it must be, since part C.1 delivers it as a closed-form
expression in `tan`, `cos`, and `R`.  Differentiability is exactly the
strength needed for first-order expansions with `o(δ)` remainder.  The
prover stage may identify `slope θ = -tan (2 θ)` and
`intercept θ = R / cos (2 θ)` from the C.1 conclusions. -/
structure SlopeInterceptDifferentiability {G : HalfCylindricalMirror}
    (law : ReflectedRayLaw G) : Prop where
  /-- `θ ↦ m (θ)` is differentiable. -/
  slope_differentiable : Differentiable ℝ law.slope
  /-- `θ ↦ b (θ)` is differentiable. -/
  intercept_differentiable : Differentiable ℝ law.intercept

/-- **Set-up for T2-C2.**  The full physical context of part C.2: a
half-cylindrical mirror `G`, the specular reflected-ray law (C.1 data), ray
`A` incident at angle `θ ∈ (0, π/2)` with reflected line
`y = m_A x + b_A`, and a neighboring ray `B`, parallel to `A` before
reflection (hence also vertical), incident at `θ + Δθ` with
`0 < |Δθ| < θ` (so `Δθ ≠ 0` and `Δθ ≪ θ`), whose reflected line is
`y = m_B x + b_B`. -/
structure CausticNeighborContext where
  /-- The half-cylindrical mirror. -/
  G : HalfCylindricalMirror
  /-- The specular reflection law (C.1 data). -/
  law : ReflectedRayLaw G
  /-- The reflected law is a differentiable function of the incidence angle
  (C.1 delivers it in closed form). -/
  law_diff : SlopeInterceptDifferentiability law
  /-- The incidence angle `θ` of ray `A`, with `0 < θ < π / 2`. -/
  θ : ℝ
  /-- The open interval containing `θ` (Figure 2g regime). -/
  θ_mem : θ ∈ Ioo 0 (Real.pi / 2)
  /-- Angular separation between the parallel rays `A` and `B`, with
  `Δθ ≪ θ` in the sense `0 < |Δθ| < θ`; in particular `Δθ ≠ 0`. -/
  Δθ : ℝ
  /-- The separation is smaller than the incidence angle and nonzero, so
  that ray `B` is a distinct neighboring ray of comparable incidence. -/
  hΔθ : 0 < |Δθ| ∧ |Δθ| < θ
  /-- Slope `m_A` of the reflected ray `A`. -/
  mA : ℝ
  /-- `m_A` is the slope delivered by the reflection law at angle `θ`. -/
  mA_eq : mA = law.slope θ
  /-- Intercept `b_A` of the reflected ray `A`. -/
  bA : ℝ
  /-- `b_A` is the intercept delivered by the reflection law at `θ`. -/
  bA_eq : bA = law.intercept θ
  /-- Slope `m_B` of the reflected ray `B`. -/
  mB : ℝ
  /-- Intercept `b_B` of the reflected ray `B`. -/
  bB : ℝ
  /-- Ray `B` is parallel to ray `A` before reflection (hence also vertical)
  and strikes the mirror at incidence angle `θ + Δθ`; being subject to the
  same reflection law, its reflected slope is the law's slope at `θ + Δθ`. -/
  mB_eq : mB = law.slope (θ + Δθ)
  /-- The reflected intercept of `B` is the law's intercept at `θ + Δθ`. -/
  bB_eq : bB = law.intercept (θ + Δθ)

namespace CausticNeighborContext

variable (C : CausticNeighborContext)

/-- The angular separation is nonzero. -/
theorem Δθ_ne_zero : C.Δθ ≠ 0 :=
  abs_pos.mp C.hΔθ.1

/-- **First-order expansion predicate for the reflected slope** (answer-blind
linear-coefficient form).  The candidate coefficient `c_m` linearizes the
reflection law's slope at `θ` in the perturbation `δ → 0`:

    slope (θ + δ) − slope θ − c_m * δ = o (δ)   as δ → 0.

The dummy asymptotic variable `δ` ranges in the filter `𝓝 0`; the fixed
nonzero separation `Δθ` of the physical rays does *not* occur here — it
appears only evaluated, in `correctionSlope`.  No standalone constant
stands inside the neighborhood clause, so the iter-014 collapse
(`c_m = 0 ∧ deriv slope θ = 0`) cannot occur. -/
def SlopeLinearizesLaw (c_m : ℝ) : Prop :=
  (fun δ : ℝ ↦ C.law.slope (C.θ + δ) - C.law.slope C.θ - c_m * δ)
    =o[𝓝 (0:ℝ)] fun δ ↦ δ

/-- **First-order expansion predicate for the reflected intercept**, the
`intercept` analog of `SlopeLinearizesLaw`:

    intercept (θ + δ) − intercept θ − c_b * δ = o (δ)   as δ → 0. -/
def InterceptLinearizesLaw (c_b : ℝ) : Prop :=
  (fun δ : ℝ ↦ C.law.intercept (C.θ + δ) - C.law.intercept C.θ - c_b * δ)
    =o[𝓝 (0:ℝ)] fun δ ↦ δ

/-- The first-order correction to the slope between rays `A` and `B` carried
by the candidate coefficient `c_m`: `Δm = c_m * Δθ`, linear in the *fixed*
nonzero separation of the two rays.  This is the quantity in which the
requested expansion reads `m_B = m_A + c_m * Δθ + o (Δθ)`. -/
def correctionSlope (c_m : ℝ) : ℝ := c_m * C.Δθ

/-- The first-order correction to the intercept between rays `A` and `B`:
`Δb = c_b * Δθ`. -/
def correctionIntercept (c_b : ℝ) : ℝ := c_b * C.Δθ

/-- **Consistency: any candidate linear coefficient is the derivative.**
If `c_m` linearizes the slope law at `θ`, then `HasDerivAt` delivers its
value: `deriv slope θ = c_m`.  This is the bridge that makes
`SlopeLinearizesLaw` constraining — the candidate is not free.  Proof left
to the prover stage (`Asymptotics.IsLittleO` against `fun δ ↦ δ` on `𝓝 0`
re-arranges to the `𝓝[≠] 0` convergence of difference quotients, whose
limit is unique and, under `SlopeInterceptDifferentiability`, equals
`deriv law.slope C.θ`). -/
theorem slopeLinearizesLaw_deriv {c_m : ℝ} (h : C.SlopeLinearizesLaw c_m) :
    deriv C.law.slope C.θ = c_m := by
  /- USER: Avoid transporting little-o through a translated filter manually.
  `hasDerivAt_iff_isLittleO_nhds_zero` already has exactly the shifted form
  used by `SlopeLinearizesLaw`.  Construct `h2 : HasDerivAt ... c_m C.θ`
  with `apply hasDerivAt_iff_isLittleO_nhds_zero.mpr` followed by
  `simpa [SlopeLinearizesLaw, mul_comm] using h`; conclude with
  `h1.unique h2`.  The intercept proof is identical.  The two existence
  lemmas use the reverse direction and the same `simpa`. -/
  -- PROOF SKETCH (prover stage): the `IsLittleO` unfold to
  --   Tendsto (fun δ ↦ (law.slope (C.θ + δ) - law.slope C.θ) / δ - c_m) (𝓝[≠] 0) (𝓝 0),
  -- while differentiability (`C.law_diff.slope_differentiable C.θ`) gives
  --   Tendsto (fun δ ↦ (law.slope (C.θ + δ) - law.slope C.θ) / δ) (𝓝[≠] 0)
  --     (𝓝 (deriv law.slope C.θ));
  -- uniqueness of limits in `𝓝[≠] 0` (a `NeBot` filter on `ℝ`) identifies the two.
  have h1 : HasDerivAt C.law.slope (deriv C.law.slope C.θ) C.θ :=
    C.law_diff.slope_differentiable C.θ |>.hasDerivAt
  have h2 : HasDerivAt C.law.slope c_m C.θ := by
    apply hasDerivAt_iff_isLittleO_nhds_zero.mpr
    simpa [SlopeLinearizesLaw, smul_eq_mul, mul_comm] using h
  exact h1.unique h2

/-- **Consistency: any candidate intercept coefficient is the derivative**,
the `intercept` analog of `slopeLinearizesLaw_deriv`. -/
theorem interceptLinearizesLaw_deriv {c_b : ℝ} (h : C.InterceptLinearizesLaw c_b) :
    deriv C.law.intercept C.θ = c_b := by
  -- PROOF SKETCH (prover stage): same uniqueness-of-difference-quotient
  -- argument, using `C.law_diff.intercept_differentiable C.θ`.
  have h1 : HasDerivAt C.law.intercept (deriv C.law.intercept C.θ) C.θ :=
    C.law_diff.intercept_differentiable C.θ |>.hasDerivAt
  have h2 : HasDerivAt C.law.intercept c_b C.θ := by
    apply hasDerivAt_iff_isLittleO_nhds_zero.mpr
    simpa [InterceptLinearizesLaw, smul_eq_mul, mul_comm] using h
  exact h1.unique h2

/-- **Existence of the slope linear coefficient, from the C.1 regularity.**
Differentiability of `θ ↦ slope θ` at `θ` is exactly a `HasDerivAt`, which
unfolds to the little-`o` first-order expansion: the derivative is a
candidate linearizing coefficient.  Proof left to the prover stage
(`HasDerivAt.isLittleO` on `deriv slope θ`, transported along
`fun δ ↦ slope (θ + δ) − slope θ − (deriv slope θ) * δ = slope (θ + δ − θ)`. -/
theorem slopeLinearizesLaw_exists :
    ∃ c_m : ℝ, C.SlopeLinearizesLaw c_m := by
  -- PROOF SKETCH (prover stage): `⟨deriv C.law.slope C.θ, _⟩` with
  -- `(C.law_diff.slope_differentiable C.θ).hasDerivAt.isLittleO`.
  refine ⟨deriv C.law.slope C.θ, ?_⟩
  have hda : HasDerivAt C.law.slope (deriv C.law.slope C.θ) C.θ :=
    C.law_diff.slope_differentiable C.θ |>.hasDerivAt
  simpa [SlopeLinearizesLaw, smul_eq_mul, mul_comm] using
    (hasDerivAt_iff_isLittleO_nhds_zero.1 hda)

/-- **Existence of the intercept linear coefficient**, the `intercept`
analog of `slopeLinearizesLaw_exists`. -/
theorem interceptLinearizesLaw_exists :
    ∃ c_b : ℝ, C.InterceptLinearizesLaw c_b := by
  -- PROOF SKETCH (prover stage): `⟨deriv C.law.intercept C.θ, _⟩` with
  -- `(C.law_diff.intercept_differentiable C.θ).hasDerivAt.isLittleO`.
  refine ⟨deriv C.law.intercept C.θ, ?_⟩
  have hda : HasDerivAt C.law.intercept (deriv C.law.intercept C.θ) C.θ :=
    C.law_diff.intercept_differentiable C.θ |>.hasDerivAt
  simpa [InterceptLinearizesLaw, smul_eq_mul, mul_comm] using
    (hasDerivAt_iff_isLittleO_nhds_zero.1 hda)

/-- **Solution predicate for T2-C2**, answer-blind: the pair of linear
coefficients `(c_m, c_b)` expands the reflected slope and intercept of the
neighboring ray `B` to first order in the incidence-angle perturbation
around ray `A`:

* `c_m` and `c_b` linearize the law, i.e.
  `slope (θ + δ) = slope θ + c_m * δ + o (δ)` and
  `intercept (θ + δ) = intercept θ + c_b * δ + o (δ)` as `δ → 0`;
* evaluated at the two rays' fixed separation `Δθ`, the named first-order
  correction terms are `c_m * Δθ` and `c_b * Δθ`.  These are approximations
  to the corresponding finite increments with the residual controlled only
  asymptotically by the preceding little-`o` clauses; they are not asserted
  to equal those finite increments exactly.

Both rays obey the specular reflection law of the half-cylindrical mirror of
Figure 2g; ray `B` is parallel to `A` and incident at `θ + Δθ`.  No
closed-form expression for `(c_m, c_b)` occurs — the predicate only records
that the pair linearizes the law. -/
def SolutionC2 (c_m c_b : ℝ) : Prop :=
  C.SlopeLinearizesLaw c_m ∧ C.InterceptLinearizesLaw c_b

/-- **T2-C2, formalized target.**  There exists a unique pair of linear
coefficients `(c_m, c_b)` that expands the reflected slope and intercept of
the neighboring ray `B` to first order in the incidence-angle perturbation
around the reference ray `A`, in the precise sense of `SolutionC2` — and
the resulting named first-order correction terms, evaluated at their fixed
nonzero separation `Δθ`, are

    Δm = c_m * Δθ,   Δb = c_b * Δθ,

The displayed equalities below merely unfold the two correction definitions.
In particular, the target does **not** identify either term with the full
finite increment `m_B - m_A` or `b_B - b_A`; nonlinear differentiable laws
have a nonzero residual at a fixed separation.

Existence is delivered by differentiability of the law (C.1 regularity)
through `slopeLinearizesLaw_exists` / `interceptLinearizesLaw_exists`;
uniqueness by the uniqueness of the limit of difference quotients through
`slopeLinearizesLaw_deriv` / `interceptLinearizesLaw_deriv`.  The concrete
C.1 values of the coefficients (`c_m = deriv slope θ`,
`c_b = deriv intercept θ` for the C.1 witness law) are intentionally kept
out of the signature; the prover reconstructs them from
`SlopeInterceptDifferentiability`. -/
theorem exists_unique_expansion :
    ∃! p : ℝ × ℝ,
      C.SolutionC2 p.1 p.2 ∧
        C.correctionSlope p.1 = p.1 * C.Δθ ∧
        C.correctionIntercept p.2 = p.2 * C.Δθ := by
  -- PROOF SKETCH (prover stage):
  --   refine ⟨⟨deriv C.law.slope C.θ, deriv C.law.intercept C.θ⟩,
  --     ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  --   · /- `slopeLinearizesLaw_exists` witness -/ sorry
  --   · /- `interceptLinearizesLaw_exists` witness -/ sorry
  --   · /- unfold `correctionSlope` -/ rfl
  --   · /- unfold `correctionIntercept` -/ rfl
  --   · rintro ⟨c_m, c_b⟩ ⟨⟨hm, hb⟩, _, _⟩
  --     exact Prod.ext (slopeLinearizesLaw_deriv C hm)
  --       (interceptLinearizesLaw_deriv C hb)
  obtain ⟨c_m, hm⟩ := slopeLinearizesLaw_exists C
  obtain ⟨c_b, hb⟩ := interceptLinearizesLaw_exists C
  refine ⟨⟨c_m, c_b⟩, ⟨⟨hm, hb⟩, rfl, rfl⟩, ?_⟩
  rintro y ⟨hy, -, -⟩
  rcases y with ⟨a, b⟩
  have hf : a = c_m :=
    (slopeLinearizesLaw_deriv C hy.1).symm.trans
      (slopeLinearizesLaw_deriv C hm)
  have hbq : b = c_b :=
    (interceptLinearizesLaw_deriv C hy.2).symm.trans
      (interceptLinearizesLaw_deriv C hb)
  rw [hf, hbq]

/-- **Pointwise two-ray reading, kept for the geometric corollaries.**
Evaluating the law fibers at the two rays' angles identifies the slope and
intercept increments, so the expanded slope and intercept of ray `B`
satisfy the affine balances `m_B = m_A + Δm`, `b_B = b_A + Δb` for the
fiber increments `Δm = slope (θ + Δθ) − slope θ`,
`Δb = intercept (θ + Δθ) − intercept θ`.  These are definitional from
`mA_eq`, `bA_eq`, `mB_eq`, `bB_eq` and are the physical content of the
requested expansion together with the separate asymptotic clauses in
`SolutionC2`; no exact equality to the first-order terms is claimed. -/
theorem expansion_pointwise :
    C.mB - C.mA = C.law.slope (C.θ + C.Δθ) - C.law.slope C.θ ∧
      C.bB - C.bA = C.law.intercept (C.θ + C.Δθ) - C.law.intercept C.θ := by
  exact ⟨by rw [C.mB_eq, C.mA_eq], by rw [C.bB_eq, C.bA_eq]⟩

end CausticNeighborContext

end Ipho2026KimiK3Blind32.ProblemIPhO2026_2C2
