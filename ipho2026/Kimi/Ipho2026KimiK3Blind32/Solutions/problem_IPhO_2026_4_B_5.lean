import Mathlib

/-!
# IPhO 2026, Experimental Exam E1, Problem 4, Part B.5 — Clausius–Clapeyron
# graph for the molar latent heat of vaporization

Answer-blind formalization of subquestion E1-B.5 (4.0 pts):

> **B5.** Using equation (3) and the expression from question B4, construct an
> appropriate graph to determine the experimental value of `Q_v`.  *(For the
> following questions, use the reference value `R = 8.31 J/(mol·K)`.)*

## Experimental context (Part B: vapor pressure of water)

* The inner cylinder (**IC**) contains dry air plus water vapor at total
  pressure approximately equal to the atmospheric pressure `P_atm` (part B,
  procedure on page 11: the syringe arrangement of Fig. 19 keeps the pressure
  inside the IC approximately atmospheric).  The water level is adjusted and
  the liquid-free air-column height `H` is recorded while the temperature `T`
  falls (part B.1), and `H` is plotted against `T` (part B.2).
* The recorded `H(T)` curve is extrapolated to `T₀ = 273.15 K` (0 °C), giving
  the value `H₀` (part B.3); at `T₀` the water vapor pressure may be taken as
  zero (part B.4).
* Part B.4 deduces an *algebraic expression* for the vapor pressure `P_v` in
  terms of `P_atm, H₀, H, T₀, T`.  B.5's only legitimate dependence on B.4
  is that expression viewed as a converter: from each recorded triple
  `(T, H, H₀)` and the separately read `P_atm` of a run it produces the
  ordinate `P_v`.  The concrete formula is a natural-language prerequisite
  (dependency policy: `natural_language_prerequisite_only;
  do_not_import_Lean_output`), so it appears here as an abstract field
  `vaporPressureOf` with the argument roles of the statement, and its
  positivity on the measurement range is recorded as a hypothesis.
* Equation (3) of the statement (page 11) is the integrated
  Clausius–Clapeyron law

      P_v = P_v0 · exp (- (Q_v / R) · (1 / T - 1 / T₀)),

  i.e. `ln (P_v / P_v0) = - (Q_v / R) · (1 / T - 1 / T₀)`, with `T₀ = 0 °C`
  the reference temperature, `P_v0` the vapor pressure at `T₀`, `R` the
  universal gas constant and `Q_v` the molar latent heat of vaporization.

## Physical content of the graph construction

Inserting the B.4 expression into the logarithm of equation (3), a plot of

    y = ln ( P_v(P_atm, H₀, H, T₀, T) / P_v0 )     against     x = 1 / T - 1 / T₀

built from the recorded runs is a straight line through the origin whose
slope is `-Q_v / R`.  Hence the experimental value of the molar latent heat
is `Q_v = -R · s`, where `s` is the slope of the best-fit straight line
through the plotted points — i.e. the slope of the least-squares (minimum
total squared vertical residual) line through the origin.  This is the
defining experimental act of B.5: the slope is *fitted to the scattered
recorded data*, not merely read off a single point.

## Answer-free statement design

The official value of `Q_v` is withheld.  Following the blind policy, the
main theorem introduces a result variable `Q` of molar-energy role and an
answer-free solution predicate `IsExperimentalLatentHeat` built from

1. the list of recorded runs, each carrying the concrete B.4 inputs
   `(T, H, H₀, P_atm)` (so the recorded heights genuinely enter the graph);
2. the least-squares best-fit slope of the transformed recorded points
   (minimality of the total squared residual on `EuclideanSpace ℝ (Fin k)`);
3. the slope-to-latent-heat conversion `Q = -R · s`.

Existence and uniqueness is asserted; the witness (`-8.31` times the
least-squares slope) and its closed form are deliberately kept out of the
theorem signature.  The idealized governing law (3), under which the fit
would be exact, is included as a derivation lemma: if an underlying latent
heat obeys (3) at every recorded temperature, the fitted slope is forced to
be `-Q/R`.
-/

namespace Ipho2026KimiK3Blind32.ProblemIPhO2026_4B5

open InnerProductSpace

/-! ## Parameters and recorded measurements -/

/-- The reference value of the universal gas constant prescribed by the
statement for the B.5–B.6 questions: `R = 8.31 J/(mol·K)` (page 12:
"For the following questions, use the reference value R = 8.31 J/(mol·K)"). -/
noncomputable def gasConstantReference : ℝ := 8.31

/-- Experimental parameters shared by the recorded runs of Part B: the
reference temperature of equation (3) and reference pressure of the
logarithm, plus the B.4 vapor-pressure expression used to convert each
recorded row into an ordinate. -/
structure CCGGraphParams where
  /-- Reference absolute temperature `T₀ = 273.15 K` (0 °C) of equation (3):
  the temperature at which `H₀` is extrapolated and the vapor pressure is
  taken as zero. -/
  T₀ : ℝ
  /-- Reference vapor pressure `P_v0`, the vapor pressure at `T₀` appearing
  in equation (3); its choice fixes the gauge of the ordinate
  `ln (P_v / P_v0)` but, as the graph passes through the origin, not the
  slope. -/
  P_v0 : ℝ
  /-- The part-B.4 algebraic expression, viewed as a converter with the
  argument roles stated in B.4: from the atmospheric pressure `P_atm`
  (approximately the constant total pressure inside the IC), the
  extrapolated height `H₀`, the recorded height `H`, the reference
  temperature `T₀` and the measurement temperature `T`, produce the
  inferred water vapor pressure `P_v`.  The concrete formula is a
  natural-language prerequisite of B.4 and is deliberately not imported as
  a Lean dependency; only its input/output roles and positivity on the
  measurement range are used. -/
  vaporPressureOf : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  /-- Reference temperature is positive (absolute scale). -/
  T₀_pos : 0 < T₀
  /-- Reference vapor pressure is positive (so the logarithm is defined). -/
  P_v0_pos : 0 < P_v0
  /-- The B.4-inferred vapor pressure is positive whenever the recorded
  temperatures and heights are positive, so that the Clausius–Clapeyron
  ordinate `ln (P_v / P_v0)` is defined on the measurement range
  (measurement range: temperatures between the ice point and the initial
  hot state, positive air-column heights). -/
  vaporPressureOf_pos :
    ∀ P_atm H₀ h T : ℝ, 0 < P_atm → 0 < H₀ → 0 < h → 0 < T →
      0 < vaporPressureOf P_atm H₀ h T₀ T

namespace CCGGraphParams

/-- One recorded run of part B.1/B.2 at thermal equilibrium: the absolute
temperature `T`, the recorded liquid-free air-column height `H`, the
extrapolated reference height `H₀` read from that run's `H(T)` graph
(part B.3), and the (approximately constant) atmospheric pressure `P_atm`
maintained by the syringe arrangement.  These are exactly the inputs the
B.4 expression consumes to produce the vapor pressure, so the recorded
heights genuinely enter the graph coordinates. -/
structure RecordedRun where
  /-- Absolute temperature `T` of the equilibrium state (Kelvin). -/
  T : ℝ
  /-- Recorded liquid-free air-column height `H` at temperature `T`
  (parts B.1–B.2). -/
  h : ℝ
  /-- Extrapolated height `H₀ = H(T₀)` at `0 °C` obtained from this run's
  graph (part B.3). -/
  H₀ : ℝ
  /-- Atmospheric pressure `P_atm` during the run: the approximately
  constant total pressure of the dry-air-plus-vapor mixture in the IC. -/
  P_atm : ℝ
  /-- Measurement temperatures are positive (absolute scale). -/
  T_pos : 0 < T
  /-- Recorded heights are positive. -/
  h_pos : 0 < h
  /-- Extrapolated reference heights are positive. -/
  H₀_pos : 0 < H₀
  /-- Total internal pressure is positive. -/
  P_atm_pos : 0 < P_atm

/-- The vapor pressure inferred from a recorded run through the B.4
expression: `P_v = P.vaporPressureOf P_atm H₀ h T₀ T`.  This is the
pressure value that enters the ordinate of the graph: it is computed from
the *recorded* heights and pressure of the run, so the measurement data
genuinely enter the graph. -/
noncomputable def runVaporPressure (G : CCGGraphParams) (m : RecordedRun) :
    ℝ :=
  G.vaporPressureOf m.P_atm m.H₀ m.h G.T₀ m.T

/-- The B.4-inferred vapor pressure of every recorded run is positive, so
the logarithm of the ordinate is defined. -/
theorem runVaporPressure_pos (G : CCGGraphParams) (m : RecordedRun) :
    0 < G.runVaporPressure m :=
  G.vaporPressureOf_pos m.P_atm m.H₀ m.h m.T
    m.P_atm_pos m.H₀_pos m.h_pos m.T_pos

/-- The abscissa of the Clausius–Clapeyron graph, `x = 1 / T - 1 / T₀`:
the transformed inverse temperature appearing in equation (3).  It vanishes
exactly at the reference temperature `T = T₀`, which anchors the graph
through the origin. -/
noncomputable def ccAbscissa (G : CCGGraphParams) (m : RecordedRun) : ℝ :=
  m.T⁻¹ - G.T₀⁻¹

/-- The ordinate of the Clausius–Clapeyron graph,
`y = ln (P_v(P_atm, H₀, h, T₀, T) / P_v0)`, with `P_v` inferred from the
recorded quantities of the run through the B.4 expression. -/
noncomputable def ccOrdinate (G : CCGGraphParams) (m : RecordedRun) : ℝ :=
  Real.log (G.runVaporPressure m / G.P_v0)

/-! ## The best-fit slope of the graph -/

/-- The Euclidean vector of abscissae of the recorded runs:
`x i = 1 / Tᵢ - 1 / T₀`. -/
noncomputable def abscissaVec (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm fun i ↦ G.ccAbscissa (runs i)

/-- The Euclidean vector of ordinates of the recorded runs:
`y i = ln (P_vᵢ / P_v0)`, computed from the recorded heights through the
B.4 expression. -/
noncomputable def ordinateVec (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm fun i ↦ G.ccOrdinate (runs i)

/-- The total squared vertical residual of the candidate slope `s` against
the plotted points: the squared L2 norm of `y - s • x`, the quantity an
experimentalist minimizes when drawing the best-fit straight line through
the origin on the Clausius–Clapeyron graph. -/
noncomputable def squaredResidual (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun) (s : ℝ) : ℝ :=
  RCLike.re ⟪G.ordinateVec runs - s • G.abscissaVec runs,
              G.ordinateVec runs - s • G.abscissaVec runs⟫_ℝ

/-- The real inner product of a vector of the Clausius–Clapeyron graph with
itself is real-valued, so the complex-coercion appearing in the total squared
residual can be re-read as the plain real inner product. -/
theorem re_real_inner_self {k : ℕ} (z : EuclideanSpace ℝ (Fin k)) :
    RCLike.re ⟪z, z⟫_ℝ = ⟪z, z⟫_ℝ := by
  exact_mod_cast inner_self_ofReal_re (𝕜 := ℝ) z

/-- The total squared residual is the plain real inner product of the residual
vector with itself. -/
theorem squaredResidual_eq_real_inner (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun) (s : ℝ) :
    G.squaredResidual runs s =
      ⟪G.ordinateVec runs - s • G.abscissaVec runs,
        G.ordinateVec runs - s • G.abscissaVec runs⟫_ℝ :=
  re_real_inner_self _

/-- The real self inner product of a graph (residual) vector vanishes only for
the zero vector. -/
theorem inner_self_eq_zero_of_real {k : ℕ} {z : EuclideanSpace ℝ (Fin k)}
    (h : ⟪z, z⟫_ℝ = 0) : z = 0 := by
  have h' := inner_self_eq_norm_sq_to_K (𝕜 := ℝ) z
  rw [h] at h'
  have hnorm : (‖z‖ : ℝ) ^ 2 = 0 := by exact_mod_cast h'.symm
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- The real self inner product of a graph (residual) vector is nonnegative. -/
theorem inner_self_nonneg_of_real {k : ℕ} {z : EuclideanSpace ℝ (Fin k)} :
    (0:ℝ) ≤ ⟪z, z⟫_ℝ :=
  real_inner_self_nonneg

/-- The total squared residual of every candidate slope is nonnegative. -/
theorem squaredResidual_nonneg (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun) (s : ℝ) :
    (0:ℝ) ≤ G.squaredResidual runs s := by
  rw [G.squaredResidual_eq_real_inner runs s]
  exact inner_self_nonneg_of_real

/-- The total squared residual of the zero candidate slope is the squared norm
of the ordinate vector; in particular it vanishes exactly when every ordinate
of the graph is zero. -/
theorem squaredResidual_zero_eq_zero_iff (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun) :
    G.squaredResidual runs 0 = 0 ↔ G.ordinateVec runs = 0 := by
  rw [G.squaredResidual_eq_real_inner runs 0]
  simp only [zero_smul, sub_zero]
  constructor
  · exact fun h ↦ inner_self_eq_zero_of_real h
  · intro h
    have h0 : ⟪G.ordinateVec runs, G.ordinateVec runs⟫_ℝ =
        RCLike.re ⟪G.ordinateVec runs, G.ordinateVec runs⟫_ℝ :=
      (re_real_inner_self _).symm
    rw [h0, h]
    simp

/-- The total squared residual of the candidate slope `s` is a quadratic
function of `s`: it expands as
`⟪x, x⟫ · s² - 2⟪y, x⟫ · s + ⟪y, y⟫`, the parabola minimized when fitting the
best straight line through the origin of the graph. -/
theorem squaredResidual_eq_quadratic (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun) (s : ℝ) :
    G.squaredResidual runs s =
      ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ * (s * s) -
        2 * ⟪G.ordinateVec runs, G.abscissaVec runs⟫_ℝ * s +
          ⟪G.ordinateVec runs, G.ordinateVec runs⟫_ℝ := by
  rw [G.squaredResidual_eq_real_inner runs s]
  rw [inner_sub_sub_self, real_inner_smul_right _ _ s, real_inner_smul_left _ _ s,
    real_inner_smul_left _ _ s, real_inner_smul_right _ _ s]
  rw [real_inner_comm (G.ordinateVec runs) (G.abscissaVec runs)]
  -- `star s = s` on `ℝ`; after clearing it the identity is pure polynomial
  -- algebra in the three inner-product scalars and `s`.
  ring

/-- `s` is the slope of the best-fit straight line through the origin for
the recorded points: its total squared vertical residual is less than or
equal to that of every other candidate slope.  This is the least-squares
estimator behind the instruction "use the graph to determine `Q_v`". -/
def IsBestFitSlope (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun) (s : ℝ) : Prop :=
  ∀ s' : ℝ, G.squaredResidual runs s ≤ G.squaredResidual runs s'

/-- The graph is non-degenerate when at least one recorded run lies off the
reference temperature, i.e. has a nonzero abscissa; then the abscissa vector
is nonzero and the best-fit slope is well determined. -/
def HasNonzeroAbscissa (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun) : Prop :=
  ∃ i : Fin k, G.ccAbscissa (runs i) ≠ 0

/-! ## The idealized governing law (equation (3)) -/

/-- Predicate expressing that `Q` is a molar latent heat of vaporization
under which the recorded data satisfy the integrated Clausius–Clapeyron law
(3): the B.4-inferred vapor pressure of every recorded run obeys

    ln (P_v(T) / P_v0) = - (Q / R) · (1 / T - 1 / T₀),

using the statement's reference value `R = 8.31 J/(mol·K)`.  Physically this
is the idealization in which measurement scatter is absent; it links the
answer-free characterization below to the printed equation (3). -/
def ObeysClausiusClapeyron (G : CCGGraphParams) (Q : ℝ) : Prop :=
  ∀ m : RecordedRun,
    Real.log (G.runVaporPressure m / G.P_v0) =
      - (Q / gasConstantReference) * (m.T⁻¹ - G.T₀⁻¹)

/-! ## The answer-free solution predicate -/

/-- The solution predicate for part B.5: a real number `Q` of molar-energy
role is *the* experimentally determined molar latent heat of vaporization
for the recorded runs when it is `-R` times the slope of the best-fit
straight line through the origin of the Clausius–Clapeyron graph plotted
from those runs:

* the recorded runs supply the points `(1/Tᵢ - 1/T₀, ln (P_vᵢ / P_v0))`,
  with each `P_vᵢ` computed from the recorded heights `hᵢ, H₀ᵢ` and
  pressure `P_atmᵢ` through the B.4 expression;
* `s` is the least-squares best-fit slope of those points (minimum total
  squared vertical residual);
* `Q = -R · s` converts the slope into the molar latent heat, using the
  statement's reference value `R = 8.31 J/(mol·K)`.

Nothing here fixes the numerical value of `Q`; the characterization is
answer-free. -/
def IsExperimentalLatentHeat (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun) (Q : ℝ) : Prop :=
  ∃ s : ℝ, G.IsBestFitSlope runs s ∧ Q = -gasConstantReference * s

/-! ## Characterization lemmas -/

/-- **Squeeze lemma.**  If a real number `d` satisfies `|t·d| ≤ t²·e` for
every real step `t` — i.e. the linear term of a nonnegative quadratic
correction is bounded by its quadratic term — then `d = 0`.  This is the
analytic heart of the normal equation: minimality of the squared residual
forces `|2t(b - as)| ≤ t²·‖x‖²` for every perturbation step `t`, and letting
`t → 0` collapses it to `b = a·s`. -/
theorem eq_zero_of_abs_mul_le_sq {d e : ℝ} (he : 0 ≤ e)
    (h : ∀ t : ℝ, |t * d| ≤ t ^ 2 * e) : d = 0 := by
  by_contra hd
  have hd0 : 0 < |d| := abs_pos.mpr hd
  set t : ℝ := |d| / (2 * (e + 1)) with htdef
  have ht0 : 0 < t := by positivity
  have hkey := h t
  have htsq : t ^ 2 = t * t := sq t
  rw [abs_mul, abs_of_pos ht0, htsq] at hkey
  -- cancel the positive factor `t` from `t * |d| ≤ t * t * e`
  have hcancel : |d| ≤ t * e := by
    rw [mul_assoc] at hkey
    exact le_of_mul_le_mul_left hkey ht0
  -- but `t * e < |d|`: with `e < e + 1` and `0 < t`, `t·e < t·(e+1) = |d|/2 < |d|`
  have hcontr : t * e < |d| := by
    have h1 : t * e ≤ t * (e + 1) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt ht0)
      linarith
    have h2 : t * (e + 1) = |d| / 2 := by
      rw [htdef]; field_simp
    nlinarith [h1, h2, hd0, ht0, he]
  linarith

/-- The real inner product `⟪u, x⟫` vanishes whenever the squared residual
`‖u - s' • x‖²` attains, at the candidate slope `s`, a global minimum in `s'`.
This is the orthogonal-projection content of the least-squares fit: the
residual `u - s • x` is orthogonal to the abscissa direction `x`. -/
theorem inner_eq_zero_of_sqResidual_min {k : ℕ}
    {x u : EuclideanSpace ℝ (Fin k)} {s : ℝ}
    (hs : ∀ s' : ℝ, ⟪u - s • x, u - s • x⟫_ℝ ≤ ⟪u - s' • x, u - s' • x⟫_ℝ) :
    ⟪u, x⟫_ℝ = s * ⟪x, x⟫_ℝ := by
  set r : EuclideanSpace ℝ (Fin k) := u - s • x
  -- minimality at `s` vs `s + t`: `‖r‖² ≤ ‖r - t•x‖²`
  have hkey : ∀ t : ℝ,
      ⟪r, r⟫_ℝ ≤ ⟪r - t • x, r - t • x⟫_ℝ := fun t ↦ by
    have hs' := hs (s + t)
    have hrt : u - (s + t) • x = r - t • x := by module
    rw [hrt] at hs'
    exact hs'
  -- expansion: `⟪r - t•x, r - t•x⟫ = ⟪r,r⟫ - 2t⟪r,x⟫ + t²⟪x,x⟫`
  have hexp : ∀ t : ℝ, ⟪r - t • x, r - t • x⟫_ℝ =
      ⟪r, r⟫_ℝ - 2 * t * ⟪r, x⟫_ℝ + t ^ 2 * ⟪x, x⟫_ℝ := fun t ↦ by
    have h1 : ⟪r - t • x, r - t • x⟫_ℝ = ⟪r, r⟫_ℝ - ⟪r, t • x⟫_ℝ -
        ⟪t • x, r⟫_ℝ + ⟪t • x, t • x⟫_ℝ := inner_sub_sub_self r (t • x)
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_right] at h1
    rw [real_inner_comm r x] at h1
    rw [h1]; ring
  -- hence `2t⟪r,x⟫ ≤ t²⟪x,x⟫` for all `t`
  have hineq : ∀ t : ℝ, 2 * t * ⟪r, x⟫_ℝ ≤ t ^ 2 * ⟪x, x⟫_ℝ := fun t ↦ by
    have h := hkey t
    rw [hexp t] at h
    linarith
  -- same for `-t`: absolute value bound
  have habs : ∀ t : ℝ, |t * (2 * ⟪r, x⟫_ℝ)| ≤ t ^ 2 * ⟪x, x⟫_ℝ := fun t ↦ by
    exact abs_le.mpr ⟨by have h := hineq (-t); linarith,
      by have h := hineq t; linarith⟩
  -- squeeze gives `⟪r, x⟫ = 0`, i.e. `⟪u,x⟫ = s⟪x,x⟫`
  have hrx : ⟪r, x⟫_ℝ = 0 := by
    have hd0 : 2 * ⟪r, x⟫_ℝ = 0 :=
      eq_zero_of_abs_mul_le_sq
        (real_inner_self_nonneg (F := EuclideanSpace ℝ (Fin k)) (x := x)) habs
    linarith
  -- `⟪r, x⟫ = ⟪u,x⟫ - s⟪x,x⟫`
  have hr : ⟪r, x⟫_ℝ = ⟪u, x⟫_ℝ - s * ⟪x, x⟫_ℝ := by
    change ⟪u - s • x, x⟫_ℝ = ⟪u, x⟫_ℝ - s * ⟪x, x⟫_ℝ
    rw [inner_sub_left, real_inner_smul_left]
  rw [hr] at hrx
  linarith


/-- The least-squares slope satisfies the normal equation of the fit: if `s`
minimizes the total squared vertical residual of the plotted points, then
the inner product `⟪y, x⟫` equals `s * ⟪x, x⟫` (the residual `y - s • x` is
orthogonal to the abscissa vector). -/
theorem bestFitSlope_normal_equation (G : CCGGraphParams) {k : ℕ}
    {runs : Fin k → RecordedRun} {s : ℝ} (hs : G.IsBestFitSlope runs s) :
    ⟪G.ordinateVec runs, G.abscissaVec runs⟫_ℝ =
      s * ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ := by
  -- rewrite minimality of the squared residual into the real-inner-product
  -- form expected by the squeeze lemma.
  have hs' : ∀ s' : ℝ,
      ⟪G.ordinateVec runs - s • G.abscissaVec runs,
        G.ordinateVec runs - s • G.abscissaVec runs⟫_ℝ ≤
      ⟪G.ordinateVec runs - s' • G.abscissaVec runs,
        G.ordinateVec runs - s' • G.abscissaVec runs⟫_ℝ := fun s' ↦ by
    have h := hs s'
    rw [G.squaredResidual_eq_real_inner runs s,
      G.squaredResidual_eq_real_inner runs s'] at h
    exact h
  exact inner_eq_zero_of_sqResidual_min hs'

/-- On a non-degenerate Clausius–Clapeyron graph (at least one recorded run
off the reference temperature) the squared norm of the abscissa vector is
strictly positive.  This is the analytic content of "the graph has a genuine
horizontal extent", and it is what makes the best-fit slope well determined. -/
theorem abscissa_self_inner_ne_zero (G : CCGGraphParams) {k : ℕ}
    {runs : Fin k → RecordedRun} (hpt : G.HasNonzeroAbscissa runs) :
    ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ ≠ 0 := by
  obtain ⟨i, hi⟩ := hpt
  intro h
  have hx : G.abscissaVec runs = 0 := inner_self_eq_zero_of_real h
  have hcoord : (WithLp.equiv 2 (Fin k → ℝ)) (G.abscissaVec runs) i = 0 := by
    rw [hx]; rfl
  have hdef : (WithLp.equiv 2 (Fin k → ℝ)) (G.abscissaVec runs) i =
      G.ccAbscissa (runs i) := rfl
  rw [hdef] at hcoord
  exact hi hcoord

/-- Two best-fit slopes of the same recorded points coincide whenever the
graph is non-degenerate: the best-fit slope of a non-degenerate
Clausius–Clapeyron graph is unique. -/
theorem bestFitSlope_unique (G : CCGGraphParams) {k : ℕ}
    {runs : Fin k → RecordedRun} (hpt : G.HasNonzeroAbscissa runs)
    {s₁ s₂ : ℝ} (h₁ : G.IsBestFitSlope runs s₁)
    (h₂ : G.IsBestFitSlope runs s₂) : s₁ = s₂ := by
  have hxx : ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ ≠ 0 :=
    G.abscissa_self_inner_ne_zero hpt
  have h1 := G.bestFitSlope_normal_equation h₁
  have h2 := G.bestFitSlope_normal_equation h₂
  -- `s₁ • ⟪x,x⟫ = ⟪y,x⟫ = s₂ • ⟪x,x⟫` with `⟪x,x⟫ ≠ 0` forces `s₁ = s₂`.
  have : s₁ * ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ =
      s₂ * ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ := by
    rw [← h1, ← h2]
  exact mul_right_cancel₀ hxx this

/-- The best-fit slope is determined by the recorded points through the
normal equation: whenever the graph is non-degenerate, `s = ⟪y, x⟫ / ⟪x, x⟫`.
This is the closed form the later proof may use to construct the witness of
the characterization. -/
theorem bestFitSlope_eq_ratio (G : CCGGraphParams) {k : ℕ}
    {runs : Fin k → RecordedRun} (hpt : G.HasNonzeroAbscissa runs)
    {s : ℝ} (hs : G.IsBestFitSlope runs s) :
    s = ⟪G.ordinateVec runs, G.abscissaVec runs⟫_ℝ /
        ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ := by
  have hxx : ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ ≠ 0 :=
    G.abscissa_self_inner_ne_zero hpt
  have h := G.bestFitSlope_normal_equation hs
  rw [h]
  field_simp

/-- **Consistency with the idealized governing law.**  If the recorded data
obey the Clausius–Clapeyron equation (3) with latent heat `Q` (the
no-scatter idealization), then the slope read from the graph — the
least-squares best-fit slope — is exactly `-Q / R`: the graph construction
recovers the governing-law parameter. -/
theorem bestFitSlope_eq_neg_div_gasConstantReference (G : CCGGraphParams)
    {k : ℕ} {runs : Fin k → RecordedRun} (hpt : G.HasNonzeroAbscissa runs)
    {Q s : ℝ} (hCC : G.ObeysClausiusClapeyron Q)
    (hs : G.IsBestFitSlope runs s) :
    s = -Q / gasConstantReference := by
  have hxx : ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ ≠ 0 :=
    G.abscissa_self_inner_ne_zero hpt
  have hnormal := G.bestFitSlope_normal_equation hs
  -- Under equation (3), at each recorded run the ordinate equals
  -- `-(Q / R)` times the abscissa, so `⟪y, x⟫ = -(Q / R) · ⟪x, x⟫`
  -- coordinatewise; combined with the normal equation `⟪y, x⟫ = s · ⟪x, x⟫`
  -- and `⟪x, x⟫ ≠ 0`, this forces `s = -Q / R`.
  have hcoord : ∀ i : Fin k, G.ccOrdinate (runs i) =
      -(Q / gasConstantReference) * G.ccAbscissa (runs i) := fun i ↦
    hCC (runs i)
  have hinner : ⟪G.ordinateVec runs, G.abscissaVec runs⟫_ℝ =
      -(Q / gasConstantReference) *
        ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ := by
    -- Euclidean inner product is `∑ i, star (y i) * (x i)` with `star = id`.
    have hy : ⟪G.ordinateVec runs, G.abscissaVec runs⟫_ℝ =
        ∑ i : Fin k, G.ccOrdinate (runs i) * G.ccAbscissa (runs i) := by
      simp only [ordinateVec, abscissaVec, WithLp.equiv_symm_apply,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
      rfl
    rw [hy]
    have hx : ⟪G.abscissaVec runs, G.abscissaVec runs⟫_ℝ =
        ∑ i : Fin k, G.ccAbscissa (runs i) * G.ccAbscissa (runs i) := by
      simp only [abscissaVec, WithLp.equiv_symm_apply,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
      rfl
    rw [hx]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoord i]
    ring
  rw [hinner] at hnormal
  -- `-(Q/R) · ⟪x,x⟫ = s · ⟪x,x⟫` with `⟪x,x⟫ ≠ 0` gives `-(Q/R) = s`.
  have : -(Q / gasConstantReference) = s := mul_right_cancel₀ hxx hnormal
  rw [← this]
  ring

/-- Any latent heat characterized by the graph construction on
non-degenerate recorded data is consistent with the governing law: the
fitted value coincides with every latent heat under which the data satisfy
equation (3). -/
theorem experimentalLatentHeat_eq_of_obeysCC (G : CCGGraphParams) {k : ℕ}
    {runs : Fin k → RecordedRun} (hpt : G.HasNonzeroAbscissa runs)
    {Qfit Qlaw : ℝ} (hfit : G.IsExperimentalLatentHeat runs Qfit)
    (hlaw : G.ObeysClausiusClapeyron Qlaw) :
    Qfit = Qlaw := by
  obtain ⟨s, hsfit, hQ⟩ := hfit
  have hs : s = -Qlaw / gasConstantReference :=
    G.bestFitSlope_eq_neg_div_gasConstantReference hpt hlaw hsfit
  rw [hQ, hs]
  have hR : (gasConstantReference : ℝ) ≠ 0 := by
    unfold gasConstantReference; norm_num
  field_simp

/-- Uniqueness half of the answer-free characterization: two latent heats
that are both `-R` times a best-fit slope of the same recorded
Clausius–Clapeyron graph, on non-degenerate data, coincide. -/
theorem experimentalLatentHeat_unique (G : CCGGraphParams) {k : ℕ}
    {runs : Fin k → RecordedRun} (hpt : G.HasNonzeroAbscissa runs)
    {Q₁ Q₂ : ℝ} (h₁ : G.IsExperimentalLatentHeat runs Q₁)
    (h₂ : G.IsExperimentalLatentHeat runs Q₂) :
    Q₁ = Q₂ := by
  obtain ⟨s₁, hs₁, hQ₁⟩ := h₁
  obtain ⟨s₂, hs₂, hQ₂⟩ := h₂
  have hs : s₁ = s₂ := G.bestFitSlope_unique hpt hs₁ hs₂
  rw [hQ₁, hQ₂, hs]

/-- **E1-B.5, answer-free characterization.**  Given the recorded Part-B
runs — each carrying its measured temperature, recorded air-column heights
and atmospheric pressure — forming a non-degenerate Clausius–Clapeyron
graph (at least one point off the reference temperature), and given that a
best-fit slope of the plotted data exists (the graph can be drawn and read),
there exists a unique experimental value `Q` of the molar latent heat of
vaporization characterized by the B.5 graph construction.  The value itself
— minus `R = 8.31` times the best-fit slope of the plotted
`(1/T - 1/T₀, ln (P_v / P_v0))` points — is deliberately kept out of this
statement; the later proof constructs it from the normal equation. -/
theorem latent_heat_exists_unique (G : CCGGraphParams) {k : ℕ}
    (runs : Fin k → RecordedRun)
    (hpt : G.HasNonzeroAbscissa runs)
    (hfit : ∃ s : ℝ, G.IsBestFitSlope runs s) :
    ∃! Q : ℝ, G.IsExperimentalLatentHeat runs Q := by
  obtain ⟨s, hs⟩ := hfit
  refine ⟨-gasConstantReference * s, ⟨s, hs, rfl⟩, fun Q' hQ' ↦ ?_⟩
  obtain ⟨s', hs'fit, hQ'⟩ := hQ'
  have hs' : s' = s := G.bestFitSlope_unique hpt hs'fit hs
  rw [hQ', hs']

end CCGGraphParams

end Ipho2026KimiK3Blind32.ProblemIPhO2026_4B5
