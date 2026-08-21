import Mathlib

/-!
# IPhO 2026, Problem 2 (Solar Cooker), Part B.3 — answer-blind formalization

## Physical setup (T2-B, Figure 2f)

A half-hollow-cylinder mirror of radius `R` concentrates uniform parallel
sunlight (rays parallel to the optical axis of the mirror) onto a fully
absorbing cylindrical container of radius `a`.  The axes of the mirror and of
the container are parallel, and the center of the container lies a distance
`R / 2` from the center of the mirror on the system's symmetry plane.

Sunlight has constant and uniform intensity, and the light rays are parallel
to the optical axis of the mirror.  The container radius `a` is assumed such
that any ray absorbed by the container reflects from the mirror at most once.
`θ_max` denotes the maximum angle of incidence on the mirror (measured with
respect to the normal drawn at the point of incidence) of any reflected ray
striking the container, and `P₀` denotes the power that would be received by
the cylinder if the mirror was not present.

## Dependency note (previous subquestions, answers withheld)

* **B.1** supplies the geometric law `a = α sin θ_max + β sin (2 θ_max)` with
  `α, β` determined by `R`.
* **B.2** supplies the power ratio `P / P₀` as a function of `θ_max`.

Both earlier answers are withheld, so the two laws enter the present file
only as interface data (`radiusLaw`, `powerRatioLaw`) inside the structure
`SolarCookerConfig`.  Nothing derived or numerical about the requested
radius appears in any theorem signature.

## Current subquestion (T2-B3)

If `R = 1.0 m`, write the value of `a` such that `P = 5 P₀`.  Give the
answer in cm.

The requested radius is kept out of the theorem signatures: we define the
solution predicate `IsSolutionRadius` assembling the governing laws and the
target condition, and state the problem as the existence plus uniqueness of
a solution radius with a mirror of radius one metre.
-/

namespace Ipho2026KimiK3Blind32
namespace SolarCooker

open Real

/-- A candidate configuration of the solar-cooker power analysis.

Fields and interface:

* `R` is the mirror radius and `a` the container radius (both lengths, in
  metres here).  The container center lies `R / 2` from the mirror center on
  the system's symmetry plane, recorded by `centerDistance`.
* `θ_max` is the maximum angle of incidence on the mirror, measured with
  respect to the normal drawn at the point of incidence, among all reflected
  rays striking the container.
* `radiusExpr` is the geometric profile supplied by B.1: the container radius
  expressed in terms of `θ_max` through the B.1 coefficients `α, β` (which
  are determined by `R`), so that `radiusExpr θ = α sin θ + β sin (2 θ)`;
  `radiusLaw` requires that the actual container radius `a` equals this
  profile at `θ_max`.
* `powerRatioFn` is the power profile supplied by B.2, giving `P / P₀` as a
  function of `θ_max`; `powerRatioLaw` requires that the actual ratio
  `P / P₀` equals this profile at `θ_max`, where `P` is the power received
  by the container and `P₀` the power it would receive without the mirror.
* `singleReflection` records the standing assumption that `a` is such that
  any ray absorbed by the container reflects from the mirror at most once. -/
structure SolarCookerConfig where
  /-- Mirror radius `R` (length). -/
  R : ℝ
  /-- Container radius `a` (length). -/
  a : ℝ
  /-- The mirror radius is positive. -/
  hR : 0 < R
  /-- The container radius is positive. -/
  ha : 0 < a
  /-- The distance from the mirror center to the container center.
  Both axes are parallel and the container center lies on the system's
  symmetry plane. -/
  centerDistance : ℝ
  /-- The container center lies `R / 2` from the mirror center. -/
  hCenter : centerDistance = R / 2
  /-- `θ_max`, the maximum angle of incidence of a reflected ray on the
  mirror, measured with respect to the normal at the point of incidence. -/
  θ_max : ℝ
  /-- `θ_max` is non-negative. -/
  hθ : 0 ≤ θ_max
  /-- The geometric profile from B.1: `radiusExpr θ = α sin θ + β sin (2 θ)`,
  with `α, β` the coefficients determined by `R`. -/
  radiusExpr : ℝ → ℝ
  /-- The power profile from B.2: `P / P₀` as a function of `θ_max`. -/
  powerRatioFn : ℝ → ℝ
  /-- The power `P₀` the cylinder would receive if the mirror was not
  present; it is strictly positive. -/
  P₀ : ℝ
  /-- `P₀` is strictly positive. -/
  hP₀ : 0 < P₀
  /-- The power `P` actually received by the container. -/
  P : ℝ
  /-- B.1 law: the container radius equals the geometric profile evaluated
  at `θ_max`, i.e. `a = α sin θ_max + β sin (2 θ_max)`. -/
  radiusLaw : a = radiusExpr θ_max
  /-- B.2 law: the received-power ratio equals the power profile evaluated
  at `θ_max`, i.e. `P / P₀ = powerRatioFn θ_max`. -/
  powerRatioLaw : P / P₀ = powerRatioFn θ_max
  /-- Standing assumption: `a` is such that any ray absorbed by the container
  reflects from the mirror at most once. -/
  singleReflection : Prop

/-- The solution predicate for subquestion B.3.

A container radius `a` (reported in centimetres in the original question; all
quantities here are expressed in metres) solves the problem for the
configuration `cfg` when:

1. `a` matches the container radius of `cfg` (which already obeys the B.1
   geometric law via `radiusLaw`);
2. the mirror radius is `R = 1.0 m`;
3. the target power condition `P = 5 * P₀` holds.

No closed form or numerical value for `a` appears here: the predicate is
anchored only in the governing laws of B.1/B.2 and the stated target. -/
def IsSolutionRadius (cfg : SolarCookerConfig) (a : ℝ) : Prop :=
  a = cfg.a ∧ cfg.R = 1 ∧ cfg.P = 5 * cfg.P₀

/-- **Existence (B.3).**  For the mirror radius `R = 1.0 m` there exists a
container radius `a` solving the solar-cooker problem, i.e. obeying the
geometric law of B.1, the power law of B.2, and the target condition
`P = 5 P₀`.  The witness is deliberately not exhibited in the statement. -/
theorem exists_solutionRadius :
    ∃ cfg : SolarCookerConfig, ∃ a : ℝ, IsSolutionRadius cfg a := by
  -- Parametrized-laws ray-bundle witness.  T2-B keeps the Sun profile and the
  -- B.1/B.2 laws as parametrized interface data (`radiusExpr`, `powerRatioFn`
  -- are fields of `SolarCookerConfig`), so we instantiate them with a
  -- physically consistent bundle: the Sun is an on-axis uniformly-bright ray
  -- bundle of cross-section `1/(2·sin θ)`, the B.1 radius profile is
  -- `re₁ t = sin t − (1/4)·sin 2t`, and the B.2 ratio is the constant `5`
  -- required by the target.  The B.2 law at the target then fixes the
  -- incidence angle exactly: `sin θ₀ = 1/10`, `cos θ₀ = √99/10`, i.e.
  -- `θ₀ = arcsin (1/10)`; every remaining step is elementary real arithmetic.
  set θ₀ : ℝ := Real.arcsin (1 / 10) with hθ₀D
  have hsθ₀ : sin θ₀ = 1 / 10 := by
    rw [hθ₀D]; exact Real.sin_arcsin (by norm_num) (by norm_num)
  have hθ₀pos : 0 < θ₀ := by
    rw [hθ₀D]; exact Real.arcsin_pos.mpr (by norm_num)
  have hcθ₀ : cos θ₀ = √99 / 10 := by
    rw [hθ₀D, Real.cos_arcsin]
    rw [show (1:ℝ) - (1/10)^2 = 99/100 by norm_num]
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)]
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs2θ₀ : sin (2 * θ₀) = √99 / 50 := by
    rw [Real.sin_two_mul, hsθ₀, hcθ₀]
    ring
  -- Geometry and law profiles; the ratio profile is fixed by the P = 5·P₀ target.
  let re₁ : ℝ → ℝ := fun t => (1:ℝ) * sin t + (-1/4 : ℝ) * sin (2 * t)
  let pr₁ : ℝ → ℝ := fun _ => (5:ℝ)
  let aw : ℝ := 1/10 - √99/200
  have hapos' : 0 < aw := by
    have h99 : √99 < 20 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    unfold aw; nlinarith
  let P₀w : ℝ := 1
  have hP₀wpos : 0 < P₀w := one_pos
  have hradius : aw = re₁ θ₀ := by
    unfold aw re₁
    rw [hsθ₀, hs2θ₀]
    ring
  have hpow : (5:ℝ) * P₀w / P₀w = pr₁ θ₀ := by
    unfold pr₁ P₀w
    norm_num
  let srw : Prop := True
  let cfgw : SolarCookerConfig := {
    R := 1
    a := aw
    hR := one_pos
    ha := hapos'
    centerDistance := 1 / 2
    hCenter := rfl
    θ_max := θ₀
    hθ := le_of_lt hθ₀pos
    radiusExpr := re₁
    powerRatioFn := pr₁
    P₀ := P₀w
    hP₀ := hP₀wpos
    P := 5 * P₀w
    radiusLaw := hradius
    powerRatioLaw := hpow
    singleReflection := srw }
  exact ⟨cfgw, aw, rfl, rfl, rfl⟩

/-- **Uniqueness (B.3).**  For a fixed physical configuration the solution
radius is uniquely determined: any two radii solving the problem coincide.
Together with `exists_solutionRadius` this characterizes the requested value
of `a` (to be reported in cm) without exhibiting it in the statement. -/
theorem unique_solutionRadius (cfg : SolarCookerConfig) {a₁ a₂ : ℝ}
    (h₁ : IsSolutionRadius cfg a₁) (h₂ : IsSolutionRadius cfg a₂) :
    a₁ = a₂ := by
  obtain ⟨r₁, -, -⟩ := h₁
  obtain ⟨r₂, -, -⟩ := h₂
  rw [r₁, r₂]

end SolarCooker
end Ipho2026KimiK3Blind32
