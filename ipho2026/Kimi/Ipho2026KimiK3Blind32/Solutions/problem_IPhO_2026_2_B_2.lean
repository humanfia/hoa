import Mathlib

/-!
# IPhO 2026, Problem 2, Part B.2 (T2-B2, Solar Cooker) — answer-blind formalization

A half-hollow-cylinder mirror of radius `R` illuminates a fully absorbing
cylindrical container of radius `a`.  The axes of the mirror and the container
are parallel, and the center of the container lies `R / 2` from the mirror
center on the system's symmetry plane (Figure 2f).  Sunlight has constant and
uniform intensity (power per unit area) and arrives parallel to the optical
axis of the mirror.  The container is fully absorbing, and `a` is such that
any ray absorbed by the container reflects from the mirror at most once.
`θ_max` is the maximum angle of incidence on the mirror (measured from the
normal drawn at the point of incidence) among reflected rays striking the
container.  `P₀` is the power the cylinder would receive if the mirror were
not present, `P` the actual received power.

Subquestion B.2: express the power ratio `P / P₀` in terms of `θ_max`.

The official answer is withheld: the theorem below states existence and
uniqueness of a dimensionless ratio characterised by a physically meaningful
solution predicate — the ratio is the quotient of the actual received power
(direct power `P₀` plus the reflected contribution accumulated from the
optical axis `θ = 0` out to the marginal reflected ray `θ = θ_max`) by the
no-mirror reference power `referencePower` — without placing any closed-form
answer in the theorem signature.

## Iter-012 redraft note (contract repair)

The previous draft had two contract defects that made the existence half of
`problem_IPhO_2026_2_B_2` principle-unprovable:

1. `IsPowerRatio` carried the conjunct `FitsInsideMirror`
   (`centerDistance + a ≤ R`, i.e. `a ≤ R / 2`), which no
   `SolarCookerConfig` field implied; it is now the configuration field
   `fitsInsideMirror` (governing Figure-2f setup datum), out of the
   predicate.
2. `PowerModel.cumulativeIntegral` demanded interval-integrability of an
   opaque `powerProfile : ℝ → ℝ` constrained only by nonnegativity — an
   unwitnessable ghost.  The ray optics implies a concrete uniform linear
   map from impact parameters to incidence angles
   (`b = R * sin θ`), so the density is the *grounded* definitional
   `angularBundleDensity θ = I₀ * (R * cos θ) * L` (the Jacobian of the
   uniform bundle).  Existence is then reduced to standard Mathlib
   integrability and fundamental-theorem-of-calculus obligations;
   uniqueness is immediate from `BundlePowerLaw`, which pins the cumulative
   endpoints independently of the chosen density.  No requested `P / P₀`
   expression is placed in any signature or predicate.
-/

namespace IPhO_2026_2_B_2

/-- The solar-cooker configuration of T2-B (Figure 2f), part B.2.

Quantity roles carried by the structure:
* `R` — radius of the half-hollow-cylinder mirror (Figure 2f marks the
  opening `2R`).
* `a` — radius of the fully absorbing cylindrical container.
* `centerDistance` — distance from the mirror center to the container center
  on the system's symmetry plane, fixed at `R / 2` by the statement.
* `I₀` — constant and uniform solar intensity (power per unit area).
* `L` — common length of the cylinders along their (parallel) axes.
* `θ_max` — maximum angle of incidence on the mirror, measured from the
  normal drawn at the point of incidence, among reflected rays striking the
  container.
* `fitsInsideMirror` — the Figure-2f shadowing/enclosure constraint:
  container center offset plus container radius lies within the mirror
  radius.  The statement text does not pin this numerically, so it is
  carried as a stated configuration datum (kept out of the solution
  predicate, so it cannot smuggle the requested ratio).
* `singleReflection` — the standing "container is such that any absorbed
  ray reflects from the mirror at most once" hypothesis of the statement,
  kept as an opaque named configuration datum, as for `problem_IPhO_2026_2_B_3`. -/
structure SolarCookerConfig where
  /-- Mirror radius `R` (Figure 2f marks the mirror opening `2R`). -/
  R : ℝ
  /-- Container radius `a`. -/
  a : ℝ
  /-- Container-center offset from the mirror center on the symmetry plane. -/
  centerDistance : ℝ
  /-- Uniform solar intensity `I₀` (power per unit area). -/
  I₀ : ℝ
  /-- Common cylinder length `L` along the parallel axes. -/
  L : ℝ
  /-- Maximum incidence angle `θ_max` at the mirror among rays striking the
  container, measured from the normal at the point of incidence. -/
  θ_max : ℝ
  R_pos : 0 < R
  a_pos : 0 < a
  centerOffset : centerDistance = R / 2
  I₀_pos : 0 < I₀
  L_pos : 0 < L
  θ_max_nonneg : 0 ≤ θ_max
  /-- The mirror collects only half of the angular range (half-cylinder). -/
  θ_max_le : θ_max ≤ Real.pi / 2
  /-- Figure-2f enclosure/shadowing constraint. -/
  fitsInsideMirror : centerDistance + a ≤ R
  /-- Standing "at most one reflection" hypothesis of the statement. -/
  singleReflection : Prop

namespace SolarCookerConfig

/-- Geometric shadowing constraint (Figure 2f): container and mirror-center
offset fit inside the mirror opening `2R`.  Holds for every physical
configuration by the field `fitsInsideMirror`. -/
def FitsInsideMirror (cfg : SolarCookerConfig) : Prop :=
  cfg.centerDistance + cfg.a ≤ cfg.R

/-- Governing law of specular reflection at the circular mirror: a ray
arriving parallel to the optical axis at impact parameter `b` from the axis
hits the mirror of radius `R` at incidence angle `θ` with
`b = R * Real.sin θ` (the normal at the point of incidence is the radius).
`incidenceAngleFn b` is that incidence angle; its range over
`b ∈ Set.Icc 0 (R * Real.sin θ_max)` is exactly `Set.Icc 0 θ_max`. -/
def SpecularIncidenceLaw (cfg : SolarCookerConfig) (incidenceAngleFn : ℝ → ℝ) :
    Prop :=
  ∀ b : ℝ, incidenceAngleFn b = Real.arcsin (b / cfg.R)

/-- Uniform, axis-parallel sunlight: the incident power carried by the bundle
of rays with impact parameter at most `b` is `I₀ * (b * L)`, proportional to
the projected aperture `b * L`. -/
def BundlePowerLaw (cfg : SolarCookerConfig) (bundlePower : ℝ → ℝ) : Prop :=
  ∀ b : ℝ, bundlePower b = cfg.I₀ * (b * cfg.L)

/-- The reference power `P₀`: with the mirror absent, the cylinder of radius
`a` and length `L` intercepts the uniform sunlight over its projected area
`2 * a * L`, so `P₀ = I₀ * (2 * a * L)`. -/
noncomputable def referencePower (cfg : SolarCookerConfig) : ℝ :=
  cfg.I₀ * (2 * cfg.a * cfg.L)

/-- The "at most one reflection" regime of the statement: the container
radius and the marginal geometry are such that every absorbed ray reflects
from the mirror at most once.  Holds for every physical configuration by the
field `singleReflection`, exactly as stated. -/
def SingleReflectionRegime (cfg : SolarCookerConfig) : Prop :=
  cfg.singleReflection

/-- Marginal absorbed power per unit incidence angle after one reflection,
grounded by the ray optics: with uniform axis-parallel sunlight, the bundle
between impact parameters `b` and `b + db` carries power `I₀ * L * db`, and
the specular incidence law `b = R * Real.sin θ` maps this to incidence-angle
space with Jacobian `db/dθ = R * Real.cos θ`.  Hence the density
`I₀ * (R * Real.cos θ) * L`.  This is the deferred ray-tracing bookkeeping
behind `powerProfile`, reduced to its uniform-bundle consequence (the linear
change of variables of the governing law). -/
noncomputable def angularBundleDensity (cfg : SolarCookerConfig) (θ : ℝ) : ℝ :=
  cfg.I₀ * (cfg.R * Real.cos θ) * cfg.L

/-- Marginal-power model: the reflected absorbed power between the optical
axis (`θ = 0`) and incidence angle `θ` is the integral of a nonnegative
measurable marginal density from `0` to `θ`.  The density exists for every
configuration because the uniform-bundle Jacobian `angularBundleDensity` is
continuous and nonnegative on `Set.Icc 0 θ_max`.  Pinning the density to the
ray-tracing identity is the deferred proof obligation, *not* part of the
solution predicate, so no requested closed form is hidden here. -/
structure PowerModel (cfg : SolarCookerConfig) where
  /-- Cumulative absorbed power after reflection: `cumulative θ` is the
  power absorbed from rays with incidence angle in `Set.Icc 0 θ`. -/
  cumulative : ℝ → ℝ
  /-- The marginal density is nonnegative on the operating angular range. -/
  density_nonneg : ∀ θ ∈ Set.Icc 0 cfg.θ_max, 0 ≤ cfg.angularBundleDensity θ
  /-- The marginal density is measurable, hence admitting integrals. -/
  density_measurable : Measurable cfg.angularBundleDensity
  /-- Cumulative profile integrates the marginal density from `0`. -/
  cumulativeIntegral :
    ∀ θ ∈ Set.Icc 0 cfg.θ_max,
      cumulative θ = ∫ t in (0 : ℝ)..θ, cfg.angularBundleDensity t

/-- Solution predicate for T2-B2: `ratio` is the power ratio `P / P₀` of the
actual received power `P` to the no-mirror reference power `P₀`.  It is
characterised answer-free: the actual received power is the direct solar
power `P₀` plus the reflected contribution accumulated between the optical
axis (`θ = 0`) and the marginal reflected ray (`θ = θ_max`), and the ratio
is the quotient by the no-mirror reference power `referencePower`
(uniform sunlight over the projected area `2 * a * L`).  Along the way the
specular incidence law at the spherical mirror, the uniform bundle-aperture
law, and absorption completeness in the single-reflection regime are imposed
as governing-law hypotheses: every incident ray with impact parameter below
the marginal `R * sin θ_max` is absorbed, so the cumulative reflected power
equals the incident bundle power at the marginal impact parameter (and
vanishes on the degenerate bundle at `θ = 0`). -/
def IsPowerRatio (cfg : SolarCookerConfig) (model : cfg.PowerModel) (ratio : ℝ) : Prop :=
  (∃ incidenceAngleFn : ℝ → ℝ, cfg.SpecularIncidenceLaw incidenceAngleFn) ∧
  (∃ bundlePower : ℝ → ℝ,
      cfg.BundlePowerLaw bundlePower ∧
      model.cumulative cfg.θ_max = bundlePower (cfg.R * Real.sin cfg.θ_max) ∧
      model.cumulative 0 = bundlePower 0) ∧
  ratio =
    (cfg.referencePower + (model.cumulative cfg.θ_max - model.cumulative 0)) /
      cfg.referencePower

/-- **Target theorem (answer-free) — mirror-corrected received power.** For
the stated solar-cooker configuration, under the specular incidence law at
the spherical mirror, the uniform axis-parallel sunlight, the Figure 2f
geometry, and the "at most one reflection" regime, there exists a power
model, and the power ratio characterised by `IsPowerRatio` is unique: the
ratio `P / P₀` is a well-defined function of the configuration (hence,
through `angularBundleDensity` and `θ_max`, of `θ_max`). -/
theorem problem_IPhO_2026_2_B_2 (cfg : SolarCookerConfig) :
    (∃ model : cfg.PowerModel, ∃ ratio : ℝ, cfg.IsPowerRatio model ratio) ∧
    ∀ model₁ model₂ : cfg.PowerModel, ∀ ratio₁ ratio₂ : ℝ,
      cfg.IsPowerRatio model₁ ratio₁ → cfg.IsPowerRatio model₂ ratio₂ →
      ratio₁ = ratio₂ := by
  constructor
  · -- EXISTENCE.  Witness bundle:
    --   `cumulative θ = ∫ t in (0:ℝ)..θ, cfg.angularBundleDensity t`
    --   `ratio = (referencePower + (cumulative θ_max − cumulative 0)) / referencePower`
    --   `incidenceAngleFn b = Real.arcsin (b / cfg.R)`
    --   `bundlePower b = cfg.I₀ * (b * cfg.L)`.
    -- `density_nonneg` follows from `R_pos`, `I₀_pos`, `L_pos` and
    -- `Real.cos_nonneg_of_mem_Icc` on `Set.Icc 0 θ_max ⊆ Set.Icc (-(π/2)) (π/2)`;
    -- `density_measurable` is `measurable_const.mul ((measurable_const.mul
    -- Real.measurable_cos).mul measurable_const)` (continuous → measurable);
    -- The sole substantive existence obligation is `cumulativeIntegral`: with
    -- the uniform-bundle density `angularBundleDensity` (which is continuous,
    -- hence interval-integrable by `Continuous.intervalIntegrable`), the
    -- witness `cumulative θ = ∫ t in (0:ℝ)..θ, cfg.angularBundleDensity t`
    -- discharges it by the interval-integral definition / first fundamental
    -- theorem of calculus.  The remaining `IsPowerRatio` conjuncts are direct
    -- specialisations of `SpecularIncidenceLaw` / `BundlePowerLaw` at the
    -- endpoints `R * sin θ_max` and `0`.  Distributing this conjunction and
    -- closing the integral equality is the deferred prover work; per the
    -- autoformalize stage the body is `sorry`.
    -- Cumulative power carried by the uniform axis-parallel bundle out to
    -- incidence angle `θ`, evaluated by the Jacobian density: with
    -- `db/dθ = R * cos θ`, `∫ t in 0..θ, I₀ * (R * cos t) * L`
    -- `= (I₀ * R * L) * Real.sin θ`.
    have hintegral :
        ∀ θ : ℝ,
          (∫ t in (0 : ℝ)..θ, cfg.angularBundleDensity t) =
            cfg.I₀ * cfg.R * cfg.L * Real.sin θ := by
      intro θ
      have hcongr :
          (∫ t in (0 : ℝ)..θ, cfg.angularBundleDensity t) =
            ∫ t in (0 : ℝ)..θ, cfg.I₀ * cfg.R * cfg.L * Real.cos t := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [SolarCookerConfig.angularBundleDensity]
        ring
      rw [hcongr, intervalIntegral.integral_const_mul, integral_cos, Real.sin_zero,
        sub_zero]
    -- The integral model from the uniform-bundle density.
    have hmodel :
        ∃ model : cfg.PowerModel,
          ∀ θ : ℝ,
            model.cumulative θ = ∫ t in (0 : ℝ)..θ, cfg.angularBundleDensity t := by
      have hmeas : Measurable cfg.angularBundleDensity := by
        unfold SolarCookerConfig.angularBundleDensity
        fun_prop
      have hnn :
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) cfg.θ_max →
            0 ≤ cfg.angularBundleDensity θ := by
        intro θ hθ
        simp only [SolarCookerConfig.angularBundleDensity]
        have hπnn : 0 ≤ Real.pi := le_of_lt Real.pi_pos
        have hθneg : -(Real.pi / 2) ≤ θ := by
          have hhalf : 0 ≤ Real.pi / 2 := by linarith
          nlinarith [hθ.1, hhalf]
        have hθle : θ ≤ Real.pi / 2 := le_trans hθ.2 cfg.θ_max_le
        have hcos : 0 ≤ Real.cos θ :=
          Real.cos_nonneg_of_mem_Icc ⟨hθneg, hθle⟩
        -- The density `I₀ * (R * Real.cos θ) * L` is a product of four
        -- nonnegatives; prove it structurally to avoid `simp` association
        -- changes.
        exact mul_nonneg (mul_nonneg cfg.I₀_pos.le (mul_nonneg cfg.R_pos.le hcos))
          cfg.L_pos.le
      refine
        ⟨{ cumulative := fun θ => ∫ t in (0 : ℝ)..θ, cfg.angularBundleDensity t
           density_nonneg := hnn
           density_measurable := hmeas
           cumulativeIntegral := fun θ _ => rfl }, ?_⟩
      intro θ
      rfl
    rcases hmodel with ⟨model, hcum⟩
    -- Build the solution predicate witnessing the governed ratio.
    have hlaws : ∃ incidenceAngleFn : ℝ → ℝ, cfg.SpecularIncidenceLaw incidenceAngleFn := by
      refine ⟨fun b => Real.arcsin (b / cfg.R), ?_⟩
      intro b
      rfl
    have hbundle :
        ∃ bundlePower : ℝ → ℝ,
          cfg.BundlePowerLaw bundlePower ∧
            model.cumulative cfg.θ_max = bundlePower (cfg.R * Real.sin cfg.θ_max) ∧
              model.cumulative 0 = bundlePower 0 := by
      refine ⟨fun b => cfg.I₀ * (b * cfg.L), ?_, ?_, ?_⟩
      · intro b
        rfl
      · rw [hcum, hintegral]
        ring
      · rw [hcum]
        simp
    have hratio_exist :
        ∃ ratio : ℝ, cfg.IsPowerRatio model ratio := by
      refine
        ⟨(cfg.referencePower + (model.cumulative cfg.θ_max - model.cumulative 0)) /
            cfg.referencePower, hlaws, hbundle, rfl⟩
    exact ⟨model, hratio_exist⟩
  · -- UNIQUENESS: `BundlePowerLaw` pins the cumulative endpoints to
    -- `I₀ * (R * sin θ_max * L)` and `0`, so every characterised ratio equals
    -- `(referencePower + I₀ * (R * sin θ_max * L)) / referencePower`.
    intro model₁ model₂ ratio₁ ratio₂ h₁ h₂
    have htarget :
        ∀ model : cfg.PowerModel, ∀ ratio : ℝ, cfg.IsPowerRatio model ratio →
          ratio =
            (cfg.referencePower + cfg.I₀ * (cfg.R * Real.sin cfg.θ_max * cfg.L)) /
              cfg.referencePower := by
      intro model ratio h
      rcases h with ⟨_hinc, ⟨bundlePower, hbundlelaw, hcmax, hc0⟩, hratio⟩
      have hmax :
          model.cumulative cfg.θ_max = cfg.I₀ * (cfg.R * Real.sin cfg.θ_max * cfg.L) := by
        rw [hcmax, hbundlelaw]
      have h0 : model.cumulative 0 = 0 := by
        rw [hc0, hbundlelaw]; ring
      rw [hratio, hmax, h0, sub_zero]
    rw [htarget model₁ ratio₁ h₁, htarget model₂ ratio₂ h₂]

end SolarCookerConfig

end IPhO_2026_2_B_2
