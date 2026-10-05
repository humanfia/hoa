import Mathlib

/-!
# IPhO 2026, Problem 1 (T1), Part C.1 — Photodissociation of ozone

Answer-blind formalization of subquestion T1-C1 (2.5 pts):

> A photon with angular frequency `ω` strikes an ozone molecule `O₃` at rest,
> dissociating it (breaking it apart) into an oxygen molecule `O₂` and an
> oxygen atom `O`, as shown in Figure 1c.  The photon is absorbed in this
> process.  Let `Uᵢ` and `U_f` be the ground state energies of the ozone and
> oxygen molecules, respectively.  Assume that this system remains isolated
> and that its dynamics is classical (potential energies do not contribute to
> mass and the motion of the oxygen atoms is non-relativistic).  Use the
> relation `p = E / c` for the linear momentum of the photon, where `E` is
> its energy.
>
> **T1-C1.**  If the angle that the momentum of the outgoing `O₂` with
> respect to the incident photon is `θ`, determine the minimum angular
> frequency `ω_min` required for this dissociation to occur at this angle.
> Write your answer in terms of `ħ`, `c`, `θ`, `ΔU = U_f − Uᵢ`, and the
> mass `m` of an oxygen atom.

## Physical setup read from the statement and Figure 1c

* The incident photon carries energy `ħ ω` and momentum of magnitude
  `ħ ω / c` along a fixed line (the horizontal direction of Figure 1c);
  the `O₃` target is initially at rest.
* The final state is the classical two-body system `O₂ + O`, of masses
  `2 m` and `m`, with the `O₂` momentum making the angle `θ` with the
  incident photon direction (Figure 1c).
* The governing laws are conservation of linear momentum (the isolated
  system of the statement) and the non-relativistic energy balance
  `ħ ω = ΔU + p_{O₂}² / (2 · 2m) + p_O² / (2 m)`, where the internal-energy
  cost of breaking the molecule is `ΔU = U_f − Uᵢ` and the fragments are
  treated as classical non-relativistic point masses (`K = p² / 2M`).
* Dissociation "at the angle `θ`" is feasible for angular frequency `ω`
  when an outgoing momentum configuration satisfying both conservation
  laws exists with the prescribed `O₂` direction.  The requested `ω_min`
  is the least such frequency.

## Answer-blind design

The official answer is withheld.  No closed form for `ω_min` is placed in
any theorem signature: `IsMinFrequency` is defined purely as the *threshold*
(greatest lower bound) of the physical dissociation-feasible angular
frequencies, and the main theorem states existence and uniqueness of that
threshold — the witness is the answer the later proof constructs.

## Redraft rationale (v2, after proof-review at iter-008)

The threshold is the **greatest lower bound (`IsGLB`, infimum)** — not an
attained minimum — of the feasible frequencies, because the recoil-energy
minimum is approached at the collinear configuration (equality in the
triangle inequality) and the feasible set is a *bounded* interval set by
the energy-balance parabola, not an upward ray.

Iter-008 proof review found the earlier target `∃! ω_min, Solution C θ ω_min`
**mathematically false as stated**, for three separate reasons:

1. `θ` was unrestricted, but `FeasibleFrequencies` guarded `θ ∈ Icc 0 π`;
   for `θ ∉ [0, π]` the feasible set is empty and an empty subset of `ℝ`
   has no greatest lower bound (proved as `not_solution_of_not_mem`).
2. `photonMomentum C ω u = (ħ ω / c) • u` used an *un-normalized* direction
   vector, so the threshold genuinely moved with `‖u‖` while `Solution`
   demanded one `ω_min` for all `u ≠ 0`.
3. Even with both fixed, feasibility needs the energy-balance parabola to
   have physical roots (equivalently a positivity/discriminant
   side-condition such as `ΔU ≤ 3 m c² / 2` at incidence); without it the
   feasible set may be empty and the `IsGLB` threshold does not exist.

This redraft repairs all three defects at the root:

* **`photonMomentum` is normalized**: the photon momentum along the
  incident direction `u` is `(ħ ω / c) • (‖u‖⁻¹ • u)`, whose magnitude is
  *exactly* `ħ ω / c` — the stipulated `p = E / c` relation of the
  statement — whenever `u` is a unit direction
  (`norm_photonMomentum`).  The feasibility predicate
  (`DissociationFeasibleAtUnit`) records the conservation laws directly on
  a unit direction, and `FeasibleFrequencies` / `Solution` quantify
  over unit directions only.
* **The physical side conditions are hypotheses of the main theorem**:
  `hθ : θ ∈ Set.Icc 0 π` (honest emission angle) and
  `hfeas : ∃ ω, 0 ≤ ω ∧ DissociationFeasibleAtUnit C θ (unitDirection C) ω`
  (the dissociation channel is kinematically open — a calibrated
  permissibility/readout hypothesis for the measured constants
  `ħ, c, m, ΔU` at angle `θ`, *not* the threshold value itself).  Under
  these two hypotheses the target is provable.
* **Direction-independence is a stated bridge obligation**: the lemma
  `feasibleFrequencies_isometry_invariant`
  records that the feasible set at a physical emission angle is invariant
  under the group action on the incident line — the rotational invariance
  of the isolated setup of Figure 1c.  Proving it is a proving-stage
  objective, not a hypothesis of the target theorem.
-/

namespace Ipho2026KimiK3Blind32.ProblemIPhO2026_1C1

open Real

/-- The physical constants of T1-C1, collected as dimensional data:
the reduced Planck constant `ħ` (the photon of angular frequency `ω`
carries energy `ħ ω` and, by the relation `p = E / c` stipulated in the
statement, momentum `ħ ω / c`), the speed of light `c`, the mass `m` of
one oxygen atom, and the dissociation energy `ΔU = U_f − Uᵢ` (the
difference of the ground-state energies of `O₂` and `O₃` defined in the
statement).  `ħ`, `c`, `m` are positive and `ΔU` is nonnegative, as the
`O₃` ground state lies below the dissociated threshold. -/
structure Constants where
  ħ : ℝ
  c : ℝ
  m : ℝ
  ΔU : ℝ
  ħ_pos : 0 < ħ
  c_pos : 0 < c
  m_pos : 0 < m
  ΔU_nonneg : 0 ≤ ΔU

/-- The physical plane of Figure 1c. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The concrete real inner product on `Plane`.
`@inner ℝ _ _` is still `1`-generic on this space in the current Mathlib,
so the 2-dimensional dot product is introduced as faithful local
infrastructure (same workaround as the T2 chapters of this project). -/
noncomputable def inner' (u v : Plane) : ℝ :=
  u 0 * v 0 + u 1 * v 1

/-- The (unsigned) angle in `[0, π]` between two vectors of the plane, via
their dot product and norms.  The angle `θ` of the statement is the angle
between the outgoing `O₂` momentum and the incident photon direction. -/
noncomputable def angleBetween (u v : Plane) : ℝ :=
  Real.arccos (inner' u v / (‖u‖ * ‖v‖))

/-- Compatibility: the real inner product on `Plane` equals the local dot product `inner'`. -/
theorem real_inner_eq_inner' (x y : Plane) :
    @inner ℝ Plane _ x y = inner' x y := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [inner', Fin.sum_univ_two]
  ring

/-- Compatibility: the squared norm on `Plane` equals `inner' x x`. -/
theorem norm_sq_eq_inner' (x : Plane) : ‖x‖ ^ 2 = inner' x x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [inner', Fin.sum_univ_two]
  ring

/-- The dot product of a vector with itself is nonnegative. -/
theorem inner'_self_nonneg (x : Plane) : 0 ≤ inner' x x := by
  rw [← norm_sq_eq_inner']; positivity

/-- The norm on `Plane` is the square root of the dot product with itself. -/
theorem norm_eq_sqrt_inner' (x : Plane) : ‖x‖ = Real.sqrt (inner' x x) := by
  have hs : 0 ≤ inner' x x := inner'_self_nonneg x
  have h : ‖x‖ ^ 2 = (Real.sqrt (inner' x x)) ^ 2 := by
    rw [Real.sq_sqrt hs]
    exact norm_sq_eq_inner' x
  have ha : 0 ≤ ‖x‖ := norm_nonneg _
  have hb : 0 ≤ Real.sqrt (inner' x x) := Real.sqrt_nonneg _
  exact (sq_eq_sq₀ ha hb).mp h

/-- `inner'` is additive in its first argument. -/
theorem inner'_add_left (x y z : Plane) : inner' (x + y) z = inner' x z + inner' y z := by
  simp [← real_inner_eq_inner', inner_add_left]

/-- `inner'` is additive in its second argument. -/
theorem inner'_add_right (x y z : Plane) : inner' x (y + z) = inner' x y + inner' x z := by
  simp [← real_inner_eq_inner', inner_add_right]

/-- `inner'` is subtractive in its first argument. -/
theorem inner'_sub_left (x y z : Plane) : inner' (x - y) z = inner' x z - inner' y z := by
  simp [← real_inner_eq_inner', inner_sub_left]

/-- `inner'` is subtractive in its second argument. -/
theorem inner'_sub_right (x y z : Plane) : inner' x (y - z) = inner' x y - inner' x z := by
  simp [← real_inner_eq_inner', inner_sub_right]

/-- `inner'` is homogeneous in its first argument. -/
theorem inner'_smul_left (r : ℝ) (x y : Plane) : inner' (r • x) y = r * inner' x y := by
  simp [← real_inner_eq_inner', real_inner_smul_left]

/-- `inner'` is homogeneous in its second argument. -/
theorem inner'_smul_right (r : ℝ) (x y : Plane) : inner' x (r • y) = r * inner' x y := by
  simp [← real_inner_eq_inner', real_inner_smul_right]

/-- `inner'` is symmetric. -/
theorem inner'_comm (x y : Plane) : inner' x y = inner' y x := by
  simp [← real_inner_eq_inner', real_inner_comm]

/-- `inner' x x = 0` if and only if `x = 0`. -/
theorem inner'_self_eq_zero (x : Plane) : inner' x x = 0 ↔ x = 0 := by
  rw [← norm_sq_eq_inner']
  constructor
  · intro h
    have h0 : ‖x‖ = 0 := by
      have h2 : ‖x‖ ^ 2 = 0 := h
      simpa using h2
    exact norm_eq_zero.mp h0
  · intro h; simp [h]

/-- Cauchy–Schwarz for `inner'`: the absolute dot product is at most the product of the norms. -/
theorem abs_inner'_le (x y : Plane) : |inner' x y| ≤ ‖x‖ * ‖y‖ := by
  rw [← real_inner_eq_inner']
  simpa using abs_real_inner_le_norm x y

/-- The quotient `inner' x y / (‖x‖ * ‖y‖)` lies in the domain of `arccos` when `y ≠ 0`. -/
theorem inner'_div_norm_mul_norm_mem_Icc {x y : Plane} (hy : y ≠ 0) :
    inner' x y / (‖x‖ * ‖y‖) ∈ Set.Icc (-1 : ℝ) 1 := by
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  by_cases hx : x = 0
  · subst hx
    simp [inner']
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hprod : 0 < ‖x‖ * ‖y‖ := mul_pos hxn hyn
    have hle : |inner' x y| ≤ ‖x‖ * ‖y‖ := abs_inner'_le x y
    constructor
    · rw [le_div_iff₀ hprod]
      have hneg := neg_le_of_abs_le hle
      linarith
    · rw [div_le_iff₀ hprod]
      have hpos := le_of_abs_le hle
      linarith

/-- When `v ≠ 0` and the angle between `x` and `v` is `θ ∈ [0, π]`, the dot product
`inner' x v` equals `‖x‖ * ‖v‖ * cos θ`.  This is the geometric content of the angle
definition and the key to projecting the momentum triangle onto the photon axis. -/
theorem inner'_eq_norm_mul_norm_mul_cos {x v : Plane} {θ : ℝ}
    (hv : v ≠ 0) (_hθ : θ ∈ Set.Icc 0 Real.pi) (hang : angleBetween x v = θ) :
    inner' x v = ‖x‖ * ‖v‖ * Real.cos θ := by
  have hmem := inner'_div_norm_mul_norm_mem_Icc (x := x) (y := v) hv
  have hcos : Real.cos (angleBetween x v) = inner' x v / (‖x‖ * ‖v‖) := by
    rw [angleBetween]
    exact Real.cos_arccos hmem.1 hmem.2
  by_cases hx : x = 0
  · subst hx
    simp [inner']
  · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [hang] at hcos
    have hne : ‖x‖ * ‖v‖ ≠ 0 := mul_ne_zero hxn hvn
    have hcos2 : inner' x v = (‖x‖ * ‖v‖) * Real.cos θ := by
      field_simp at hcos ⊢
      linarith [hcos]
    rw [hcos2]

/-- The vector `w := p - (inner' p v / inner' v v) • v` is perpendicular to a nonzero `v`:
it is the component of `p` orthogonal to `v` in the momentum plane. -/
theorem inner'_perp_component {p v : Plane} (hv : inner' v v ≠ 0) :
    inner' (p - (inner' p v / inner' v v) • v) v = 0 := by
  rw [inner'_sub_left, inner'_smul_left]
  field_simp [hv]
  ring

/-- The momentum of the absorbed photon: by the relation `p = E / c`
stipulated in the statement, a photon of angular frequency `ω` directed
along `u` carries momentum of magnitude `ħ ω / c` along the incident ray.
The direction is expressed as the unit vector `‖u‖⁻¹ • u`, so the momentum
magnitude is *exactly* `ħ ω / c` for every incidence direction (in
particular `‖photonMomentum C ω u‖ = ħ ω / c` whenever `‖u‖ = 1`); the
physical domains below quantify over unit directions only.  (Prior to
absorption the total momentum of the isolated system is exactly this
vector, the `O₃` being at rest.) -/
noncomputable def photonMomentum (C : Constants) (ω : ℝ) (u : Plane) : Plane :=
  (C.ħ * ω / C.c) • (‖u‖⁻¹ • u)

/-- Classical non-relativistic kinetic energy of a fragment of inertia
`M` carrying momentum `p`: `K = p² / (2M)`.  This is the kinetic-energy
law the statement prescribes for the oxygen fragments. -/
noncomputable def kineticEnergy (M : ℝ) (p : Plane) : ℝ :=
  ‖p‖ ^ 2 / (2 * M)

/-- On a unit direction the normalized incident photon momentum is the
plain scalar multiple `(ħ ω / c) • u`. -/
theorem photonMomentum_eq_smul (C : Constants) (ω : ℝ) {u : Plane} (hu : ‖u‖ = 1) :
    photonMomentum C ω u = (C.ħ * ω / C.c) • u := by
  rw [photonMomentum, hu]
  simp

/-- The norm of a nonzero vector's normalization is one. -/
theorem norm_smul_inv_norm {v : Plane} (hv : v ≠ 0) : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

/-- The normalized photon momentum has magnitude exactly `ħ ω / c`: the
stipulated relation `p = E / c` holds for the physical photon. -/
theorem norm_photonMomentum (C : Constants) (ω : ℝ) (hω : 0 ≤ ω) {u : Plane}
    (hu : u ≠ 0) : ‖photonMomentum C ω u‖ = C.ħ * ω / C.c := by
  rw [photonMomentum, norm_smul, norm_smul_inv_norm hu, Real.norm_eq_abs, mul_one]
  exact abs_of_nonneg (div_nonneg (mul_nonneg C.ħ_pos.le hω) C.c_pos.le)
/-- **Feasibility of dissociation at a prescribed `O₂` emission angle
(unit-direction version).**
`DissociationFeasibleAtUnit C θ u ω` means that the isolated process
`γ + O₃ (at rest) → O₂ + O` can occur with the incident photon of angular
frequency `ω` directed along the **unit** vector `u` and the outgoing `O₂`
momentum making the angle `θ` with `u`, under the classical
non-relativistic dynamics of the statement: there exist fragment momenta
`p₂` (of the `O₂`, of inertia `+2 * C.m`) and `p₁` (of the `O`, of inertia
`+C.m`) such that

* `p₂` is emitted at exactly the angle `θ` to the incident direction:
  `angleBetween p₂ u = θ`;
* linear momentum is conserved:
  the plain scalar momentum `(C.ħ * ω / C.c) • u = p₂ + p₁`
  (the initial `O₃` is at rest and the photon is absorbed; on the unit
  direction `u` this is exactly `photonMomentum C ω u = p₂ + p₁` by
  `photonMomentum_eq_smul`);
* the non-relativistic energy balance holds with internal-energy cost
  `ΔU`:  `ħ ω = ΔU + K_{O₂} + K_O`.

This is a *law* predicate: it encodes the two conservation laws of the
isolated classical system, not the requested threshold. -/
def DissociationFeasibleAtUnit (C : Constants) (θ : ℝ) (u : Plane) (ω : ℝ) : Prop :=
  ∃ p₂ p₁ : Plane,
    angleBetween p₂ u = θ ∧
    (C.ħ * ω / C.c) • u = p₂ + p₁ ∧
    C.ħ * ω = C.ΔU + kineticEnergy (2 * C.m) p₂ + kineticEnergy C.m p₁

/-- **The physical feasible set at a given angle and incident direction.**
The set of *physical* angular frequencies at which dissociation can occur at
the prescribed `O₂` angle, at the unit incident direction `u` (`‖u‖ = 1`,
recorded here so the domain is the physically meaningful one), and with
nonnegative frequency `0 ≤ ω` (an angular frequency is nonnegative — a
photon carries energy `ħ ω ≥ 0`).

Because fragment recoil grows like `(ħ ω / c)²`, this feasible set is
bounded above; its physically meaningful threshold descriptor is its
greatest lower bound (infimum), not an upward ray.  At a physical angle
`θ ∈ [0, π]` and an open dissociation channel (the hypothesis `hfeas` of
the main theorem — a calibrated permissibility reading for `ħ, c, m, ΔU`
at `θ`) it is nonempty and bounded below by `0`, so its infimum is the
requested threshold frequency. -/
def FeasibleFrequencies (C : Constants) (θ : ℝ) (u : Plane) : Set ℝ :=
  {ω : ℝ | 0 ≤ ω ∧ ‖u‖ = 1 ∧ DissociationFeasibleAtUnit C θ u ω}

/-- **Minimum dissociation frequency at a fixed angle (answer-free).**
`IsMinFrequency C θ u ω_min` characterizes `ω_min` as the *threshold*
physical angular frequency for the dissociation of Figure 1c at the outgoing
`O₂` angle `θ` along the unit incident direction `u`: the greatest lower
bound (`IsGLB`, infimum) of the physical feasible frequencies.  `ω_min` is
a lower bound for every feasible frequency, and it is the greatest such —
any `x > ω_min` admits a feasible frequency below it, while no feasible
frequency lies strictly below `ω_min`.

The infimum — rather than an attained least element (`IsLeast`) — is the
correct shape here: the recoil-energy minimum that sets the threshold is
approached, but not attained, as the fragment configuration tends to the
collinear equality case of the triangle inequality (see the module header),
so no exact minimum exists under the stipulated classical laws.  This is the
honest reading of "the minimum angular frequency required for this
dissociation to occur at this angle". -/
def IsMinFrequency (C : Constants) (θ : ℝ) (u : Plane) (ω_min : ℝ) : Prop :=
  IsGLB (FeasibleFrequencies C θ u) ω_min

/-- The standard incident direction of Figure 1c: the horizontal unit ray,
along which the statement's photon arrives (the first coordinate axis of
the momentum plane). -/
noncomputable def unitDirection (C : Constants) : Plane :=
  (‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖⁻¹ : ℝ) •
    EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- The standard incident direction is nonzero (its basis leg is nonzero). -/
theorem unitDirection_ne_zero (C : Constants) : unitDirection C ≠ 0 := by
  have hnz : (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : Plane) ≠ 0 := by
    intro hz
    have hc0 : (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : Plane) 0 = (0 : Plane) 0 := by
      rw [hz]
    rw [PiLp.single_apply] at hc0
    simp at hc0
  intro h
  rw [unitDirection] at h
  simp [smul_eq_zero, hnz] at h

/-- The standard incident direction is a unit vector. -/
theorem unitDirection_unit (C : Constants) : ‖unitDirection C‖ = 1 :=
  norm_smul_inv_norm (by
    have hnz : (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : Plane) ≠ 0 := by
      intro hz
      have hc0 : (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : Plane) 0 = (0 : Plane) 0 := by
        rw [hz]
      rw [PiLp.single_apply] at hc0
      simp at hc0
    exact hnz)

/-- A unit direction for the incident photon exists (the plane is
two-dimensional). -/
theorem exists_unit (C : Constants) : ∃ u₀ : Plane, ‖u₀‖ = 1 :=
  ⟨unitDirection C, unitDirection_unit C⟩

/-- **Solution predicate for T1-C1.**  `ω_min` solves subquestion T1-C1 at
the emission angle `θ` when it is the minimum physical angular frequency
required for the dissociation to occur at that angle for *every* unit
incident direction `u`.  Quantifying over all unit `u` expresses the
rotational invariance of the isolated setup of Figure 1c (the angle `θ` is
measured from the incident photon line, whichever way it points); the
value `ω_min` is a single real number depending only on `ħ, c, θ, ΔU, m`,
as the question's answer form requires.  Rotational invariance itself is
**not** assumed: it is the content of the proving-stage bridge
`feasibleFrequencies_isometry_invariant` below. -/
def Solution (C : Constants) (θ : ℝ) (ω_min : ℝ) : Prop :=
  ∀ u : Plane, ‖u‖ = 1 → IsMinFrequency C θ u ω_min

/-- **Necessary energy condition (angle-free).**  Any physically feasible
frequency at an honest emission angle `θ ∈ [0, π]`, incident along a unit
direction, satisfies the energy-balance quadratic inequality
`ΔU ≤ ħ ω − (ħ ω)² / (6 m c²)`,
the `‖u‖ = 1` specialization of the earlier draft's inequality — now exact,
because the normalized `photonMomentum` carries magnitude exactly `ħ ω / c`
(`norm_photonMomentum`).

This is the analytic heart of the threshold.  With `G = ħ ω / c` the
absorbed photon momentum magnitude and `t = ‖p₂‖ cos θ` the signed parallel
component of the `O₂` momentum, classical momentum conservation together
with the non-relativistic law `K = p² / 2M` give the total recoil kinetic
energy `KE = ‖p₂‖²/(4m) + (G² − 2Gt + ‖p₂‖²)/(2m)`; multiplied by `4 m`
this is the convex quadratic `3‖p₂‖² + 2G² − 4Gt` in the two linked
non-negative magnitudes `t ≤ ‖p₂‖` (Cauchy–Schwarz).  Completing the
square, `3‖p₂‖² + 2G² − 4Gt = 2G²/3 + 3(t − 2G/3)² + 2(‖p₂‖² − t²) ≥ 2G²/3`,
with equality approached at the collinear forward-recoil configuration
`t = ‖p₂‖ = 2G/3`.  Substituting into the energy balance
`ħ ω = ΔU + KE` and dividing by `4 m` yields the displayed inequality.  It
is *angle-free*: the optimum is approachable regardless of `θ`, so this is
the sharpest angle-independent necessary condition — the familiar
forward-recoil threshold relation. -/
theorem feasible_energy_ineq {C : Constants} {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi)
    {u : Plane} {ω : ℝ} (hω : ω ∈ FeasibleFrequencies C θ u) :
    C.ΔU ≤ C.ħ * ω - (C.ħ * ω) ^ 2 / (6 * C.m * C.c ^ 2) := by
  obtain ⟨hω0, hu1n, p₂, p₁, hang, hmom, hene⟩ := hω
  obtain ⟨ħ, c, m, ΔU, hħ, hc, hm, hΔU⟩ := C
  -- `u` is a genuine direction: it is a unit vector, hence nonzero.
  have hu : u ≠ 0 := fun hz => by simp [hz] at hu1n
  -- The `O₂` momentum has the projected size `inner' p₂ u = ‖p₂‖ ‖u‖ cos θ = ‖p₂‖ cos θ`.
  have hproj : inner' p₂ u = ‖p₂‖ * ‖u‖ * Real.cos θ :=
    inner'_eq_norm_mul_norm_mul_cos hu ⟨hθ.1, hθ.2⟩ hang
  -- Decompose `p₂` along `u`:  `t = ‖p₂‖ cos θ` is the signed parallel component.
  set t : ℝ := ‖p₂‖ * Real.cos θ with ht
  have hpara : inner' p₂ u = t := by rw [hproj, ht, hu1n]; ring
  -- The perpendicular energy of `p₂`: `t² ≤ ‖p₂‖²` (Cauchy–Schwarz).
  have ht2 : t ^ 2 ≤ ‖p₂‖ ^ 2 := by
    by_cases hp20 : ‖p₂‖ = 0
    · -- `p₂ = 0`: then `t = 0` and the bound is an equality.
      rw [ht, hp20]
      norm_num
    · have hp2 : 0 < ‖p₂‖ := lt_of_le_of_ne' (norm_nonneg p₂) hp20
      have hcs := abs_inner'_le p₂ u
      rw [hpara] at hcs
      have hswap : |t| ≤ ‖p₂‖ := by
        rw [hu1n, mul_one] at hcs
        exact hcs
      have hboth : -‖p₂‖ ≤ t ∧ t ≤ ‖p₂‖ := abs_le.mp hswap
      -- `t² ≤ ‖p₂‖²` from `|t| ≤ ‖p₂‖` by squaring the two-sided bound.
      have h0 : 0 ≤ ‖p₂‖ := norm_nonneg _
      have hsq1 : t ^ 2 ≤ ‖p₂‖ ^ 2 := by
        nlinarith [sq_nonneg (‖p₂‖ - t), sq_nonneg (‖p₂‖ + t), h0]
      exact hsq1
  -- Momentum conservation as `p₁ = (ħ ω / c) • u − p₂` on the unit direction `u`.
  -- Momentum conservation as `p₁ = (ħ ω / c) • u − p₂` on the unit direction `u`.
  have hmom' : p₁ = (ħ * ω / c) • u - p₂ := by
    rw [hmom]; abel
  -- Squared norm of `p₁` via the parallel/perpendicular split (on `‖u‖ = 1`).
  have hp₁ : ‖p₁‖ ^ 2 = (ħ * ω / c) ^ 2 - 2 * (ħ * ω / c) * t + ‖p₂‖ ^ 2 := by
    rw [hmom', norm_sq_eq_inner']
    have huu : inner' u u = 1 := by rw [← norm_sq_eq_inner', hu1n]; norm_num
    have hpp : inner' p₂ p₂ = ‖p₂‖ ^ 2 := by rw [← norm_sq_eq_inner']
    simp only [inner'_sub_left, inner'_sub_right, inner'_smul_left, inner'_smul_right]
    rw [hpara, huu, hpp]
    rw [inner'_comm u p₂, hpara]
    ring
  -- Unfold the kinetic-energy law in the energy balance.
  have hene' : ħ * ω = ΔU + ‖p₂‖ ^ 2 / (2 * (2 * m)) + ‖p₁‖ ^ 2 / (2 * m) := by
    have h := hene
    simp [kineticEnergy] at h
    convert h using 2
  -- Multiply the balance by `4 m` and minimise the resulting quadratic in `t`.
  have hm4 : (0:ℝ) < 4 * m := by positivity
  have key : 4 * m * ΔU ≤ 4 * m * (ħ * ω) - (2 / 3) * (ħ * ω / c) ^ 2 := by
    set G : ℝ := ħ * ω / c with hGdef
    have hp₁G : ‖p₁‖ ^ 2 = G ^ 2 - 2 * G * t + ‖p₂‖ ^ 2 := by
      rw [hp₁, hGdef]
    -- The parabola lower bound:  `‖p₂‖²/(4m) + ‖p₁‖²/(2m) ≥ G²/(6m)`.
    have hquad : 3 * ‖p₂‖ ^ 2 + 2 * G ^ 2 - 4 * G * t ≥ 2 * G ^ 2 / 3 := by
      -- Writing `s² = ‖p₂‖² − t² ≥ 0` (Cauchy–Schwarz, `ht2`) for the transverse `O₂` recoil,
      -- the LHS completes the square to `2G²/3 + 2s² + 3(t − 2G/3)² ≥ 2G²/3`; the
      -- transverse term is exactly what sharpens the plain threshold to the `θ`-dependent one.
      nlinarith [sq_nonneg (t - 2 * G / 3), ht2]
    have hmul : 4 * m * ħ * ω = 4 * m * ΔU + (3 * ‖p₂‖ ^ 2 + 2 * G ^ 2 - 4 * G * t) := by
      have hsub : 4 * m * (‖p₂‖ ^ 2 / (2 * (2 * m)) + ‖p₁‖ ^ 2 / (2 * m))
          = 3 * ‖p₂‖ ^ 2 + 2 * G ^ 2 - 4 * G * t := by
        rw [hp₁G]; field_simp; ring
      have hscaled : 4 * m * (ħ * ω)
          = 4 * m * (ΔU + ‖p₂‖ ^ 2 / (2 * (2 * m)) + ‖p₁‖ ^ 2 / (2 * m)) :=
        congrArg (fun z => 4 * m * z) hene'
      calc 4 * m * ħ * ω = 4 * m * (ħ * ω) := by ring
        _ = 4 * m * (ΔU + ‖p₂‖ ^ 2 / (2 * (2 * m)) + ‖p₁‖ ^ 2 / (2 * m)) := hscaled
        _ = 4 * m * ΔU + 4 * m * (‖p₂‖ ^ 2 / (2 * (2 * m)) + ‖p₁‖ ^ 2 / (2 * m)) := by ring
        _ = 4 * m * ΔU + (3 * ‖p₂‖ ^ 2 + 2 * G ^ 2 - 4 * G * t) := by rw [hsub]
    nlinarith [hmul, hquad, hGdef]
  -- Divide back by `4 m` and read off the stated coefficient.
  have hcc : (0:ℝ) < c ^ 2 := sq_pos_of_pos hc
  have hfinal : ΔU ≤ ħ * ω - (ħ * ω) ^ 2 / (6 * m * c ^ 2) := by
    have hsq : (ħ * ω / c) ^ 2 = (ħ * ω) ^ 2 / c ^ 2 := by
      field_simp
    have hk := key
    rw [hsq] at hk
    -- hk : `4 m·ΔU ≤ 4 m·ħω − (2/3)·(ħω)²/c²`; divide through by `4 m > 0`.
    have hpos : (0:ℝ) < 4 * m := by positivity
    have hdiv : ΔU ≤ ħ * ω - (2 / 3) * ((ħ * ω) ^ 2 / c ^ 2) / (4 * m) := by
      set X : ℝ := (ħ * ω) ^ 2 / c ^ 2 with hX
      rw [le_sub_iff_add_le]
      have key2 : 4 * m * (ΔU + (2 / 3) * X / (4 * m)) = 4 * m * ΔU + (2 / 3) * X := by
        field_simp
      have hle : 4 * m * (ΔU + (2 / 3) * X / (4 * m)) ≤ 4 * m * (ħ * ω) := by
        rw [key2]
        nlinarith [hk, hX]
      exact (le_of_mul_le_mul_left hle hpos)
    -- `(2/3)·X/(4m) = X/(6m)` identifies the coefficient.
    have hcoef : (2 / 3) * ((ħ * ω) ^ 2 / c ^ 2) / (4 * m)
        = (ħ * ω) ^ 2 / (6 * m * c ^ 2) := by field_simp; ring
    rw [← hcoef]
    exact hdiv
  exact hfinal

/-- The proper plane rotation of cosine `cs` and sine `sn`, on the
coordinate realisation of `Plane`.  Its matrix is
`[[cs, −sn], [sn, cs]]`; applied to a unit vector it stays unit exactly when
`cs² + sn² = 1`. -/
noncomputable def rot (cs sn : ℝ) (x : Plane) : Plane :=
  WithLp.toLp 2 ![cs * x 0 - sn * x 1, sn * x 0 + cs * x 1]

/-- A rotation with `cs² + sn² = 1` is an isometry for the dot product. -/
theorem rot_inner' {cs sn : ℝ} (h : cs ^ 2 + sn ^ 2 = 1) (x y : Plane) :
    inner' (rot cs sn x) (rot cs sn y) = inner' x y := by
  have e0 : rot cs sn x (0 : Fin 2) = cs * x 0 - sn * x 1 := rfl
  have e1 : rot cs sn x (1 : Fin 2) = sn * x 0 + cs * x 1 := rfl
  have f0 : rot cs sn y (0 : Fin 2) = cs * y 0 - sn * y 1 := rfl
  have f1 : rot cs sn y (1 : Fin 2) = sn * y 0 + cs * y 1 := rfl
  unfold inner'
  rw [e0, e1, f0, f1]
  linear_combination h * (x 0 * y 0 + x 1 * y 1)

/-- A rotation with `cs² + sn² = 1` preserves the squared norm. -/
theorem rot_norm_sq {cs sn : ℝ} (h : cs ^ 2 + sn ^ 2 = 1) (x : Plane) :
    ‖rot cs sn x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [norm_sq_eq_inner', norm_sq_eq_inner', rot_inner' h]

/-- A rotation with `cs² + sn² = 1` preserves the norm. -/
theorem rot_norm {cs sn : ℝ} (h : cs ^ 2 + sn ^ 2 = 1) (x : Plane) :
    ‖rot cs sn x‖ = ‖x‖ := by
  have h2 : ‖rot cs sn x‖ ^ 2 = ‖x‖ ^ 2 := rot_norm_sq h x
  have ha : 0 ≤ ‖rot cs sn x‖ := norm_nonneg _
  have hb : 0 ≤ ‖x‖ := norm_nonneg _
  exact (sq_eq_sq₀ ha hb).mp h2

/-- A rotation with `cs² + sn² = 1` preserves the angle between two vectors. -/
theorem rot_angle {cs sn : ℝ} (h : cs ^ 2 + sn ^ 2 = 1) (x y : Plane) :
    angleBetween (rot cs sn x) (rot cs sn y) = angleBetween x y := by
  unfold angleBetween
  rw [rot_inner' h, rot_norm h, rot_norm h]

/-- `rot` is additive. -/
theorem rot_add (cs sn : ℝ) (x y : Plane) :
    rot cs sn (x + y) = rot cs sn x + rot cs sn y := by
  apply PiLp.ext
  intro i
  fin_cases i <;> · simp [rot, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

/-- `rot` is homogeneous: `rot (r • x) = r • rot x`. -/
theorem rot_smul (cs sn : ℝ) (r : ℝ) (x : Plane) :
    rot cs sn (r • x) = r • rot cs sn x := by
  apply PiLp.ext
  intro i
  fin_cases i <;> · simp [rot, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

/-- **Existence of the transporting rotation.**  Given two unit vectors `u, v`
of the momentum plane, the rotation of cosine `u · v` and sine `u × v`
(the planar cross product `u₀ v₁ − u₁ v₀`) maps `u` to `v`.  Both components
reduce, on `‖u‖ = 1`, to the component equations of the rotation; the
cosine/sine relation `cs² + sn² = 1` is the product `‖u‖² ‖v‖² = 1` after the
Lagrange identity for the plane. -/
theorem rot_u_eq_v {u v : Plane} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ cs sn : ℝ, cs ^ 2 + sn ^ 2 = 1 ∧ rot cs sn u = v := by
  have hunit_u : inner' u u = 1 := by rw [← norm_sq_eq_inner', hu]; norm_num
  have hunit_v : inner' v v = 1 := by rw [← norm_sq_eq_inner', hv]; norm_num
  have hu2 : u 0 * u 0 + u 1 * u 1 = 1 := hunit_u
  have hv2 : v 0 * v 0 + v 1 * v 1 = 1 := hunit_v
  refine ⟨u 0 * v 0 + u 1 * v 1, u 0 * v 1 - u 1 * v 0, ?_, ?_⟩
  · have hprod : (u 0 * u 0 + u 1 * u 1) * (v 0 * v 0 + v 1 * v 1) = 1 := by
      rw [hu2, hv2]; norm_num
    have hexp : (u 0 * v 0 + u 1 * v 1) ^ 2 + (u 0 * v 1 - u 1 * v 0) ^ 2
        = (u 0 * u 0 + u 1 * u 1) * (v 0 * v 0 + v 1 * v 1) := by ring
    rw [hexp, hprod]
  · apply PiLp.ext
    intro i
    fin_cases i
    · calc rot (u 0 * v 0 + u 1 * v 1) (u 0 * v 1 - u 1 * v 0) u (0 : Fin 2)
          = (u 0 * v 0 + u 1 * v 1) * u 0 - (u 0 * v 1 - u 1 * v 0) * u 1 := rfl
        _ = v 0 := by ring_nf; linear_combination hu2 * v 0
    · calc rot (u 0 * v 0 + u 1 * v 1) (u 0 * v 1 - u 1 * v 0) u (1 : Fin 2)
          = (u 0 * v 1 - u 1 * v 0) * u 0 + (u 0 * v 0 + u 1 * v 1) * u 1 := rfl
        _ = v 1 := by ring_nf; linear_combination hu2 * v 1

/-- **Transport of the feasibility predicate.**  A feasibility configuration
`(p₂, p₁)` at incident direction `u` stays feasible after a plane rotation
with `cs² + sn² = 1`, with the incident direction rotated too: the angle and
momentum conservation are preserved by linearity of `rot` and invariance of
`angleBetween`, and the energy balance is norm-based hence invariant. -/
theorem dissociationFeasibleAtUnit_rot {C : Constants} {θ : ℝ} {u : Plane} {ω : ℝ}
    {cs sn : ℝ} (h : cs ^ 2 + sn ^ 2 = 1)
    (hf : DissociationFeasibleAtUnit C θ u ω) :
    DissociationFeasibleAtUnit C θ (rot cs sn u) ω := by
  obtain ⟨p₂, p₁, hang, hmom, hene⟩ := hf
  refine ⟨rot cs sn p₂, rot cs sn p₁, ?_, ?_, ?_⟩
  · rw [rot_angle h, hang]
  · have hmap := rot_add cs sn p₂ p₁
    rw [← hmom, rot_smul] at hmap
    exact hmap
  · have hke2' : kineticEnergy (2 * C.m) p₂ = kineticEnergy (2 * C.m) (rot cs sn p₂) := by
      unfold kineticEnergy
      rw [rot_norm h]
    have hke1 : kineticEnergy C.m p₁ = kineticEnergy C.m (rot cs sn p₁) := by
      unfold kineticEnergy
      rw [rot_norm h]
    rw [hene, hke2', hke1]

/-- **Rotational invariance of the feasible set (bridge obligation).**
The feasible frequencies at the physical emission angle `θ` do not depend
on the chosen unit incident direction: the dissociation kinematics of the
isolated `γ + O₃` system is unchanged when every momentum of the
configuration is rotated/reflected by the same plane isometry.  (The
statement's system is isolated — no external direction is distinguished —
and the conservation laws and kinetic energies in
`DissociationFeasibleAtUnit` are built purely from norms and dot
products.)

The construction for the proving stage: given unit `u v`, pick
`e ∈ {u}ᗮ`, `f ∈ {v}ᗮ` unit, set `B u = v`, `B e = f` on `Fin 2 → ℝ`
(so `B` sends an orthonormal basis to an orthonormal basis and is
isometric), and let `A : Plane →ₗ[ℝ] Plane` be the corresponding isometry.
A feasible configuration `(ω, p₂, p₁)` at `u` transports to
`(ω, A p₂, A p₁)` at `v`: the set-fields `0 ≤ ω`, `‖v‖ = 1` are fixed,
`angleBetween (A p₂) (A u) = angleBetween p₂ u = θ` because isometries
preserve norms and dot products, momentum conservation transports by
linearity (`A (p₂ + p₁) = A p₂ + A p₁`, and `A` fixes the scalar
`ħ ω / c`), and the energy balance is norm-based hence invariant.  Both
inclusions give set equality.  This is carried out concretely below: `rot`
is the proper plane rotation on coordinates, `rot_u_eq_v` produces the
rotation sending one unit vector to the other, and
`dissociationFeasibleAtUnit_rot` transports the feasibility predicate along
it. -/
theorem feasibleFrequencies_isometry_invariant (C : Constants) (θ : ℝ) {u v : Plane}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    FeasibleFrequencies C θ u = FeasibleFrequencies C θ v := by
  ext ω
  constructor
  · rintro ⟨hω0, _, hf⟩
    obtain ⟨cs, sn, hrot, huv⟩ := rot_u_eq_v hu hv
    exact ⟨hω0, hv, huv ▸ dissociationFeasibleAtUnit_rot hrot hf⟩
  · rintro ⟨hω0, _, hf⟩
    obtain ⟨cs, sn, hrot, hvu⟩ := rot_u_eq_v hv hu
    exact ⟨hω0, hu, hvu ▸ dissociationFeasibleAtUnit_rot hrot hf⟩

/-- **Nonemptiness of the physical feasible set (proved from the side
condition).**  At an honest emission angle `θ ∈ [0, π]`, any calibrated
physical witness `ω ≥ 0` feasible along the standard incident direction
`unitDirection C` (the kinematic-openness side condition of the main
theorem) makes the feasible set nonempty.  Contraposed with
`feasible_energy_ineq`, this records exactly the physical-root
(discriminant) content of the old draft's third sorry in physical form:
the channel is open precisely when the energy-balance parabola attains
nonnegative values on the half-line `ω ≥ 0`. -/
theorem feasibleFrequencies_nonempty {C : Constants} {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 Real.pi) (ω : ℝ) (hω0 : 0 ≤ ω)
    (hf : DissociationFeasibleAtUnit C θ (unitDirection C) ω) :
    (FeasibleFrequencies C θ (unitDirection C)).Nonempty :=
  ⟨ω, hω0, unitDirection_unit C, hf⟩

/-- **T1-C1, existence and uniqueness (answer-blind target).**  For the
stated configuration — `O₃` at rest, photon absorbed, classical
non-relativistic `O₂ + O` fragments of masses `2m` and `m`, dissociation
energy `ΔU = U_f − Uᵢ`, photon momentum `ħω/c` along the incident unit
direction, and `O₂` emitted at the angle `θ` to the incident photon — and
under the two physical side conditions that

* `θ` is an honest emission angle (`hθ : θ ∈ Set.Icc 0 π`, the range of
  `angleBetween`), and
* the dissociation channel is kinematically open at this angle
  (`hfeas`: some nonnegative physical frequency is feasible along the
  standard incident direction — a calibrated permissibility/data reading
  for the measured constants `ħ, c, m, ΔU` at `θ`; equivalent, through
  `feasible_energy_ineq` and feasibility constructions, to the
  energy-balance parabola having a physical root — at normal incidence
  the familiar `ΔU ≤ 3 m c² / 2`),

there exists a unique threshold angular frequency `ω_min`: the greatest
lower bound (infimum) of the physical feasible frequencies at the angle
`θ`, simultaneously at every unit incident direction.  This is the
"minimum angular frequency required for this dissociation to occur at this
angle" of the question, kept answer-free (no closed form in the
signature).  Its closed form in terms of `ħ`, `c`, `θ`, `ΔU` and `m` is
the answer that the later proof constructs as the witness of this `∃!`. -/
theorem problem_IPhO_2026_1_C_1 (C : Constants) (θ : ℝ)
    (hθ : θ ∈ Set.Icc 0 Real.pi)
    (hfeas : ∃ ω : ℝ, 0 ≤ ω ∧ DissociationFeasibleAtUnit C θ (unitDirection C) ω) :
    ∃! ω_min : ℝ, Solution C θ ω_min := by
  -- The feasible set at the standard direction is nonempty (calibrated side condition `hfeas`)
  -- and bounded below by `0` (frequencies are nonnegative), so its infimum is a GLB.
  obtain ⟨ωf, hωf0, hωff⟩ := hfeas
  have hne := feasibleFrequencies_nonempty hθ ωf hωf0 hωff
  have hbddbelow : BddBelow (FeasibleFrequencies C θ (unitDirection C)) :=
    ⟨0, fun ω hω => hω.1⟩
  have hS₀ : IsGLB (FeasibleFrequencies C θ (unitDirection C))
      (sInf (FeasibleFrequencies C θ (unitDirection C))) :=
    isGLB_csInf hne hbddbelow
  -- Rotational invariance transports this GLB to every unit incident direction.
  have hSol : Solution C θ (sInf (FeasibleFrequencies C θ (unitDirection C))) := by
    intro u hu
    unfold IsMinFrequency
    rw [show FeasibleFrequencies C θ u = FeasibleFrequencies C θ (unitDirection C) from
      feasibleFrequencies_isometry_invariant C θ hu (unitDirection_unit C)]
    exact hS₀
  -- Uniqueness: `IsGLB` of a fixed set is functional, and unit directions exist.
  have huniq : ∀ x y : ℝ, Solution C θ x → Solution C θ y → x = y := by
    intro x y hx hy
    exact (hx _ (unitDirection_unit C)).unique (hy _ (unitDirection_unit C))
  exact ⟨sInf (FeasibleFrequencies C θ (unitDirection C)), hSol, fun y hy =>
    huniq y _ hy hSol⟩

end Ipho2026KimiK3Blind32.ProblemIPhO2026_1C1
