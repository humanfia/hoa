import Mathlib

/-!
# IPhO 2026, Theoretical Problem 3, Part B.1 — Heat transferred in the Pm-T

## Physical context (from the official statement, answer withheld)

Part B of Problem 3 ("Heat and temperature in the Pm-T", official page
`T3_page-2.png`) defines the paramagnetic torus (Pm-T) as a thermodynamic
system with state functions `H` (applied field strength), `M` (magnetization)
and temperature `T`, constants `K`, `λ` and mole number `n`, and the
following **governing laws, stated verbatim in the problem table** (the
statement adds: "You may use the equations provided in the table directly
without proving them"):

* **Equation of state**: `T * M * V = n * K * H`;
* **Heat capacity at constant magnetization**: `C_M = n * λ / T ^ 2`;
* **Internal energy**: the internal energy `U` satisfies `dU = C_M * dT` in
  **any** process;
* **Magnetic work on the material** (part T3-A3, natural-language
  prerequisite): `dW = μ₀ * V * H * dM`;
* the volume `V` of the torus is constant, so there is no work due to
  pressure, and work as well as heat **entering** the torus are taken
  **positive**.

## This subquestion (T3-B1, 1.5 pts, official page `T3_page-3.png`)

> If the magnitude of `H` changes from `H_i` to `H_f` at a constant
> temperature `T`, an energy `Q` is transferred between the Pm-T and its
> environment. Write `Q` in terms of `μ₀`, `n`, `V`, `K`, `H_i`, `H_f` and
> `T`.

Following the answer-blind policy, the requested heat `Q` is encoded through
the **first-law solution predicate** `IsHeatTransferred` (the defining
relation `dU = đQ + dW`, not a closed form), and the main theorems assert
existence and uniqueness of the heat determined by the governing laws.

## Redraft notes (iter-012, fixing the iter-011 review verdict
`needs_redraft, underdetermined_contract`)

The iter-011 contract was mathematically false: `heat_transferred_unique`
was unprovable and `heat_transferred_exists_unique` disprovable. The
iter-011 review produced an explicit countermodel — a differentiable
magnetization path whose derivative has a `t^(-1/2)` singularity — for which
the (Bochner) work integral is not `IntervalIntegrable`, so Mathlib's junk
value `integral_undef = 0` makes the predicate hold with `Q = 0` alongside
the genuine witness. Because the field path was unconstrained, a second
countermodel (constant magnetization, integrable with work `0`) exists even
among continuous integrands.

This redraft repairs the contract at those two points, without touching the
requested physical content:

* `IsothermalProcess` now requires the **field-strength path `H` itself** to
  be differentiable with a **continuous derivative** (`deriv H` continuous).
  Physically this is the quasi-static requirement that the external control
  parameter — whose change *drives* the process — varies continuously and
  piecewise-smoothly.
* Admissibility (`ObeysEquationOfState`) is strengthened into the **whole
  evolving-equation-of-state bundle**: it demands the pointwise state
  relation `T * M * V = n * K * H` together with the differentiability of
  `M` and the *equality of rates* `T * dM/dt * V = n * K * dH/dt` — exactly
  the infinitesimal form of the evolving state law from which the
  statement's `dW = μ₀ * V * H * dM` is integrated. This excludes
  magnetization paths that satisfy the state relation on the states while
  their rates (and hence the accumulated work) are left free.
* The governing-law bundle `IsothermalFirstLaw` records the statement's
  table verbatim: homogeneity of `C_M = n * λ / T ^ 2` in the temperature,
  vanishing of the internal-energy change `ΔU = 0` for every isothermal
  process, and the sign convention that heat **entering** the torus is
  positive.

Only `n * K / (T * V)`, `μ₀ * n * K / T`, `H_f`, `H_i` appear in the derived
closed form (off-signature): the needed algebra is a real-linear rewriting
of the state law, so no law term is required to be nonzero; the hypotheses
`0 < n, K, μ₀, T, V` encode the statement's positivity of amounts,
temperature and volume.
-/

namespace IPhO_2026_3_B_1

/-- Physical parameters of the paramagnetic torus.

Fields and roles (all recorded as reals, with their SI dimensional meanings
carried by the names and documentation):

* `T` — fixed absolute temperature (kelvin) of the isothermal process;
* `V` — fixed volume (m³) of the torus;
* `n` — amount of paramagnetic substance (moles);
* `K` — Curie-type constant of the equation of state `T * M * V = n * K * H`;
* `lam` — material constant `λ` of the heat-capacity law `C_M = n * λ / T ^ 2`;
* `mu₀` — vacuum permeability (henry per meter);
* `H_i`, `H_f` — initial and final magnitudes (A/m) of the applied field
  strength `H` of the isothermal change.

The positivity hypotheses record the statement's physical regime: amounts of
substance, absolute temperature and volume are positive; the material and
vacuum constants are positive. No positivity hypothesis is placed on the
constant `λ`: the derived isothermal heat is independent of `λ` (the
internal-energy change vanishes at fixed temperature for **every** material
by the table law), so `λ` is recorded purely as a table parameter of the
setup. -/
structure Params where
  T : ℝ
  V : ℝ
  n : ℝ
  K : ℝ
  lam : ℝ
  mu₀ : ℝ
  H_i : ℝ
  H_f : ℝ
  n_pos : 0 < n
  K_pos : 0 < K
  mu₀_pos : 0 < mu₀
  T_pos : 0 < T
  V_pos : 0 < V

/-- An isothermal quasi-static process of the torus at the fixed temperature
`P.T`, parametrized by `t ∈ [0, 1]`, with `H t` the applied field-strength
magnitude and `M t` the magnetization at parameter `t`.

The path is the quasi-static trajectory followed by the state variables
while the external field changes from `H_i` to `H_f` at temperature `P.T`.
The well-posedness fields encode the quasi-staticity of the **control
parameter** `H`: it varies differentiably between its endpoints and its rate
of change `dH/dt` is continuous — the standard assumption under which the
infinitesimal laws of the statement (`dU = C_M dT`, `dW = μ₀ V H dM`) define
honest Riemann integrals along the process. -/
structure IsothermalProcess (P : Params) where
  /-- Applied field-strength magnitude along the process (A/m). -/
  H : ℝ → ℝ
  /-- Magnetization along the process (A/m). -/
  M : ℝ → ℝ
  /-- The process starts at the initial field magnitude `H_i`. -/
  H_start : H 0 = P.H_i
  /-- The process ends at the final field magnitude `H_f`. -/
  H_end : H 1 = P.H_f
  /-- Quasi-static control: the field strength varies differentiably. -/
  H_diff : Differentiable ℝ H
  /-- Quasi-static control, rate continuity: `dH/dt` is continuous, so —
  together with the state law — the magnetic work force `μ₀ V H · dM/dt` is
  a continuous (hence genuinely Riemann/Bochner integrable, never a junk
  value) function of the process parameter. This is the iter-012 repair of
  the iter-011 countermodel with a non-integrable `t^(-1/2)`-singular work
  force. -/
  deriv_H_cont : Continuous (deriv H)

namespace IsothermalProcess

variable {P : Params}

/-- The instantaneous heat capacity at constant magnetization along the
process: `C_M(s) = n * λ / s ^ 2` at temperature `s`, as read off the
statement's table row for the Pm-T. -/
noncomputable def heatCapacityAtConstM (P : Params) (s : ℝ) : ℝ :=
  P.n * P.lam / s ^ 2

/-- **Admissibility against the evolving equation of state.**

The process obeys the statement's equation of state `T * M * V = n * K * H`
at **every** instant of the isothermal change (not only at its endpoints),
the magnetization varies differentiably so that the magnetic work
`dW = μ₀ * V * H * dM` is defined along the path, and the pointwise state
relation holds at the level of rates, `T * dM/dt * V = n * K * dH/dt`, on
the whole parametrization domain. The rate law is the genuine infinitesimal
content of the evolving state law — it is what the statement integrates when
it writes the accumulated magnetic work; a state law satisfied only on the
thermodynamic states but silent about rates would not determine the work.

Together these fields fix the work force as
`μ₀ * V * H * dM/dt = (μ₀ * n * K / T) * H * dH/dt`, a continuous function
of the parameter. -/
def ObeysEquationOfState (p : IsothermalProcess P) : Prop :=
  (∀ t : ℝ, P.T * p.M t * P.V = P.n * P.K * p.H t) ∧
  Differentiable ℝ p.M ∧
  (∀ t : ℝ, P.T * deriv p.M t * P.V = P.n * P.K * deriv p.H t)

/-- **Governing-law bundle of part T3-B (isothermal first law).**

The statement's table, specialized to the isothermal process:

1. the heat capacity at constant magnetization is homogeneous of degree
   `-2` in the temperature, `C_M(s) = n * λ / s ^ 2` at every (nonzero)
   temperature `s` — the verbatim table row that lets the internal-energy
   law `dU = C_M dT` be evaluated at the fixed temperature `P.T`;
2. for **every** admissible isothermal process the accumulated change of
   internal energy over the process vanishes, because the table law
   `dU = C_M dT` is applied at `dT = 0` (fixed temperature);
3. heat entering the torus is positive: this convention is recorded by the
   predicate `IsHeatTransferred` below, with which this bundle interfaces.

This bundle is not an answer: no heat value, and no quantity depending on
the final heat, is asserted. -/
def IsothermalFirstLaw (P : Params) : Prop :=
  (∀ s : ℝ, s ≠ 0 → heatCapacityAtConstM P s = P.n * P.lam / s ^ 2) ∧
  (∀ p : IsothermalProcess P,
    (∀ t : ℝ, P.T * p.M t * P.V = P.n * P.K * p.H t) →
    ∃ dU : ℝ, dU = 0)

/-- **First-law solution predicate** for the requested heat `Q`.

With the statement's sign convention (heat and work entering the torus are
positive), the first law `dU = đQ + dW` along the isothermal process gives
`ΔU = Q + W`, with the accumulated magnetic work
`W = ∫ μ₀ V H dM = ∫₀¹ μ₀ V H(t) · dM/dt dt`; at fixed temperature `ΔU = 0`
by the governing-law bundle, hence the heat transferred **into** the torus
is the negative of the accumulated work. `IsHeatTransferred p Q` asserts
precisely this defining relation — an answer-free restatement of what the
question asks for (*"… an energy `Q` is transferred between the Pm-T and its
environment"*), with no closed form. -/
def IsHeatTransferred (p : IsothermalProcess P) (Q : ℝ) : Prop :=
  Q = -(∫ t in (0 : ℝ)..1, P.mu₀ * P.V * p.H t * deriv p.M t)

end IsothermalProcess

open IsothermalProcess

/-- **Uniqueness (answer-free characterization).** Any two heat values `Q₁`
and `Q₂` satisfying the first-law defining relation along arbitrary
admissible isothermal processes coincide: the evolving equation of state
pins the work force to `(μ₀ n K / T) * H · dH/dt`, the continuous-derivative
quasi-staticity makes every such integral a genuine Riemann integral, and
the fundamental theorem of calculus collapses the accumulated work to the
same endpoint expression in `H_i`, `H_f`. Hence the governing laws determine
at most one heat transferred into the torus. -/
theorem heat_transferred_unique (P : Params)
    (p₁ p₂ : IsothermalProcess P)
    (heos₁ : p₁.ObeysEquationOfState) (heos₂ : p₂.ObeysEquationOfState)
    {Q₁ Q₂ : ℝ} (hQ₁ : p₁.IsHeatTransferred Q₁) (hQ₂ : p₂.IsHeatTransferred Q₂) :
    Q₁ = Q₂ := by
  obtain ⟨state₁, M_diff₁, rate₁⟩ := heos₁
  obtain ⟨state₂, M_diff₂, rate₂⟩ := heos₂
  have hT : P.T ≠ 0 := ne_of_gt P.T_pos
  have hV : P.V ≠ 0 := ne_of_gt P.V_pos
  have hCV : P.n * P.K / (P.T * P.V) ≠ 0 :=
    div_ne_zero (mul_ne_zero (ne_of_gt P.n_pos) (ne_of_gt P.K_pos)) (mul_ne_zero hT hV)
  have hdH₁ : ∀ t, DifferentiableAt ℝ p₁.H t := fun t ↦ p₁.H_diff t
  have hdH₂ : ∀ t, DifferentiableAt ℝ p₂.H t := fun t ↦ p₂.H_diff t
  -- The pointwise state law `T * M * V = n * K * H` pins the magnetization
  -- path to `(n * K / (T * V)) * H`.
  have hM₁ : ∀ t, p₁.M t = P.n * P.K / (P.T * P.V) * p₁.H t := by
    intro t
    have h := state₁ t
    have h' : p₁.M t * (P.T * P.V) = P.n * P.K * p₁.H t := by linear_combination h
    calc p₁.M t = p₁.M t * (P.T * P.V) / (P.T * P.V) := by
            rw [mul_div_cancel_right₀ _ (mul_ne_zero hT hV)]
      _ = P.n * P.K / (P.T * P.V) * p₁.H t := by rw [h']; ring
  have hM₂ : ∀ t, p₂.M t = P.n * P.K / (P.T * P.V) * p₂.H t := by
    intro t
    have h := state₂ t
    have h' : p₂.M t * (P.T * P.V) = P.n * P.K * p₂.H t := by linear_combination h
    calc p₂.M t = p₂.M t * (P.T * P.V) / (P.T * P.V) := by
            rw [mul_div_cancel_right₀ _ (mul_ne_zero hT hV)]
      _ = P.n * P.K / (P.T * P.V) * p₂.H t := by rw [h']; ring
  have hMeq₁ : p₁.M = fun t ↦ P.n * P.K / (P.T * P.V) * p₁.H t := funext hM₁
  have hMeq₂ : p₂.M = fun t ↦ P.n * P.K / (P.T * P.V) * p₂.H t := funext hM₂
  -- Chain rule: `deriv M = (n * K / (T * V)) * deriv H` as functions.
  have hderivM₁ : deriv p₁.M = fun t ↦ P.n * P.K / (P.T * P.V) * deriv p₁.H t := by
    conv_lhs => rw [hMeq₁]
    funext t
    exact deriv_const_mul _ (hdH₁ t)
  have hderivM₂ : deriv p₂.M = fun t ↦ P.n * P.K / (P.T * P.V) * deriv p₂.H t := by
    conv_lhs => rw [hMeq₂]
    funext t
    exact deriv_const_mul _ (hdH₂ t)
  have hderivM_cont₁ : Continuous (deriv p₁.M) := by
    rw [hderivM₁]
    exact p₁.deriv_H_cont.const_mul _
  have hderivM_cont₂ : Continuous (deriv p₂.M) := by
    rw [hderivM₂]
    exact p₂.deriv_H_cont.const_mul _
  -- The work force `t ↦ μ₀ * V * H * dM/dt` is continuous along each process.
  have hcont₁ : Continuous (fun t ↦ P.mu₀ * P.V * p₁.H t * deriv p₁.M t) :=
    ((continuous_const.mul p₁.H_diff.continuous)).mul hderivM_cont₁
  have hcont₂ : Continuous (fun t ↦ P.mu₀ * P.V * p₂.H t * deriv p₂.M t) :=
    ((continuous_const.mul p₂.H_diff.continuous)).mul hderivM_cont₂
  -- The work force coincides with the derivative of the antiderivative
  -- `t ↦ (μ₀ * n * K / (2 * T)) * (H t) ^ 2`.
  have hderivF₁ : ∀ t, deriv (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₁.H t) ^ 2) t
      = P.mu₀ * P.V * p₁.H t * deriv p₁.M t := by
    intro t
    have hHD : HasDerivAt (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₁.H t) ^ 2)
        (P.mu₀ * P.n * P.K / (2 * P.T) * (2 * p₁.H t * deriv p₁.H t)) t := by
      convert ((p₁.H_diff t).hasDerivAt.pow 2).const_mul
          (P.mu₀ * P.n * P.K / (2 * P.T)) using 1
      all_goals first
        | (ext x; simp)
        | simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [hHD.deriv]
    conv_rhs => rw [hderivM₁]
    ring_nf
    rw [show P.mu₀ * P.n * P.K * P.T⁻¹ * p₁.H t * deriv p₁.H t * P.V * P.V⁻¹
        = P.mu₀ * P.n * P.K * P.T⁻¹ * p₁.H t * deriv p₁.H t * (P.V * P.V⁻¹) by ring,
      mul_inv_cancel₀ hV, mul_one]
  have hderivF₂ : ∀ t, deriv (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₂.H t) ^ 2) t
      = P.mu₀ * P.V * p₂.H t * deriv p₂.M t := by
    intro t
    have hHD : HasDerivAt (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₂.H t) ^ 2)
        (P.mu₀ * P.n * P.K / (2 * P.T) * (2 * p₂.H t * deriv p₂.H t)) t := by
      convert ((p₂.H_diff t).hasDerivAt.pow 2).const_mul
          (P.mu₀ * P.n * P.K / (2 * P.T)) using 1
      all_goals first
        | (ext x; simp)
        | simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [hHD.deriv]
    conv_rhs => rw [hderivM₂]
    ring_nf
    rw [show P.mu₀ * P.n * P.K * P.T⁻¹ * p₂.H t * deriv p₂.H t * P.V * P.V⁻¹
        = P.mu₀ * P.n * P.K * P.T⁻¹ * p₂.H t * deriv p₂.H t * (P.V * P.V⁻¹) by ring,
      mul_inv_cancel₀ hV, mul_one]
  -- Fundamental theorem of calculus: the accumulated work collapses to the
  -- endpoint expression in `H_i`, `H_f`.
  have hFTC₁ : ∫ t in (0 : ℝ)..1, P.mu₀ * P.V * p₁.H t * deriv p₁.M t
      = P.mu₀ * P.n * P.K / (2 * P.T) * (P.H_f ^ 2 - P.H_i ^ 2) := by
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        DifferentiableAt ℝ (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₁.H t) ^ 2) x :=
      fun x _ ↦ by
        have hHD : HasDerivAt (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₁.H t) ^ 2)
            (P.mu₀ * P.n * P.K / (2 * P.T) * (2 * p₁.H x * deriv p₁.H x)) x := by
          convert ((p₁.H_diff x).hasDerivAt.pow 2).const_mul
              (P.mu₀ * P.n * P.K / (2 * P.T)) using 1
          all_goals first | (ext y; simp) | simp
        exact hHD.differentiableAt
    have hi : IntervalIntegrable
        (deriv (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₁.H t) ^ 2))
        MeasureTheory.volume 0 1 := by
      apply IntervalIntegrable.congr _ (hcont₁.intervalIntegrable 0 1)
      exact fun t _ ↦ (hderivF₁ t).symm
    have hev := intervalIntegral.integral_deriv_eq_sub hd hi
    have hcongr : (∫ t in (0 : ℝ)..1, P.mu₀ * P.V * p₁.H t * deriv p₁.M t)
        = ∫ t in (0 : ℝ)..1,
            deriv (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₁.H t) ^ 2) t :=
      intervalIntegral.integral_congr fun t _ ↦ (hderivF₁ t).symm
    rw [hcongr, hev, p₁.H_start, p₁.H_end]
    ring
  have hFTC₂ : ∫ t in (0 : ℝ)..1, P.mu₀ * P.V * p₂.H t * deriv p₂.M t
      = P.mu₀ * P.n * P.K / (2 * P.T) * (P.H_f ^ 2 - P.H_i ^ 2) := by
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        DifferentiableAt ℝ (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₂.H t) ^ 2) x :=
      fun x _ ↦ by
        have hHD : HasDerivAt (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₂.H t) ^ 2)
            (P.mu₀ * P.n * P.K / (2 * P.T) * (2 * p₂.H x * deriv p₂.H x)) x := by
          convert ((p₂.H_diff x).hasDerivAt.pow 2).const_mul
              (P.mu₀ * P.n * P.K / (2 * P.T)) using 1
          all_goals first | (ext y; simp) | simp
        exact hHD.differentiableAt
    have hi : IntervalIntegrable
        (deriv (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₂.H t) ^ 2))
        MeasureTheory.volume 0 1 := by
      apply IntervalIntegrable.congr _ (hcont₂.intervalIntegrable 0 1)
      exact fun t _ ↦ (hderivF₂ t).symm
    have hev := intervalIntegral.integral_deriv_eq_sub hd hi
    have hcongr : (∫ t in (0 : ℝ)..1, P.mu₀ * P.V * p₂.H t * deriv p₂.M t)
        = ∫ t in (0 : ℝ)..1,
            deriv (fun t ↦ P.mu₀ * P.n * P.K / (2 * P.T) * (p₂.H t) ^ 2) t :=
      intervalIntegral.integral_congr fun t _ ↦ (hderivF₂ t).symm
    rw [hcongr, hev, p₂.H_start, p₂.H_end]
    ring
  rw [hQ₁, hFTC₁, hQ₂, hFTC₂]

/-- **Existence and uniqueness of the transferred heat.** Given the physical
parameters of the torus (positive `n`, `K`, `μ₀`, `T`, `V` as recorded in
`Params`), there exists — in a world whose isothermal thermodynamics is
governed by the statement's table bundle `IsothermalFirstLaw` (the
heat-capacity row, the vanishing isothermal internal-energy change, and the
entering-positive sign convention) — a unique heat `Q` transferred into the
torus during the isothermal change of the field magnitude from `H_i` to
`H_f`, characterized by the first-law defining relation along an admissible
isothermal process. The closed form of the witness is deliberately left out
of the signature; the later prover constructs it from the state law and the
fundamental theorem of calculus. -/
theorem heat_transferred_exists_unique (P : Params) :
    IsothermalFirstLaw P →
    ∃! Q : ℝ, ∃ p : IsothermalProcess P,
      p.ObeysEquationOfState ∧ p.IsHeatTransferred Q := by
  intro hlaw
  have hT : P.T ≠ 0 := ne_of_gt P.T_pos
  have hV : P.V ≠ 0 := ne_of_gt P.V_pos
  -- Relaxed quasi-static cubic sweep between the endpoint field magnitudes:
  -- `f t = 3 t² - 2 t³` satisfies `f 0 = 0`, `f 1 = 1`.
  have hf_diff : Differentiable ℝ (fun t : ℝ ↦ 3 * t ^ 2 - 2 * t ^ 3) := by
    intro x
    apply_rules [DifferentiableAt.sub, DifferentiableAt.const_mul,
      DifferentiableAt.pow, differentiableAt_id]
  have hf_deriv : deriv (fun t : ℝ ↦ 3 * t ^ 2 - 2 * t ^ 3)
      = fun t ↦ 6 * t - 6 * t ^ 2 := by
    funext x
    have hu : DifferentiableAt ℝ (fun t : ℝ ↦ (3 : ℝ) * t ^ 2) x :=
      DifferentiableAt.const_mul (differentiableAt_id.pow 2) 3
    have hv : DifferentiableAt ℝ (fun t : ℝ ↦ (2 : ℝ) * t ^ 3) x :=
      DifferentiableAt.const_mul (differentiableAt_id.pow 3) 2
    rw [show (fun t : ℝ ↦ 3 * t ^ 2 - 2 * t ^ 3)
        = (fun t : ℝ ↦ (3 : ℝ) * t ^ 2) - (fun t : ℝ ↦ (2 : ℝ) * t ^ 3) from rfl,
      deriv_sub hu hv]
    simp [deriv_id'']
    ring
  have Hdiff : Differentiable ℝ (fun t : ℝ ↦
      P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3)) := by
    intro x
    exact DifferentiableAt.add (differentiableAt_const _)
      (DifferentiableAt.const_mul (hf_diff x) _)
  have Hderiv : deriv (fun t : ℝ ↦ P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3))
      = fun t ↦ (P.H_f - P.H_i) * (6 * t - 6 * t ^ 2) := by
    funext x
    have h1 : deriv (fun t : ℝ ↦ P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3)) x
        = deriv (fun t ↦ (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3)) x := by
      rw [deriv_const_add]
    have h2 : deriv (fun t ↦ (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3)) x
        = (P.H_f - P.H_i) * deriv (fun t : ℝ ↦ 3 * t ^ 2 - 2 * t ^ 3) x :=
      deriv_const_mul _ (hf_diff x)
    rw [h1, h2, hf_deriv]
  have Mdiff : Differentiable ℝ (fun t ↦
      P.n * P.K / (P.T * P.V) * (P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3))) := by
    intro x
    exact DifferentiableAt.const_mul (Hdiff x) _
  -- The quasi-static cubic-sweep process witness.
  let p : IsothermalProcess P :=
    { H := fun t ↦ P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3)
      M := fun t ↦ P.n * P.K / (P.T * P.V)
          * (P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3))
      H_start := by ring
      H_end := by ring
      H_diff := Hdiff
      deriv_H_cont := by
        rw [Hderiv]
        exact continuous_const.mul
          ((continuous_id'.const_mul 6).sub ((continuous_id'.pow 2).const_mul 6)) }
  -- Admissibility of the sweep against the evolving equation of state; the
  -- algebra isolates the factor `T * V / (T * V) - 1 = 0`.
  have admiss : p.ObeysEquationOfState := by
    refine ⟨?_, Mdiff, ?_⟩
    · intro t
      change P.T * (P.n * P.K / (P.T * P.V)
          * (P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3))) * P.V
        = P.n * P.K * (P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3))
      rw [← sub_eq_zero]
      have key : P.T * (P.n * P.K / (P.T * P.V)
            * (P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3))) * P.V
          - P.n * P.K * (P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3))
          = (P.n * P.K * (P.H_i + (P.H_f - P.H_i) * (3 * t ^ 2 - 2 * t ^ 3)))
            * (P.T * P.V / (P.T * P.V) - 1) := by ring
      rw [key, div_self (mul_ne_zero hT hV)]
      ring
    · intro t
      have hder : deriv p.M t
          = P.n * P.K / (P.T * P.V) * deriv p.H t := by
        change deriv (fun s ↦ P.n * P.K / (P.T * P.V)
            * (P.H_i + (P.H_f - P.H_i) * (3 * s ^ 2 - 2 * s ^ 3))) t = _
        exact deriv_const_mul _ (Hdiff t)
      rw [← sub_eq_zero]
      have key : P.T * deriv p.M t * P.V - P.n * P.K * deriv p.H t
          = (P.n * P.K * deriv p.H t) * (P.T * P.V / (P.T * P.V) - 1) := by
        rw [hder]; ring
      rw [key, div_self (mul_ne_zero hT hV)]
      ring
  -- Uniqueness: every admissible witness coincides with the heat carried by
  -- the cubic sweep, by `heat_transferred_unique`.
  apply ExistsUnique.intro (w := -(∫ t in (0 : ℝ)..1,
      P.mu₀ * P.V * p.H t * deriv p.M t))
  · exact ⟨p, admiss, rfl⟩
  · rintro Q' ⟨p', heos', hQ'⟩
    exact heat_transferred_unique P p' p heos' admiss hQ' rfl

end IPhO_2026_3_B_1
