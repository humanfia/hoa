import Mathlib

/-!
# IPhO 2026, Problem 3 (Paramagnetic Torus), Part B.2 — Answer-blind formalization

**Physical setup (Pm-T, "paramagnetic torus").**

The torus is a paramagnetic material whose thermodynamic state is described by
the state functions `H` (applied magnetic field magnitude), `M` (magnitude of the
magnetization) and the temperature `T`. The constants of the material are `K`,
`λ` and the number of moles `n`; the volume `V` is fixed, so there is no
pressure–volume work. Work and heat *entering* the torus are taken to be positive.

The governing laws are (see the official statement, part T3-B):

* **Equation of state:** `T * M * V = n * K * H`.
* **Heat capacity at constant magnetization:** `C_M = n * λ / T ^ 2`.
* **Internal energy:** `dU = C_M dT` in any process.
* **Magnetic work on the material (from part A.3):** `dW = μ₀ * V * H * dM`.

**Current subquestion (T3-B2).** The field is changed *adiabatically* from `H_i`
to `H_f`, starting at temperature `T_i`. We are to determine the temperature
change `ΔT = T_f - T_i`.

Since the official answer is withheld, we do **not** place a closed-form value of
`ΔT` in the theorem signature. Instead we define a physically meaningful solution
predicate `IsAdiabaticFinalTemperature` capturing the governing laws and the
boundary / initial conditions, and we state that the final temperature `T_f` is
*uniquely determined* by the data. The concrete witness is for the later prover.

The adiabatic condition (no heat exchange, `đQ = 0`) together with the first law
`dU = đQ + đW` and the sign convention "work entering the torus is positive" gives
`dU = đW`, i.e. `C_M dT = μ₀ * V * H * dM`. Along a quasi-static adiabat
parametrised by the applied field `H`, the pair `(T, M)` therefore obeys

  `C_M (T H) * dT/dH = μ₀ * V * H * dM/dH`,

subject to the equation of state at every point and the initial condition
`T H_i = T_i`.
-/

namespace IPhO2026

open Real

/-- The constant parameters describing the paramagnetic torus and the
adiabatic process of part T3-B2.

Dimensional roles (kept as named `ℝ` fields; Lean has no unit API in scope):

* `μ₀` — vacuum permeability.
* `V`   — (fixed) volume of the torus.
* `n`   — number of moles of the paramagnetic material.
* `K`   — material constant entering the equation of state `T * M * V = n * K * H`.
* `lam` — material constant `λ` entering the heat capacity `C_M = n * λ / T ^ 2`.
* `Hi`, `Hf` — initial and final magnitudes of the applied field `H`.
* `Ti`  — the (given) initial temperature.

All are recorded as strictly positive, as befits thermodynamic temperature,
the magnitude `H ≥ 0` of the applied field, and the positive material constants. -/
structure ParamagneticTorusData where
  μ₀ : ℝ
  V : ℝ
  n : ℝ
  K : ℝ
  lam : ℝ
  Hi : ℝ
  Hf : ℝ
  Ti : ℝ
  hμ₀ : 0 < μ₀
  hV : 0 < V
  hn : 0 < n
  hK : 0 < K
  hlam : 0 < lam
  hHi : 0 < Hi
  hHf : 0 < Hf
  hTi : 0 < Ti

namespace ParamagneticTorusData

variable (d : ParamagneticTorusData)

/-- The heat capacity at constant magnetization, `C_M = n * λ / T ^ 2`.

This is a function of the instantaneous temperature `T` (it depends on `T`
through `T ^ 2`), evaluated while `M` is held fixed. -/
noncomputable def heatCapacityM (T : ℝ) : ℝ :=
  d.n * d.lam / T ^ 2

/--
A *quasi-static adiabatic path* of the paramagnetic torus, parametrised by the
applied field magnitude `H`.

It consists of two functions `T` and `M` of `H` (the temperature and the
magnetization as the field is swept), which must:

1. obey the equation of state `T H * M H * V = n * K * H` at every field value;
2. obey the adiabatic first-law differential relation
   `C_M (T H) * dT/dH = μ₀ * V * H * dM/dH`;
3. keep the temperature strictly positive (thermodynamic temperature);
4. start from the prescribed initial temperature `T Hi = Ti`.

Both `T` and `M` are required differentiable, reflecting the quasi-static
(reversible) character of the change.
-/
structure AdiabaticPath (d : ParamagneticTorusData) where
  T : ℝ → ℝ
  M : ℝ → ℝ
  Tdiff : Differentiable ℝ T
  Mdiff : Differentiable ℝ M
  Tpos : ∀ H, 0 < T H
  eqOfState : ∀ H, T H * M H * d.V = d.n * d.K * H
  adiabatic :
    ∀ H, d.heatCapacityM (T H) * deriv T H = d.μ₀ * d.V * H * deriv M H
  initial : T d.Hi = d.Ti

/--
**Solution predicate (answer-free).**

`IsAdiabaticFinalTemperature d Tf` asserts that the real number `Tf` is the
final temperature reached after the adiabatic change `H_i → H_f` starting at
`T_i`, i.e. that there *exists* a quasi-static adiabatic path of the torus whose
temperature at the final field `Hf` equals `Tf`.

This captures the full content of the question (governing laws + initial
condition + endpoint) without revealing the closed-form value of `Tf` or of
`ΔT = Tf - Ti`.
-/
def IsAdiabaticFinalTemperature (d : ParamagneticTorusData) (Tf : ℝ) : Prop :=
  ∃ p : d.AdiabaticPath, p.T d.Hf = Tf

/--
The temperature change `ΔT = T_f - T_i` determined by a candidate final
temperature `Tf`.
-/
noncomputable def deltaT (d : ParamagneticTorusData) (Tf : ℝ) : ℝ :=
  Tf - d.Ti

section AdiabaticWitness

/-! ### The explicit adiabatic path (for the prover).

Substituting the magnetization forced by the equation of state,
`M H = n * K * H / (V * T H)`, into the adiabatic first-law relation
`C_M (T H) * dT/dH = μ₀ * V * H * dM/dH` and expanding the quotient derivative
gives, with `TB H = λ + μ₀ * K * H ^ 2`, the separable relation

  `TB H * (T H)' = μ₀ * K * H * T H`.

Hence the quantity `Φ H = (T H) ^ 2 / TB H` is constant along any adiabatic
path: `Φ' = (2 * T * T' * TB − T ^ 2 * TB') / TB ^ 2 = 0`.  From the initial
condition `Φ = T i ^ 2 / TB H i` everywhere, and since the temperature is
positive this determines `T` uniquely; the equation of state then determines
`M`.  The explicit path is

  `Tw H = T i * √(TB H) / √(TB H i)`,
  `Mw H = n * K * √(TB H i) * H / (T i * V * √(TB H)) = n * K * H / (V * Tw H)`. -/

/-- The positive material factor `TB H = λ + μ₀ * K * H ^ 2` appearing in the
integrated adiabatic relation `(T H) ^ 2 / TB H = const` along the path. -/
noncomputable def TB (d : ParamagneticTorusData) (H : ℝ) : ℝ :=
  d.lam + d.μ₀ * d.K * H ^ 2

/-- The explicit temperature profile
`Tw H = T i * √(TB H) / √(TB H i)` of the adiabatic path. -/
noncomputable def Tw (d : ParamagneticTorusData) (H : ℝ) : ℝ :=
  d.Ti * √(d.TB H) / √(d.TB d.Hi)

/-- The explicit magnetization profile
`Mw H = n * K * √(TB H i) * H / (T i * V * √(TB H))`, equal to
`n * K * H / (V * Tw H)`, the value forced by the equation of state. -/
noncomputable def Mw (d : ParamagneticTorusData) (H : ℝ) : ℝ :=
  d.n * d.K * √(d.TB d.Hi) * H / (d.Ti * d.V * √(d.TB H))

/-- The derivative profile of `Tw`:
`Tw' = T i * μ₀ * K * H / (√(TB H) * √(TB H i))`. -/
noncomputable def dTw (d : ParamagneticTorusData) (H : ℝ) : ℝ :=
  d.Ti * d.μ₀ * d.K * H / (√(d.TB H) * √(d.TB d.Hi))

/-- The derivative profile of `Mw`, from the quotient rule applied to
`n * K * √(TB H i) * H / (T i * V * √(TB H))`. -/
noncomputable def dMw (d : ParamagneticTorusData) (H : ℝ) : ℝ :=
  d.n * d.K * √(d.TB d.Hi) * d.lam / (d.Ti * d.V * √(d.TB H) * d.TB H)

variable (d : ParamagneticTorusData)

lemma TB_pos (H : ℝ) : 0 < d.TB H := by
  have h1 : 0 < d.μ₀ * d.K := mul_pos d.hμ₀ d.hK
  have h2 : 0 ≤ d.μ₀ * d.K * H ^ 2 := mul_nonneg h1.le (sq_nonneg H)
  unfold TB
  linarith [d.hlam]

lemma TB_ne_zero (H : ℝ) : d.TB H ≠ 0 := ne_of_gt (d.TB_pos H)

lemma sqrt_TB_pos (H : ℝ) : 0 < √(d.TB H) := Real.sqrt_pos_of_pos (d.TB_pos H)

lemma sqrt_TB_ne_zero (H : ℝ) : √(d.TB H) ≠ 0 := ne_of_gt (d.sqrt_TB_pos H)

lemma Tw_pos (H : ℝ) : 0 < d.Tw H := by
  unfold Tw
  exact div_pos (mul_pos d.hTi (d.sqrt_TB_pos H)) (d.sqrt_TB_pos d.Hi)

lemma Tw_ne_zero (H : ℝ) : d.Tw H ≠ 0 := ne_of_gt (d.Tw_pos H)

lemma hasDerivAt_TB (H : ℝ) : HasDerivAt d.TB (2 * d.μ₀ * d.K * H) H := by
  have h0 : HasDerivAt (fun x : ℝ => x ^ 2) (↑(2 : ℕ) * H ^ (2 - 1)) H :=
    hasDerivAt_pow 2 H
  have h1 := h0.const_mul (d.μ₀ * d.K)
  have h2 := h1.const_add d.lam
  have e : d.TB = fun x => d.lam + d.μ₀ * d.K * x ^ 2 := rfl
  rw [e]
  exact h2.congr_deriv (by ring)

lemma hasDerivAt_sqrt_TB (H : ℝ) :
    HasDerivAt (fun x => √(d.TB x)) (d.μ₀ * d.K * H / √(d.TB H)) H := by
  have h := (d.hasDerivAt_TB H).sqrt (d.TB_ne_zero H)
  exact h.congr_deriv (by field_simp)

lemma hasDerivAt_Tw (H : ℝ) : HasDerivAt d.Tw (d.dTw H) H := by
  have e : d.Tw = fun x => (d.Ti / √(d.TB d.Hi)) * √(d.TB x) := by
    funext x
    unfold Tw
    rw [div_mul_eq_mul_div, mul_div_assoc]
  have h := (d.hasDerivAt_sqrt_TB H).const_mul (d.Ti / √(d.TB d.Hi))
  rw [e]
  unfold dTw
  exact h.congr_deriv (by field_simp)

lemma hasDerivAt_Mw (H : ℝ) : HasDerivAt d.Mw (d.dMw H) H := by
  set cM : ℝ := d.n * d.K * √(d.TB d.Hi) / (d.Ti * d.V) with hcM
  have hnum : HasDerivAt (fun x : ℝ => cM * x) cM H :=
    ((hasDerivAt_id H).const_mul cM |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => congrArg (cM * ·) (id_eq y))).congr_deriv
      (mul_one cM)
  have hden := d.hasDerivAt_sqrt_TB H
  have efunc : d.Mw = fun x => (cM * x) / √(d.TB x) := by
    funext x
    unfold Mw
    rw [hcM]
    have hTi : d.Ti ≠ 0 := ne_of_gt d.hTi
    have hV : d.V ≠ 0 := ne_of_gt d.hV
    have eH : √(d.TB x) ≠ 0 := d.sqrt_TB_ne_zero x
    field_simp
  rw [efunc]
  have hdiv := hnum.div hden (d.sqrt_TB_ne_zero H)
  refine hdiv.congr_deriv ?_
  have e := d.sqrt_TB_ne_zero H
  have eTB := d.TB_ne_zero H
  have esq : √(d.TB H) ^ 2 = d.TB H := Real.sq_sqrt (d.TB_pos H).le
  unfold dMw
  rw [hcM]
  field_simp
  rw [esq]
  unfold TB
  ring

lemma Tw_at_Hi : d.Tw d.Hi = d.Ti := by
  unfold Tw
  rw [mul_div_cancel_right₀ d.Ti (d.sqrt_TB_ne_zero d.Hi)]

lemma eqOfState_witness (H : ℝ) : d.Tw H * d.Mw H * d.V = d.n * d.K * H := by
  have hTi : d.Ti ≠ 0 := ne_of_gt d.hTi
  have hV : d.V ≠ 0 := ne_of_gt d.hV
  have eH : √(d.TB H) ≠ 0 := d.sqrt_TB_ne_zero H
  have eHi : √(d.TB d.Hi) ≠ 0 := d.sqrt_TB_ne_zero d.Hi
  unfold Tw Mw
  field_simp

lemma differentiable_Tw : Differentiable ℝ d.Tw :=
  fun H => (d.hasDerivAt_Tw H).differentiableAt

lemma differentiable_Mw : Differentiable ℝ d.Mw :=
  fun H => (d.hasDerivAt_Mw H).differentiableAt

lemma adiabatic_witness (H : ℝ) :
    d.heatCapacityM (d.Tw H) * deriv d.Tw H = d.μ₀ * d.V * H * deriv d.Mw H := by
  rw [(d.hasDerivAt_Tw H).deriv, (d.hasDerivAt_Mw H).deriv]
  have hn : d.n ≠ 0 := ne_of_gt d.hn
  have hV : d.V ≠ 0 := ne_of_gt d.hV
  have hTi : d.Ti ≠ 0 := ne_of_gt d.hTi
  have eH : √(d.TB H) ≠ 0 := d.sqrt_TB_ne_zero H
  have eHi : √(d.TB d.Hi) ≠ 0 := d.sqrt_TB_ne_zero d.Hi
  have eB : d.TB H ≠ 0 := d.TB_ne_zero H
  have hsq : √(d.TB H) ^ 2 = d.TB H := Real.sq_sqrt (d.TB_pos H).le
  unfold heatCapacityM dTw dMw Tw
  field_simp
  rw [hsq]
  unfold TB
  ring

/-- **Uniqueness of the temperature profile.**  Along any adiabatic path `p`,
the quotient `Φ H = (p.T H) ^ 2 / (λ + μ₀ * K * H ^ 2)` has zero derivative:
differentiating the equation of state gives
`d.M = n * K / (V * p.T) - n * K * x * p.T' / (V * p.T ^ 2)`, and substituting
this into `(n λ / p.T ^ 2) * p.T' = μ₀ V x * d.M` and clearing denominators
gives `(λ + μ₀ K x ^ 2) * p.T' = μ₀ K x * p.T`, which is exactly
`d.(p.T ^ 2 / TB) = 0` after clearing the positive denominator.  Since the
invariant agrees with the witness value at `Hi`, it agrees everywhere;
positivity of the temperature then identifies the profiles. -/
lemma Tw_eq_of_path (p : d.AdiabaticPath) (H : ℝ) : p.T H = d.Tw H := by
  have hn : d.n ≠ 0 := ne_of_gt d.hn
  have hV : d.V ≠ 0 := ne_of_gt d.hV
  -- the derivative of the magnetization of `p`, from the equation of state
  have hderivM : ∀ x : ℝ, deriv p.M x =
      d.n * d.K / (d.V * p.T x) - d.n * d.K * x * deriv p.T x / (d.V * p.T x ^ 2) := by
    intro x
    have hxT : p.T x ≠ 0 := ne_of_gt (p.Tpos x)
    have hne : d.V * p.T x ≠ 0 := mul_ne_zero hV hxT
    have eMfun : p.M = fun y => d.n * d.K * y / (d.V * p.T y) := by
      funext y
      have hy := p.eqOfState y
      have h1 : d.n * d.K * y / (d.V * p.T y) = p.M y := by
        have hney : d.V * p.T y ≠ 0 := mul_ne_zero hV (ne_of_gt (p.Tpos y))
        rw [div_eq_iff hney]
        linear_combination -hy
      rw [← h1]
    have hnum : HasDerivAt (fun y : ℝ => d.n * d.K * y) (d.n * d.K) x := by
      have h := (hasDerivAt_id x).const_mul (d.n * d.K)
      exact h.congr_deriv (by ring)
    have hden : HasDerivAt (fun y : ℝ => d.V * p.T y) (d.V * deriv p.T x) x :=
      (p.Tdiff x).hasDerivAt.const_mul d.V
    have hdiv : HasDerivAt (fun y => d.n * d.K * y / (d.V * p.T y))
        ((d.n * d.K * (d.V * p.T x) - d.n * d.K * x * (d.V * deriv p.T x)) /
          (d.V * p.T x) ^ 2) x := hnum.div hden hne
    have hder : deriv p.M x =
        (d.n * d.K * (d.V * p.T x) - d.n * d.K * x * (d.V * deriv p.T x)) /
          (d.V * p.T x) ^ 2 := by rw [eMfun]; exact hdiv.deriv
    rw [hder]
    field_simp
  -- the invariant `Φ H = (p.T H) ^ 2 / TB H` has zero derivative
  have hq : ∀ x : ℝ, HasDerivAt (fun y => p.T y ^ 2 / d.TB y) 0 x := by
    intro x
    have hxT : p.T x ≠ 0 := ne_of_gt (p.Tpos x)
    have hx0 : (p.T x) ^ 2 ≠ 0 := pow_ne_zero 2 hxT
    have hnum : HasDerivAt (fun y : ℝ => p.T y ^ 2) (2 * p.T x * deriv p.T x) x := by
      have h := (p.Tdiff x).hasDerivAt.pow 2
      exact h.congr_deriv (by ring)
    have hden : HasDerivAt d.TB (2 * d.μ₀ * d.K * x) x := d.hasDerivAt_TB x
    have hdiv := hnum.div hden (d.TB_ne_zero x)
    refine hdiv.congr_deriv ?_
    have had := p.adiabatic x
    have hCM : d.heatCapacityM (p.T x) = d.n * d.lam / p.T x ^ 2 := rfl
    rw [hCM, hderivM x] at had
    -- key cancellation: `TB x * p.T' = μ₀ * K * x * p.T x`
    have key : d.TB x * deriv p.T x = d.μ₀ * d.K * x * p.T x := by
      have hstep : d.lam * deriv p.T x = d.μ₀ * d.K * x * (p.T x - x * deriv p.T x) := by
        -- multiply `had` by `(p.T x) ^ 2` and clear the field factors
        have hmul := congrArg (· * p.T x ^ 2) had
        have h1e : d.n * d.lam / p.T x ^ 2 * deriv p.T x * p.T x ^ 2 =
            d.n * d.lam * deriv p.T x := by field_simp
        have h2e : d.μ₀ * d.V * x * (d.n * d.K / (d.V * p.T x) -
                d.n * d.K * x * deriv p.T x / (d.V * p.T x ^ 2)) * p.T x ^ 2 =
            d.μ₀ * d.n * d.K * x * (p.T x - x * deriv p.T x) := by
          field_simp
        rw [h1e, h2e] at hmul
        exact mul_left_cancel₀ hn (by
          calc d.n * (d.lam * deriv p.T x) = d.n * d.lam * deriv p.T x := by ring
            _ = _ := hmul
            _ = d.n * (d.μ₀ * d.K * x * (p.T x - x * deriv p.T x)) := by ring)
      have hTBdef : d.TB x = d.lam + d.μ₀ * d.K * x ^ 2 := rfl
      rw [hTBdef]
      linear_combination hstep
    -- quotient rule: it suffices that the numerator vanishes
    refine div_eq_zero_iff.mpr (Or.inl ?_)
    linear_combination 2 * p.T x * key
  -- Φ is constant
  have hq_const : ∀ x y : ℝ, p.T x ^ 2 / d.TB x = p.T y ^ 2 / d.TB y :=
    fun x y => is_const_of_deriv_eq_zero (fun z => (hq z).differentiableAt)
      (fun z => (hq z).deriv) x y
  -- evaluate at `Hi` vs `H`
  have hqH : p.T H ^ 2 / d.TB H = d.Ti ^ 2 / d.TB d.Hi := by
    have h := hq_const H d.Hi
    rw [p.initial] at h
    exact h
  -- the witness attains the same invariant value
  have hw : d.Tw H ^ 2 / d.TB H = d.Ti ^ 2 / d.TB d.Hi := by
    have hsqH : √(d.TB H) ^ 2 = d.TB H := Real.sq_sqrt (d.TB_pos H).le
    have hsqHi : √(d.TB d.Hi) ^ 2 = d.TB d.Hi := Real.sq_sqrt (d.TB_pos d.Hi).le
    have eTwsq : d.Tw H ^ 2 = d.Ti ^ 2 * d.TB H / d.TB d.Hi := by
      unfold Tw
      rw [div_pow, mul_pow, hsqH, hsqHi]
    rw [eTwsq]
    rw [div_div]
    have hcomm1 : d.Ti ^ 2 * d.TB H = d.TB H * d.Ti ^ 2 := mul_comm _ _
    rw [hcomm1]
    rw [div_eq_div_iff (mul_ne_zero (d.TB_ne_zero d.Hi) (d.TB_ne_zero H)) (d.TB_ne_zero d.Hi)]
    ring
  -- hence the squares agree; positivity identifies the profiles
  have hsq_eq : p.T H ^ 2 = d.Tw H ^ 2 := by
    have h1 : p.T H ^ 2 / d.TB H = d.Tw H ^ 2 / d.TB H := by rw [hqH, hw]
    have hB : d.TB H ≠ 0 := d.TB_ne_zero H
    calc p.T H ^ 2 = p.T H ^ 2 / d.TB H * d.TB H := (div_mul_cancel₀ _ hB).symm
      _ = d.Tw H ^ 2 / d.TB H * d.TB H := by rw [h1]
      _ = d.Tw H ^ 2 := div_mul_cancel₀ _ hB
  have habs : |p.T H| = |d.Tw H| := (sq_eq_sq_iff_abs_eq_abs (p.T H) (d.Tw H)).mp hsq_eq
  rwa [abs_of_nonneg (p.Tpos H).le, abs_of_nonneg (d.Tw_pos H).le] at habs

/-- The explicit adiabatic path obtained from the witness profiles `Tw`, `Mw`. -/
noncomputable def witnessPath (d : ParamagneticTorusData) : d.AdiabaticPath where
  T := d.Tw
  M := d.Mw
  Tdiff := d.differentiable_Tw
  Mdiff := d.differentiable_Mw
  Tpos := d.Tw_pos
  eqOfState := d.eqOfState_witness
  adiabatic := d.adiabatic_witness
  initial := d.Tw_at_Hi

end AdiabaticWitness

/--
**Main characterization (T3-B2).**

The final temperature of the adiabatic change is *uniquely determined* by the
physical data: there exists a unique real number `Tf` that is the final
temperature of a quasi-static adiabatic path from `Hi` to `Hf` starting at `Ti`.

This is the answer-free existence/uniqueness statement; the prover may later
construct the closed-form witness for `Tf` (and hence for `ΔT = Tf - Ti`) in
terms of `μ₀, V, n, K, λ, H_i, H_f` and `T_i`.
-/
theorem adiabatic_final_temperature_unique (d : ParamagneticTorusData) :
    ∃! Tf : ℝ, d.IsAdiabaticFinalTemperature Tf := by
  refine ⟨d.Tw d.Hf, ⟨d.witnessPath, rfl⟩, ?_⟩
  intro Tf hTf
  obtain ⟨p, hp⟩ := hTf
  rw [← hp]
  exact d.Tw_eq_of_path p d.Hf

/--
Consequently the requested temperature change `ΔT = T_f - T_i` is also uniquely
determined by the data.
-/
theorem adiabatic_temperature_change_unique (d : ParamagneticTorusData) :
    ∃! Δ : ℝ, ∃ Tf : ℝ, d.IsAdiabaticFinalTemperature Tf ∧ Δ = Tf - d.Ti := by
  obtain ⟨Tf0, hTf0, huniq⟩ := d.adiabatic_final_temperature_unique
  refine ⟨Tf0 - d.Ti, ⟨Tf0, hTf0, rfl⟩, ?_⟩
  intro Δ hΔ
  obtain ⟨Tf', hTf', hΔeq⟩ := hΔ
  have hTT : Tf' = Tf0 := huniq Tf' hTf'
  rw [hΔeq, hTT]

end ParamagneticTorusData

end IPhO2026
