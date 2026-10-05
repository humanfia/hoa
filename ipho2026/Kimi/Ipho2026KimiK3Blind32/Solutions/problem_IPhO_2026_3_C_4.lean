import Mathlib

/-!
# IPhO 2026, Problem 3, Part C.4 — answer-blind formalization

Context (problem T3, part C, as printed on the official page `T3_page-4.png`):
a paramagnetic torus working substance performs a sequence of Carnot
refrigeration cycles `1 → 2 → 3 → 4 → 1` between a hot reservoir at
temperature `T_h` and a cooled body whose instantaneous temperature is `T_c`.

Subquestion T3-C4 (transcribed from the official source page): "In order to
continuously lower the temperature of a body with constant heat capacity `C_c`,
Carnot cycles are allowed to occur over time in such a way that the power `P`
transferred to the refrigerator remains constant.  It is then assumed that the
temperature `T_h` of the hot reservoir remains constant and that in each
operating cycle the temperature `T_c` of the cooled body decreases by `dT_c`,
satisfying the relation `dQ_c / dQ_h = T_c / T_h`.  If at `t = 0` we have
`T_c = T₀`, determine the time `t` that the Carnot refrigerator must operate
for the cooled body to reach a temperature `T < T₀`."

Governing laws (preserved in the definitions below):
* thermal inertia of the body: the heat extracted from the body per
  infinitesimal cycle is `dQ_c = -C_c * dT_c` (constant heat capacity);
* Carnot balance per infinitesimal cycle at constant input power `P`:
  energy conservation `dQ_h = dQ_c + P * dt` together with the stated
  per-cycle relation `dQ_c / dQ_h = T_c / T_h`;
* combining the two gives the cold-side extraction-rate law
  `-C_c * T'(t) = P * T(t) / (T_h - T(t))`, carried in `HasDerivWithinAt`
  form by `CarnotCoolingLaw` below;
* initial condition `T(0) = T₀` and terminal condition `T(t) = T`.

The governing law is posed **on the operating interval `[0, t]`**, with
one-sided (within-set) derivatives at the endpoints: nothing in the physical
setup constrains the body at negative times, and once the body has reached
`T` the requested process is over.  (An earlier redraft-target version of
this file required the derivative law on the whole of `(-∞, t)`; the
backward IVP from `(0, T₀)` reaches `T_h` at a finite negative time, where
the finite-derivative form blows up, so that contract was unsatisfiable for
any `t > 0`.  The interval carrier below resolves both flagged defects: the
law constrains the evolution exactly where the physics does, including the
terminal endpoint that the uniqueness claim quantifies over.)

The official answer is withheld: the final theorem states the *existence* of
a pair of an admissible temperature evolution and an elapsed time satisfying
the stated initial, terminal and balance constraints, together with the
*uniqueness of the elapsed time* and the *uniqueness of the temperature law
on the operating interval* (both in an answer-free form), without placing
the closed-form elapsed time in the signature.
-/

namespace IPhO_2026_3_C_4

open Filter Topology

/-- The physical parameters of the refrigeration process, collected as
dimensional data: the constant heat capacity `C_c` of the cooled body
(joule/kelvin), the constant input power `P` transferred to the refrigerator
(watt), and the constant hot-reservoir temperature `T_h` (kelvin).  All are
positive real numbers. -/
structure Params where
  /-- Constant heat capacity `C_c` of the cooled body (joule/kelvin). -/
  C_c : ℝ
  /-- Constant input power `P` supplied to the refrigerator (watt). -/
  P : ℝ
  /-- Constant hot-reservoir temperature `T_h` (kelvin). -/
  T_h : ℝ
  C_c_pos : 0 < C_c
  P_pos : 0 < P
  T_h_pos : 0 < T_h

/-- The temperature-evolution law of the cooled body over an operating
interval `[0, t]`: the body temperature stays strictly below the
hot-reservoir temperature (the cold side of a Carnot refrigerator) and
strictly positive (kelvin scale) throughout the operation, and the evolution
is differentiable on the operating interval, so that the rate `T'` is
defined everywhere the physics requires it. -/
structure IsAdmissible (par : Params) (T : ℝ → ℝ) (t : ℝ) : Prop where
  differentiable : DifferentiableOn ℝ T (Set.Icc 0 t)
  cold_side : ∀ s ∈ Set.Icc 0 t, T s < par.T_h
  temperature_pos : ∀ s ∈ Set.Icc 0 t, 0 < T s

/-- The Carnot cooling law, the governing ODE of the process, posed on the
operating interval `[0, t]`.  Over one infinitesimal cycle taking time `dt`,
energy balance for the refrigerator gives `dQ_h = dQ_c + P * dt`, the Carnot
relation stated in the problem is `dQ_c / dQ_h = T_c / T_h`, and the body's
constant heat capacity gives `dQ_c = -C_c * dT_c`.  Eliminating `dQ_h` and
`dQ_c` and writing `T` for the instantaneous cold-body temperature `T_c`
yields the extraction-rate law

`-C_c * T'(s) = P * T(s) / (T_h - T(s))`,

i.e. the heat removed from the body per unit time equals the Carnot
refrigeration power at constant input power `P`.  The derivative is required
at every instant of the whole operating interval `Set.Icc 0 t`, in the
within-set sense (`HasDerivWithinAt`): one-sided at the endpoints `0` (from
the right) and `t` (from the left), two-sided in the interior — which is
exactly the range over which the physics of the cooling process constrains
the evolution. -/
def CarnotCoolingLaw (par : Params) (T : ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ s ∈ Set.Icc 0 t,
    HasDerivWithinAt T (par.P * T s / (par.C_c * (T s - par.T_h))) (Set.Icc 0 t) s

/-- Solution predicate for subquestion T3-C4: the pair of a temperature law
`T` and an elapsed time `t` constitutes a solution to the cooling task from
`T₀` to `Tt` (the initial and target temperatures, both below `T_h` with
`Tt < T₀`) if the evolution is admissible, obeys the Carnot cooling law
throughout the operating interval, starts at `T₀` at time zero, and reaches
exactly `Tt` at the nonnegative final time `t`.  The physical ordering of
the initial, target and hot-reservoir temperatures is recorded as hypotheses
of the final theorem below, so this predicate keeps only the dynamical and
boundary constraints of the cooling process.

Nothing in the physics of the question constrains the temperature law at
times beyond `t` (once the body has reached `Tt` the requested process is
over) or at negative times, and this predicate accordingly leaves the
outside of the operating interval unconstrained: any physically irrelevant
modification of the law there yields the same cooling process.  The target
theorem therefore asserts uniqueness only *modulo agreement on the operating
interval* `Set.Icc 0 ev.2`, where two solutions must coincide, together with
the equality of their elapsed times — not pointwise equality of the whole
functions on `ℝ`. -/
def Solution (par : Params) (T₀ Tt : ℝ) (ev : (ℝ → ℝ) × ℝ) : Prop :=
  IsAdmissible par ev.1 ev.2 ∧ CarnotCoolingLaw par ev.1 ev.2 ∧
    ev.1 0 = T₀ ∧ ev.1 ev.2 = Tt ∧ 0 ≤ ev.2

/-- **The nondimensionalized elapsed-time primitive**
`y(u) = (C_c/P)(u - T_h log u)`.  Separation of variables in
`-C_c T' = P T/(T_h - T)` gives `y(T(s)) - s` derivative `0`, so along any
admissible evolution `T` of the Carnot cooling law,
`y (T s) = y T₀ + s` identically on the operating interval: `y` is the
"elapsed-time clock" of the process.  Its bracket `u - T_h log u` has
derivative `1 - T_h/u`, strictly negative on `(0, T_h)`, hence `y` is
strictly antitone (and therefore injective) there.  Both the existence
witness (the inverse branch of `y` restricted to the relevant range) and
the uniqueness argument (via this first integral) go through `yprim`. -/
noncomputable def yprim (par : Params) (u : ℝ) : ℝ :=
  (u - par.T_h * Real.log u) * (par.C_c / par.P)

/-- The primitive is differentiable at every `u ≠ 0`, with derivative
`(1 - T_h/u)·(C_c/P)`.  Used both for the inverse-function derivative of
the existence witness and for the chain-rule first integral. -/
private theorem yprim_hasDerivAt (par : Params) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (yprim par) ((1 - par.T_h * u⁻¹) * (par.C_c / par.P)) u := by
  have hlog := (Real.hasDerivAt_log (ne_of_gt hu)).const_mul par.T_h
  have hsub := (hasDerivAt_id u).sub hlog
  have hC := hsub.const_mul (par.C_c / par.P)
  -- functional identity plus derivative identity
  have hfun : (fun v => par.C_c / par.P * (v - par.T_h * Real.log v)) = yprim par := by
    funext v; simp only [yprim]; ring
  have hder : par.C_c / par.P * (1 - par.T_h * u⁻¹)
      = (1 - par.T_h * u⁻¹) * (par.C_c / par.P) := by ring
  -- hC has function `C_c/P * (id - T_h log ·)`, which is definitionally our target
  -- after multiplication commutativity; transport via `hfun` and `hder`.
  simpa only [← hder] using hfun ▸ hC

/-- The reciprocal of `yprim'` at `T ∉ {0, T_h}` equals the Carnot cooling
slope `P·T / (C_c·(T - T_h))`: the inverse branch of `y` solves the law. -/
private theorem yprim_deriv_inv (par : Params) {T : ℝ}
    (hT1 : T ≠ 0) (hT2 : T ≠ par.T_h) :
    ((1 - par.T_h * T⁻¹) * (par.C_c / par.P))⁻¹
      = par.P * T / (par.C_c * (T - par.T_h)) := by
  have hC : par.C_c ≠ 0 := ne_of_gt par.C_c_pos
  have hP : par.P ≠ 0 := ne_of_gt par.P_pos
  have h1 : (1 - par.T_h * T⁻¹) = (T - par.T_h) / T := by
    field_simp
  rw [h1]
  field_simp

/-- On the cold band `(0, T_h)` the primitive `yprim` is strictly
antitone: its derivative is `(1 - T_h/u)·(C_c/P) < 0` there. -/
private theorem yprim_strictAntiOn (par : Params) :
    StrictAntiOn (yprim par) (Set.Ioo 0 par.T_h) := by
  have hconv : Convex ℝ (Set.Ioo 0 par.T_h) := convex_Ioo 0 par.T_h
  have hcont : ContinuousOn (yprim par) (Set.Ioo 0 par.T_h) :=
    fun u hu => (yprim_hasDerivAt par hu.1).continuousAt.continuousWithinAt
  refine strictAntiOn_of_deriv_neg hconv hcont ?_
  intro u hu
  have hum : u ∈ Set.Ioo (0 : ℝ) par.T_h := by
    simpa [interior_Ioo] using hu
  have hd : deriv (yprim par) u = (1 - par.T_h * u⁻¹) * (par.C_c / par.P) :=
    (yprim_hasDerivAt par hum.1).deriv
  rw [hd]
  have hbig : 1 < par.T_h * u⁻¹ := by
    have hpos : (0 : ℝ) < u := hum.1
    have h2lt : u < par.T_h := hum.2
    have h1 : u * u⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
    nlinarith [mul_lt_mul_of_pos_right h2lt (inv_pos.2 hpos)]
  have hneg1 : 1 - par.T_h * u⁻¹ < 0 := by linarith
  exact mul_neg_of_neg_of_pos hneg1 (div_pos par.C_c_pos par.P_pos)

/-- Hence `yprim` is injective on the cold band. -/
private theorem yprim_injOn (par : Params) :
    Set.InjOn (yprim par) (Set.Ioo 0 par.T_h) :=
  (yprim_strictAntiOn par).injOn


/-- **Target theorem (answer-free).**  For the stated configuration — a body
of constant heat capacity `C_c` cooled from `T₀` to a target temperature
`T < T₀` by a continuously operating Carnot refrigerator with constant input
power `P` and constant hot-reservoir temperature `T_h`, with the per-cycle
relation `dQ_c / dQ_h = T_c / T_h` — there exists a pair of a
temperature-evolution law and an elapsed operating time satisfying all the
constraints of the problem, and the physical data of such a pair are unique:
two solutions have the same elapsed time, and their temperature laws agree
everywhere on the common operating interval.  (Pointwise equality of the
laws off the operating interval is deliberately *not* claimed: the question
constrains the process only up to the time at which the body reaches `T`.)
The hypotheses `0 < Tt`, `Tt < T₀` and `T₀ < T_h` express the physical
ordering assumed in the question: a cold body is cooled strictly below its
initial temperature and remains colder than the hot reservoir, on the
absolute (kelvin) temperature scale. -/
theorem problem_IPhO_2026_3_C_4 (par : Params) (T₀ Tt : ℝ)
    (hTt : 0 < Tt) (hT : Tt < T₀) (hT₀ : T₀ < par.T_h) :
    (∃ ev : (ℝ → ℝ) × ℝ, Solution par T₀ Tt ev) ∧
      ∀ ev₁ ev₂ : (ℝ → ℝ) × ℝ,
        Solution par T₀ Tt ev₁ → Solution par T₀ Tt ev₂ →
          ev₁.2 = ev₂.2 ∧ Set.EqOn ev₁.1 ev₂.1 (Set.Icc 0 ev₁.2) := by
  /- USER: The elapsed-time bracket is
  `par.T_h * log (T₀ / Tt) - (T₀ - Tt)`, not its negative.  A robust route
  for both halves is the invariant
  `F x = par.C_c / par.P * (x - par.T_h * log x)`: along any admissible
  solution, the chain rule gives `(F ∘ T)' = 1`.  Hence
  `F (T s) = F T₀ + s`; strict antitonicity/injectivity of `F` on
  `(0, par.T_h)` yields law uniqueness and the endpoint formula for time.
  For existence, construct the inverse branch of this continuous strictly
  antitone `F` on `Set.Icc Tt T₀` and restrict it to the corresponding time
  interval.  Do not retry an exponential witness; this ODE is nonlinear. -/
  -- Shared abbreviations and positivity facts.
  set y : ℝ → ℝ := yprim par with hy_def
  set c := -Real.log par.T_h with hc_def
  have hTh : 0 < par.T_h := par.T_h_pos
  have hCc : 0 < par.C_c := par.C_c_pos
  have hP : 0 < par.P := par.P_pos
  have hTt₀ : Tt < T₀ := hT
  have h0Tt : 0 < Tt := hTt
  have hT₀h : T₀ < par.T_h := hT₀
  have h0T₀ : 0 < T₀ := lt_trans hTt hT
  have hyTtmem : Tt ∈ Set.Ioo (0:ℝ) par.T_h := ⟨hTt, lt_trans hT hT₀⟩
  have hyT₀mem : T₀ ∈ Set.Ioo (0:ℝ) par.T_h := ⟨h0T₀, hT₀⟩
  -- The core turnstile lemma (from `yprim_strictAntiOn`):
  have hyTt_pos : 0 < y Tt - y T₀ := by
    have hyanti : StrictAntiOn y (Set.Ioo (0:ℝ) par.T_h) := yprim_strictAntiOn par
    have hlt : y T₀ < y Tt := hyanti hyTtmem hyT₀mem hT
    linarith
  -- The law's right-hand side `P T/(C_c (T - T_h))` is `yprim'(T s)⁻¹` and is
  -- negative throughout the operating interval, since `0 < T s < T_h` there.
  -- We will need both the witness and uniqueness halves to know that the
  -- primitive satisfies the *functional* identity  `h·(T') = P T/(C_c (T-t)) ⇒ y'(T)·T' = 1`.
  have hlaw'_to_eq1 : ∀ (T : ℝ → ℝ) (t : ℝ), CarnotCoolingLaw par T t →
      ∀ s ∈ Set.Icc 0 t, T s ∈ Set.Ioo (0:ℝ) par.T_h →
      HasDerivWithinAt (fun s => yprim par (T s)) 1 (Set.Icc 0 t) s := by
    intro T t hlaw s hs hband
    have hTlaw := hlaw s hs
    have hband' := hband
    -- derivative of yprim at T s
    have hy := yprim_hasDerivAt par hband'.1
    -- chain rule within
    have hcomp := hy.comp_hasDerivWithinAt s hTlaw
    -- hcomp : (yprim ∘ T)' = y'(T s) * P T s / (C_c (T s - T_h)) within Icc 0 t
    -- use yprim_deriv_inv arithmetic: y'(u) * P u / (C_c (u - T_h)) = 1 for u ∉ {0,T_h}
    have hT1 : T s ≠ 0 := ne_of_gt hband'.1
    have hT2 : T s ≠ par.T_h := ne_of_lt hband'.2
    have hinv := yprim_deriv_inv par hT1 hT2
    -- slope computation: y'(u) · P u / (C_c (u - T_h)) = 1
    have hslope : ((1 - par.T_h * (T s)⁻¹) * (par.C_c / par.P))
        * (par.P * T s / (par.C_c * (T s - par.T_h))) = 1 := by
      have hC : par.C_c ≠ 0 := ne_of_gt par.C_c_pos
      have hP : par.P ≠ 0 := ne_of_gt par.P_pos
      have hsub : T s - par.T_h ≠ 0 := sub_ne_zero_of_ne hT2
      rw [mul_comm ((1 - par.T_h * (T s)⁻¹) * (par.C_c / par.P))
        (par.P * T s / (par.C_c * (T s - par.T_h)))]
      -- invert relation: a * b = 1 where b = a⁻¹
      have hdiv : par.P * T s / (par.C_c * (T s - par.T_h))
          = ((1 - par.T_h * (T s)⁻¹) * (par.C_c / par.P))⁻¹ := hinv.symm
      rw [hdiv]
      exact inv_mul_cancel₀ (by
        intro heq0
        have h1 : (1 - par.T_h * (T s)⁻¹) ≠ 0 := by
          intro h10
          have heq1 : par.T_h * (T s)⁻¹ = 1 := by linarith [h10]
          have hu2 : T s < par.T_h := hband'.2
          have hpos : (0:ℝ) < T s := hband'.1
          have h1' : (T s) * (T s)⁻¹ = 1 := mul_inv_cancel₀ hT1
          have hmul := mul_lt_mul_of_pos_right hu2 (inv_pos.2 hpos)
          rw [h1'] at hmul
          linarith
        exact mul_ne_zero h1 (div_ne_zero hC hP) heq0)
    -- now replace the composed derivative's slope by 1
    have hrw : (1 : ℝ) = ((1 - par.T_h * (T s)⁻¹) * (par.C_c / par.P))
        * (par.P * T s / (par.C_c * (T s - par.T_h))) := hslope.symm
    rw [hrw]
    exact hcomp


  -- **The first integral** `s ↦ y(T s) − (y T₀ + s)` is constant along any solution.
  -- Its domain derivative vanishes by the cooling law; continuity on the closed
  -- interval then pins it to its value at 0.
  have hconst : ∀ (T : ℝ → ℝ) (t : ℝ),
      IsAdmissible par T t → CarnotCoolingLaw par T t → T 0 = T₀ →
      (∀ s ∈ Set.Icc 0 t, T s ∈ Set.Ioo (0:ℝ) par.T_h) →
      ∀ s ∈ Set.Icc 0 t, yprim par (T s) = yprim par (T 0) + s := by
    intro T t hadm hlaw hT0 hband s hs
    by_cases ht0 : 0 < t
    · -- nontrivial interval: MVT machinery on [0, t]
      -- the Φ function and its zero-derivative on the whole closed interval
      have hderivΦ : ∀ x ∈ Set.Icc 0 t,
          HasDerivWithinAt (fun s => yprim par (T s) - (yprim par (T 0) + s)) 0
            (Set.Icc 0 t) x := by
        intro x hx
        have hmem : x ∈ Set.Icc 0 t := hx
        have h1 := hlaw'_to_eq1 T t hlaw x hmem (hband x hmem)
        have h2 : HasDerivAt (fun s => yprim par (T 0) + s) 1 x :=
          (hasDerivAt_id x).const_add (yprim par (T 0))
        have hsub := h1.sub h2.hasDerivWithinAt
        have h0 : (1 : ℝ) - 1 = 0 := sub_self 1
        rw [h0] at hsub
        exact hsub
      have hΦconst0 : ∀ x ∈ Set.Icc 0 t,
          (fun s => yprim par (T s) - (yprim par (T 0) + s)) x
            = (fun s => yprim par (T s) - (yprim par (T 0) + s)) 0 :=
        constant_of_derivWithin_zero
          (fun x hx => (hderivΦ x hx).differentiableWithinAt)
          (fun x hx => (hderivΦ x ⟨hx.1, le_of_lt hx.2⟩).derivWithin
            (uniqueDiffOn_Icc ht0 x ⟨hx.1, le_of_lt hx.2⟩))
      have hΦs := hΦconst0 s hs
      have hΦ0 : (fun s => yprim par (T s) - (yprim par (T 0) + s)) 0 = 0 := by
        simp
      rw [hΦ0] at hΦs
      -- hΦs : yprim (T s) - (yprim (T 0) + s) = 0
      linarith [hΦs]
    · -- degenerate interval t ≤ 0: hs forces s = 0
      have ht_le : t ≤ 0 := not_lt.mp ht0
      have : s = 0 := le_antisymm (le_trans hs.2 ht_le) hs.1
      subst this
      simp

  -- ======= uniqueness half =======
  have huniq : ∀ (ev₁ ev₂ : (ℝ → ℝ) × ℝ),
      Solution par T₀ Tt ev₁ → Solution par T₀ Tt ev₂ →
        ev₁.2 = ev₂.2 ∧ Set.EqOn ev₁.1 ev₂.1 (Set.Icc 0 ev₁.2) := by
    intro ev₁ ev₂ h₁ h₂
    rcases h₁ with ⟨h₁adm, h₁law, h₁0, h₁T, h₁pos⟩
    rcases h₂ with ⟨h₂adm, h₂law, h₂0, h₂T, h₂pos⟩
    have hband₁ : ∀ s ∈ Set.Icc 0 ev₁.2, ev₁.1 s ∈ Set.Ioo (0:ℝ) par.T_h :=
      fun s hs => ⟨h₁adm.temperature_pos s hs, h₁adm.cold_side s hs⟩
    have hband₂ : ∀ s ∈ Set.Icc 0 ev₂.2, ev₂.1 s ∈ Set.Ioo (0:ℝ) par.T_h :=
      fun s hs => ⟨h₂adm.temperature_pos s hs, h₂adm.cold_side s hs⟩
    have hi₁ := hconst ev₁.1 ev₁.2 h₁adm h₁law h₁0 hband₁ ev₁.2
      ⟨h₁pos, le_rfl⟩
    have hi₂ := hconst ev₂.1 ev₂.2 h₂adm h₂law h₂0 hband₂ ev₂.2
      ⟨h₂pos, le_rfl⟩
    rw [h₁T, h₁0] at hi₁
    rw [h₂T, h₂0] at hi₂
    have htime : ev₁.2 = ev₂.2 := by linarith [hi₁, hi₂]
    refine ⟨htime, ?_⟩
    intro s hs
    have hsband := hband₁ s hs
    have hi₁s := hconst ev₁.1 ev₁.2 h₁adm h₁law h₁0 hband₁ s hs
    have hi₂s := hconst ev₂.1 ev₂.2 h₂adm h₂law h₂0 hband₂ s
      ⟨hs.1, htime ▸ hs.2⟩
    rw [h₁0] at hi₁s
    rw [h₂0] at hi₂s
    have hEq : yprim par (ev₁.1 s) = yprim par (ev₂.1 s) := by linarith [hi₁s, hi₂s]
    exact yprim_injOn par hsband (hband₂ s ⟨hs.1, htime ▸ hs.2⟩) hEq
  -- ======= existence half (inverse-branch witness) =======
  constructor
  · -- abbreviations
    set yb : ℝ → ℝ := yprim par with hyb_def
    set θt : ℝ := -Real.log par.T_h with hθt_def
    -- the branch map hbr(θ) = y (exp(−θ)) on Ioi θt is differentiable with
    -- strictly negative derivative, hence a strictly antitone bijection
    -- onto the range, and the needed range contains [y Tt, y T₀].
    set hbr : ℝ → ℝ := fun θ => yb (Real.exp (-θ)) with hbr_def
    have hbr_mem : ∀ θ ∈ Set.Ioi θt, Real.exp (-θ) ∈ Set.Ioo (0:ℝ) par.T_h := by
      intro θ hθ
      simp only [Set.mem_Ioi] at hθ
      constructor
      · exact Real.exp_pos _
      · have : Real.exp (-θ) < Real.exp (Real.log par.T_h) := by
          apply Real.exp_lt_exp.mpr
          linarith
        rwa [Real.exp_log par.T_h_pos] at this
    have hbr_deriv : ∀ θ ∈ Set.Ioi θt,
        HasDerivAt hbr
          ((1 - par.T_h * (Real.exp (-θ))⁻¹) * (par.C_c / par.P)
            * (-Real.exp (-θ))) θ := by
      intro θ hθ
      have hexp : 0 < Real.exp (-θ) := Real.exp_pos _
      have hyl := yprim_hasDerivAt par hexp
      have hneg : HasDerivAt (fun θ => Real.exp (-θ)) (-Real.exp (-θ)) θ := by
        have hE := Real.hasDerivAt_exp (-θ)
        have hN := hasDerivAt_neg θ
        have hcomp := hE.comp θ hN
        have hval : Real.exp (-θ) * -1 = -Real.exp (-θ) := by ring
        rw [hval] at hcomp
        exact hcomp
      have hcomp := hyl.comp θ hneg
      have hval : (1 - par.T_h * (Real.exp (-θ))⁻¹) * (par.C_c / par.P)
          * (-Real.exp (-θ))
          = ((1 - par.T_h * (Real.exp (-θ))⁻¹) * (par.C_c / par.P))
            * (-Real.exp (-θ)) := rfl
      rw [show (1 : ℝ) - par.T_h * (Real.exp (-θ))⁻¹ =
          (1 - par.T_h * (Real.exp (-θ))⁻¹) from rfl]
      exact hcomp
    have hbr_strict : StrictMonoOn hbr (Set.Ioi θt) := by
      have hconv : Convex ℝ (Set.Ioi θt) := convex_Ioi _
      have hcont : ContinuousOn hbr (Set.Ioi θt) :=
        fun θ hθ => (hbr_deriv θ hθ).continuousAt.continuousWithinAt
      refine strictMonoOn_of_deriv_pos hconv hcont (fun θ hθ => ?_)
      have hmem : θ ∈ Set.Ioi θt := by rwa [interior_Ioi] at hθ
      have hder : deriv hbr θ =
          (1 - par.T_h * (Real.exp (-θ))⁻¹) * (par.C_c / par.P) * (-Real.exp (-θ)) :=
        (hbr_deriv θ hmem).deriv
      rw [hder]
      have hexp : 0 < Real.exp (-θ) := Real.exp_pos _
      have hlt : Real.exp (-θ) < par.T_h := (hbr_mem θ hmem).2
      have h1 : 1 - par.T_h * (Real.exp (-θ))⁻¹ < 0 := by
        have hpos : 0 < (Real.exp (-θ))⁻¹ := inv_pos.2 hexp
        have hmul := mul_lt_mul_of_pos_right hlt hpos
        rw [mul_inv_cancel₀ (ne_of_gt hexp)] at hmul
        linarith [hmul]
      have h2 : (1 - par.T_h * (Real.exp (-θ))⁻¹) * (par.C_c / par.P) < 0 :=
        mul_neg_of_neg_of_pos h1 (div_pos par.C_c_pos par.P_pos)
      -- product of two negatives is positive: hbr is strictly increasing.
      exact mul_pos_of_neg_of_neg h2 (neg_neg_of_pos (Real.exp_pos (-θ)))
    -- quantitative: y T₀ and y Tt are in the branch's range.
    have hyT₀_range : y T₀ ∈ hbr '' Set.Ioi θt := by
      -- hbr(−log T₀) = y (exp(log T₀)) = y T₀, and −log T₀ > θt since T₀ < T_h
      have hlog : θt < -Real.log T₀ := by
        rw [hθt_def]
        have : Real.log T₀ < Real.log par.T_h :=
          Real.log_lt_log (lt_trans hTt hT) hT₀
        linarith
      refine ⟨-Real.log T₀, by simp only [Set.mem_Ioi]; exact hlog, ?_⟩
      rw [hbr_def, hyb_def]
      have hexp0 : Real.exp (-(-Real.log T₀)) = T₀ := by
        rw [neg_neg, Real.exp_log (lt_trans hTt hT)]
      rw [show (fun θ => yprim par (Real.exp (-θ))) (-Real.log T₀)
          = yprim par (Real.exp (-(-Real.log T₀))) from rfl, hexp0]
    have hyTt_range : y Tt ∈ hbr '' Set.Ioi θt := by
      have hlog : θt < -Real.log Tt := by
        rw [hθt_def]
        have : Real.log Tt < Real.log par.T_h :=
          Real.log_lt_log hTt (lt_trans hT hT₀)
        linarith
      refine ⟨-Real.log Tt, by simp only [Set.mem_Ioi]; exact hlog, ?_⟩
      rw [hbr_def, hyb_def]
      have hexp0 : Real.exp (-(-Real.log Tt)) = Tt := by
        rw [neg_neg, Real.exp_log hTt]
      rw [show (fun θ => yprim par (Real.exp (-θ))) (-Real.log Tt)
          = yprim par (Real.exp (-(-Real.log Tt))) from rfl, hexp0]
    -- Now the witness: the inverse branch of `hbr` on `Ioi θt`.
    set θ₀ : ℝ → ℝ := Function.invFunOn hbr (Set.Ioi θt) with hθ₀_def
    set Tc : ℝ → ℝ := fun s => Real.exp (-θ₀ (s + y T₀)) with hTc_def
    -- quantitative core: `y T_h < y v` for cold-band v, and surjectivity
    -- of the branch map `hbr` onto `(y T_h, ∞)`.
    -- -----------------------------------------------------------------
    have hygt : ∀ v ∈ Set.Ioo (0:ℝ) par.T_h,
        yprim par par.T_h < yprim par v := by
      intro v hv
      have hlog : Real.log (par.T_h / v) > 1 - v / par.T_h := by
        have hx1 : (0:ℝ) < v / par.T_h := div_pos hv.1 par.T_h_pos
        have hx2 : v / par.T_h ≠ 1 := by
          intro e
          have hv2 : v = par.T_h := by
            field_simp at e
            linarith [e]
          exact ne_of_lt hv.2 hv2
        have h := Real.log_lt_sub_one_of_pos hx1 hx2
        -- −log(T_h/v) = log(v/T_h) < v/T_h − 1, so log(T_h/v) > 1 − v/T_h
        have hneg : Real.log (v / par.T_h) = -Real.log (par.T_h / v) := by
          rw [← Real.log_inv, inv_div]
        rw [hneg] at h
        linarith
      have hmain : (0:ℝ) < par.T_h * (Real.log (par.T_h / v) - (1 - v / par.T_h)) :=
        mul_pos par.T_h_pos (by linarith [hlog])
      have hb : (v - par.T_h * Real.log v) - (par.T_h - par.T_h * Real.log par.T_h)
          = par.T_h * (Real.log (par.T_h / v) - (1 - v / par.T_h)) := by
        rw [Real.log_div (ne_of_gt par.T_h_pos) (ne_of_gt hv.1)]
        field_simp
        ring
      have hsum : yprim par v - yprim par par.T_h =
          ((v - par.T_h * Real.log v) - (par.T_h - par.T_h * Real.log par.T_h))
            * (par.C_c / par.P) := by
        simp [yprim]; ring
      have hpos := mul_pos hmain (div_pos par.C_c_pos par.P_pos)
      linarith [hpos, hb ▸ hsum]
    have hyT₀_gt : yprim par par.T_h < y T₀ := hygt T₀ hyT₀mem
    have hyTt_gt : yprim par par.T_h < y Tt := hygt Tt hyTtmem
    -- the branch map tends to +∞ at +∞
    have hbr_tendsto_top : Filter.Tendsto hbr Filter.atTop Filter.atTop := by
      have hlin : Filter.Tendsto (fun θ : ℝ => (par.C_c / par.P) * (par.T_h * θ))
          Filter.atTop Filter.atTop :=
        have hThθ : Filter.Tendsto (fun θ : ℝ => par.T_h * θ) Filter.atTop Filter.atTop :=
          Tendsto.const_mul_atTop par.T_h_pos (tendsto_id (x := Filter.atTop))
        Tendsto.const_mul_atTop (div_pos par.C_c_pos par.P_pos) hThθ
      refine Filter.tendsto_atTop_mono ?_ hlin
      intro θ
      simp only [hbr_def, hyb_def, yprim, Real.log_exp]
      have hexp : (0:ℝ) ≤ Real.exp (-θ) := le_of_lt (Real.exp_pos _)
      have hstep : par.T_h * θ ≤ Real.exp (-θ) + par.T_h * θ := by linarith [hexp]
      have hmul := mul_le_mul_of_nonneg_left hstep
        (le_of_lt (div_pos par.C_c_pos par.P_pos))
      calc (par.C_c / par.P) * (par.T_h * θ)
          ≤ (par.C_c / par.P) * (Real.exp (-θ) + par.T_h * θ) := hmul
        _ = (Real.exp (-θ) - par.T_h * -θ) * (par.C_c / par.P) := by ring
    -- the branch map tends to `y T_h` as θ → θt⁺
    have hbr_tendsto_right : Filter.Tendsto hbr
        (nhdsWithin θt (Set.Ioi θt)) (𝓝 (yprim par par.T_h)) := by
      have hv : Real.exp (-θt) = par.T_h := by
        simp [hθt_def, Real.exp_log par.T_h_pos]
      have hexpc : Filter.Tendsto (fun θ : ℝ => Real.exp (-θ))
          (nhdsWithin θt (Set.Ioi θt)) (𝓝 par.T_h) := by
        have hc : ContinuousAt (fun θ : ℝ => Real.exp (-θ)) θt := by
          fun_prop
        have h := (hc).tendsto.mono_left (nhdsWithin_le_nhds (a := θt) (s := Set.Ioi θt))
        rwa [hv] at h
      have hycont : ContinuousAt (yprim par) par.T_h :=
        (yprim_hasDerivAt par par.T_h_pos).continuousAt
      have hcomp := hycont.tendsto.comp hexpc
      have hfun : (fun x => yprim par (Real.exp (-x))) = hbr := by
        ext v; simp [hbr_def, hyb_def]
      show Filter.Tendsto hbr (nhdsWithin θt (Set.Ioi θt)) (𝓝 (yprim par par.T_h))
      exact hfun ▸ hcomp
    -- surjectivity via IVT between a near point (value < v) and a far point (v < value)
    have hbr_surj : ∀ v, yprim par par.T_h < v →
        ∃ θ ∈ Set.Ioi θt, hbr θ = v := by
      intro v hv
      have htop_ev : ∀ᶠ θ in Filter.atTop, v < hbr θ :=
        hbr_tendsto_top.eventually_gt_atTop v
      obtain ⟨aT, haT⟩ := eventually_atTop.mp htop_ev
      have h_ev : ∀ᶠ θ in nhdsWithin θt (Set.Ioi θt), hbr θ < v :=
        hbr_tendsto_right (Iio_mem_nhds hv)
      obtain ⟨θ₁, hθ₁v, hθ₁mem⟩ := (h_ev.and self_mem_nhdsWithin).exists
      obtain ⟨θ₂, hθ₂gt, hθ₂v⟩ : ∃ θ₂, θ₁ < θ₂ ∧ v < hbr θ₂ := by
        refine ⟨max (θ₁ + 1) aT + 1, ?_, ?_⟩
        · have h1 : θ₁ < θ₁ + 1 := by linarith
          have h2 : θ₁ + 1 ≤ max (θ₁ + 1) aT := le_max_left _ _
          have h3 : max (θ₁ + 1) aT < max (θ₁ + 1) aT + 1 := by linarith
          linarith
        · exact haT _ (by
            have h1 : aT ≤ max (θ₁ + 1) aT := le_max_right _ _
            have h2 : max (θ₁ + 1) aT ≤ max (θ₁ + 1) aT + 1 := by linarith
            linarith)
      have hcont : ContinuousOn hbr (Set.Icc θ₁ θ₂) := by
        intro x hx
        have h1 : θt < x := lt_of_lt_of_le hθ₁mem hx.1
        exact (hbr_deriv x h1).continuousAt.continuousWithinAt
      have him := intermediate_value_Icc (le_of_lt hθ₂gt) hcont
      have hmemv : v ∈ Set.Icc (hbr θ₁) (hbr θ₂) := ⟨le_of_lt hθ₁v, le_of_lt hθ₂v⟩
      obtain ⟨θ, hθmem, hθeq⟩ := him hmemv
      exact ⟨θ, lt_of_lt_of_le hθ₁mem hθmem.1, hθeq⟩

    -- -----------------------------------------------------------------
    -- (2) the inverse branch θ₀ and its right-inverse identity
    -- -----------------------------------------------------------------
    have hbr_injOn : Set.InjOn hbr (Set.Ioi θt) := hbr_strict.injOn
    have hbr_leftInv : Set.LeftInvOn θ₀ hbr (Set.Ioi θt) :=
      hbr_injOn.leftInvOn_invFunOn
    have hθ₀_rightInv : ∀ v, yprim par par.T_h < v → hbr (θ₀ v) = v := by
      intro v hv
      exact Function.invFunOn_eq (hbr_surj v hv)
    have hθ₀_mem : ∀ v, yprim par par.T_h < v → θ₀ v ∈ Set.Ioi θt := by
      intro v hv
      exact Function.invFunOn_mem (hbr_surj v hv)
    -- θ₀ is strictly monotone on (y T_h, ∞)
    have hθ₀_strict : StrictMonoOn θ₀ (Set.Ioi (yprim par par.T_h)) := by
      intro v₁ hv₁ v₂ hv₂ hlt
      have hm₁ := hθ₀_mem v₁ hv₁
      have hm₂ := hθ₀_mem v₂ hv₂
      have hr₁ := hθ₀_rightInv v₁ hv₁
      have hr₂ := hθ₀_rightInv v₂ hv₂
      by_contra hnot
      replace hnot : θ₀ v₂ ≤ θ₀ v₁ := le_of_not_gt hnot
      have hmono : MonotoneOn hbr (Set.Ioi θt) := hbr_strict.monotoneOn
      rcases eq_or_lt_of_le hnot with heq | hlt2
      · have hvv : v₁ = v₂ := by rw [← hr₁, ← hr₂, heq]
        linarith [hvv, hlt]
      · have h := hmono hm₂ hm₁ (le_of_lt hlt2)
        rw [hr₂, hr₁] at h
        linarith [h, hlt]
    -- continuity of θ₀ at any point of (y T_h, ∞)
    have hθ₀_cont : ∀ v ∈ Set.Ioi (yprim par par.T_h), ContinuousAt θ₀ v := by
      intro v hv
      refine hθ₀_strict.continuousAt_of_exists_between (Ioi_mem_nhds hv) ?_ ?_
      · intro b hb
        have hmem := hθ₀_mem v hv
        have hmax : max b θt < θ₀ v := max_lt hb hmem
        set m := (max b θt + θ₀ v) / 2 with hm_def
        have hmb : b < m := by
          have h1 : m > max b θt := by
            rw [hm_def]; linarith [hmax]
          have h2 : b ≤ max b θt := le_max_left _ _
          linarith
        have hmθt : θt < m := by
          have h1 : m > max b θt := by rw [hm_def]; linarith [hmax]
          have h2 : θt ≤ max b θt := le_max_right _ _
          linarith
        have hmlt : m < θ₀ v := by rw [hm_def]; linarith [hmax]
        refine ⟨hbr m, ?_, ?_⟩
        · have hexp_mem := hbr_mem m hmθt
          have h := hygt (Real.exp (-m)) hexp_mem
          simpa only [Set.mem_Ioi, hbr_def, hyb_def] using h
        · rw [hbr_leftInv hmθt]
          exact ⟨le_of_lt hmb, hmlt⟩
      · intro b hb
        have hmem := hθ₀_mem v hv
        set m := (θ₀ v + min b (θ₀ v + 1)) / 2 with hm_def
        have hmin : θ₀ v < min b (θ₀ v + 1) := by
          refine lt_min hb ?_
          linarith
        have hmb : θ₀ v < m := by rw [hm_def]; linarith [hmin]
        have hmθt : θt < m := lt_trans hmem hmb
        have hmltb : m < b := by
          rw [hm_def]
          have h1 : min b (θ₀ v + 1) ≤ b := min_le_left _ _
          have h2 : θ₀ v < b := hb
          linarith
        refine ⟨hbr m, ?_, ?_⟩
        · have hexp_mem := hbr_mem m hmθt
          have h := hygt (Real.exp (-m)) hexp_mem
          simpa only [Set.mem_Ioi, hbr_def, hyb_def] using h
        · rw [hbr_leftInv hmθt]
          exact ⟨hmb, le_of_lt hmltb⟩
    -- -----------------------------------------------------------------
    -- (3) the derivative of θ₀ at band points, via the inverse rule
    -- -----------------------------------------------------------------
    have hθ₀_deriv : ∀ v, yprim par par.T_h < v →
        HasDerivAt θ₀
          ((1 - par.T_h * (Real.exp (-(θ₀ v)))⁻¹) * (par.C_c / par.P)
            * (-Real.exp (-(θ₀ v))))⁻¹ v := by
      intro v hv
      have hmem := hθ₀_mem v hv
      refine (hbr_deriv (θ₀ v) hmem).of_local_left_inverse
          (hθ₀_cont v (by simpa only [Set.mem_Ioi] using hv)) ?_ ?_
      · have hexp : 0 < Real.exp (-(θ₀ v)) := Real.exp_pos _
        have hlt : Real.exp (-(θ₀ v)) < par.T_h := (hbr_mem (θ₀ v) hmem).2
        have h1 : (1 - par.T_h * (Real.exp (-(θ₀ v)))⁻¹) * (par.C_c / par.P) < 0 := by
          have hpos : 0 < (Real.exp (-(θ₀ v)))⁻¹ := inv_pos.2 hexp
          have hmul := mul_lt_mul_of_pos_right hlt hpos
          rw [mul_inv_cancel₀ (ne_of_gt hexp)] at hmul
          have h1' : 1 - par.T_h * (Real.exp (-(θ₀ v)))⁻¹ < 0 := by linarith [hmul]
          exact mul_neg_of_neg_of_pos h1' (div_pos par.C_c_pos par.P_pos)
        have h2 : 0 < (1 - par.T_h * (Real.exp (-(θ₀ v)))⁻¹) * (par.C_c / par.P)
            * (-Real.exp (-(θ₀ v))) :=
          mul_pos_of_neg_of_neg h1 (neg_neg_of_pos hexp)
        exact ne_of_gt h2
      · filter_upwards [Ioi_mem_nhds hv] with v' hv'
        exact hθ₀_rightInv v' hv'
    -- -----------------------------------------------------------------
    -- (4) assemble the witness Tc and verify `Solution`.
    -- -----------------------------------------------------------------
    set that := y Tt - y T₀ with hthat_def
    have hthat_pos : 0 < that := hyTt_pos
    have hband_v : ∀ s ∈ Set.Icc 0 that,
        yprim par par.T_h < s + y T₀ := by
      intro s hs
      have h1 : yprim par par.T_h < y T₀ := hyT₀_gt
      have h2 : (0:ℝ) ≤ s := hs.1
      have h3 : (0:ℝ) + y T₀ ≤ s + y T₀ := by
        simp only [add_le_add_iff_right]; exact h2
      rw [zero_add] at h3
      exact lt_of_lt_of_le h1 h3
    have hTc_band : ∀ s ∈ Set.Icc 0 that, Real.exp (-θ₀ (s + y T₀))
        ∈ Set.Ioo (0:ℝ) par.T_h := by
      intro s hs
      exact hbr_mem (θ₀ (s + y T₀)) (hθ₀_mem (s + y T₀) (hband_v s hs))
    have hTc0 : Real.exp (-θ₀ (0 + y T₀)) = T₀ := by
      obtain ⟨θ, hθmem, hθeq⟩ := hyT₀_range
      have h1 : θ₀ (0 + y T₀) = θ := by
        rw [zero_add, ← hθeq]
        exact hbr_leftInv hθmem
      rw [h1]
      have h2 : Real.exp (-θ) = T₀ := by
        have hmeme : Real.exp (-θ) ∈ Set.Ioo (0:ℝ) par.T_h := hbr_mem θ hθmem
        have hsy : yprim par (Real.exp (-θ)) = yprim par T₀ := by
          have : hbr θ = y T₀ := hθeq
          rwa [hbr_def, hyb_def] at this
        exact yprim_injOn par hmeme hyT₀mem hsy
      rw [h2]
    have hTct : Real.exp (-θ₀ (that + y T₀)) = Tt := by
      have hthat : that + y T₀ = y Tt := by
        rw [hthat_def]; ring
      obtain ⟨θ, hθmem, hθeq⟩ := hyTt_range
      have h1 : θ₀ (that + y T₀) = θ := by
        rw [hthat, ← hθeq]
        exact hbr_leftInv hθmem
      rw [h1]
      have h2 : Real.exp (-θ) = Tt := by
        have hmeme : Real.exp (-θ) ∈ Set.Ioo (0:ℝ) par.T_h := hbr_mem θ hθmem
        have hsy : yprim par (Real.exp (-θ)) = yprim par Tt := by
          have : hbr θ = y Tt := hθeq
          rwa [hbr_def, hyb_def] at this
        exact yprim_injOn par hmeme hyTtmem hsy
      rw [h2]
    -- the candidate evolution satisfies the cooling law on [0, that]
    have hTc_law : ∀ s ∈ Set.Icc 0 that,
        HasDerivWithinAt (fun s => Real.exp (-θ₀ (s + y T₀)))
          (par.P * Real.exp (-θ₀ (s + y T₀))
            / (par.C_c * (Real.exp (-θ₀ (s + y T₀)) - par.T_h)))
          (Set.Icc 0 that) s := by
      intro s hs
      have hv := hband_v s hs
      have hmem := hθ₀_mem (s + y T₀) hv
      have hband' := hTc_band s hs
      have hd0 := hθ₀_deriv (s + y T₀) hv
      have hshift : HasDerivAt (fun x => θ₀ (x + y T₀))
          (((1 - par.T_h * (Real.exp (-(θ₀ (s + y T₀))))⁻¹) * (par.C_c / par.P)
            * (-Real.exp (-(θ₀ (s + y T₀)))))⁻¹) s := by
        have h1 : HasDerivAt (fun x : ℝ => x + y T₀) 1 s :=
          (hasDerivAt_id s).add_const (y T₀)
        have h := hd0.comp s h1
        rwa [mul_one] at h
      have hexpchain : HasDerivAt (fun x => Real.exp (-θ₀ (x + y T₀)))
          (Real.exp (-(θ₀ (s + y T₀)))
            * (-(((1 - par.T_h * (Real.exp (-(θ₀ (s + y T₀))))⁻¹) * (par.C_c / par.P)
              * (-Real.exp (-(θ₀ (s + y T₀)))))⁻¹))) s := by
        have hneg := hshift.neg
        exact (Real.hasDerivAt_exp (-(θ₀ (s + y T₀)))).comp s hneg
      -- algebra: the chain-computed slope equals the Carnot slope
      have hslope_same : Real.exp (-(θ₀ (s + y T₀)))
            * (-(((1 - par.T_h * (Real.exp (-(θ₀ (s + y T₀))))⁻¹) * (par.C_c / par.P)
              * (-Real.exp (-(θ₀ (s + y T₀)))))⁻¹))
          = par.P * Real.exp (-θ₀ (s + y T₀))
            / (par.C_c * (Real.exp (-θ₀ (s + y T₀)) - par.T_h)) := by
        set E := Real.exp (-(θ₀ (s + y T₀))) with hE_def
        have hE_pos : 0 < E := Real.exp_pos _
        have hE_ne : E ≠ 0 := ne_of_gt hE_pos
        have hE_lt : E < par.T_h := hband'.2
        have hEth : E - par.T_h ≠ 0 := sub_ne_zero_of_ne (ne_of_lt hE_lt)
        have hC : par.C_c ≠ 0 := ne_of_gt par.C_c_pos
        have hP : par.P ≠ 0 := ne_of_gt par.P_pos
        have h1 : (1 - par.T_h * E⁻¹) = (E - par.T_h) / E := by
          field_simp
        rw [h1]
        field_simp
      -- conclude: expand Tc = exp ∘ (Neg.neg ∘ θ₀ ∘ (· + yT₀)) at s
      have hHc : HasDerivAt (fun x => Real.exp (-θ₀ (x + y T₀)))
          (par.P * Real.exp (-θ₀ (s + y T₀))
            / (par.C_c * (Real.exp (-θ₀ (s + y T₀)) - par.T_h))) s := by
        rw [← hslope_same]
        exact hexpchain
      -- Tc is definitionally the same function; turn HasDerivAt into WithinAt.
      have hfun : (fun s => Real.exp (-θ₀ (s + y T₀)))
          = (fun x => Real.exp (-θ₀ (x + y T₀))) := rfl
      show HasDerivWithinAt (fun s => Real.exp (-θ₀ (s + y T₀)))
        (par.P * Real.exp (-θ₀ (s + y T₀))
          / (par.C_c * (Real.exp (-θ₀ (s + y T₀)) - par.T_h)))
        (Set.Icc 0 that) s
      exact hHc.hasDerivWithinAt
    -- admissibility
    have hTc_adm : IsAdmissible par (fun s => Real.exp (-θ₀ (s + y T₀))) that := by
      refine ⟨?_, ?_, ?_⟩
      · intro s hs
        exact (hTc_law s hs).differentiableWithinAt
      · intro s hs
        exact (hTc_band s hs).2
      · intro s hs
        exact (hTc_band s hs).1
    have hsol : Solution par T₀ Tt (Tc, that) :=
      ⟨hTc_adm, (fun s hs => hTc_law s hs), hTc0, hTct, le_of_lt hthat_pos⟩
    exact Exists.intro ⟨Tc, that⟩ hsol
  · exact huniq

end IPhO_2026_3_C_4
