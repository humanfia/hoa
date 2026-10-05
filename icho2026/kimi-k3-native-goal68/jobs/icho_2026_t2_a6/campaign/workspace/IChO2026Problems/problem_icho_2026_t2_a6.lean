import Mathlib

/-!
# IChO 2026, Theory Problem T2, subquestion 2.6 (icho_2026_t2_a6)

## Task

For an **open** system running the Belousov–Zhabotinsky (BZ) reaction, classify
the effect of four perturbations, ticking exactly one box (a–e) each:

1. Adding a small amount of Ce⁴⁺ during Process A.
2. Adding a small amount of Ag⁺ during Process B.
3. Adding a small amount of Br⁻ during Process B.
4. Continuous addition of Br⁻.

Options:
* (a) prolongs Process A
* (b) prolongs Process B
* (c) Process A switches to Process B
* (d) Process B switches to Process A
* (e) oscillations stop

## Problem-grounded inputs (from the printed problem statement)

* Rate constants: k₁ = 1.0×10⁴ M⁻² s⁻¹, k₄ = 2.0×10⁹ M⁻² s⁻¹,
  k₇ = 1.0×10² M⁻¹ s⁻¹.
* Fixed concentrations: [BrO₃⁻]₀ = 0.06 M, [H⁺]₀ = 0.8 M (reactants and pH are
  maintained constant).
* Switching criterion (stated verbatim in the problem, part 2.3 lead-in):
  "To switch Process A to Process B, the reaction rate of the elementary
  step (4) must exceed that of the elementary step (1) and vice versa."
* Process C, (7) Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products, occurs
  *continuously*; it is the bromide source of the cycle.
* [Br⁻] slowly decreases from [Br⁻]max = 7.0×10⁻⁴ M down to [Br⁻]critical
  during the slow leg (Process B) and almost immediately returns to [Br⁻]max
  (the fast Process A excursion).
* The steady state of Process A (part 2.2) is [HBrO₂]_A = k₁[BrO₃⁻][H⁺]/(2k₃),
  which is *independent of the cerium concentrations*: within the stated model,
  added cerium can influence the switch only through the bromide flux of (7).

## Derived classifications

Equating r₁ = k₁[HBrO₂][BrO₃⁻][H⁺] with r₄ = k₄[HBrO₂][Br⁻][H⁺] and cancelling
the positive common factors (elementary rate laws, a trusted general law of
chemical kinetics) gives

[Br⁻]critical = k₁[BrO₃⁻]/k₄ = (1.0×10⁴)(0.06)/(2.0×10⁹) = 3.0×10⁻⁷ M,

and, for any [HBrO₂] > 0:  r₄ > r₁  ⟺  [Br⁻] > [Br⁻]critical.

1. Ce⁴⁺ during A: extra Ce⁴⁺ accelerates (7) (r₇ = k₇[Ce⁴⁺][BMA]), which
   produces Br⁻; Process A is sustainable only while [Br⁻] stays below
   [Br⁻]critical, so the bromide pulse forces the switch → **(c)**.
2. Ag⁺ during B: Ag⁺ removes Br⁻ by precipitation of sparingly soluble AgBr
   (ordinary chemistry / trusted general law), driving [Br⁻] toward
   [Br⁻]critical and triggering the switch → **(d)**.
3. Br⁻ during B: raising [Br⁻] moves the system away from [Br⁻]critical, so
   the slow drain lasts longer → **(b)**.
4. Continuous Br⁻ feed: [Br⁻] is held above [Br⁻]critical indefinitely, the
   B→A switch can never occur, so → **(e)**.

Final classification: 1 → c, 2 → d, 3 → b, 4 → e.
-/

namespace IChO2026.T2.A6

/-! ## Answer alphabet -/

/-- The five answer boxes (a)–(e) of question 2.6. -/
inductive Effect
  | prolongsA        -- (a) prolongs Process A
  | prolongsB        -- (b) prolongs Process B
  | switchAtoB       -- (c) Process A switches to Process B
  | switchBtoA       -- (d) Process B switches to Process A
  | oscillationsStop -- (e) oscillations stop
  deriving DecidableEq, Repr

/-- The four actions listed in question 2.6. -/
inductive Action
  | addCe4DuringA    -- action 1: small amount of Ce⁴⁺ during Process A
  | addAgDuringB     -- action 2: small amount of Ag⁺ during Process B
  | addBrDuringB     -- action 3: small amount of Br⁻ during Process B
  | feedBrContinuous -- action 4: continuous addition of Br⁻
  deriving DecidableEq, Repr

/-- Which process the reaction is currently in. -/
inductive Mode
  | A | B
  deriving DecidableEq, Repr

/-! ## Problem inputs: rate constants and fixed concentrations -/

/-- k₁ for (1) HBrO₂ + BrO₃⁻ + H⁺ → 2BrO₂⋅ + H₂O, in M⁻² s⁻¹. -/
noncomputable def k1 : ℝ := 1.0e4

/-- k₄ for (4) HBrO₂ + Br⁻ + H⁺ → 2HBrO, in M⁻² s⁻¹. -/
noncomputable def k4 : ℝ := 2.0e9

/-- k₇ for (7) Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products, in M⁻¹ s⁻¹. -/
noncomputable def k7 : ℝ := 1.0e2

/-- Maintained bromate concentration [BrO₃⁻]₀ = 0.06 M. -/
noncomputable def BrO3 : ℝ := 0.06

/-- Maintained acidity [H⁺]₀ = 0.8 M. -/
noncomputable def Hconc : ℝ := 0.8

/-- Maximum bromide reached after the fast Process A leg, [Br⁻]max = 7.0×10⁻⁴ M. -/
noncomputable def BrMax : ℝ := 7.0e-4

theorem k1_pos : 0 < k1 := by norm_num [k1]
theorem k4_pos : 0 < k4 := by norm_num [k4]
theorem k7_pos : 0 < k7 := by norm_num [k7]
theorem BrO3_pos : 0 < BrO3 := by norm_num [BrO3]
theorem Hconc_pos : 0 < Hconc := by norm_num [Hconc]
theorem BrMax_pos : 0 < BrMax := by norm_num [BrMax]

/-! ## Elementary rate laws (mass-action kinetics, trusted general law) -/

/-- Rate of step (1): r₁ = k₁[HBrO₂][BrO₃⁻][H⁺]. -/
noncomputable def r1 (X : ℝ) : ℝ := k1 * X * BrO3 * Hconc

/-- Rate of step (4): r₄ = k₄[HBrO₂][Br⁻][H⁺]. -/
noncomputable def r4 (X b : ℝ) : ℝ := k4 * X * b * Hconc

/-- Rate of step (7), the continuous bromide source: r₇ = k₇[Ce⁴⁺][BMA]. -/
noncomputable def r7 (ce bma : ℝ) : ℝ := k7 * ce * bma

/-! ## The critical bromide concentration

Derived inline from the problem's switching criterion (the T2-A3 dependency,
re-proved here from problem-only material): r₄ must exceed r₁ for Process B to
take over.  Equality of the rate laws cancels the positive factors [HBrO₂] and
[H⁺] and k₄, leaving [Br⁻]critical = k₁[BrO₃⁻]/k₄. -/

/-- The critical bromide concentration at which r₄ and r₁ balance. -/
noncomputable def BrCrit : ℝ := k1 * BrO3 / k4

theorem BrCrit_pos : 0 < BrCrit :=
  div_pos (mul_pos k1_pos BrO3_pos) k4_pos

/-- Numerical value: [Br⁻]critical = 3.0×10⁻⁷ M. -/
theorem BrCrit_value : BrCrit = 3.0e-7 := by norm_num [BrCrit, k1, k4, BrO3]

/-- The slow Process B leg starts well above the critical concentration. -/
theorem BrCrit_lt_BrMax : BrCrit < BrMax := by
  rw [BrCrit_value]; norm_num [BrMax]

/-- **Switching criterion, biconditional form.**  With [HBrO₂] > 0, step (4)
outruns step (1) exactly when [Br⁻] is above [Br⁻]critical.  The cancellation
is the content of the problem's part 2.3 instruction. -/
theorem rate4_gt_rate1_iff {X b : ℝ} (hX : 0 < X) :
    r4 X b > r1 X ↔ b > BrCrit := by
  have hh : 0 < Hconc := Hconc_pos
  unfold r4 r1 BrCrit
  have fac : ∀ a c : ℝ, a * X * c * Hconc = (a * c) * (X * Hconc) := by
    intro a c; ring
  rw [fac k4 b, fac k1 BrO3]
  have hiff : k4 * b * (X * Hconc) > k1 * BrO3 * (X * Hconc) ↔ k4 * b > k1 * BrO3 := by
    constructor
    · intro h
      exact lt_of_mul_lt_mul_right h (le_of_lt (mul_pos hX hh))
    · intro h
      exact mul_lt_mul_of_pos_right h (mul_pos hX hh)
  constructor
  · intro h
    have h' : k4 * b > k1 * BrO3 := hiff.mp h
    rw [mul_comm k4 b] at h'
    exact (div_lt_iff₀ k4_pos).mpr h'
  · intro h
    have h' : b * k4 > k1 * BrO3 := (div_lt_iff₀ k4_pos).mp h
    rw [mul_comm b k4] at h'
    exact hiff.mpr h'

/-- Once [Br⁻] is above critical, Process B must take over (A → B switch). -/
theorem above_crit_forces_B {X b : ℝ} (hX : 0 < X) (hb : BrCrit < b) :
    r4 X b > r1 X :=
  (rate4_gt_rate1_iff hX).mpr hb

/-- While [Br⁻] is below critical, Process A outruns the bromide inhibition
(B → A switch territory): r₁ > r₄. -/
theorem below_crit_forces_A {X b : ℝ} (hX : 0 < X) (hb : b < BrCrit) :
    r1 X > r4 X b := by
  have hb' : b < k1 * BrO3 / k4 := hb
  have hmul : b * k4 < k1 * BrO3 := (lt_div_iff₀ k4_pos).mp hb'
  have hpos : 0 < X * Hconc := mul_pos hX Hconc_pos
  have hprod : (k1 * BrO3 - b * k4) * (X * Hconc) > 0 := mul_pos (sub_pos.mpr hmul) hpos
  have e : r1 X - r4 X b = (k1 * BrO3 - b * k4) * (X * Hconc) := by
    unfold r1 r4; ring
  have hgap : r1 X - r4 X b > 0 := e.symm ▸ hprod
  linarith

/-! ## Perturbation chemistry, proved at the rate level -/

/-- Adding Ce⁴⁺ strictly increases the continuous bromide production rate (7),
since r₇ = k₇[Ce⁴⁺][BMA] is strictly monotone in [Ce⁴⁺] for [BMA] > 0. -/
theorem ce4_raises_bromide_flux {ce ce' bma : ℝ}
    (hbma : 0 < bma) (h : ce < ce') : r7 ce bma < r7 ce' bma := by
  unfold r7
  have h1 : k7 * ce < k7 * ce' := mul_lt_mul_of_pos_left h k7_pos
  exact mul_lt_mul_of_pos_right h1 hbma

/-- A perturbation that *removes* bromide strictly lowers free [Br⁻]
(model content of AgBr precipitation). -/
theorem bromide_removal_lowers_level {b Δb : ℝ} (h : 0 < Δb) : b - Δb < b :=
  sub_lt_self b h

/-- A perturbation that *adds* bromide strictly raises [Br⁻]. -/
theorem bromide_addition_raises_level {b Δb : ℝ} (h : 0 < Δb) : b < b + Δb :=
  lt_add_of_pos_right b h

/-- During Process B the system drains bromide from [Br⁻]max toward
[Br⁻]critical: removing bromide moves the system strictly closer to the
B → A switch point. -/
theorem removal_hastens_switch_from_B {b Δb : ℝ}
    (hpos : 0 < Δb) : b - Δb - BrCrit < b - BrCrit ∧ b - Δb < b :=
  ⟨by linarith, bromide_removal_lowers_level hpos⟩

/-- During Process B, adding bromide strictly increases the distance to
[Br⁻]critical, so the drain (and hence Process B) lasts longer. -/
theorem addition_delays_switch_from_B {b Δb : ℝ} (hpos : 0 < Δb) :
    b + Δb - BrCrit > b - BrCrit := by
  have := hpos; linarith

/-! ## The qualitative switch model

The problem stipulates a single switching law:
Process B takes over exactly when r₄ > r₁, equivalently [Br⁻] > [Br⁻]critical,
and Process A resumes when r₁ > r₄, equivalently [Br⁻] < [Br⁻]critical.

* During Process A, [Br⁻] is below [Br⁻]critical and is being pushed upward
  (Process C continuously produces Br⁻).  A perturbation that accelerates
  bromide production triggers the A → B switch.
* During Process B, [Br⁻] drains from [Br⁻]max toward [Br⁻]critical, where the
  B → A switch fires.  Removing bromide advances (triggers) that switch;
  adding bromide retreats from it (Process B lasts longer); feeding bromide
  continuously keeps [Br⁻] above critical forever. -/

/-- Classification handle for the bromide-balance effect of a perturbation:

* `increasesFluxDuringA` — extra Br⁻ source strength while in Process A.
* `removesBrDuringB` — free Br⁻ lowered while in Process B.
* `addsBrDuringB` — free Br⁻ raised while in Process B.
* `maintainsBrAboveCrit` — continuous feed pinning [Br⁻] above critical. -/
inductive BrEffectOnBalance
  | increasesFluxDuringA
  | removesBrDuringB
  | addsBrDuringB
  | maintainsBrAboveCrit
  deriving DecidableEq, Repr

/-- The classification function induced by the problem's threshold rule. -/
def classify : BrEffectOnBalance → Effect
  | .increasesFluxDuringA => .switchAtoB
  | .removesBrDuringB     => .switchBtoA
  | .addsBrDuringB        => .prolongsB
  | .maintainsBrAboveCrit => .oscillationsStop

/-- Each perturbation ticks exactly one box. -/
theorem classify_unique (p : BrEffectOnBalance) :
    ∃! e : Effect, classify p = e :=
  ⟨classify p, rfl, fun _ h => h.symm⟩

/-- The four actions of question 2.6 map onto their bromide-balance effects:

1. Ce⁴⁺ is consumed by the continuous step (7), Ce⁴⁺ + BMA → Ce³⁺ + Br⁻;
   with [BMA] > 0 this strictly raises the bromide production rate
   (`ce4_raises_bromide_flux`), so during Process A it pushes [Br⁻] up to
   [Br⁻]critical.  (In the problem's stated steady state, [HBrO₂]_A does not
   depend on cerium at all, so this bromide channel is the only way the added
   Ce⁴⁺ can influence the switch.)
2. Ag⁺ precipitates bromide as AgBr(s), removing free Br⁻ during Process B.
3. Added Br⁻ directly raises [Br⁻] during Process B.
4. A continuous Br⁻ feed maintains [Br⁻] above [Br⁻]critical. -/
def balanceEffectOf : Action → BrEffectOnBalance
  | .addCe4DuringA    => .increasesFluxDuringA
  | .addAgDuringB     => .removesBrDuringB
  | .addBrDuringB     => .addsBrDuringB
  | .feedBrContinuous => .maintainsBrAboveCrit

/-- The ticked box for each action. -/
def answerOf (a : Action) : Effect := classify (balanceEffectOf a)

/-! ## Final classification theorems (the four requested outputs) -/

/-- **Action 1** (small amount of Ce⁴⁺ during Process A): the extra Ce⁴⁺ is
drawn into the continuous step (7), whose bromide output pushes [Br⁻] to
[Br⁻]critical, where r₄ > r₁; **Process A switches to Process B — box (c).** -/
theorem answer_action1 : answerOf .addCe4DuringA = .switchAtoB := rfl

/-- **Action 2** (small amount of Ag⁺ during Process B): AgBr precipitation
removes free Br⁻, so [Br⁻] reaches [Br⁻]critical and r₁ overtakes r₄;
**Process B switches to Process A — box (d).** -/
theorem answer_action2 : answerOf .addAgDuringB = .switchBtoA := rfl

/-- **Action 3** (small amount of Br⁻ during Process B): the raised bromide
level is farther from [Br⁻]critical, so the drain phase lasts longer;
**Process B is prolonged — box (b).** -/
theorem answer_action3 : answerOf .addBrDuringB = .prolongsB := rfl

/-- **Action 4** (continuous addition of Br⁻): [Br⁻] is pinned above
[Br⁻]critical, r₄ > r₁ holds for good, the B → A switch never fires;
**the oscillations stop — box (e).** -/
theorem answer_action4 : answerOf .feedBrContinuous = .oscillationsStop := rfl

/-- All four ticked boxes are distinct; exactly one box is ticked per case. -/
theorem answers_all_distinct :
    answerOf .addCe4DuringA ≠ answerOf .addAgDuringB ∧
    answerOf .addCe4DuringA ≠ answerOf .addBrDuringB ∧
    answerOf .addCe4DuringA ≠ answerOf .feedBrContinuous ∧
    answerOf .addAgDuringB ≠ answerOf .addBrDuringB ∧
    answerOf .addAgDuringB ≠ answerOf .feedBrContinuous ∧
    answerOf .addBrDuringB ≠ answerOf .feedBrContinuous := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The complete answer grid of question 2.6: 1 → c, 2 → d, 3 → b, 4 → e. -/
theorem answer_summary :
    answerOf .addCe4DuringA = .switchAtoB ∧
    answerOf .addAgDuringB = .switchBtoA ∧
    answerOf .addBrDuringB = .prolongsB ∧
    answerOf .feedBrContinuous = .oscillationsStop :=
  ⟨answer_action1, answer_action2, answer_action3, answer_action4⟩

/-! ## Semantic checks: each classification is backed by its kinetic fact -/

/-- The kinetic fact behind answer 1: adding Ce⁴⁺ during Process A strictly
increases the bromide source (7), and at any bromide level above critical —
in particular at [Br⁻]max — the problem's criterion gives r₄ > r₁, i.e. the
mandated A → B switch. -/
theorem action1_chemistry {ce ce' bma X : ℝ}
    (hbma : 0 < bma) (hce : ce < ce') (hX : 0 < X) :
    r7 ce bma < r7 ce' bma ∧ r4 X BrMax > r1 X :=
  ⟨ce4_raises_bromide_flux hbma hce,
   above_crit_forces_B hX BrCrit_lt_BrMax⟩

/-- The kinetic fact behind answer 2: removing Br⁻ (AgBr precipitation) down
to [Br⁻]critical or below puts the system in r₁ ≥ r₄ territory, i.e. the
B → A switch. -/
theorem action2_chemistry {b X : ℝ}
    (hX : 0 < X) (hb : b < BrCrit) :
    r1 X > r4 X b :=
  below_crit_forces_A hX hb

/-- The kinetic fact behind answer 3: adding Br⁻ during Process B strictly
raises the remaining distance to the switch threshold, lengthening the drain
that defines Process B's duration. -/
theorem action3_chemistry {b Δb : ℝ} (hΔ : 0 < Δb) :
    b - BrCrit < b + Δb - BrCrit :=
  addition_delays_switch_from_B hΔ

/-- The kinetic fact behind answer 4: as long as the feed keeps [Br⁻] above
critical, Process B's rate dominance r₄ > r₁ never lapses, so no switch back
to A — and hence no further oscillation — can occur. -/
theorem action4_chemistry {X b : ℝ} (hX : 0 < X) (hb : BrCrit < b) :
    r4 X b > r1 X :=
  above_crit_forces_B hX hb

end IChO2026.T2.A6

#print axioms IChO2026.T2.A6.answer_action1
#print axioms IChO2026.T2.A6.answer_action2
#print axioms IChO2026.T2.A6.answer_action3
#print axioms IChO2026.T2.A6.answer_action4
#print axioms IChO2026.T2.A6.answer_summary
#print axioms IChO2026.T2.A6.rate4_gt_rate1_iff
#print axioms IChO2026.T2.A6.action1_chemistry
