# Verification record — icho_2026_t2_a6

## Command run (exact)

```
cd /home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t2_a6/campaign/workspace
timeout 1800 lake env lean IChO2026Problems/problem_icho_2026_t2_a6.lean
```

Toolchain: `leanprover/lean4:v4.31.0` (lean-toolchain), Lake 5.0.0-src,
Mathlib v4.31.0 (pinned in lakefile.toml / lake-manifest.json).

## Result

Exit code 0. No errors, no warnings (in particular no `sorry`/`admit`
anywhere in the file). Full output:

```
'IChO2026.T2.A6.answer_action1' does not depend on any axioms
'IChO2026.T2.A6.answer_action2' does not depend on any axioms
'IChO2026.T2.A6.answer_action3' does not depend on any axioms
'IChO2026.T2.A6.answer_action4' does not depend on any axioms
'IChO2026.T2.A6.answer_summary' does not depend on any axioms
'IChO2026.T2.A6.rate4_gt_rate1_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T2.A6.action1_chemistry' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The classification theorems (`answer_action1` … `answer_action4`,
`answer_summary`) are pure definitional computations over the derived switch
model and depend on **no axioms at all**. The quantitative and kinetic
lemmas (`rate4_gt_rate1_iff`, `above_crit_forces_B`, `below_crit_forces_A`,
`BrCrit_value`, `BrCrit_lt_BrMax`, `ce4_raises_bromide_flux`, …) depend only
on the standard Lean logical axioms `propext`, `Classical.choice`,
`Quot.sound`. No custom/unchecked axioms anywhere; `sorryAx` does not appear.

`#print axioms` commands are embedded at the end of the Lean source itself,
so the reported axiom sets above are produced by the same compile run.

## Semantic faithfulness check (independent of build success)

* Theorem statements encode the *problem's own* criterion: `rate4_gt_rate1_iff`
  states r₄ > r₁ ⟺ [Br⁻] > [Br⁻]critical for [HBrO₂] > 0, with the elementary
  rate laws r₁ = k₁[HBrO₂][BrO₃⁻][H⁺], r₄ = k₄[HBrO₂][Br⁻][H⁺] written out as
  definitions using the printed constants (k₁ = 1.0×10⁴, k₄ = 2.0×10⁹,
  [BrO₃⁻]₀ = 0.06 M, [H⁺]₀ = 0.8 M).
* `BrCrit_value` proves [Br⁻]critical = 3.0×10⁻⁷ M (the T2-A3 dependency,
  derived inline from problem-only material; consistent with the part 2.3
  fallback 1×10⁻⁷ M in the sense that no conclusion changes).
* `BrCrit_lt_BrMax` proves 3.0×10⁻⁷ < 7.0×10⁻⁴, grounding the "slow drain
  from [Br⁻]max to [Br⁻]critical" leg used for actions 2–4.
* `ce4_raises_bromide_flux` proves r₇ = k₇[Ce⁴⁺][BMA] is strictly increasing
  in [Ce⁴⁺] — the only channel by which cerium can affect the switch, since
  the part 2.2 steady state [HBrO₂]_A = k₁[BrO₃⁻][H⁺]/(2k₃) is
  cerium-independent.
* Each action is mapped (definition `balanceEffectOf`) to its signed effect
  on the bromide balance — increase during A (Ce⁴⁺ via (7)), removal during
  B (Ag⁺ via AgBr), addition during B (Br⁻), continuous pinning above
  critical — and `classify` applies the problem's threshold rule. The final
  theorems `answer_action1 … answer_action4` evaluate to the ticks
  c, d, b, e respectively, matching answer.md.
* Backing kinetic facts per action are stated and proved as
  `action1_chemistry … action4_chemistry`, tying each classification to a
  proved rate/level statement rather than to the classifier alone.

## One-box-per-case format

`classify_unique` proves each perturbation class ticks exactly one box, and
the blank answer sheet A2-5 (located in theory_problem.pdf, page A2-5)
confirms the required grid format (rows 1–4, columns a–e).
