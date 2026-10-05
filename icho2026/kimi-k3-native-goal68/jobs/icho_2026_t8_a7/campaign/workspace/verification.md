# Verification record — IChO 2026 T8-A7 (icho_2026_t8_a7)

All commands executed from the workspace root
(`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t8_a7/campaign/workspace`)
on 2026-09-14, with the pinned toolchain `leanprover/lean4:v4.31.0`.

## 1. Direct compilation of the final file (required command)

Command:

    lake env lean IChO2026Problems/problem_icho_2026_t8_a7.lean

Result: exit code 0.  Full stdout/stderr:

    'IChO2026.T8.A7.co_rate_trend' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026.T8.A7.measured_rates_increase_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026.T8.A7.endpoint_rate_increases_robust' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026.T8.A7.last_step_direction_not_determined' depends on axioms: [propext, Classical.choice, Quot.sound]

Interpretation: the file compiles with **no errors, no warnings, and no
`sorryAx`**.  The four `#print axioms` lines show that every final theorem
depends only on the standard Lean logical axioms (`propext`,
`Classical.choice`, `Quot.sound`).  No custom or unchecked axioms are used.

## 2. Full library build (Project umbrella)

Commands:

    lake build IChO2026Chem        # builds shared chemistry infrastructure (8561 jobs)
    lake build IChO2026Problems    # builds IChO2026Problems/All.lean + target file

Result for `IChO2026Problems`: exit code 0 — "Build completed successfully
(8564 jobs).  Built IChO2026Problems (12 s)".  The only warning is a
pre-existing style-linter note in the generic, controller-owned umbrella
`IChO2026Problems.lean` (line > 100 chars); that file is part of the fixed
infrastructure and was not modified.

## 3. Semantic faithfulness audit

* Requested output: classification of the trend of the CO formation rate per
  gram of loaded C₃N₄ as ω_cat increases (boxes a/b/c).
* Theorem `co_rate_trend : tickedBox = RateTrend.increases ∧ coRatePerGram
  0.1 62 < coRatePerGram 3.8 8` states exactly: (i) the ticked box is
  "increases" (value-level, `rfl`-checked) and (ii) the rate at the highest
  measured loading strictly exceeds the rate at the lowest measured loading.
* `coRatePerGram` is defined from **problem-stated inputs only**:
  TOF definition (Q8-2 text), mass fraction → catalyst molecules per gram via
  N_A (constants page G1-3) and M_cat (8.5).  No empirical rate law is
  assumed.
* The seven data points used are read from the diagram on Q8-3 and are
  double-anchored by the text statement "TOF of 8 h⁻¹ ... with ω_cat = 3.8%"
  on Q8-2, which coincides with the final point of the diagram.
* Honesty about limits of the source: the theorem
  `last_step_direction_not_determined` proves that the small final displayed
  dip (31.9 → 30.4 %·h⁻¹) is not sign-determined within the integer-display
  tolerance.  The classification answer rests on
  `endpoint_rate_increases_robust` plus the strict interior chain
  `measured_rates_increase_interior`, not on that final step.

## 4. Prohibited-action audit

* `sorry` / `admit` / `axiom` / unsafe declarations: none present
  (confirmed by clean `#print axioms` output above and by grep:
  `rg -n 'sorry|admit|^axiom|axiom ' IChO2026Problems/problem_icho_2026_t8_a7.lean`
  yields no matches).
* Source inputs and generic infrastructure untouched: only
  `IChO2026Problems/problem_icho_2026_t8_a7.lean`,
  `IChO2026Problems/All.lean` (single import line as required for the
  library target), `answer.md`, `verification.md`, and `result.json`
  were created/edited.
* No official solutions, marking schemes, external solver agents, or answer
  repositories consulted; no external writes performed.
