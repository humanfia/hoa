# Verification record — `icho_2026_t8_a9` (IChO 2026 T8, subquestion 8.9)

## Build environment

* Lean toolchain: `leanprover/lean4:v4.31.0` (`lean-toolchain`)
* Lake 5.0.0-src+68218e8 (Lean 4.31.0)
* Pinned dependencies: Mathlib v4.31.0, Physlib
  `1706ae68b63996f1d97717e672e50c9e3933d933`, crnt-lean
  `99137993e729c8add247388718a22a0e0f393dab` (all pre-built in `.lake/packages`).

## Commands executed and results

1. Build the shared chemistry infrastructure (needed once so that
   `import IChO2026Chem` resolves):

   ```
   $ lake build IChO2026Chem
   ✔ [8561/8561] Built IChO2026Chem
   Build completed successfully (8561 jobs).
   ```

2. Compile the final target file and print the axiom dependencies of all
   final theorems:

   ```
   $ lake env lean IChO2026Problems/problem_icho_2026_t8_a9.lean
   ```

   Exit code 0.  The only diagnostic is one style linter warning about the
   explicit model hypothesis `hpop` being definitionally true
   (`unusedVariables`); it is semantically the kinetic model specification and
   intentionally kept.  Full output:

   ```
   IChO2026Problems/problem_icho_2026_t8_a9.lean:155:5: warning: Variable name `hpop` is not explicitly referenced.
   'IChO2026.ProbT8A9.quenchingPercentage_S1' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.ProbT8A9.quenchingPercentage_T1' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.ProbT8A9.fractionQuenched_of_competingChannels' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.ProbT8A9.validSubmission_S1' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026.ProbT8A9.validSubmission_T1' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   All five inspected theorems depend only on the standard Lean logical axioms
   `propext`, `Classical.choice`, `Quot.sound`.  No `sorryAx`, no custom
   unchecked axioms, no `unsafe`/`admit` anywhere (a `grep -n
   "sorry\|admit\|unsafe\|axiom "` of the final file returns nothing).

## What is proved (faithfulness audit)

* `fractionQuenched_of_competingChannels`: the physics is *derived*, not
  asserted.  For the model population `N(t) = N₀·exp(−(k₀+kq)t)` the fraction of
  the initial population consumed by the quenching channel,
  `(∫₀^∞ kq·N(t) dt) / N₀`, is proved equal to `kq/(k₀+kq)` using
  FTC-2 on `(0,∞)` (`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'`),
  differentiability of the exponential decay, its limit 0 at +∞, and its
  integrability.  This is exactly the competing-channels (Stern–Volmer)
  quenching probability that problem 8.9 asks to evaluate.
* `quenchingPercentage_S1`: instantiated with problem-printed data
  (k_S = 2.7×10⁹ M⁻¹ s⁻¹, [Red] = 0.1 M, τ₀(S₁) = 2.9 ns) the quenching
  percentage equals the exact rational `78300/1783` % = 43.9147… %,
  reporting to **43.9 %** at 3 significant figures.
* `quenchingPercentage_T1`: with k_T = 1.5×10⁸ M⁻¹ s⁻¹, [Red] = 0.1 M,
  τ₀(T₁) = 84 μs the percentage equals `126000/1261` % = 99.9207… %,
  reporting to **99.9 %** at 3 significant figures.
* Ordering facts `η_q(S₁) < 100`, `η_q(T₁) > 99`, `η_q(T₁) > η_q(S₁)` are
  proved as consistency checks of the chemistry (triplet essentially fully
  quenched, singlet only partly).
* `validSubmission_S1`/`validSubmission_T1`: both raw answers and their 3-s.f.
  displays (quantum 0.1 %) satisfy the project-wide answer-blind reporting
  contract `IChO2026Chem.Reporting.ValidNumericSubmission`
  (nearest multiple of the quantum, ties half away from zero).

## Semantic check against the requested chemistry

* Requested outputs from `TASK.json`: numeric percentage quenching of S₁ and
  of T₁ states (unit %, 3 significant figures).  Both are given, exact raw
  values plus reported displays.
* No `previous_parts` are needed (none listed); no other subquestion result is
  consumed as input.
* Measurement policy: all printed constants are stipulated, hence treated as
  exact; no intermediate rounding was performed (all arithmetic is exact
  rational until the reporting boundary).
* Sources used: only `icho_2026_source/image/T8_page-5.png` (question page) and
  the corresponding text in `TASK.json`/`theory_problem.pdf`.  No official
  solutions, marking schemes, grading reports, or answer repositories were
  accessed.

Note: the umbrella `IChO2026Problems.lean` (shared run infrastructure, not part
of this target) imports `IChO2026Problems.All`, which is rewritten by the
trusted controller and is not present in this workspace; per task instructions
the target is verified directly with `lake env lean` on the final file, which
succeeds as recorded above.
