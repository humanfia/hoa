# Verification record — icho_2026_t8_a10

## Sources inspected (problem-only inputs)

- `icho_2026_source/raw/theory_problem.pdf`, PDF page 76 (printed page Q8-5):
  question 8.10 text, options a/b/c, the quenching reactions with
  `k_S = 2.7 × 10⁹ M⁻¹ s⁻¹`, `k_T = 1.5 × 10⁸ M⁻¹ s⁻¹`, and
  `τ₀(S1) = 2.9 ns`, `τ₀(T1) = 84 µs` ("emission lifetime in the absence of the
  quencher").
- `icho_2026_source/image/T8_page-5.png`: rendered version of the same page,
  including the Jablonski diagram with quenching channels `k_S`, `k_T`.
- `icho_2026_source/image/T8_page-4.png`: page Q8-4 (context for 8.8).
- `theory_problem.pdf` PDF page 83 (printed page A8-7): blank student answer
  sheet — for 8.10 there is exactly one tick row with a single set of boxes
  `a ☐  b ☐  c ☐`, i.e. one answer applying to both S1 and T1.

No official solutions, marking schemes, or answer repositories were consulted.

## Commands and results

Run from the workspace root
(`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t8_a10/campaign/workspace`):

1. `lake build IChO2026Chem`
   (one-time build of the shared infrastructure the target file imports)
   Result: `Build completed successfully (8561 jobs).`

2. `lake env lean IChO2026Problems/problem_icho_2026_t8_a10.lean`
   Result: exit code 0, **no errors, no warnings**. The only output is the
   four requested `#print axioms` reports:

   ```
   'IChO2026Problems.answer_T8_A10' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026Problems.lifetime_s1' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026Problems.lifetime_t1' depends on axioms: [propext, Classical.choice, Quot.sound]
   'IChO2026Problems.sternVolmerLifetime_strictAntiOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Only the three standard Lean logical axioms appear; `sorryAx` is absent, and
   a source scan confirms no `sorry`/`admit`/custom `axiom`/`unsafe` in the
   file.

## Semantic faithfulness check (independent of the successful build)

- The theorem `sternVolmerLifetime_strictAntiOn` states strict antitonicity of
  the Stern–Volmer lifetime `τ₀ / (1 + K·[Red])` on `[0, ∞)` for positive
  `τ₀, K` — the physical domain of concentrations. The model is grounded by
  the problem-printed quenching rate constants and by the Q8.9 quenching
  formalism (η_q = 1 − τ/τ₀); Stern–Volmer lifetime quenching is a trusted
  general photophysical law.
- `KS_val : KS = 7.83` and `KT_val : KT = 12600` tie the formal constants
  `k_S·τ₀(S1)` and `k_T·τ₀(T1)` numerically to the printed data
  (2.7e9 × 2.9e-9 = 7.83 M⁻¹; 1.5e8 × 84e-6 = 1.26 × 10⁴ M⁻¹).
- `tauS1_strictAntiOn` and `tauT1_strictAntiOn` instantiate the general theorem
  with exactly the printed constants `k_S, τ₀(S1)` and `k_T, τ₀(T1)`.
- `lifetime_s1` / `lifetime_t1` (combined in `answer_T8_A10`, alias
  `icho_2026_t8_a10_answer`) evaluate the classification to
  `LifetimeTrend.decreases` for **both** S1 and T1, i.e. tick box
  **b) decreases**, matching the answer derived in `answer.md` and the
  single-box answer-sheet layout on page A8-7.

## Notes

- Requested outputs are classifications (`exact_symbolic`), so no rounding or
  display quantum applies; the project-wide reporting conventions in
  `IChO2026Chem.Reporting` are not needed here.
- The answer sheet shows one shared tick row for 8.10, and both states have the
  same trend, so a single answer (b) is the faithful formalization.
