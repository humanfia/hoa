# Verification record — icho_2026_t5_a4

## Environment

- Workspace: `/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t5_a4/campaign/workspace`
- Lean toolchain: the repo-pinned toolchain in `lean-toolchain`, run via
  `export PATH="$HOME/.elan/bin:$PATH"` and `lake env lean`.
- `IChO2026Chem` library olean built earlier with `lake build IChO2026Chem`.

## Exact commands and results

### 1. Compile the formalization

```
export PATH="$HOME/.elan/bin:$PATH"
lake env lean IChO2026Problems/problem_icho_2026_t5_a4.lean
```

Result (2026-09-14): exit code 0, **no output** — no errors, no warnings,
no `sorry`/`admit` diagnostics.

### 2. Axiom inspection

A scratch copy of the file was extended with:

```
#print axioms IChO2026.T5_A4.subquestion_5_4_answer
#print axioms IChO2026.T5_A4.x_is_IBr
#print axioms IChO2026.T5_A4.xAdduct_residual_eq
#print axioms IChO2026.T5_A4.halogen_forced_bromine
#print axioms IChO2026.T5_A4.multivalent_residuals_not_halogen
#print axioms IChO2026.T5_A4.robust_to_measurement_quantum
#print axioms IChO2026.T5_A4.acid_carbonCount_forced
#print axioms IChO2026.T5_A4.iodine_mass_in_window
```

and compiled with `lake env lean`. Result: every theorem reports

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. only the standard Lean logical axioms. **No custom axioms.**

### 3. Independent numerical cross-checks

The arithmetic encoded in the theorems was independently recomputed with a
hand calculator / Python before encoding:

- M(RCOOH) = 100·2·2·126.904/181.0 = 253808/905 = 280.45083 g/mol.
- Fatty-acid lattice at k = 2: M(c,2) = 14.027·c + 42.000; c = 17 gives
  280.452 (linoleic, C₁₈H₃₂O₂); c = 16 → 266.425 and c = 18 → 294.479, both
  ≥ 13.9 g/mol away — far outside the ±0.7 g/mol iodine window.
- Back-check: 100·2·2·126.904/280.452 = 180.9992 g ∈ 181.0 ± 0.05 g.
- Required residual: 126.904·(100/36.57 − 1) − 280.45083/2
  = 6609842429/82739625 = 79.887266 g/mol; |79.887266 − 79.904| = 0.0167.
- Predicted iodine fractions (residual given → w(I)):
  F: 44.3507 %; Cl: 41.9398 %; Br: 36.5682 %; I: 32.2098 %;
  At: 26.6028 %; measured 36.57 ± 0.005 % → only Br within window
  (0.35 half-quanta; others 872–1994 half-quanta).
- Multivalent residuals 79.887266/v for v = 2, 3, 5 → 39.94, 26.63, 15.98:
  each ≥ 4 g/mol from any halogen standard mass.
- Robustness corners: sliding m(I₂) ∈ [180.95, 181.05] and w ∈ [36.565,
  36.575] % keeps required residual in (79.327, 80.449) — only Br (79.904)
  is inside.

### 4. Semantic faithfulness check

- The final theorem `subquestion_5_4_answer` states existence of a
  monovalent reagent X = I–R′ whose residual mass matches bromine's
  standard mass within the measurement window, and proves (via
  `halogen_forced_bromine`) that bromine is the *unique* halogen with that
  property — i.e. the formal content "X = IBr" requested by the problem.
- All printed numbers (100 g, 181.0 g, 36.57 %) appear as definitionally
  exact measured data; tolerances were derived from the ±½-last-quantum
  measurement policy rather than invented.
- No `sorry`, `admit`, custom axioms, or external answer sources used.
