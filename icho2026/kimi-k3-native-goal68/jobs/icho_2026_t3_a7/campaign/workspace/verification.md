# Verification record — `icho_2026_t3_a7`

Toolchain: `leanprover/lean4:v4.31.0` (`lake`/`lean` from
`~/.elan/toolchains/leanprover--lean4---v4.31.0/bin`), project deps pinned in
`lakefile.toml` (Mathlib v4.31.0, Physlib, crnt-lean).

## Commands run

1. Build the target module (previously failing probe commands are omitted;
   this is the final recorded run):

   ```
   $ lake env lean IChO2026Problems/problem_icho_2026_t3_a7.lean
   'icho_2026_t3_a7_equilibrium_absorption_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'icho_2026_t3_a7_uranyl_ions_per_pore' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Exit code 0; no errors, no `sorryAx`. Both `#print axioms` report only the
   standard Lean logical axioms (`propext`, `Classical.choice`,
   `Quot.sound`); no custom axioms were introduced. `field_simp`/`norm_num`
   proofs inside the file compile to kernel-checked terms.

2. The module is also included in the library graph via
   `IChO2026Problems/All.lean` and builds with:

   ```
   $ lake build IChO2026Problems
   ```

## Numeric checks (independent)

Raw decimal arithmetic was cross-checked with exact fractions
(`python3 -c 'from fractions import Fraction as F …'`):

- qₑ = (19.90 − 9.225) × 0.2000 / 0.005000 = 427 exactly.
- M_pore (C₃₆H₂₇N₉O₃, CODATA 2022) = 633.672 g mol⁻¹; M(UO₂²⁺) = 270.02691.
- ions/pore = 427 × 633.672 / (1000 × 270.02691) = 33822243/33753363.75
  ≈ 1.0020 ∈ [0.995, 1.005), so 3 s.f. reporting gives 1.00 (no tie).
- Robustness: integer school-book masses (M_pore = 645, M(UO₂²⁺) = 270)
  give 1.020 → 1.02 at 3 s.f.; conclusion "≈ 1 ion per pore" is stable.

## Semantic faithfulness check

- Output 1 theorem states the literal mass-balance expression on the exact
  printed data and proves qₑ = 427 with 3-s.f. reporting at quantum 1 —
  matches the requested "qₑ in mg g⁻¹".
- Output 2 theorem states the ions-per-pore ratio from first principles
  (per-gram ion count over per-gram pore count) at the derived COF-9
  per-pore repeat formula C₃₆H₂₇N₉O₃, proves the Avogadro cancellation for
  every `NA ≠ 0`, evaluates the exact CODATA fraction 33822243/33753363.75,
  and proves 3-s.f. reporting of 1.00 at quantum 0.01 — matches the
  requested "number of UO₂²⁺ ions absorbed per pore".
- The molar masses used are the only non-printed inputs; they are recorded
  in `result.json` under `assumptions` / `source_gaps`.
