# Verification record — `icho_2026_t6_a7`

## Environment

* Lean toolchain: `leanprover/lean4:v4.31.0` (from `lean-toolchain`), Lean 4.31.0.
* Project: `lakefile.toml` requires Mathlib `v4.31.0`, Physlib, crnt-lean;
  dependency oleans pre-fetched under `.lake/packages` (Mathlib 6.9 GiB with
  prebuilt `build/lib/lean` oleans).

## Commands executed and results

### 1. Type-check of the formalisation

```
$ lake env lean IChO2026Problems/problem_icho_2026_t6_a7.lean
```

Result: **exit code 0**, no errors and no warnings (after one development
iteration; an earlier draft used `let`-bound names in a `refine` pattern that
left opaque goals and introduced `sorryAx`; this was removed by spelling the
definitions directly, and re-verified below).

### 2. Axiom audit (output printed by the same command)

The file ends with four `#print axioms` commands; observed output:

```
'IChO2026T6A7.minimum_electrons_removed' depends on axioms: [propext, Quot.sound]
'IChO2026T6A7.global_pi_electron_count' depends on axioms: [propext, Quot.sound]
'IChO2026T6A7.p6_neutral_not_globally_aromatic' depends on axioms: [propext, Quot.sound]
'IChO2026T6A7.huckelLabel_aromatic_disjoint_antiaromatic' depends on axioms: [propext, Quot.sound]
```

Only standard Lean logical axioms (`propext`, `Quot.sound`) appear — no
`sorryAx`, no custom unchecked axioms. (`Classical.choice` is not even
needed.) A workspace-wide `grep` confirms the file contains no
`sorry`/`admit`/`axiom` declarations.

### 3. What the theorems state (semantic-faithfulness check)

* `minimum_electrons_removed : residualCount p6Units p6PathwayDoublesPerUnit 2 = 82
  ∧ HuckelAromaticCountN … ∧ HuckelAromaticCountZ …
  ∧ (∀ nE' < 2, ¬ HuckelAromaticCountN (residualCount … nE'))`
  — states that removing **2** electrons from P6 leaves **82** π electrons,
  that 82 is 4·20 + 2 (Hückel-aromatic, in both ℕ and ℤ formulations), and
  that the removals 0 and 1 (leaving 84 and 83) are *not* aromatic: n(e) = 2
  is the genuine minimum.
* `global_pi_electron_count` — states 82 is Hückel-aromatic, equals
  `residualCount … 2`, and is the largest Hückel-aromatic count below the
  neutral 84, pinning n(t) = 82 independently of the oxidation framing.
* `p6_neutral_count` / `p6_neutral_not_globally_aromatic` — the problem-input
  layer: per-unit pathway count 7 double-bond equivalents (3 porphyrin-rim
  C=C + 2 bridges × 2 alkyne doubles) × 6 units × 2 e⁻ = 84; 84 = 4·21 is
  anti-aromatic, matching the problem statement that neutral P6 exhibits
  global anti-aromaticity.
* `residual_4e_antiaromatic` — 80 = 4·20 cross-check.

Problem inputs (ring size 6, 7 pathway double-bond equivalents per porphyrin,
Hückel's 4k+2/4k rule) are separated from derived lemmas in §2 vs §1/§3 of
the Lean file, and are documented line-by-line in `answer.md`. No condition
used is ungrounded in the problem text; no source gap was found (the P6
structure and the counting rule are both given to the student).

### 4. Numerical sanity checks performed in `answer.md`

84 = 6 × 14; 84 = 4×21 (anti-aromatic); 83 irregular; 82 = 4×20+2
(aromatic); 80 = 4×20 (anti-aromatic). Minimum removal = 84 − 82 = 2.
