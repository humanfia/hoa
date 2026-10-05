# Verification record — icho_2026_t1_a5 (T1-A5)

## Build command

Run from the workspace root
(`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t1_a5/campaign/workspace`):

```
lake env lean IChO2026Problems/problem_icho_2026_t1_a5.lean
```

Result: **exit code 0 — no errors.** The only output is linter warnings
(deprecated `Symmetric`/`Irreflexive`/`push_neg` names and unused simp
arguments); none are errors and none affect soundness.

## Axiom audit

The file ends with the block

```
#print axioms structures_EFG
#print axioms empirical_formula_E
#print axioms empirical_formula_G
#print axioms empirical_ratio_E
#print axioms empirical_ratio_G
#print axioms hexamethylbenzene_axis
#print axioms melliticAcid_axis
#print axioms melliticTrianhydride_axis
#print axioms E_hydrogen_fraction
#print axioms G_oxygen_fraction
```

Observed output of the build (verbatim, diagnostics from stdout/stderr
combined):

```
'IChO2026T1A5.structures_EFG' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A5.empirical_formula_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A5.empirical_formula_G' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A5.empirical_ratio_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A5.empirical_ratio_G' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A5.hexamethylbenzene_axis' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A5.melliticAcid_axis' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A5.melliticTrianhydride_axis' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A5.E_hydrogen_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T1A5.G_oxygen_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every final theorem depends **only** on the three standard logical axioms
of Lean's kernel (`propext`, `Classical.choice`, `Quot.sound`). No
`sorryAx`, no `native_decide` trusted-computation axioms
(`Lean.ofReduceBool`/`._native.*`), no custom axioms appear anywhere.

Additional audit commands and results:

```
grep -nE "sorry|admit|native_decide" IChO2026Problems/problem_icho_2026_t1_a5.lean
```
→ matches nothing (no unsafe shortcuts anywhere in the file).

```
grep -n '^axiom' IChO2026Problems/problem_icho_2026_t1_a5.lean
```
→ matches nothing: 0 custom axioms declared.

## Environment

- Lean toolchain: `leanprover/lean4:v4.31.0` (from `lean-toolchain`)
- Dependencies pinned in `lake-manifest.json` (Mathlib etc., prebuilt under
  `.lake/packages/*/`.lake/build/lib/lean)
- Build time for the final file: ~90 s after Mathlib import elaboration;
  all proofs are constructive (`norm_num`, `nlinarith`, `omega`, `decide`
  over the explicit finite graphs only — kernel-reducible).

## What each audited theorem asserts (semantic spot-check)

- `structures_EFG` packages the three explicit molecular graphs
  (E = hexamethylbenzene C₆(CH₃)₆, F = mellitic acid C₆(COOH)₆,
  G = mellitic trianhydride C₁₂O₉) together with: exact atom counts
  (12 C / 18 H; 12 C / 6 H / 12 O; 12 C / 9 O / 0 H), E a hydrocarbon, G a
  binary C/O compound, a six-fold axis for E and F, a three-fold axis for
  G, and reproduction of both measured mass fractions inside the printed
  windows. This is exactly the requested "draw the structures of E, F, G"
  content plus every datum of the problem verified.
- `empirical_ratio_E` / `empirical_ratio_G`: at molecular scale
  (`a ≤ 488`, `x ≤ 1430`, declared modelling bounds) the measured windows
  are *equivalent* to the empirical lines `2b = 3a` resp. `4y = 3x` — the
  derivation of the ratios is proved, not assumed.
- `empirical_formula_E` / `empirical_formula_G`: adding the symmetry
  divisibility (`6 ∣ a`, `2 ∣ b` from valence parity; `3 ∣ x`) and the
  minimal-mass convention forces `(a,b) = (12,18)` resp. `(x,y) = (12,9)`.
