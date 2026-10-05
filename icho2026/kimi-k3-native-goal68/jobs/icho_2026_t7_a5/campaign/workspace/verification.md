# Verification — IChO 2026 T7-A5 (`icho_2026_t7_a5`)

## File under verification

`IChO2026Problems/problem_icho_2026_t7_a5.lean`

Toolchain: `leanprover/lean4:v4.31.0` (see `lean-toolchain`).

## Command run (exact)

From the campaign workspace root:

```
lake env lean IChO2026Problems/problem_icho_2026_t7_a5.lean
```

## Result (exact output, exit code 0)

```
'IChO2026T7A5.t7_a5_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry` / `admit` / custom axioms are present; `t7_a5_answer` depends only on
the standard Lean logical axioms (`propext`, `Classical.choice`, `Quot.sound`).
The file was re-run at 2026-09-14T04:23:54Z and exited 0 with the same output.

## What is proven (theorem inventory)

- `nN2_value`, `n4_value` — definitions of the two amounts, ground truth.
- `n2_mo_ratio` — `n(N2)/n(4)` ∈ `[5/2 − 1e-4, 5/2 + 1e-4]` (proved by
  `norm_num` interval arithmetic from the printed inputs).
- `n2_per_mo4_is_two_point_five` — `|n(N2)/n(4) − 5/2| ≤ 1e-4` (the 1 N2 : 2 Mo
  stoichiometry).
- `two_Mo_per_N2` — the ratio rounds to 2 (two Mo per N2).
- `structure5_two_fragments`, `structure5_pincer_donors`,
  `structure5_bridge_and_stoichiometry` — explicit connectivity of 5
  (dinuclear, meridional PNP on each Mo, single μ-N2, end-on at both Mo).
- `reduction_consistent` — Mo(III) − 3e → Mo(0) (3 equiv Na-Hg).
- `t7_a5_answer` — the bundled final classification (all of the above).

## Semantic-faithfulness note

The build being green only establishes that the stated Lean propositions hold.
Faithfulness was checked separately: the structure encoded in `structure5`
(`[(PNP)Mo]2(μ-N2)`, end-on bridge, 1 N2 : 2 Mo) matches the structure derived
in `answer.md` from the gas-uptake data, and the numerical theorem uses exactly
the printed inputs with no intermediate rounding.
