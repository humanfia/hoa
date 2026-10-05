# Verification record — icho_2026_t7_a2

Toolchain: Lean v4.31.0 (`leanprover/lean4:v4.31.0`), Mathlib v4.31.0
(prebuilt in the workspace `.lake`), Physlib and crnt-lean pinned per
`lakefile.toml` (untouched infrastructure).

All commands were run from the workspace root
`…/jobs/icho_2026_t7_a2/campaign/workspace`.

## 1. Type-checking the target formalisation

```
lake env lean IChO2026Problems/problem_icho_2026_t7_a2.lean
```

Result: exit code 0, **no errors, no warnings** (final run, after the two
`show` → `change` style-linter fixes).

## 2. Building the module (olean) through Lake

```
lake build IChO2026Problems.problem_icho_2026_t7_a2
```

Result:

```
Build completed successfully (8561 jobs).
```

## 3. Axioms used by the final theorems

A throwaway checker file was created outside the deliverables:

```
cat > /tmp/axiom_check_t7a2.lean <<'EOF'
import IChO2026Problems.problem_icho_2026_t7_a2
open IChO2026T7A2
#print axioms methane_mol_chain
#print axioms methaneMassTons_raw_value
#print axioms methaneMassTons_reports_280e3
#print axioms annual_methane_mass_chain
#print axioms methane_ratio_H2_exact
#print axioms feed_split_H2_exact
EOF
lake env lean /tmp/axiom_check_t7a2.lean
```

Result (verbatim):

```
'IChO2026T7A2.methane_mol_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T7A2.methaneMassTons_raw_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T7A2.methaneMassTons_reports_280e3' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T7A2.annual_methane_mass_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T7A2.methane_ratio_H2_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T7A2.feed_split_H2_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the standard Lean logical axioms appear; there are no custom axioms,
no `sorry`/`admit` (checked with
`grep -nE '\bsorry\b|\badmit\b|\baxiom\b'` on the target file — no matches).

## 4. Numerical cross-check of the raw value

Independent Python (exact fractions) reproduction of the raw chain:

```
n(NH3) = 660000·10³ kg / 17.034 kg·kmol⁻¹ = 38 746 037.337 kmol a⁻¹
n(CH4) = (7/16)·n(NH3)/0.970              = 17 475 661.170 kmol a⁻¹
m(CH4) = 16.042·n(CH4)·10⁻³ t             = 280 344.556 t a⁻¹
       = 77 202 125 000 / 275 383 t   (matches methaneMassTons_raw_value)
```

The 3-significant-figure reporting cell at quantum 1000 t is
[279 500, 280 500); the raw value lies strictly inside, hence the reported
answer 280 000 t (proved as `methaneMassTons_reports_280e3`,
`annual_methane_mass_chain`).

## 5. Semantic self-check

* `methane_ratio_H2_exact` states `8·methane = 7·n2` at `excess = 0` — the
  exact net-reaction statement `7 CH₄ + 7 H₂O + 8 N₂ → 16 NH₃ + 7 CO₂`.
* `methane_mol_chain` states `methane = (7/16)·nh3 / overallYield` — the
  problem-relevant mole chain including the 97.0 % overall yield.
* The raw numeric definitions use exactly the printed inputs 660 000,
  0.970, 16.042 (= 12.01 + 4·1.008), 17.034 (= 14.01 + 3·1.008).
* No statement was weakened: the final theorems quantify over every
  `PlantState` satisfying `OperatesPerFig1` with H₂-exact operation
  (excess = 0), and the numerical theorem bundles the raw value together
  with the reporting-policy proof.
