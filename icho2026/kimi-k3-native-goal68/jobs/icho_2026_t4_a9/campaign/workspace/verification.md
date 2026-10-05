# Verification record — `icho_2026_t4_a9`

All commands were run in the workspace
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t4_a9/campaign/workspace`
with the pinned toolchain on `PATH`
(`~/.elan/toolchains/leanprover--lean4---v4.31.0/bin`, toolchain
`leanprover/lean4:v4.31.0` per `lean-toolchain`).

## 1. Compilation of the formalization

```
lake env lean IChO2026Problems/problem_icho_2026_t4_a9.lean
```

Result: exits 0, no errors and no warnings (the file contains no `sorry`,
`admit`, or `axiom`; `grep -nE 'sorry|admit|axiom'` on the file returns
nothing).

## 2. Full project build

```
lake build
```

Result: `Build completed successfully (8581 jobs).`

(The library umbrella `IChO2026Problems/All.lean` required by the trusted
controller's `IChO2026Problems.lean` was created to import exactly this
target's file — the sole target in the authorized scope; no source inputs or
generic infrastructure were modified.)

## 3. Axiom audit of the final theorems

A probe file containing the same definitions and theorems in namespace
`IChO2026T4A9` (the problem file itself is a bare file target not in the
`IChO2026Problems` import graph, so the audit imports `Mathlib` and
`IChO2026Chem` and re-checks the identical theorem bodies, as the target file
does when compiled standalone) was checked with:

```
lake env lean /tmp/check_axioms.lean
```

Output:

```
'IChO2026T4A9.deltaE_MeV_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T4A9.explosionEnergy_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T4A9.totalFissions_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T4A9.enrichedUraniumMass_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T4A9.totalFissions_reported' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T4A9.enrichedUraniumMass_reported' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard Lean logical axioms appear; no custom or unchecked
axioms.

## 4. Semantic-faithfulness cross-check (independent of the Lean kernel)

An independent exact-rational computation (Python `fractions`) of the same
formula chain from the same problem-stated inputs

```
E   = 30000 t × 4.184e9 J/t                       = 1.2552e14 J
ΔE  = (8.45 − 7.59) × 235 MeV                     = 202.1 MeV
    = 202.1e6 × 1.602176634e-19 J                 = 3.237998977314e-11 J
TN  = E / ΔE                                      = 3.8764681792…e24
m   = TN × 0.23504 / 6.02214076e23 / (0.33×0.90)  = 5.0941373462… kg
```

confirms the bound claims proved in Lean at every displayed digit:
`3.875e24 ≤ TN < 3.885e24` and `5.085 ≤ m < 5.095`, i.e. TN → 3.88e24
fissions (quantum 1e22) and m → 5.09 kg (quantum 0.01 kg) at three
significant figures.

The theorem statements were inspected against the problem text: they encode
(i) every given constant as a separate definition tied to its printed source,
(ii) the physical relations TN = E/ΔE, m_fis = TN·M(²³⁵U)/N_A, and
m = m_fis/(0.33·0.90), and (iii) the reporting contract from
`IChO2026Chem.Reporting`. Nothing about the requested statement was weakened;
the two non-printed physical constants (eV→J factor, N_A) are the trusted
general laws disclosed in `answer.md` and `result.json`.

## 5. Reporting-policy compliance

* No intermediate rounding anywhere: the Lean proofs operate on the exact
  rational values of the definitions, and the reporting relation
  (`ReportsAtQuantum`, ties away from zero) is applied only at the final
  boundary through `ValidNumericSubmission`.
* Three significant figures for both requested outputs (uniform blind-evaluation
  default), with raw (unrounded) values stated in `answer.md`.
