# Verification — icho_2026_t2_a3

All commands run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t2_a3/campaign/workspace`.

## 1. Lean compile of the target file

```
$ time lake env lean IChO2026Problems/problem_icho_2026_t2_a3.lean

real	0m58.900s
user	0m14.163s
sys	0m57.005s
```

Result: **exit 0, no output** — zero errors, zero warnings.  (Toolchain:
`leanprover/lean4:v4.31.0`; prebuilt Mathlib + Physlib from
`/home/jing/icho-full68-dependencies`.)

A final clean re-run was performed immediately before this record with the
same command and result.

## 2. No sorry / admit / custom axioms / unsafe

```
$ grep -nE 'sorry|admit|axiom|unsafe' IChO2026Problems/problem_icho_2026_t2_a3.lean
40:proved by `norm_num`/`nlinarith`; no `sorry` and no custom axioms are used.
```

Only the doc-comment at line 40 matches; no tactic or term-level occurrence.

## 3. Axiom audit of the final theorems

Command (uses a temp copy so the deliverable file itself is not touched):

```
cp IChO2026Problems/problem_icho_2026_t2_a3.lean /tmp/axrun.lean
cat >> /tmp/axrun.lean <<'EOF'

#print axioms IChO2026T2A3.answer_bromideCritical
#print axioms IChO2026T2A3.BZData.bromide_critical_switch
#print axioms IChO2026T2A3.BZData.hbrO2_B_steadyState
EOF
timeout 240 lake env lean --root=. /tmp/axrun.lean
```

Output:

```
'IChO2026T2A3.answer_bromideCritical' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A3.BZData.bromide_critical_switch' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A3.BZData.hbrO2_B_steadyState' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the **standard Lean logical axioms** appear (`propext`, `Classical.choice`,
`Quot.sound`); no custom or unchecked axioms.

## 4. Numeric cross-check (independent, Python)

```
k1, k3, k4, k5 = 1.0e4, 4.0e7, 2.0e9, 2.1
cBrO3, cH = 0.06, 0.8
xcrit = k1*cBrO3/k4          = 3.0e-07     (≡ 0.30 µmol/L)
XA    = k1*cBrO3*cH/k3       = 1.2e-05
beta  = k5*cBrO3*cH**2/2     = 0.04032 = 126/3125
T     = k5*cBrO3**2*cH**2    = 0.0048384
D     = beta*b + 16*k4*cH*T  = 123863040.001626
                               = 1209600000015876 / 9765625 (exact)
XB    = (-beta + sqrt(D))/(8*k4*cH) = 8.694794547770724e-07
sqrtD bounds: 11129**2 = 123854641 < D*9765625 < 123876900 = 11130**2
```

All Lean-side numerics (`bromide_critical_value = 3.0e-7`,
`hbrO2A_value = 1.2e-5`, the bounds `8.6e-7 < [HBrO2]B < 8.7e-7`, and the
exact discriminant) match this independent computation.

## 5. Semantic faithfulness check (independent re-review)

- `bromideCritical` is **defined** as `k₁[BrO3⁻]₀/k₄` and *proved* to equal
  `3.0e-7` — the value is not baked into the definition as a numeral, it is
  derived from the printed rate constants and buffered concentrations.
- `bromide_critical_switch` proves the *problem-stated* switch criterion as a
  first-order `if-and-only-if`, for arbitrary positive `[HBrO2]`: equality at
  the threshold, `r₄ < r₁` below, and `r₄ > r₁` above.
- The T2-A2 steady-state prerequisites are both proved (`r₁ = k₃X²` for A and
  the quadratic for B) and both levels proved strictly positive, which is the
  only side condition the cancellation needs.

## 6. Note on the T2-A2 (Process B) steady-state equation

The exact quadratic for `[HBrO2]B` depends on the conventional Field–Körös–
Noyes elimination of `[Br⁻]`.  Its precise form is a *modelling* choice of the
standard treatment; however, the requested output `[Br⁻]critical` **does not
depend on `[HBrO2]B` at all** (the HBrO2 factor cancels).  So even though the
B-level derivation is included for completeness and faithfully proved, its
specific numeric value is irrelevant to the requested answer.  This is
recorded as a mild source gap in `result.json`.
