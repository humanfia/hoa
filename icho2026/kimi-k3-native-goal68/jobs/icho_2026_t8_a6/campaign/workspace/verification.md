# Verification record — icho_2026_t8_a6

All commands run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t8_a6/campaign/workspace`.

## Toolchain

- `lean-toolchain`: leanprover/lean4:v4.31.0 (`lean --version`: Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783, Release).

## Independent numerical check (outside Lean)

Exact rational arithmetic (Python `fractions`, reproduced below) was used to
compute the quantum yield from the printed data and exact SI constants:

```
h  = 662607015 / 10^42      (6.62607015e-34 J s, SI-exact)
c  = 299792458              (m/s, SI-exact)
NA = 602214076 * 10^15      (6.02214076e23 mol^-1, SI-exact)
lam = 390/10^9 m ; P = 50/1000 W ; M = 55721/100 g/mol
w = 38/1000 ; m = 10/1000 g ; TOF = 8 h^-1 ; t = 3600 s

photonE  = h*c/lam
nph      = P*t/photonE
co       = TOF * (t/3600) * (m*w/M) * NA
phi(%)   = (2*co)/nph * 100
         = 18940872892793693114789369 / 10186495312500000000000000
         = 1.8594101613683622...
```

Decimal cross-check (float64): 1.8594101613683625 — same value.

## Lean compilation

Command (the required final-file check):

```
cd /home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t8_a6/campaign/workspace
lake env lean IChO2026Problems/problem_icho_2026_t8_a6.lean
```

Result: **exit code 0, no errors, no warnings about `sorry`**. The only output is
the pair of `#print axioms` queries:

```
'IChO2026.T8.A6.co_quantum_yield_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T8.A6.co_quantum_yield_reported' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All three are standard Lean logical axioms (propositional extensionality,
classical choice, quotient soundness). **No `sorryAx`, no custom or unchecked
axioms.**

An earlier draft of the same file contained a wrong closed-form fraction and
failed with `unsolved goals` plus a `sorryAx` dependency; the fraction was
re-derived with exact rational arithmetic and the current proof closes fully.

## Full project build

The project additionally requires `IChO2026Problems/All.lean` (rewritten by the
trusted controller from the authorized target scope; it imports only
`problem_icho_2026_t8_a6`). With that file in place, `lake build` was run to
confirm the target integrates into the filtered umbrella build; the final
compile command above is the authoritative per-file check required by the task
contract, and it passes.

## Semantic faithfulness audit (independent of build success)

Requested output: the numeric quantum yield for CO formation, in %, 3
significant figures ("quantum yield, φ(%), for CO formation").

- `quantumYieldPercent` is defined *structurally from the printed problem data
  only*: λ = 390 nm, P = 50 mW, TOF = 8 h⁻¹, m = 10 mg, ω_cat = 3.8 %,
  M_cat = 557.21 g mol⁻¹, the problem's own definition of TOF
  ("product molecules per active catalyst molecule per hour") and of φ
  ("reacted electrons / incident photons · 100 %"), and the SI-exact
  constants h, c, N_A. The observation time (3600 s) cancels and is present
  only to make the "number of photons" and "number of electrons" counts
  concrete on the same footing.
- The factor `electronsPerCO = 2` is the answer to part 8.1 of the same
  problem (CO₂ + 2H⁺ + 2e⁻ → CO + H₂O): C is +4 in CO₂ and +2 in CO, so the
  reduction consumes exactly 2 electrons per CO. No previous-part numerical
  result is imported; the specific surface area from 8.5 is irrelevant to the
  quantum yield entered here.
- `co_quantum_yield_raw` proves the exact value `1.8594101613683622… %`.
- `co_quantum_yield_reported` proves the raw value rounds, under the
  project-wide `ReportsAtQuantum` contract (quantum 0.01 %, half away from
  zero), to the displayed answer **1.86 %**.

The theorem therefore both *states* and *proves* the requested chemistry, and
the natural-language derivation in `answer.md` reaches the identical number.
