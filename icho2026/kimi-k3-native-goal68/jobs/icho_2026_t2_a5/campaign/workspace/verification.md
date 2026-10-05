# Verification — `icho_2026_t2_a5` (IChO 2026 T2-2.5, period of oscillations)

Target deliverable: `IChO2026Problems/problem_icho_2026_t2_a5.lean`
(namespace `IChO2026T2A5`).

## Build

```
$ lake env lean IChO2026Problems/problem_icho_2026_t2_a5.lean
(no output, exit 0)
```

```
$ lake build IChO2026Problems.problem_icho_2026_t2_a5
✔ [8561/8561] Built IChO2026Problems.problem_icho_2026_t2_a5 (65s)
Build completed successfully (8561 jobs).
```

Toolchain: Lean `v4.31.0` (per `lean-toolchain`), Mathlib from the pinned
`lake-manifest.json`. No `sorry`, `admit`, `axiom`, `unsafe`, or
`native_decide` appears anywhere in the file.

## Axiom audit

Checker file (scratch, `/tmp/check_axioms.lean`):

```lean
import Mathlib
import IChO2026Chem
import IChO2026Chem.Reporting
import IChO2026Problems.problem_icho_2026_t2_a5
open IChO2026T2A5
#print axioms tauSubmission_valid
#print axioms tauSubmission_contract
#print axioms tau_report_band
#print axioms log_ratio_bounds
#print axioms brCritical_characterisation
#print axioms hbrO2_B_value
```

Command and result:

```
$ lake env lean /tmp/check_axioms.lean
'IChO2026T2A5.tauSubmission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A5.tauSubmission_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A5.tau_report_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A5.log_ratio_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A5.brCritical_characterisation' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T2A5.hbrO2_B_value' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard Lean logical axioms appear — no custom unchecked
axioms.

## Theorem inventory and semantic check

| theorem | content | what it establishes |
|---|---|---|
| `k1_value … k7_value`, `brMax_value` | printed constants as exact reals | data transcription |
| `brCritical_value` | `[Br⁻]crit = 3×10⁻⁷ M` exactly | 2.3 answer |
| `hbrO2_A_value` | `[HBrO₂]A = 1.2×10⁻⁵ M` exactly | 2.2 dependency |
| `hbrO2_B_value` | `[HBrO₂]B = 5.04×10⁻¹¹ M` exactly | 2.2 dependency |
| `lambda_value` | `λ = 0.16128 s⁻¹` exactly | decay constant |
| `lambda_eq_twice_k5` | `λ = 2·k₅[BrO₃⁻][H⁺]²` | equality of the two Br⁻ sinks |
| `br_ratio` | `[Br⁻]max/[Br⁻]crit = 7000/3` | log argument |
| `tau_eq` | `τ = ln(brMax/brCritical)/λ` (definitional anchor) | semantics of τ |
| `hbrO2_A_gt_B` | `[HBrO₂]B < [HBrO₂]A` | consistency with phase portrait |
| `brCritical_characterisation` | `k₄·x·b·h = k₁·x·brO3·h ↔ b = [Br⁻]crit` for `x,h ≠ 0` | switching criterion iff |
| `log_two_bounds`, `log_875_768_bounds` | certified rational squeezes of `ln 2` and `ln(875/768)` via the Mathlib artanh-series lemmas `Real.sum_range_le_log_div` / `Real.log_div_le_sum_range_add`, using `7000/3 = 2¹¹·(875/768)` | transcendental exactness |
| `ratio_decompose` | `7000/3 = 2¹¹·(875/768)` | algebra |
| `log_ratio_bounds` | `7.75504327 ≤ ln(brMax/brCritical) ≤ 7.75505986` | certified log bounds |
| `tau_report_band` | `48.05 < τ < 48.15` | half-quantum band |
| `tau_pos` | `0 < τ` | sanity |
| `tauSubmission_raw` | `tauSubmission.rawValue = tau` (rfl) | raw = derived |
| `tauSubmission_valid` | `ReportsAtQuantum τ 48.1 0.1` | reporting contract |
| `tauSubmission_contract` | `ValidNumericSubmission tau tauSubmission` | target-independent contract |

### Faithfulness assessment (independent re-check of the chemistry)

- The switching criterion formalized in `brCritical_characterisation` is
  exactly the problem's "rate of step (4) must exceed that of step (1)"
  statement (equality at the switch point), page Q2-3.
- The decay constant `λ = k₄[HBrO₂]B[H⁺] + k₅[BrO₃⁻][H⁺]²` comes from
  steps (4) and (5) being the only Br⁻ sinks during Process B, with step (7)
  off (colourless ⇒ [Ce⁴⁺] ≈ 0) and step (1) off (Process A off); per event
  of either step (4) or step (5) exactly one Br⁻ is consumed. The stationary
  `d[HBrO₂]B/dt = 0` from 2.2 makes the two sinks equal (rate of (4) =
  rate of (5)). `[HBrO₂]B` is independent of `[Br⁻]` (the `[Br⁻]` factor
  cancels in the 2.2 balance), giving an exact first-order exponential
  decay — matching the problem's "not at a constant velocity … slowly
  decreases" statement (a constant-velocity linear model was considered and
  discarded as incompatible with that text).
- The return leg is stipulated "almost immediate" on page Q2-3, so
  `τ = descent duration = ln([Br⁻]max/[Br⁻]crit)/λ`.
- Numerics independently recomputed (IEEE-double cross-check):
  `ln(7000/3) = 7.755053139369286`, `τ = 48.084406866… s`;
  thresholds `48.05·λ = 7.749504`, `48.15·λ = 7.765632`; the certified
  Lean bounds sit strictly inside with margin ≥ 5.5×10⁻⁶.
- Reported value `48.1 s` is the multiple of the quantum `0.1 s` (3 s.f.)
  whose half-quantum band provably contains τ, so the display is forced.

## Known simplifications / declared source gaps

None blocking. The model assumptions (steady state, negligible Ce⁴⁺ during
the colourless leg, negligible return-leg time) are all grounded in the
problem text itself; see `answer.md`, section "Role of assumptions", for the
exact source sentences.

## Environment note

`lake env lean` must be run from the workspace root (the file imports
`Mathlib`, `IChO2026Chem`, and `IChO2026Chem.Reporting` via the local
lakefile). All commands above were executed from
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t2_a5/campaign/workspace`.
