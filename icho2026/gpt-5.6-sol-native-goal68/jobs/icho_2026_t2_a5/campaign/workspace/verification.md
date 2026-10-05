# Verification record for `icho_2026_t2_a5`

## Source and scope audit

- Read `GOAL.txt` and `TASK.json` before solving.
- Inspected `T2_page-2.png` and `T2_page-3.png` at original resolution. The
  former supplies the elementary mechanism, constants, steady-state prompt,
  and maintained concentrations; the latter supplies the switching rule,
  phase portrait, maximum bromide concentration, slow-decay/rapid-reset
  statement, and T2-A5 prompt.
- Inspected the original 93-page `theory_problem.pdf`, including PDF page 17
  (`Q2-3`, containing T2-A5) and the corresponding blank student answer-sheet
  page 22 (`A2-4`, showing only `2.5 (9.0 pt) τ = ___ s`). There is no extra
  precision instruction on the answer sheet.
- Also inspected `T2_page-4.png` to check the immediate continuation of the T2
  question and confirm that it adds no condition to T2-A5.
- No official solution, marking scheme, grading report, historical answer, or
  answer repository was consulted.

The input-integrity command

```bash
sha256sum icho_2026_source/raw/theory_problem.pdf \
  icho_2026_source/image/T2_page-2.png \
  icho_2026_source/image/T2_page-3.png
```

returned

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
77bd97168be820a9643a8acac845ca1ef8c4c1a4a99f678c78227e6e5e48ef8b  icho_2026_source/image/T2_page-2.png
c3149da1c24d984ae95dea8947243aba8fe833b79e4447761bb04ec17b831260  icho_2026_source/image/T2_page-3.png
```

These exactly match `TASK.json` and `isolation_manifest.json`.

## Semantic audit

The final Lean file covers each required scientific link:

1. `hbro2_processA` derives the positive Process A stationary concentration
   from both intermediate balances, rather than adopting the fallback.
2. `hbro2_processB` derives the positive Process B stationary concentration;
   `hbro2B_is_stationary` proves that the result satisfies the original
   balance.
3. `bromide_critical` derives the critical bromide concentration from equality
   of rates (1) and (4); `bromideCritical_is_switch` proves the converse check.
4. `processB_bromide_loss_rate` proves that steps (4) and (5), each consuming
   bromide and having equal stationary rates, give the first-order coefficient
   `0.16128 s⁻¹`.
5. `bromide_slow_phase_rate` proves that the stated exponential trajectory
   solves that first-order rate law, and `bromide_at_period` proves that the raw
   time reaches the independently derived critical concentration.
6. `period_raw_exact` keeps the unrounded result as
   `(3125/504) * log (7000/3)`. `period_bounds` proves
   `48.05 ≤ periodRaw < 48.15` with certified logarithm bounds.
7. `oscillation_period` proves the project reporting contract for `48.1 s` at
   quantum `0.1 s` (three significant figures).

The period uses the problem's own approximation that the return to
`[Br⁻]max` is almost immediate. On the slow colourless Process B branch,
Ce(IV) is negligible (the colourless state is attributed to Ce(III)), so the
Ce(IV)-dependent Process C contribution belongs to the rapid regeneration
transient and is omitted from the long decay time. This assumption is stated
explicitly in both deliverables rather than hidden in an algebraic formula.

## Numerical cross-check

Command:

```bash
python3 - <<'PY'
from decimal import Decimal, getcontext
getcontext().prec = 40
ratio = Decimal(7000) / Decimal(3)
kappa = Decimal('0.16128')
print('hbro2_A =', Decimal('1e4') * Decimal('0.06') * Decimal('0.8') / (2 * Decimal('4e7')))
print('hbro2_B =', Decimal('2.1') * Decimal('0.06') * Decimal('0.8') / Decimal('2e9'))
print('bromide_critical =', Decimal('1e4') * Decimal('0.06') / Decimal('2e9'))
print('kappa =', kappa)
print('ratio =', ratio)
print('tau =', ratio.ln() / kappa)
PY
```

Result (exit code 0):

```text
hbro2_A = 0.000006
hbro2_B = 5.04E-11
bromide_critical = 3E-7
kappa = 0.16128
ratio = 2333.333333333333333333333333333333333333
tau = 48.08440686612934440577927747131539340149
```

## Lean compilation and axiom audit

Dependency build command:

```bash
lake build IChO2026Chem
```

Result: exit code 0 (`Build completed successfully (8561 jobs)`). The only
messages were pre-existing style warnings in the generic infrastructure about
short copyright headers.

Final target command:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t2_a5.lean
```

Result: exit code 0. The embedded `#print axioms` commands returned the same
set for every audited theorem:

```text
[propext, Classical.choice, Quot.sound]
```

The audited declarations are `processA_reduced_balance`, `hbro2_processA`,
`hbro2_processB`, `bromide_critical`, `hbro2B_is_stationary`,
`bromideCritical_is_switch`, `bromideCritical_lt_max`,
`bromide_decay_constant_value`, `processB_bromide_loss_rate`,
`bromide_slow_phase_initial`, `bromide_slow_phase_rate`, `period_raw_exact`,
`bromide_at_period`, `period_bounds`, and `oscillation_period`. This is every
declaration listed in `result.json`. The reported dependencies are standard
Lean logical axioms; there is no `sorryAx` or custom unchecked axiom.

Shortcut scan command:

```bash
if grep -nE '\b(sorry|admit|unsafe|axiom)\b' \
  IChO2026Problems/problem_icho_2026_t2_a5.lean; then
  exit 1
else
  echo 'PASS: no sorry/admit/unsafe/custom axiom tokens'
fi
```

Result (exit code 0):

```text
PASS: no sorry/admit/unsafe/custom axiom tokens
```

## Metadata validation

Command:

```bash
python3 -m json.tool result.json >/dev/null
```

Result: exit code 0.
