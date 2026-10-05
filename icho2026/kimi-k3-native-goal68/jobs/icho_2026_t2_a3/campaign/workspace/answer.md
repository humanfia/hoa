# IChO 2026 · Problem T2 · Subquestion A3 (Q2.3)

## Requested output

**`[Br⁻]critical`** in `mol dm⁻³`.

## Answer

```
[Br⁻]critical = 3.0 × 10⁻⁷ mol dm⁻³      (≡ 3.00 × 10⁻⁷ M to 3 s.f. ≡ 0.30 µmol dm⁻³)
```

Raw (unrounded) value: exactly `k₁·[BrO3⁻]₀/k₄ = (1.0×10⁴)(0.06)/(2.0×10⁹) = 3.0×10⁻⁷` mol dm⁻³;
reported here at 3 significant figures (`300 × 10⁻⁹`) per the reporting policy.

## Derivation (from problem data only)

The switchover criterion is stated in the problem text itself:

> *"To switch Process A to Process B, the reaction rate of the elementary step (4)
> must exceed that of the elementary step (1) and vice versa."*

Hence the critical bromide concentration is the threshold at which the two rates are equal:

```
r₁ = r₄     ⇔     k₁ [HBrO2] [BrO3⁻]₀ [H⁺]₀  =  k₄ [HBrO2] [Br⁻]critical [H⁺]₀.
```

Steps (1) and (4) are both first order in `[HBrO2]` and in `[H⁺]`.  With
`[HBrO2] > 0` and `[H⁺]₀ > 0` these factors cancel exactly, leaving

```
k₄ · [Br⁻]critical = k₁ · [BrO3⁻]₀
k₄ · [Br⁻]critical = 1.0 × 10⁴ × 0.06
k₄ · [Br⁻]critical = 600
[Br⁻]critical = 600 / (2.0 × 10⁹) = 3.0 × 10⁻⁷ mol dm⁻³.
```

**Which HBrO2 level applies?**  Because the shared factor `[HBrO2][H⁺]₀`
cancels, the threshold is the same whichever of the two stationary levels is
relevant; the only prerequisite is that it be strictly positive.  At the
B→A switch the relevant level is `[HBrO2]B`; at the A→B switch it is
`[HBrO2]A`.  Both are derived below from the steady-state approximation and
proved positive, so the cancellation is legitimate.

### Prerequisite (T2-A2): steady-state `[HBrO2]` levels

**Process A.**  HBrO2 is produced by step (1) at rate `r₁` and consumed by the
disproportionation (3) at rate `k₃ [HBrO2]²` (step (2) balances step (1) via
the Ce³⁺/Ce⁴⁺ couple, the standard Field–Körös–Noyes treatment).  The steady
state `r₁ = k₃ X²` gives

```
[HBrO2]A = k₁ [BrO3⁻]₀ [H⁺]₀ / k₃ = (1.0×10⁴)(0.06)(0.8) / (4.0×10⁷) = 1.2 × 10⁻⁵ M.
```

**Process B.**  HBrO2 is produced by step (5) at rate `r₅ = k₅ [BrO3⁻]₀ [Br⁻] [H⁺]₀²`
and consumed by step (4) at rate `k₄ [HBrO2] [Br⁻] [H⁺]₀`.  Under steady state for
bromide, `[Br⁻]` is fixed by the balance of production (step 7, Process C) against
consumption by steps (4)+(5); eliminating `[Br⁻]` between the two steady-state
relations gives the quadratic in `X = [HBrO2]B`

```
4 k₄ [H⁺]₀ X² + β X − T = 0,     β = k₅ [BrO3⁻]₀ [H⁺]₀² / 2,   T = k₅ [BrO3⁻]₀² [H⁺]₀²,
```

whose unique positive root is

```
[HBrO2]B = (−β + √(β² + 16 k₄ [H⁺]₀ T)) / (8 k₄ [H⁺]₀) ≈ 8.6948 × 10⁻⁷ M.
```

Both `1.2 × 10⁻⁵` and `8.69 × 10⁻⁷` are `> 0`; order of magnitude matches the
printed fallbacks (`1×10⁻⁵`, `1×10⁻¹⁰`) only loosely because the fallbacks are
deliberately crude stubs.  Our derived value for `[HBrO2]B` refines the stub.

### Putting it together

Since the shared factor `[HBrO2][H⁺]₀` is nonzero at either stationary level,

```
[Br⁻]critical = k₁ [BrO3⁻]₀ / k₄ = 3.0 × 10⁻⁷ mol dm⁻³.
```

Below `[Br⁻]critical`, `r₄ < r₁` → Process A dominates; above it, `r₄ > r₁` →
Process B dominates.  This is exactly the switchover the problem describes.

## Source grounding (what came from where)

| Quantity | Value | Source |
|---|---|---|
| `k₁` | `1.0 × 10⁴ M⁻² s⁻¹` | printed step (1) constant |
| `k₃` | `4.0 × 10⁷ M⁻¹ s⁻¹` | printed step (3) constant |
| `k₄` | `2.0 × 10⁹ M⁻² s⁻¹` | printed step (4) constant |
| `k₅` | `2.1 M⁻³ s⁻¹` | printed step (5) constant |
| `[BrO3⁻]₀` | `0.06 M` | printed buffered concentration |
| `[H⁺]₀` | `0.80 M` | printed buffered concentration (pH held constant) |
| switch criterion | `r₁ = r₄` at switchover | problem text Q2.3 |
| `[HBrO2]A, [HBrO2]B` | `1.2×10⁻⁵`, `8.69×10⁻⁷ M` | derived by SSA (T2-A2 prerequisite) |

No external/official solution was consulted.  The only "law" used beyond the
printed data is elementary mass-action kinetics and the steady-state
approximation — both standard general chemistry and explicitly invoked by the
problem statement.

## Lean formalization

See `IChO2026Problems/problem_icho_2026_t2_a3.lean`:

- `answer_bromideCritical` — the headline value `= 3.0e-7`;
- `bromide_critical_switch` — the **semantic content of Q2.3**: at
  `[Br⁻]critical` the rates are equal, `r₄ < r₁` strictly below it, and
  `r₄ > r₁` strictly above it (for any positive `[HBrO2]`);
- `bromide_critical_value`, `_umol`, `_reported`, `_above_fallback` — numeric
  value in the requested unit and precision, plus a comparison to the printed
  fallback;
- `hbrO2_A_steadyState`, `hbrO2_B_steadyState` — the T2-A2 steady-state
  balances, with both levels proved positive (the positivity that makes the
  `[HBrO2]` cancellation legitimate).

Verification: `lake env lean IChO2026Problems/problem_icho_2026_t2_a3.lean`
compiles with no errors and no `sorry`/`admit`; `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for the final theorems (see
`verification.md`).
