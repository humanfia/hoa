# IChO 2026 — Problem T2, subquestion 2.5 (`icho_2026_t2_a5`)

**Question (page Q2-3, 9 pt):** "Calculate based on the data the period of
oscillations, τ, of the BZ reaction, in seconds."

## Answer

**τ = 48.1 s** (raw exact expression
τ = ln(7000/3) / 0.16128 = 48.084406866… s, reported to three significant
figures per the uniform answer-blind default; quantum 0.1 s).

## Complete derivation

### Data (all printed on pages Q2-1 … Q2-3)

Rate constants (page Q2-2):

| step | reaction | k |
|---|---|---|
| (1) | HBrO₂ + BrO₃⁻ + H⁺ → 2 BrO₂· + H₂O | k₁ = 1.0×10⁴ M⁻² s⁻¹ |
| (2) | BrO₂· + Ce³⁺ + H⁺ → HBrO₂ + Ce⁴⁺ | k₂ = 6.2×10⁴ M⁻² s⁻¹ |
| (3) | 2 HBrO₂ → BrO₃⁻ + HBrO + H⁺ | k₃ = 4.0×10⁷ M⁻¹ s⁻¹ |
| (4) | HBrO₂ + Br⁻ + H⁺ → 2 HBrO | k₄ = 2.0×10⁹ M⁻² s⁻¹ |
| (5) | BrO₃⁻ + Br⁻ + 2 H⁺ → HBrO + HBrO₂ | k₅ = 2.1 M⁻³ s⁻¹ |
| (6) | HBrO + MA → BMA + H₂O | k₆ = 8.2 M⁻¹ s⁻¹ |
| (7) | Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products | k₇ = 1.0×10² M⁻¹ s⁻¹ |

Maintained concentrations (page Q2-2): [BrO₃⁻] = 0.06 M, [MA] = 0.1 M,
[H⁺] = 0.8 M; pH and all reactants except Ce⁴⁺ held constant. When Process A
occurs the solution is yellow and Process B practically does not occur; when
Process B occurs the solution is colourless and Process A practically does not
occur. Page Q2-3 stipulates [Br⁻]max = 7.0×10⁻⁴ M and that the system "does
not traverse the phase portrait … at a constant velocity, that is the
concentration of [Br⁻] slowly decreases from [Br⁻]max … to [Br⁻]critical, and
then almost immediately reaches [Br⁻]max again".

### Step 1 — dependencies 2.2 and 2.3 (re-derived here, answer-blind)

*Steady state of HBrO₂ in Process A (2.2):* production at the rate of step (1)
balances disproportionation in step (3):
k₁[BrO₃⁻][H⁺] = k₃[HBrO₂]A, so

[HBrO₂]A = k₁[BrO₃⁻][H⁺]/k₃ = (1.0×10⁴)(0.06)(0.8)/(4.0×10⁷) = **1.2×10⁻⁵ M**.

*Steady state of HBrO₂ in Process B (2.2):* production at the rate of step (5)
balances consumption at the rate of step (4):
k₅[BrO₃⁻][Br⁻][H⁺]² = k₄[HBrO₂]B[Br⁻][H⁺]
(the common factor [Br⁻] cancels — [HBrO₂]B is therefore independent of [Br⁻],
which is crucial below), so

[HBrO₂]B = (k₅/k₄)[BrO₃⁻][H⁺] = (2.1/2.0×10⁹)(0.06)(0.8) = **5.04×10⁻¹¹ M**.

*Critical bromide (2.3):* the switch A → B occurs when the rate of step (4)
exceeds that of step (1), i.e. at equality
k₄[HBrO₂][Br⁻]crit[H⁺] = k₁[HBrO₂][BrO₃⁻][H⁺], so

[Br⁻]crit = k₁[BrO₃⁻]/k₄ = (1.0×10⁴)(0.06)/(2.0×10⁹) = **3.0×10⁻⁷ M**.

### Step 2 — the slow phase is Process B (colourless segment)

During the colourless segment, Process A is off. Crucially, colourless means
[Ce⁴⁺] ≈ 0, so step (7) — the only Br⁻ source — is also off, while steps (4)
and (5) both consume Br⁻. With [HBrO₂] clamped to its stationary value
[HBrO₂]B (independent of [Br⁻]) and all other concentrations maintained:

d[Br⁻]/dt = −k₄[HBrO₂]B[Br⁻][H⁺] − k₅[BrO₃⁻][Br⁻][H⁺]²
          = −(k₄[HBrO₂]B[H⁺] + k₅[BrO₃⁻][H⁺]²)·[Br⁻] = −λ[Br⁻].

The two contributions to λ are *equal*, exactly by the 2.2 stationary
condition for Process B:
k₄[HBrO₂]B[H⁺] = k₅[BrO₃⁻][H⁺]² = (2.1)(0.06)(0.8)² = 0.08064 s⁻¹,
so

λ = 2·k₅[BrO₃⁻][H⁺]² = 2(2.1)(0.06)(0.8)² = **0.16128 s⁻¹** (exact).

Bromide therefore decays exponentially, [Br⁻](t) = [Br⁻]max·e^(−λt) — exactly
the non-constant ("slow") traversal the problem text announces; a constant-rate
(linear) decay model was checked and is inconsistent with this statement.

### Step 3 — the period

The slow descent lasts until [Br⁻] hits [Br⁻]critical:

τ = λ⁻¹ ln([Br⁻]max/[Br⁻]crit)
  = ln(7.0×10⁻⁴ / 3.0×10⁻⁷)/0.16128
  = ln(7000/3)/0.16128
  = (7.7550531393…)/(0.16128)
  = 48.084406866… s.

The return leg — Br⁻ regeneration by step (7) during the yellow Process-A
burst — is "almost immediate" per the problem, so the descent duration is the
requested period.

**τ = 48.1 s** (3 significant figures).

## Source grounding

- Rate constants, mechanism steps (1)–(7), maintained concentrations, and the
  A↔B colour exclusivity rules: page Q2-2 (`icho_2026_source/image/T2_page-2.png`).
- [Br⁻]max = 7.0×10⁻⁴ M, the switching-rate criterion for 2.3, and the
  "slowly decreases … then almost immediately reaches [Br⁻]max" statement:
  page Q2-3 (`icho_2026_source/image/T2_page-3.png`).
- No fall-back values were needed: both 2.2 concentrations and 2.3's
  [Br⁻]critical were re-derived from the printed rate constants.

## Role of assumptions (explicit)

1. **Steady state for HBrO₂** in Processes A and B — mandated by 2.2.
2. **Colourless ⇒ [Ce⁴⁺] ≈ 0**, switching off step (7) during Process B —
   grounded in the problem's own colour definitions ("yellow (due to Ce⁴⁺)…
   colourless (due to Ce³⁺)", plus "when Process B occurs the solution is
   colourless"). This is what makes the descending leg purely consumptive.
3. **Return leg negligible** — stated verbatim on page Q2-3 ("almost
   immediately reaches [Br⁻]max again").
4. **[HBrO₂]B independent of [Br⁻]** — a *consequence* of the 2.2 stationary
   condition (the [Br⁻] factor cancels), not an extra assumption; this turns
   the descent into an exact first-order exponential decay rather than a
   linear (constant-velocity) one, as the problem text requires.

All numerical values are exact consequences of the printed decimals; only the
final display is rounded (48.1 s).
