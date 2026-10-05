# IChO 2026, Theory T2, Question 2.6 (icho_2026_t2_a6) — Answer

## Requested outputs

Tick exactly one box (a–e) for each of the four actions performed on an
**open** system in which the Belousov–Zhabotinsky reaction is running:

| Action | Ticked box | Meaning |
|--------|------------|---------|
| 1. Adding a small amount of Ce⁴⁺ during Process A | **c** | Process A switches to Process B |
| 2. Adding a small amount of Ag⁺ during Process B | **d** | Process B switches to Process A |
| 3. Adding a small amount of Br⁻ during Process B | **b** | prolongs Process B |
| 4. Continuous addition of Br⁻ | **e** | oscillations stop |

## Solution

### The switching criterion (stated in the problem)

The problem gives (lead-in to part 2.3): "To switch Process A to Process B,
the reaction rate of the elementary step (4) must exceed that of the
elementary step (1) and vice versa."

Writing the elementary rate laws (mass-action kinetics):

```
r₁ = k₁[HBrO₂][BrO₃⁻][H⁺]        r₄ = k₄[HBrO₂][Br⁻][H⁺]
```

Equating them and cancelling the positive common factors [HBrO₂] and [H⁺]
(and dividing by k₄ > 0) gives the critical bromide concentration, which only
depends on quantities held constant during the experiment:

```
[Br⁻]critical = k₁[BrO₃⁻]/k₄ = (1.0×10⁴)(0.06)/(2.0×10⁹) = 3.0×10⁻⁷ M
```

Hence, for any [HBrO₂] > 0:

```
r₄ > r₁   ⟺   [Br⁻] > [Br⁻]critical
```

so Process **B** takes over whenever [Br⁻] is above the critical value and
Process **A** runs when it is below. This is exactly the [Br⁻]critical
computed in part 2.3 (the dependency is re-derived here from the printed
constants; the problem's own fallback value 1×10⁻⁷ M would not change any of
the conclusions below).

### The roles in the cycle

* Process C — (7) Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products — runs
  *continuously* (problem statement) and is the bromide **source** of the
  cycle: r₇ = k₇[Ce⁴⁺][BMA].
* During Process B (the slow leg), [Br⁻] drains from [Br⁻]max = 7.0×10⁻⁴ M
  down to [Br⁻]critical, where the B → A switch fires.
* Process A is sustainable only while [Br⁻] < [Br⁻]critical: the moment
  [Br⁻] is pushed above critical, r₄ outruns r₁ and the system must be in
  Process B.
* Note also that the steady state of Process A derived in part 2.2,
  [HBrO₂]_A = k₁[BrO₃⁻][H⁺]/(2k₃), contains **no cerium concentration at
  all**: within the stated mechanism, added cerium can influence the switch
  *only* through the bromide production rate of step (7).

### Case-by-case reasoning

**1. Ce⁴⁺ during Process A → (c).** Adding Ce⁴⁺ strictly raises the
continuous bromide production rate r₇ = k₇[Ce⁴⁺][BMA] (monotone in [Ce⁴⁺]
since [BMA] > 0). The extra Br⁻ pushes [Br⁻] up to [Br⁻]critical, at which
r₄ > r₁ and — by the problem's stated criterion — Process A switches to
Process B. (Ce⁴⁺ accelerates exactly the process that terminates Process A;
it cannot prolong A because [HBrO₂]_A is cerium-independent.)

**2. Ag⁺ during Process B → (d).** Ag⁺ removes free bromide by precipitating
sparingly soluble AgBr(s) (ordinary general chemistry). Lowering [Br⁻] during
Process B brings it to [Br⁻]critical sooner, where r₁ overtakes r₄ and the
system switches from Process B to Process A.

**3. Br⁻ during Process B → (b).** Adding Br⁻ during Process B raises [Br⁻]
back away from [Br⁻]critical. The slow drain that defines the duration of
Process B then has farther to go before the B → A switch can fire, so
Process B is prolonged.

**4. Continuous addition of Br⁻ → (e).** A continuous feed keeps [Br⁻] pinned
above [Br⁻]critical indefinitely; then r₄ > r₁ holds permanently, the B → A
switch can never occur, the alternation of Processes A and B ceases, and the
oscillations stop.

## Source grounding

* Mechanism, rate constants k₁…k₇, fixed concentrations [BrO₃⁻]₀ = 0.06 M,
  [H⁺]₀ = 0.8 M, [MA]₀ = 0.1 M, and "Process C occurs continuously":
  problem page Q2-2 (`T2_page-2.png`, theory_problem.pdf p. 17 of the Q2
  block).
* Switching criterion ("rate of step (4) must exceed that of step (1) and
  vice versa"), phase portrait, and [Br⁻]max = 7.0×10⁻⁴ M with the slow
  decrease toward [Br⁻]critical: problem page Q2-3 (`T2_page-3.png`).
* Question text, answer boxes (a)–(e), and the blank answer grid on sheet
  A2-5 (confirming exactly one box per action): problem page Q2-4
  (`T2_page-4.png`) and the answer sheet page of theory_problem.pdf.
* Elementary (mass-action) rate laws and the low solubility of AgBr are
  trusted general laws of chemistry, not competition-specific answers.

## Assumptions and gaps

* The one-box-per-action format and the meaning of boxes (a)–(e) are taken
  from the printed question and the blank answer sheet A2-5; no answer keys,
  marking schemes, or external solutions were used.
* No quantitative scale of "a small amount" is needed: each conclusion
  depends only on the *sign* of the induced change of the bromide balance
  (proved as monotonicity statements in the Lean formalization), plus the
  threshold rule quoted above. For action 2, "small" only has to mean "large
  enough to move [Br⁻] to the neighbourhood of [Br⁻]critical relative to the
  slow drain", consistent with the intended tick-box semantics.
* The only premise not literally printed is the standard chemical fact that
  Ag⁺ precipitates Br⁻ as AgBr(s) (Ksp ≈ 5×10⁻¹³). This is ordinary textbook
  chemistry and is recorded as an explicit assumption in result.json and the
  Lean file header.
