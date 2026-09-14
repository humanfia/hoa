# IChO 2026, T2-A2 — Stationary HBrO₂ concentrations in Processes A and B

## Answers (blank answer sheet boxes, A2-1/A2-2)

- **[HBrO₂]A = 6.00 × 10⁻⁶ M** (mol dm⁻³)
- **[HBrO₂]B = 5.04 × 10⁻¹¹ M** (mol dm⁻³)

For comparison, the problem's own printed fallback values for later parts
are 1 × 10⁻⁵ M (Process A) and 1 × 10⁻¹⁰ M (Process B); both computed values
are of exactly those orders of magnitude, as expected.

## Problem data used (official statement, Q2-1/Q2-2)

Process A:
(1) HBrO₂ + BrO₃⁻ + H⁺ —k₁→ 2 BrO₂• + H₂O,  k₁ = 1.0 × 10⁴ M⁻² s⁻¹
(2) BrO₂• + Ce³⁺ + H⁺ —k₂→ HBrO₂ + Ce⁴⁺,    k₂ = 6.2 × 10⁴ M⁻² s⁻¹
(3) 2 HBrO₂ —k₃→ BrO₃⁻ + HBrO + H⁺,          k₃ = 4.0 × 10⁷ M⁻¹ s⁻¹

Process B:
(4) HBrO₂ + Br⁻ + H⁺ —k₄→ 2 HBrO,            k₄ = 2.0 × 10⁹ M⁻² s⁻¹
(5) BrO₃⁻ + Br⁻ + 2 H⁺ —k₅→ HBrO + HBrO₂,     k₅ = 2.1 M⁻³ s⁻¹
(6) HBrO + MA —k₆→ BMA + H₂O,                 k₆ = 8.2 M⁻¹ s⁻¹

Held constant throughout: [BrO₃⁻]₀ = 0.06 M, [MA]₀ = 0.1 M, [H⁺]₀ = 0.8 M
(pH fixed); only Ce⁴⁺ is allowed to vary. When Process A runs, B is off and
vice versa.

## Derivation

### Process A — [HBrO₂]A = 6.00 × 10⁻⁶ M

Rates: r₁ = k₁[HBrO₂][BrO₃⁻][H⁺], r₂ = k₂[BrO₂•][Ce³⁺][H⁺], r₃ = k₃[HBrO₂]².

Steady state for the radical BrO₂• (formed by step 1 with stoichiometric
coefficient 2, consumed by step 2):

  d[BrO₂•]/dt = 2 r₁ − r₂ = 0  ⇒  r₂ = 2 r₁.

Steady state for HBrO₂ (consumed in 1 and 3, produced in 2; stoichiometric
coefficient of HBrO₂ in step 3 is 2):

  d[HBrO₂]/dt = −r₁ + r₂ − 2 r₃ = 0.

Substituting r₂ = 2 r₁ eliminates k₂, Ce³⁺ and Ce⁴⁺ entirely (whether the
Ce⁴⁺-consuming effect is treated as part of step 2 or as a fast reverse
annihilation, the condition r₂ = 2 r₁ with net flux
k₂[BrO₂•][Ce³⁺+Ce⁴⁺][H⁺] gives the same total balance):

  −r₁ + 2 r₁ − 2 r₃ = 0  ⇒  r₁ = 2 r₃
  k₁[HBrO₂][BrO₃⁻][H⁺] = 2 k₃[HBrO₂]².

The nonzero root:

  [HBrO₂]A = k₁[BrO₃⁻][H⁺] / (2 k₃)
           = (1.0 × 10⁴)(0.06)(0.8) / (2 × 4.0 × 10⁷)
           = 480 / 8.0 × 10⁷ = **6.00 × 10⁻⁶ M** (raw value 6.0 × 10⁻⁶ M).

### Process B — [HBrO₂]B = 5.04 × 10⁻¹¹ M

Step 6 involves HBrO and MA only; only steps 4 and 5 touch HBrO₂:

  d[HBrO₂]/dt = r₅ − r₄ = k₅[BrO₃⁻][Br⁻][H⁺]² − k₄[HBrO₂][Br⁻][H⁺] = 0.

Since Br⁻ is a reactant held constant during Process B, the factor
[Br⁻][H⁺] ≠ 0 divides out (so [Br⁻] itself cancels):

  [HBrO₂]B = k₅[BrO₃⁻][H⁺] / k₄
           = (2.1)(0.06)(0.8) / (2.0 × 10⁹)
           = 0.1008 / 2.0 × 10⁹ = **5.04 × 10⁻¹¹ M** (raw 5.04 × 10⁻¹¹ M).

## Source grounding

- Question statement (subquestion 2.2): TASK.json `question`/`shared_context`
  fields, and source images `T2_page-1.png` (T2 header, concentration
  assumptions) and `T2_page-2.png` (mechanism, rate constants, and the 2.2
  box "Using the steady-state approximation, calculate the stationary molar
  concentrations of HBrO₂ in Processes A and B, [HBrO₂]A and [HBrO₂]B").
- The blank student answer sheets A2-1/A2-2 in `theory_problem.pdf`
  (PDF pages 19–20) confirm the requested units are mol dm⁻³
  ("[HBrO2]A = ___ M", "[HBrO2]B = ___ M").
- The problem-stated fallback values on Q2-2 (1 × 10⁻⁵ M, 1 × 10⁻¹⁰ M) are
  order-of-magnitude markers supplied for later parts only; the values above
  are derived from first principles using the printed rate constants and
  concentrations, and they are fully consistent with those markers.
- Mass-action kinetics (rate of an elementary step = k × product of reactant
  concentrations) and the steady-state approximation are trusted general
  laws explicitly invoked by the problem statement ("Using the steady-state
  approximation").

## Assumptions and gaps

- The radical BrO₂• steady state (r₂ = 2 r₁) is required to derive Process A;
  it is the standard full SSA as instructed by "the steady-state
  approximation". No Ce³⁺/Ce⁴⁺ concentration is needed because it cancels.
- [Br⁻] cancels in Process B because the problem fixes all reactants except
  Ce⁴⁺, so [Br⁻][H⁺] is a common nonzero factor during Process B.
- No source gap: every constant used (k₁, k₃, k₄, k₅, [BrO₃⁻]₀, [H⁺]₀) is
  printed in the official statement; k₂, k₆, [MA]₀, [Ce⁴⁺]₀ are not needed.
- No intermediate rounding was used; final values are reported to three
  significant figures per the reporting policy.

## Lean formalization

`IChO2026Problems/problem_icho_2026_t2_a2.lean` proves:

- `hbro2_process_A`: under the SSA balance `k₁ X B H = 2 k₃ X²` (with the
  radical conditions recorded as hypotheses), the unique root is the closed
  form `hbro2A = k₁[BrO₃⁻][H⁺]/(2 k₃)`.
- `hbro2_process_B`: under the SSA balance `k₅ B Br H² = k₄ X Br H`, the
  unique root is `hbro2B = k₅[BrO₃⁻][H⁺]/k₄`.
- `hbro2A_value`, `hbro2B_value`: exact numeric evaluations
  6.0 × 10⁻⁶ and 5.04 × 10⁻¹¹.
- `valid_submission_A`, `valid_submission_B`: the reported values
  6.00 × 10⁻⁶ and 5.04 × 10⁻¹¹ satisfy the fixed 3-significant-figure
  reporting contract (quanta 10⁻⁸ and 10⁻¹³), tie-free, with no intermediate
  rounding.
- `icho_2026_t2_a2_answer`: the combined statement.

All final theorems depend only on the standard Lean logical axioms
(`propext`, `Classical.choice`, `Quot.sound`).
