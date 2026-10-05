# IChO 2026 — T8-A10 (Q8.10)

**Question (source: theory_problem.pdf, printed page Q8-5 / PDF page 76; image T8_page-5.png):**

> How do the emission lifetimes of the S1 and T1 states change when [Red] increases?
> Tick the correct box. a) increases  b) decreases  c) doesn't change

**Answer: b) decreases — for both S1 and T1.**

## Reasoning

The problem statement gives the two pseudo-first-order quenching channels on page Q8-5:

- PS(S1) + Red → PS•− + Red•+ with k_S = 2.7 × 10⁹ M⁻¹ s⁻¹
- PS(T1) + Red → PS•− + Red•+ with k_T = 1.5 × 10⁸ M⁻¹ s⁻¹

and defines τ₀(S1) = 2.9 ns and τ₀(T1) = 84 µs as the emission lifetimes **in the
absence of the quencher**.

For an excited state that decays by intrinsic processes (rate 1/τ₀) plus a
bimolecular quenching channel with rate constant k_q, the observed lifetime in the
presence of quencher is the Stern–Volmer lifetime form:

  τ([Red]) = 1 / (1/τ₀ + k_q · [Red]) = τ₀ / (1 + k_q τ₀ · [Red])

This is the same quenching model used in Q8.9, where the quenching percentage is
η_q = 1 − τ/τ₀ = k_q τ₀ [Red] / (1 + k_q τ₀ [Red]); the note k_F ≫ k_ISC only
justifies neglecting reverse ISC in the S1 kinetics.

For both excited states:

- S1: τ(S1) = τ₀(S1) / (1 + k_S τ₀(S1) [Red]), with K_S = k_S τ₀(S1) = (2.7 × 10⁹)(2.9 × 10⁻⁹) = 7.83 M⁻¹ > 0
- T1: τ(T1) = τ₀(T1) / (1 + k_T τ₀(T1) [Red]), with K_T = k_T τ₀(T1) = (1.5 × 10⁸)(84 × 10⁻⁶) = 1.26 × 10⁴ M⁻¹ > 0

Each function has the form f(x) = τ₀ / (1 + K x) with τ₀ > 0 and K > 0, which is
strictly decreasing on [Red] ≥ 0 (derivative −τ₀ K / (1 + Kx)² < 0 everywhere).
Therefore, **when [Red] increases, the emission lifetimes of both S1 and T1 decrease**.

The magnitude of the effect differs strongly — quenching of T1 is far more efficient
because K_T ≫ K_S (cf. the η_q values computed in Q8.9) — but the blank answer
sheet (PDF page 83, A8-7) provides exactly one tick row for 8.10 with a single set
of boxes a / b / c, i.e. one answer applying to both states. Both trends are the
same: **b) decreases**.

Physically: quenching opens an additional decay pathway for the excited state, so
its population is drained faster and the observed emission lifetime shortens. The
intrinsic lifetime τ₀ is unchanged, but the *emission lifetime in the presence of
Red* — what the question asks about — decreases with increasing [Red].

## Source grounding

| Item | Source |
|---|---|
| Question text, options a/b/c, single tick box | theory_problem.pdf p. 76 (Q8-5); image T8_page-5.png |
| k_S = 2.7 × 10⁹ M⁻¹ s⁻¹, k_T = 1.5 × 10⁸ M⁻¹ s⁻¹ | same page, printed quenching equations |
| τ₀(S1) = 2.9 ns, τ₀(T1) = 84 µs ("emission lifetime in the absence of the quencher") | same page |
| Quenching model underpinning (η_q definition and k_F ≫ k_ISC note in Q8.9, consistent with Stern–Volmer form) | same page |
| Answer-sheet layout: one row of boxes a/b/c shared by both states for 8.10 | theory_problem.pdf p. 83 (A8-7) |

The Stern–Volmer relation τ = τ₀/(1 + k_q τ₀ [Q]) is a standard, general
photophysical law (trusted general knowledge), fully grounded here by the rate
constants and lifetime definitions printed in the problem itself.

No numerical display quantum is required for 8.10 (a classification/tick question);
the requested outputs are the exact symbolic trends:

- `lifetime_s1`: **decreases**
- `lifetime_t1`: **decreases**

The Lean 4 formalization in
`IChO2026Problems/problem_icho_2026_t8_a10.lean` proves strict antitonicity of
τ(S1)([Red]) and τ(T1)([Red]) on [0, ∞) from the printed constants, and derives
the box-b answer (`LifetimeTrend.decreases`) for both states.
