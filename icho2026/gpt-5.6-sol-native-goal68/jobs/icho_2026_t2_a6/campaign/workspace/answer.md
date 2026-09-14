# IChO 2026 T2-A6

## Boxes to tick

| Action | Choice | Effect |
|---|---:|---|
| 1. Add a small amount of Ce⁴⁺ during Process A | **c** | Process A switches to Process B |
| 2. Add a small amount of Ag⁺ during Process B | **d** | Process B switches to Process A |
| 3. Add a small amount of Br⁻ during Process B | **b** | Prolongs Process B |
| 4. Continuously add Br⁻ | **e** | Oscillations stop |

Thus the answer sequence is **1-c, 2-d, 3-b, 4-e**.

## Derivation

From the elementary steps printed on T2 page 2,

\[
v_1=k_1[\mathrm{HBrO_2}][\mathrm{BrO_3^-}][\mathrm H^+],\qquad
v_4=k_4[\mathrm{HBrO_2}][\mathrm{Br^-}][\mathrm H^+].
\]

For positive \([\mathrm{HBrO_2}]\) and \([\mathrm H^+]\), cancellation of the common factors gives

\[
v_4>v_1
\iff [\mathrm{Br^-}]>
\frac{k_1[\mathrm{BrO_3^-}]}{k_4}
=\frac{(1.0\times10^4)(0.06)}{2.0\times10^9}
=3.00\times10^{-7}\ \mathrm M.
\]

This derives the required earlier-part dependency directly from the problem data. The problem says that step (4) exceeding step (1) selects Process B, and vice versa selects Process A.

1. Process C occurs continuously, and its printed step (7) is
   \(\mathrm{Ce^{4+}+BMA\to Ce^{3+}+Br^-+\cdots}\). Its elementary rate is proportional to \([\mathrm{Ce^{4+}}][\mathrm{BMA}]\). A Ce⁴⁺ pulse therefore accelerates Br⁻ production. During A this advances the rise through the critical Br⁻ level, selecting the **A-to-B switch (c)**.

2. The trusted general-chemistry fact used here is that Ag⁺ removes dissolved Br⁻ by precipitation of very sparingly soluble AgBr: \(\mathrm{Ag^++Br^-\to AgBr(s)}\). This lowers \([\mathrm{Br^-}]\), weakens step (4), and, once the critical boundary is crossed, selects the **B-to-A switch (d)**.

3. The source says that during the slow part of the cycle \([\mathrm{Br^-}]\) decreases from its maximum to the critical value. Adding Br⁻ increases the distance still to be consumed before that boundary is reached, so it **prolongs Process B (b)**. This argument uses monotonicity, not a constant traversal speed; the source explicitly says the phase portrait is not traversed at constant velocity.

4. Continuous Br⁻ addition, in the intended regime where it maintains \([\mathrm{Br^-}]>[\mathrm{Br^-}]_\text{critical}\), prevents the B-to-A boundary from being reached. The system remains in Process B and therefore **the oscillations stop (e)**.

## Source grounding and scope

- `T2_page-2.png` (original PDF page 16) supplies steps (1), (4), and (7), their rate constants, the maintained concentrations, and the fact that Process C is continuous.
- `T2_page-3.png` (original PDF page 17) supplies the phase portrait, the A/B switching rule, and the slow decrease of Br⁻ from its maximum to its critical value.
- `T2_page-4.png` (original PDF page 18) supplies the four actions and choices. The original blank student answer grid was independently inspected on PDF page 23 (A2-5); it requests exactly one of a-e for each action.
- The AgBr precipitation statement is a stable general chemistry law, not an answer imported from competition material.

There is a literal quantitative gap in the prompt: neither the two “small” pulse sizes nor the continuous Br⁻ feed rate is specified. Therefore an *instantaneous* switch in actions 1 or 2 requires a pulse large enough to cross the critical boundary, and action 4 requires a feed strong enough to keep Br⁻ above that boundary. A sub-threshold pulse would merely advance the corresponding switch, while an insufficient continuous feed could change the period rather than stop oscillation. The choices above are the intended qualitative classifications; the Lean formalization exposes these threshold/invariance conditions rather than claiming that every arbitrarily small dose or feed rate has the unconditional stated effect.
