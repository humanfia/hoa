# Answer — IChO 2026, T7 (Nitrogen Fixation), Part 7.3 (target `icho_2026_t7_a3`)

## Source grounding

The question text used here comes from the official English problem page
`T7_page-2.png` (printed page 2, box 7.3, 15.0 pt), read against the cyclic-model
description printed immediately above it:

> Consider a model of a real reaction system, which includes recirculation of
> reagents. An open system operates in a cyclic mode. Each cycle consists of four
> steps:
> 1. A stoichiometric N₂ : H₂ = 1 : 3 mixture with a total amount of n₀ mol is fed
>    into the reactor **after each cycle**.
> 2. The reaction proceeds with a constant yield of η = 0.150.
> 3. Ammonia is separated by liquification.
> 4. Unreacted gases are returned into the reactor.
>
> The cycle is repeated until the required overall yield is reached.

(Fig. 2 confirms the loop: after the cooler (CLR), the unreacted N₂, H₂ stream
returns to the reactor while NH₃ leaves the system.)

**7.3 a)** Calculate the amount of nitrogen, present in the system after the 58th
cycle (before the addition of the 59th portion of mixture), if n₀ = 4 mol.
Provide 4 decimal places. (Hint: a formula for the sum of the terms of a geometric
progression is needed.)

**7.3 b)** Calculate the number of cycles needed to increase the **overall** yield
from 15.0 % to 97.0 %.

## Model (derived from the four printed steps)

Follow the nitrogen; H₂ is always fed and recycled in the same fixed 3 : 1
proportion, so it behaves identically and the nitrogen inventory determines the
whole stoichiometric inventory.

* Each freshly fed portion carries n₀/4 mol of N₂ (a 1 : 3 stoichiometric mixture
  of total n₀ mol is one quarter N₂).
* In every cycle the reaction converts the constant fraction η = 0.150 of the
  nitrogen then present in the reactor (step 2); the ammonia formed is liquefied
  and removed (step 3), and the fraction 1 − η = 0.85 of the nitrogen survives and
  is recycled (step 4), where it mixes with the next fresh portion (step 1).

Let Aₖ be the nitrogen inventory inside the reactor during cycle k (after the k-th
portion has been added, before reaction) and Nₖ the inventory after cycle k
(after ammonia removal, before portion k + 1 is added). The four steps give

* Aₖ = (1 − η)·Nₖ₋₁ + n₀/4, with N₀ = 0 (the system starts empty; the 1st portion
  is the first feed),
* Nₖ = (1 − η)·Aₖ.

**Recurrence** (proved in Lean as `nitrogen_recurrence`):

  Nₖ = (1 − η)²·Nₖ₋₁ + n₀·(1 − η)/4,   N₀ = 0.

**Closed form** (geometric progression, exactly the suggested hint). Unrolling,

  Nₖ = Σⱼ₌₁…ₖ (n₀(1−η)/4)·(1 − η)^{2(k−j)}
     = (n₀(1−η)/4)·Σᵢ₌₀…ᵏ⁻¹ (1 − η)²ⁱ
     = (n₀(1−η)/4)·[1 − (1 − η)^{2k}]/[1 − (1 − η)²]
     = (n₀(1−η)/4)·[1 − (1 − η)^{2k}]/[η(2 − η)].

With n₀ = 4 mol and η = 0.150:

  **Nₖ = 0.85·(1 − 0.85^{2k})/0.2775 mol of N₂.**

(Checked against the recurrence: at k = 1, N₁ = 0.85·A₁ = 0.85·1 = 0.85 mol, and
the closed form gives 0.85·(1 − 0.85²)/0.2775 = 0.85·0.2775/0.2775 = 0.85 ✓.)

## 7.3 a) Nitrogen after the 58th cycle

  N₅₈ = 0.85·(1 − 0.85¹¹⁶)/0.2775      (raw exact expression; no intermediate rounding)

Since 0.85¹¹⁶ ≈ 6.50 × 10⁻⁹ is negligible, the system is essentially at its
steady-state inventory:

  N₅₈ ≈ 0.85/0.2775 = 3.06306304… mol  →  **N₅₈ = 3.0631 mol**

at the requested 4 decimal places (tie rule irrelevant: the raw value is not a
half-quantum tie).

## 7.3 b) Cycles needed to raise the overall yield from 15.0 % to 97.0 %

In a recycle process the **overall** yield is the fraction of all fed reactant
that has left the system as product. Every portion fed experiences the constant
per-cycle conversion η: after 1 cycle a portion has been 15.0 % converted (the
single-pass yield — exactly the "from 15.0 %" baseline named in the question),
and the unconverted fraction of the feed that remains after n cycles is 0.85ⁿ.
Hence the overall yield after n cycles is

  **Y(n) = 1 − (1 − η)ⁿ = 1 − 0.85ⁿ.**

Require Y(n) ≥ 0.970, i.e. 0.85ⁿ ≤ 0.030:

  n ≥ ln(0.030)/ln(0.85) = 21.5763…   ⟹   **n = 22 cycles.**

Boundary check with the exact printed constants, no intermediate rounding:

* 21 cycles: 0.85²¹ = 0.0324174957698178… > 0.030, so Y(21) = 0.96758… < 0.970 —
  not enough;
* 22 cycles: 0.85²² = 0.0275548714043452… < 0.030, so Y(22) = 0.9719962… ≥ 0.970
  — enough.

## Final answers

* **a) Amount of N₂ after the 58th cycle = 3.0631 mol** (raw value
  0.85·(1 − 0.85¹¹⁶)/0.2775 = 3.06306304… mol).
* **b) 22 cycles.**

## Lean formalization

`IChO2026Problems/problem_icho_2026_t7_a3.lean` proves, without `sorry`/`admit`
and without custom axioms:

* `nitrogen_recurrence` — the inventory recurrence derived from the four printed
  cycle steps;
* `nitrogen_inventory_geo_sum` / `nitrogen_inventory_closedForm` — the geometric
  sum and the closed form Nₖ = 0.85·(1 − 0.7225ᵏ)/0.2775, valid for every k;
* `overallYield_eq_one_sub_pow` — overall yield after n cycles is 1 − 0.85ⁿ;
* `twenty_one_cycles_yield_below` / `twenty_two_cycles_yield_at_least` — the
  boundary check at the exact constants 0.150 and 0.970 printed in the problem;
* `cycles_for_97_percent` — 22 is the least number of cycles with overall yield
  at least 97.0 %;
* `nitrogen_after_58_cycles_reports_3_0631_mol` — the exact inventory
  0.85·(1 − 0.7225⁵⁸)/0.2775 mol reports as **3.0631** at the requested
  4-decimal-place quantum under the project answer-blind reporting contract
  `IChO2026Chem.Reporting.ValidNumericSubmission`.

Only Lean's standard logical axioms appear in `#print axioms` of the final
theorems (`propext`, `Classical.choice`, `Quot.sound`); no custom axioms are used.
