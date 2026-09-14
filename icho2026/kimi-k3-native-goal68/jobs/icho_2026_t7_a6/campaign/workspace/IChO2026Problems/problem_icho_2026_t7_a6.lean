import Mathlib

/-!
# IChO 2026, Problem T7 (Nitrogen Fixation), subquestion 7.6 (target `icho_2026_t7_a6`)

**Task.** "Rank the following Red/Ad combinations A–D by the decrease in ammonia
yield."  (6.0 pt; printed page 3 of problem T7, source page 65 of
`theory_problem.pdf`, image `T7_page-3.png`.)

## Problem data (read directly from the printed table of 7.6)

| # | Red                 | E deg (V) | Ad                            | pKa  |
|---|---------------------|-----------|--------------------------------|------|
| A | Cp2Ni (nickelocene) | -0.09     | 1,10-phenanthrolinium CF3SO3-  | 13.7 |
| B | Cp2V (vanadocene)   | -1.10     | 2,6-lutidinium CF3SO3-         | 15.0 |
| C | Cp2V (vanadocene)   | -1.10     | 1,10-phenanthrolinium CF3SO3-  | 13.7 |
| D | Cp2V (vanadocene)   | -1.10     | anilinium CF3SO3-              | 10.6 |

The preceding text on the same page gives the measured NH3 yields (mol) for the
reference combinations 1-4, which establish the *trends* of the underlying CPET
reduction of the Mo-NN complex 5:

- Reductant effect: combination 3 (Cp2Co, E deg = -1.15 V) gives 9.1 mol NH3
  while combination 1 (Cp2Cr, E deg = -0.88 V) gives 0 mol NH3, with (nearly)
  the same acid (pKa 13.9 vs 14.4).  Hence a **more negative E deg of the
  reductant (stronger reductant) increases the NH3 yield**.
- Acid/counterion effect: combination 4 (pKa 14.4, CF3SO3- counterion) gives
  11.8 mol NH3 while combination 2 (pKa 14.4, Cl- counterion) gives only
  0.7 mol NH3, with the same reductant (Cp2Co).  Hence for a given acid the
  CF3SO3- counterion outperforms Cl-, and among the CF3SO3- acids used in 7.6
  a **higher pKa (stronger acid) increases the NH3 yield**, consistent with
  3 (pKa 13.9, 9.1 mol) vs 4 (pKa 14.4, 11.8 mol).

## Solution (derived, not an input)

In a concerted proton-electron transfer (CPET) step of this N2-fixation
chemistry the driving force is governed by the Bordwell relation
BDFE = 1.37*pKa + 23.06*E deg + C, i.e. equivalently by the volt-equivalent
score  E deg - 0.0591*pKa : **lowering E deg and raising pKa both increase the
driving force, with 0.0591 V per pKa unit** (RT ln 10 / F at 298 K).

The four combinations A-D split into pairwise single-parameter comparisons
plus one quantitative comparison:

- C vs A (same acid, pKa 13.7): only the reductant changes, -1.10 V vs -0.09 V.
  Stronger reductant => C > A.
- B vs C (same reductant Cp2V, -1.10 V): only the acid changes, pKa 15.0 vs
  13.7.  Stronger acid => B > C.
- C vs D (same reductant): only the acid changes, pKa 13.7 vs 10.6.  Stronger
  acid => C > D.
- D vs A: D lowers E deg by 1.01 V relative to A (favouring D) but lowers pKa
  by 3.1 (favouring A by 3.1 x 0.0591 = 0.183 V).  Net 1.01 - 0.183 = +0.83 V
  favours D by more than a factor of five, so D > A.

Hence the ranking by decreasing NH3 yield is  **B > C > D > A**.
-/

namespace IChO2026.Problems.T7A6

/-- The four Red/Ad combinations of question 7.6. -/
inductive Combo : Type
  | A   -- Cp2Ni, E deg = -0.09 V; 1,10-phenanthrolinium CF3SO3-, pKa 13.7
  | B   -- Cp2V,  E deg = -1.10 V; 2,6-lutidinium CF3SO3-,       pKa 15.0
  | C   -- Cp2V,  E deg = -1.10 V; 1,10-phenanthrolinium CF3SO3-, pKa 13.7
  | D   -- Cp2V,  E deg = -1.10 V; anilinium CF3SO3-,            pKa 10.6
  deriving DecidableEq, Repr

/-- Printed standard reduction potential E deg of the reductant, in volts
(table of 7.6, `T7_page-3.png`). -/
def potential : Combo → ℝ
  | .A => -0.09
  | .B => -1.10
  | .C => -1.10
  | .D => -1.10

/-- Printed pKa of the protonated additive (table of 7.6, `T7_page-3.png`). -/
def pKa : Combo → ℝ
  | .A => 13.7
  | .B => 15.0
  | .C => 13.7
  | .D => 10.6

/-- The NH3-yield order: a score function `f` together with the two
experimentally grounded monotonicity principles (stronger reductant at fixed
acid => higher yield; stronger acid at fixed reductant => higher yield), plus
the Bordwell conversion factor 0.0591 V/pKa used to settle the one comparison
(D vs A) where the two single-parameter trends conflict.  Combination `x`
ranks above `y` (higher NH3 yield) iff `f x > f y`. -/
structure YieldOrder where
  f : Combo → ℝ
  /-- At fixed acid, making E deg more negative raises the yield
  (experiment 1 vs 3 on the same page: Cp2Cr gives 0 mol NH3, Cp2Co 9.1 mol). -/
  potential_mono : ∀ x y, pKa x = pKa y → potential x < potential y → f y < f x
  /-- At fixed reductant, raising the pKa raises the yield
  (experiments 3 vs 4: pKa 13.9 gives 9.1 mol, pKa 14.4 gives 11.8 mol, same
  reductant and counterion). -/
  pKa_mono : ∀ x y, potential x = potential y → pKa y < pKa x → f y < f x
  /-- Driving-force additivity across both parameters: by the Bordwell linear
  free-energy relation, the joint change of E deg by `potential y - potential x`
  volts and of pKa by `pKa x - pKa y` units shifts the yield score of `x`
  relative to `y` by at least `0.0591*(pKa x - pKa y) - (potential x - potential y)`
  in volt-equivalent units; if that shift is positive the yield of `x` exceeds
  that of `y`. -/
  bordwell_joint : ∀ x y,
    0 < (potential y - potential x) - (0.0591 : ℝ) * (pKa y - pKa x) →
    f y < f x

section Consequences

variable (ord : YieldOrder)

/-- C ranks strictly above A: same acid (pKa 13.7) and Cp2V is a far stronger
reductant than Cp2Ni (-1.10 V vs -0.09 V). -/
theorem C_above_A : ord.f .A < ord.f .C :=
  ord.potential_mono .C .A rfl (by norm_num [potential])

/-- B ranks strictly above C: same reductant (Cp2V, -1.10 V) and lutidinium is
a stronger acid than phenanthrolinium (pKa 15.0 vs 13.7). -/
theorem B_above_C : ord.f .C < ord.f .B :=
  ord.pKa_mono .B .C rfl (by norm_num [pKa])

/-- C ranks strictly above D: same reductant (Cp2V) and phenanthrolinium is a
much stronger acid than anilinium (pKa 13.7 vs 10.6). -/
theorem C_above_D : ord.f .D < ord.f .C :=
  ord.pKa_mono .C .D rfl (by norm_num [pKa])

/-- B ranks strictly above D (transitivity through C). -/
theorem B_above_D : ord.f .D < ord.f .B :=
  lt_trans (C_above_D ord) (B_above_C ord)

/-- B ranks strictly above A (transitivity through C). -/
theorem B_above_A : ord.f .A < ord.f .B :=
  lt_trans (C_above_A ord) (B_above_C ord)

/-- D ranks strictly above A.  Switching A -> D changes E deg by -1.01 V
(helping the yield by 1.01 V) and pKa by -3.1 (hurting by 3.1 x 0.0591 V =
0.183 V).  The Bordwell volt-equivalent net change 1.01 - 0.183 = +0.827 V is
positive, so the stronger-reductant advantage of D outweighs its weaker acid
by a factor of more than five. -/
theorem D_above_A : ord.f .A < ord.f .D := by
  apply ord.bordwell_joint .D .A
  norm_num [pKa, potential]

/-- The complete strict ranking requested by 7.6: **B > C > D > A** by
decreasing NH3 yield. -/
theorem ranking_BCDA :
    ord.f .A < ord.f .D ∧ ord.f .D < ord.f .C ∧ ord.f .C < ord.f .B :=
  ⟨D_above_A ord, C_above_D ord, B_above_C ord⟩

/-- Rank-space phrasing: B is #1, C is #2, D is #3, A is #4. -/
theorem rank_positions :
    ord.f .B > ord.f .C ∧ ord.f .C > ord.f .D ∧ ord.f .D > ord.f .A :=
  ⟨B_above_C ord, C_above_D ord, D_above_A ord⟩

/-- Totality sanity check: the ranking B > C > D > A decides all six ordered
pairs of distinct combos.  The three missing comparisons (B vs D, B vs A,
C vs A) follow from transitivity, proved above as `B_above_D`, `B_above_A` and
`C_above_A`. -/
theorem all_pairs :
    ord.f .C < ord.f .B ∧ ord.f .D < ord.f .B ∧ ord.f .A < ord.f .B ∧
    ord.f .D < ord.f .C ∧ ord.f .A < ord.f .C ∧ ord.f .A < ord.f .D :=
  ⟨B_above_C ord, B_above_D ord, B_above_A ord,
   C_above_D ord, C_above_A ord, D_above_A ord⟩

end Consequences

end IChO2026.Problems.T7A6
