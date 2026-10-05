# IChO 2026, T7-A6 (subquestion 7.6) — Ranking of Red/Ad combinations by NH3 yield

## Task (as printed, T7_page-3.png / theory_problem.pdf p. 65)

"7.6 Rank the following **Red/Ad** combinations **A–D** by the decrease in ammonia
yield. 6.0 pt"

## Final answer

**B > C > D > A**

i.e. decreasing ammonia yield: **B** (highest yield) > **C** > **D** > **A** (lowest yield).

## Data from the problem (table of 7.6, printed page Q7-3)

| # | Red (reductant)     | E° (V) | Ad (protonated additive, CF3SO3− salt)   | pKa  |
|---|---------------------|--------|-------------------------------------------|------|
| A | Cp2Ni (nickelocene) | −0.09  | 1,10-phenanthrolinium                     | 13.7 |
| B | Cp2V (vanadocene)   | −1.10  | 2,6-lutidinium                            | 15.0 |
| C | Cp2V (vanadocene)   | −1.10  | 1,10-phenanthrolinium                     | 13.7 |
| D | Cp2V (vanadocene)   | −1.10  | anilinium                                 | 10.6 |

All four additives are triflate (CF3SO3−) salts, so the counterion does not
distinguish any pair in this question.

## Reasoning (source-grounding)

The reference table printed immediately above 7.6 on the same page reports measured
NH3 yields for combinations 1–4 and establishes the two single-parameter trends of
this PCET/CPET N2-fixation chemistry:

1. **Reductant trend.** Combination 3 (Cp2Co, E° = −1.15 V) gives 9.1 mol NH3 while
   combination 1 (Cp2Cr, E° = −0.88 V) gives 0 mol NH3, at essentially the same acid
   (pKa 13.9 vs 14.4).  A more negative E° of the reductant → higher yield.
2. **Acid trend.** Combination 4 (pKa 14.4, CF3SO3−) gives 11.8 mol NH3 while
   combination 2 (pKa 14.4, Cl−) gives 0.7 mol NH3 at the same reductant (Cp2Co);
   and among the triflate acids, 4 (pKa 14.4, 11.8 mol) outperforms 3 (pKa 13.9,
   9.1 mol).  A higher pKa (stronger acid, with CF3SO3−) → higher yield.

Applying these to A–D:

- **C > A** (pure reductant comparison): A and C share the same acid
  (1,10-phenanthrolinium, pKa 13.7); only the reductant changes, Cp2V
  (E° = −1.10 V) vs Cp2Ni (E° = −0.09 V).  By trend 1, C ≫ A.
- **B > C** (pure acid comparison): B and C share the same reductant (Cp2V,
  E° = −1.10 V); only the acid changes, 2,6-lutidinium (pKa 15.0) vs
  1,10-phenanthrolinium (pKa 13.7).  By trend 2, B > C.
- **C > D** (pure acid comparison): C and D share the same reductant; only the acid
  changes, pKa 13.7 (phenanthrolinium) vs pKa 10.6 (anilinium).  By trend 2, C > D.
- **D vs A** (both parameters change; quantitative comparison): switching A → D
  makes E° more negative by 1.01 V (favouring D), but lowers pKa by 3.1 (favouring
  A).  The two effects are brought onto a common scale by the Bordwell thermochemical
  relation for CPET,

      BDFE = 1.37·pKa + 23.06·E° + C   (kcal/mol),

  which in volt-equivalent units means the CPET driving force changes by
  Δ = ΔE° − 0.0591·ΔpKa, with 0.0591 V = RT·ln10/F per pKa unit at 298 K (a trusted
  general law of physical-organic/thermochemistry, not competition-specific data).

      Δ(A → D) = (−1.10 − (−0.09)) − 0.0591·(10.6 − 13.7)
               = −1.01 + 0.183 = −0.83 V,

  so the net driving force in D exceeds that in A by ≈ 0.83 V — the stronger
  reductant of D outweighs its weaker acid by a factor of more than five (1.01 V vs
  0.183 V).  Hence **D > A**.

Combining: **B > C > D > A**.

Note on framework consistency: this ordering is structurally forced by the two trends
for the chained comparisons B > C and C > D and C > A.  Only D vs A requires the
quantitative Bordwell weighing; the margin (a factor > 5) makes the conclusion robust
to any reasonable uncertainty in the 0.0591 V/pKa coefficient.

## Formalization

See `IChO2026Problems/problem_icho_2026_t7_a6.lean`.  The four combos are an
inductive type `Combo` with the printed `potential` (E°/V) and `pKa` functions; the
two experimentally grounded trends and the Bordwell weighing are packaged as the
structure `YieldOrder` (a score function `f : Combo → ℝ` with monotonicity fields),
and the ranking is proved as

- `C_above_A : f A < f C`
- `B_above_C : f C < f B`
- `C_above_D : f D < f C`
- `D_above_A : f A < f D`  (via the Bordwell joint hypothesis; arithmetic by `norm_num`)
- transitivity corollaries `B_above_D`, `B_above_A`
- `ranking_BCDA : f A < f D ∧ f D < f C ∧ f C < f B` — the requested ranking
- `all_pairs` — all six ordered-pair comparisons.

Verification: `lake env lean IChO2026Problems/problem_icho_2026_t7_a6.lean` compiles
without errors; `#print axioms` on the final theorems shows only the standard Lean
logical axioms `[propext, Classical.choice, Quot.sound]` (see `verification.md`).
