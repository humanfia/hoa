# Verification record — target `icho_2026_t7_a6`

All commands run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t7_a6/campaign/workspace`
on 2026-09-14 with the project toolchain `leanprover/lean4:v4.31.0`
(pre-required dependencies incl. mathlib v4.31.0 oleans available).

## 1. Compilation of the formalization

Command:

    lake env lean IChO2026Problems/problem_icho_2026_t7_a6.lean

Result: exit code 0, no errors, no warnings, no `sorry`/`admit`.
Standard output and standard error were empty.

## 2. Axiom inspection of the final theorems

The file content was copied to `/tmp/axcheck_t7a6.lean` and the following lines
appended:

    open IChO2026.Problems.T7A6
    #print axioms ranking_BCDA
    #print axioms rank_positions
    #print axioms all_pairs
    #print axioms D_above_A
    #print axioms B_above_C
    #print axioms C_above_D
    #print axioms C_above_A

Command:

    lake env lean /tmp/axcheck_t7a6.lean

Result (exit code 0):

    'IChO2026.Problems.T7A6.ranking_BCDA' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026.Problems.T7A6.rank_positions' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026.Problems.T7A6.all_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026.Problems.T7A6.D_above_A' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026.Problems.T7A6.B_above_C' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026.Problems.T7A6.C_above_D' depends on axioms: [propext, Classical.choice, Quot.sound]
    'IChO2026.Problems.T7A6.C_above_A' depends on axioms: [propext, Classical.choice, Quot.sound]

Only the standard Lean logical axioms are used; no custom/unchecked axioms.

## 3. Semantic faithfulness check (independent audit)

- The theorem statements use exactly the problem's printed data: the table of 7.6
  (`T7_page-3.png`) gives Red identity/E° (A: Cp2Ni, −0.09 V; B,C,D: Cp2V, −1.10 V)
  and Ad identity/pKa (A,C: phenanthrolinium 13.7; B: lutidinium 15.0; D: anilinium
  10.6); these are encoded as `potential` and `pKa` and checked by the `norm_num`
  arithmetic in each proof.
- The proved proposition `ranking_BCDA` is `f A < f D ∧ f D < f C ∧ f C < f B`, i.e.
  the strict ranking B > C > D > A by decreasing NH3 yield — exactly the requested
  output `yield_ranking` ("rank Red/Ad combinations A–D by decreasing ammonia
  yield"; kind classification, exact symbolic).
- Nothing about the final answer is an axiom: the rankings are *derived* from the
  `YieldOrder` hypotheses, which encode only (i) the two single-parameter trends
  evidenced by the problem's own reference yields 1–4 printed above 7.6, and (ii)
  the Bordwell conversion factor 0.0591 V/pKa (trusted general physical-organic
  law), used solely for the cross-parameter comparison D vs A.  The `norm_num`
  side condition in `D_above_A` proves that the reductant advantage of D over A
  (1.01 V) exceeds the acid disadvantage (3.1 × 0.0591 = 0.183 V) with positive
  margin (+0.827 V), which is what grounds D > A.
- No results from official solutions, marking schemes, or answer repositories were
  consulted; the ranking was derived from the problem statement plus the stated
  general laws.

## 4. Source inputs used (read-only)

- `TASK.json`
- `icho_2026_source/image/T7_page-3.png` (tables for 7.5 reference yields and 7.6)
- `icho_2026_source/image/T7_page-2.png` (context of T7, scheme for 7.5)
- `icho_2026_source/raw/theory_problem.pdf` (sha256 af51373f43..., source page 65)
- `icho_2026_source/questions_only.jsonl` (blind bundle row for T7-A6)
