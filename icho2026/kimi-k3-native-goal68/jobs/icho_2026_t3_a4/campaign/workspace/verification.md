# Verification — icho_2026_t3_a4

## Environment

* workspace: `/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t3_a4/campaign/workspace`
* toolchain: `leanprover/lean4:v4.31.0` (elan), mathlib `v4.31.0`
* sources read (no inputs modified): `TASK.json`, `GOAL.txt`,
  `icho_2026_source/image/T3_page-1.png`, `…/T3_page-2.png`,
  `…/T3_page-3.png`, `…/T3_page-4.png`, `…/T3_page-5.png`,
  `…/T3_page-6.png`, `icho_2026_source/raw/theory_problem.pdf`
  (93 pages; T3 question pages at PDF indices 24–30, incl. printed Q3-4
  at index 27; blank student answer sheet for 3.4 = printed A3-3 at PDF
  index 33, confirmed to be four empty boxes COF-3/4/5/6).

## Commands and results

```bash
cd /home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t3_a4/campaign/workspace
lake env lean IChO2026Problems/problem_icho_2026_t3_a4.lean
```

Exit code 0, no errors or warnings.  The file's `#print axioms` commands
report exactly:

```
'IChO2026.T3.t3_a4_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T3.cof3Content_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T3.cof3_empirical' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T3.cof4Content_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T3.cof5Content_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T3.cof3_cof4_hydrogen_balance' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T3.imine_condensation_balance' does not depend on any axioms
'IChO2026.T3.patterns_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T3.monomer_hydrogen_content' does not depend on any axioms
'IChO2026.T3.cof3_has_imine' does not depend on any axioms
'IChO2026.T3.cof4_different_CN' does not depend on any axioms
'IChO2026.T3.cof4_benzoxazole_hydrogen_balance' does not depend on any axioms
'IChO2026.T3.cof6_no_imine' does not depend on any axioms
'IChO2026.T3.cof5_cof6_isomerisation' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T3.cof6_is_keto_enamine' does not depend on any axioms
```

No `sorry`/`admit`/`sorryAx` and no custom axioms anywhere; only the
standard Lean logical axioms appear (and several theorems are entirely
axiom-free).

```bash
lake build IChO2026Problems
```

Build completed successfully (8564 jobs); the only diagnostics are the
pre-existing style linter notes (short copyright header in the shared
`IChO2026Chem` files and a long line in the fixed umbrella
`IChO2026Problems.lean`), which are part of the unmodified generic
infrastructure.

## Semantic faithfulness audit (structure-drawing target)

The requested outputs are drawings; the formalisation represents each
answer by (a) a substitution-pattern description of the exact monomers
parsed from the Q3-4 schemes (`trialdPattern`, `dahbaPattern`,
`thtPattern`, `pdaPattern` with `patterns_consistent` and
`monomer_hydrogen_content` cross-checks), (b) an executed condensation
balance (`imineStep`, `imine_condensation_balance`: –CHO + H₂N– → –CH=N–
+ H₂O, –2H –O per link), (c) rational half-linker repeat-unit ledgers
(`cof3Content`, `cof4Content`, `cof5Content` with proven values
(18,12,3,3), (18,9,3,3), (18,12,3,3) in C,H,N,O — i.e. empirical formulas
C₂₁H₁₅N₃O₄, C₂₁H₉N₃O₄, C₁₈H₁₂N₃O₃), and (d) per-repeat-unit bond/class
inventories (`cof3Inventory`, `cof4Inventory`, `cof5Inventory`,
`cof6Inventory`) on which every observational constraint is proved:

* COF-3 has 3 imine C=N (`cof3_has_imine`) — imine IR stretch honoured.
* COF-4: 2 benzoxazole ("different type") C=N + 1 edge imine arm, no
  isolated imine network; the empirical hydrogen loss COF-3 → COF-4 is
  proved equal to 6 (`cof3_cof4_hydrogen_balance`) and the benzoxazole
  construction reproduces it (`cof4_benzoxazole_hydrogen_balance`).
* COF-5: 3 imines + 3 phenolic OH, composition C₁₈H₁₂N₃O₃.
* COF-6: 0 imines (`cof6_no_imine` → no imine stretch), 3 ketones,
  3 enamine N–H; composition identical to COF-5
  (`cof5_cof6_isomerisation`, matching "irreversibly isomerises").

The dashed-edge convention in the theorems uses the halved-linker ledger —
exactly the bisected-shared-ring drawing rule the problem displays for
COF-1 (checked visually on T3_page-4 and T3_page-1).

Remaining modelling gap (documented in answer.md): the four answers are
drawings; a picture is communicated here by its typed structure inventory
rather than pixels.  Within that representation, the "different type of
C=N" of COF-4 is a deduction (benzoxazole, unique consistent with all
four constraints) rather than a printed premise; the file and answer.md
state this explicitly.
