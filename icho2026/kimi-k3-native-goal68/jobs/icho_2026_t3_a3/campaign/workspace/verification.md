# Verification record — icho_2026_t3_a3 (IChO 2026 T3.3)

## Build command

```
cd /home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t3_a3/campaign/workspace
lake env lean IChO2026Problems/problem_icho_2026_t3_a3.lean
```

Exit code: **0** (no errors, no warnings).

Toolchain: `lean-toolchain` in repo; `lake env lean` runs Lean with Mathlib
on the path (Mathlib is a cached dependency, `lake-manifest.json` present).

## Shortcut audit

```
grep -n "sorry\|native_decide\|admit\b\|axiom " IChO2026Problems/problem_icho_2026_t3_a3.lean
```

Output: only line 39 — the English word "admit" inside a doc comment
("the 2D topology figures admit only planar building blocks"). No `sorry`,
no `admit`, no `native_decide`, no custom `axiom` declarations in code.

## Axiom inspection (`#print axioms`)

```
'IChO2026T3A3.table_fill_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A3.filled_entries_realise' depends on axioms: [propext]
'IChO2026T3A3.square_net_exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A3.hexagonal2_net_exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A3.trigonal_net_exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A3.tetrahedral_net_exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T3A3.supplied_hexagonal1' depends on axioms: [propext]
'IChO2026T3A3.supplied_hexagonal2' depends on axioms: [propext]
'IChO2026T3A3.supplied_kagome' depends on axioms: [propext]
```

Every final theorem uses only the standard Lean logical axioms
(`propext`, `Classical.choice`, `Quot.sound`). **No** `sorryAx`, no custom
unchecked axioms.

## Semantic-faithfulness check (independent of the build)

The requested output is a completed table (exact-symbolic classification).
The formalization encodes:

* every monomer connectivity counted from the printed structures;
* the three allowed condensation classes from the Q3-3 banner;
* each net's role signature read off its printed figure/example;
* the three printed table examples (proved to realise their columns);
* exhaustive enumeration certificates (`*_net_exhaustive`, proved by
  `fin_cases` over all 15×15 ordered printed pairs) that *list* every
  admissible pair per net — this is what grounds each XXX;
* the master theorem `table_fill_correct`, whose conjuncts state that
  (i) every filled entry is new, (ii) every admissible pair of every column
  except Hexagonal 1 is already committed (justifying those XXX cells), and
  (iii) Hexagonal 1 retains an uncommitted witness E1+D4 (justifying the
  *absence* of an XXX in that column).

Single remaining interpretive point (declared honestly in `answer.md`): the
Hexagonal 1 vs Hexagonal 2 distinction rests on the role signature forced by
the printed examples (3,2 with A2+B3 vs 3,3 with E1+D2). No official
solution, marking scheme, or answer repository was consulted; enumeration
was independently computed both in Python and kernel-checked in Lean.
