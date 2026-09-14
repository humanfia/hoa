# Verification – target `icho_2026_t6_a1` (IChO 2026, T6, subquestion 6.1)

Date: 2026-09-14 (UTC). Toolchain: `leanprover/lean4:v4.31.0` (see
`lean-toolchain`); Lake 5.0.0; project deps pinned in `lake-manifest.json`
(Mathlib v4.31.0, Physlib, crnt-lean).

## Files

* Formalisation: `IChO2026Problems/problem_icho_2026_t6_a1.lean`
* Umbrella import: `IChO2026Problems/All.lean` (imports the file above; this
  is the file the fixed `IChO2026Problems.lean` umbrella expects)
* Natural-language answer: `answer.md`

No source inputs or generic infrastructure were modified.

## Commands and results

### 1. Direct compile of the final file

```
$ lake env lean IChO2026Problems/problem_icho_2026_t6_a1.lean
exit code: 0
stdout/stderr (the `#print axioms` reports):

'IChO2026Problems.T6A1.answer_c18_aromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A1.answer_c18_antiaromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A1.answer_c16_aromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A1.answer_c16_antiaromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A1.answer_triplet_c13_aromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A1.answer_triplet_c13_antiaromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A1.answer_singlet_c13_aromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A1.answer_singlet_c13_antiaromatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A1.huckel_exclusion' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T6A1.c13_loop_not_closed_shell' depends on axioms: [propext]
'IChO2026Problems.T6A1.completedTable_correct' depends on axioms: [propext, Quot.sound]
```

All eight answer theorems and all supporting lemmas depend **only** on Lean's
three standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`).
`Classical.choice` enters solely through the classical `if` on the Hückel
propositions — the propositions themselves are each proved or refuted
constructively (by `norm_num` witnesses and `omega` refutations).
No `sorryAx`, no custom axioms.

### 2. Full project build

```
$ lake build
✔ [8580/8581] Built IChO2026Run (10s)
Build completed successfully (8581 jobs).
```

(One pre-existing style warning about line length in the fixed infrastructure
file `IChO2026Problems.lean`, unrelated to this target.)

### 3. No proof shortcuts

```
$ grep -n "sorry\|admit\|axiom " IChO2026Problems/problem_icho_2026_t6_a1.lean
grep-exit=1   (no matches)
```

## Semantic faithfulness check (independent of the green build)

* The eight theorem names `answer_c18_aromatic` …
  `answer_singlet_c13_antiaromatic` correspond one-to-one to the eight
  requested outputs of `TASK.json` (`c18_aromatic`, `c18_antiaromatic`,
  `c16_aromatic`, `c16_antiaromatic`, `triplet_c13_aromatic`,
  `triplet_c13_antiaromatic`, `singlet_c13_aromatic`,
  `singlet_c13_antiaromatic`).
* Each statement computes the number of the molecule's cyclic π loops whose
  electron count satisfies the corresponding Hückel predicate
  (`HuckelAromaticCount n := ∃ k, n = 4k+2`,
  `HuckelAntiaromaticCount n := ∃ k, n = 4k`) and equates it to the answered
  integer. The predicates are stated from first principles; the residues
  (18 = 4·4+2, 16 = 4·4, 12 = 4·3, 13 neither, 13 odd) are all proved with
  `norm_num`/`omega`, so no answer value is assumed.
* `completedTable_correct` pins the filled 4×2 table
  (rows C18, C16, ³C13, ¹C13; columns A, AA) to (2,0), (0,2), (0,1), (0,0),
  matching the natural-language answer in `answer.md`.
* The problem's given spin labels for C13 (triplet S = 1, singlet S = 0)
  enter through the electron-counting structure `CyclocarbonPiCounting`,
  which records the two orthogonal π loops per sp-hybridised ring carbon as
  `problem inputs`, while every classification is a derived theorem.
