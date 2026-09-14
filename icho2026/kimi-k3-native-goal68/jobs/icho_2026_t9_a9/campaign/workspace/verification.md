# Verification record — icho_2026_t9_a9

## Target

IChO 2026 Theory Problem 9, subquestion 9.9 (T9-A9, 4.0 pt).
Requested output (from TASK.json): a single exact integer
`arrangement_count` — the number of functional-group arrangements on a
hexadifferentiated α-CD (only CH₂OH groups modified).

Derived value: **120**.

## Files

* `answer.md` — natural-language answer and source grounding.
* `IChO2026Problems/problem_icho_2026_t9_a9.lean` — formalized model and proof.

## Verification commands

All commands were run from the workspace root
`.../campaign/workspace` with the pinned toolchain
`/home/jing/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lake`
(Lean 4 v4.31.0, mathlib v4.31.0, dependencies pre-built in the shared
`.lake/packages` store).

### 1. Direct elaboration of the target file

```
$ /home/jing/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lake env lean \
    IChO2026Problems/problem_icho_2026_t9_a9.lean

exit=0
```

stdout:
```
'IChO2026.T9.A9.patterns_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T9.A9.rotation_action_isFree' depends on axioms: [propext, Quot.sound]
'IChO2026.T9.A9.orbit_card_eq_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026.T9.A9.arrangement_count' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit code 0 (success).  All four theorems depend only on the standard Lean
logical axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`,
no custom axioms, no `unsafe` declarations are used.

### 2. Theorem-to-question cross-check (semantic faithfulness)

* Requested output: "the number of all possible arrangements of the functional
  groups on a hexadifferentiated α-CD (assume only the CH₂OH groups have been
  modified)" — an exact integer.
* Formal statement proven:
  `arrangement_count : Fintype.card Arrangement = 120`, where
  `Arrangement := MulAction.orbitRel.Quotient Rot Pattern` is exactly the set of
  bijective assignments of six distinct groups (`Fin 6`) to six sites
  (`ZMod 6`) modulo the six cyclic rotations.  This matches "possible
  arrangements of the functional groups" under the problem's stipulation that
  only the CH₂OH sites are modified and the standard chemist's convention that
  arrangements differing by a rotation of the chiral macrocycle are the same
  molecule, whereas reflection (enantiomer) is a different molecule and is
  therefore **not** quotiented out.
* Supporting proved facts: `patterns_count` (6! = 720 addressed patterns),
  `rotation_action_isFree` (no nontrivial rotation fixes an arrangement —
  this is where the "all six groups distinct" hypothesis enters),
  `orbit_card_eq_six` (each equivalence class has exactly 6 elements).

## Notes on scope and assumptions

* The count 120 is conditional on the chemically standard reading of
  "arrangement": assignments considered up to the 6 rotations of the
  macrocycle.  The problem's context (Logical counting analogues in 9.6;
  Sollogoub *et al.*'s hexadifferentiated α-CD in 9.8) and the chirality of
  α-CD justify the absence of a reflection factor.  This modelling choice is
  stated explicitly in both `answer.md` and the Lean module docstring.
* No numerical input is measured; all constants (`6`, `120`, `720`) are exact
  derived integers, so the answer-blind reporting policy ("exact integer")
  is satisfied by construction.
