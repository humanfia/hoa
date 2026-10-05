# Verification record — icho_2026_t9_a3 (IChO 2026, T9, question 9.3)

All commands run from the workspace root
`/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t9_a3/campaign/workspace`
with `$HOME/.elan/bin` on `PATH` (Lake 5.0.0 / Lean 4.31.0, Mathlib v4.31.0
pinned in `lakefile.toml`, prebuilt oleans in `.lake/packages/*/.../lib/lean`).

## Compilation command

```
export PATH="$HOME/.elan/bin:$PATH"
lake env lean IChO2026Problems/problem_icho_2026_t9_a3.lean
echo "LEAN_EXIT: $?"
```

Result: `LEAN_EXIT: 0`. No errors, no linter warnings in the final build.

## Axiom inspection

The file ends with `#print axioms` commands for the final theorems and the
key supporting lemmas. Output of the compile run (captured verbatim):

```
'IChO2026T9A3.icho_2026_t9_a3_ring_size' depends on axioms: [propext, Quot.sound]
'IChO2026T9A3.icho_2026_t9_a3_stereocentres' does not depend on any axioms
'IChO2026T9A3.icho_2026_t9_a3_answer' depends on axioms: [propext, Quot.sound]
'IChO2026T9A3.x_ring_is_cycle' depends on axioms: [propext, Quot.sound]
'IChO2026T9A3.x_bond_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T9A3.x_backbone_mem_ring' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T9A3.ringList_isWalk' depends on axioms: [propext, Quot.sound]
'IChO2026T9A3.ringList_closes' depends on axioms: [propext, Quot.sound]
```

Only Lean's standard logical axioms appear (`propext`, `Classical.choice`,
`Quot.sound`). In particular **no `sorryAx`** appears anywhere — there are no
`sorry`/`admit` placeholders. This was additionally checked source-side:

```
grep -c -E '\bsorry\b|\badmit\b' IChO2026Problems/problem_icho_2026_t9_a3.lean
# -> 0
```

## What the final theorems state (semantic-faithfulness check)

The requested outputs of 9.3 are two integers:

- `icho_2026_t9_a3_ring_size : rsX = 7 * 5 ∧ rsX = 35` where
  `rsX := ringList.length` and `ringList` is the explicit 35-atom closed
  traverse of the macrocycle's bond graph (7 units × 5 ring atoms per unit:
  C1, glycosidic O, C4, C5, ring O5). Substantiveness is carried by
  - `x_ring_is_cycle`: the traverse is a walk of real bonds, closes onto its
    start, has 35 distinct atoms (`ringList_isWalk`, `ringList_closes`,
    `ringList_nodup`);
  - `x_backbone_mem_ring` / `x_ring_elems_backbone`: the ring passes through
    exactly the backbone atoms (5 per unit);
  - `x_bond_exact` with `ringEdges_disjoint_armEdges`: every one of the
    7 × 8 = 56 bonds of X is either one of the 35 ring edges or one of the 21
    pendant-arm stubs, so no chord can shorten the ring and arms cannot lie
    on any cycle — the counted ring is the actual macrocyclic ring.
- `icho_2026_t9_a3_stereocentres : scX = 7 * 3 ∧ scX = 21` where
  `scX := 7 * 3`, justified per unit by `scX_per_unit`: C1, C4, C5 each bear
  four pairwise distinct substituents (`c1_stereogenic`, `c4_stereogenic`,
  `c5_stereogenic` — the two ring directions at each centre are
  diastereomorphic, CIP rule 5, since X is chiral with no mirror/inversion
  symmetry), while the former C2/C3 (now –CH₂OAc arms) and C6 carry two
  hydrogens each (`arm2_not_stereogenic`, `arm3_not_stereogenic`,
  `arm6_not_stereogenic`).

The theorem statements express 35 and 21 as consequences of an explicit
structural model of X (the bond graph of the NaIO₄-cleaved, NaBH₄-reduced,
acetylated β-CD), i.e. they encode the requested chemistry rather than merely
asserting the numerals.

## Answer-blindness and provenance

Source inputs consulted: `icho_2026_source/image/T9_page-{1..5}.png` and the
`TASK.json` problem text (page Q9-1 gives β-CD with "n = 7", "(OH)₁₄", 7 ×
CH₂OH; page Q9-2 gives the scheme `X ← NaIO₄; NaBH₄/H₂O; Ac₂O/Py` from the
7-fold bracketed unit bearing a free 2,3-vicinal diol, and the question text
of 9.3). No solutions, marking schemes, answer repositories, or external
solver agents were used. General reactivity facts (Malaprade periodate
cleavage of vicinal diols; NaBH₄ reduction of aldehydes; Ac₂O/Py acetylation;
ethers/ketals inert to these reagents) are ordinary textbook laws, permitted
by the candidate domain policy (`trusted_general_law`).
