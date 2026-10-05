# IChO 2026 — Theory Problem T5 (Cardiolipins), subquestion 5.1 (`icho_2026_t5_a1`)

## Ticked answer

**(b) — n is an odd number.**

## Source grounding

All inputs come from the official problem sheet (image `T5_page-1.png`,
`theory_problem.pdf`, printed page 44).  The statement says PL1 (the
non-ionised form of a cardiolipin) can be assembled "using only the
structural elements a–d in the quantities stated below", and the figure
gives:

| fragment | identity | quantity | free valences per fragment | transferable H per fragment |
|---|---|---|---|---|
| a | bare hydrogen  —H | n | 1 (the cap) | 0 (it *is* the cap, not an acid proton) |
| b | phosphoric acid  HO–P(=O)(OH)–,  with P=O fixed | 2 | 2 (two P–OH oxygens) | 2 (the two P–OH protons) |
| c | glycerol skeleton | 3 | 3 | 0 |
| d | fatty acid residue  R–C(=O)–  (with free valence on the acyl O side) | 4 | 1 | 0 |

The worked example on the same page (assembly of W from one a, one b, one c,
one d, one e fragment into a phospholipid with an intact P–OH proton) shows
the grammar of the game: fragments are joined at their wavy valences; a
hydrogen fragment caps a wavy valence without consuming a hydrogen atom,
whereas joining two fragments condenses off H₂O and consumes exactly one of
the acidic (transferable) hydrogens.

Nothing else from the page is needed for 5.1: in particular the "no peroxide
bonds" clause and the later chirality/acidity paragraphs are irrelevant to
the parity question.

## Derivation

Let a, b, c denote the numbers of phosphate, glycerol and fatty-acyl
fragments (stipulated as a = 2, b = 3, c = 4) and n the unknown number of
hydrogen fragments.  Let k be the number of inter-fragment bonds.

**Hydrogen (condensation) balance.**  The total budget of transferable
hydrogens is 2a + 0·b + 0·c + 0·n = 2a … plus the n capping hydrogens
contribute nothing to condensation; precisely: only the 2a phosphate P–OH
protons plus — read as a balance — every inter-fragment bond was formed by
eliminating one H₂O and so consumed exactly one of these hydrogens:

  k = 2a + n         (budget = number of condensation bonds × 1)

**Valence balance.**  Every inter-fragment bond pairs exactly two free
valences, so the total valence count is even and equals 2k:

  2k = 2a + 3b + c + n

Eliminating k gives

  2(2a + n) = 2a + 3b + c + n   ⟹   n + 2a = 3b + c.

Hence n ≡ 3b + c (mod 2).  With the stipulated quantities,

  n + 2·2 = 3·3 + 4 = 13   ⟹   n = 9, and in particular n ≡ 1 (mod 2).

So n is forced to be **odd**; (b) is the unique correct statement.

## Consistency check

Cardiolipin (1,3-bis(sn-3′-phosphatidyl)-sn-glycerol skeleton) does indeed
assemble from 3 glycerols, 2 phosphates and 4 fatty acyl residues: the
non-ionised molecule still bears exactly one P–OH proton on each phosphate,
and 13 condensation bonds join 26 free valences — 4 + 9 + 4 + 9 = 26 = 2×13
— exactly as the balances require with n = 9.  This shows the counting model
is satisfiable, so the parity theorem is not vacuous.

## Lean formalization

`IChO2026Problems/problem_icho_2026_t5_a1.lean` defines:

* `Recipe` — fragment multiplicities (a phosphates, b glycerols, c acyls,
  n hydrogens), with `Recipe.PL1 n = ⟨2, 3, 4, n⟩` the stipulated PL1
  quantities;
* `Recipe.attachPoints`, `Recipe.transferableH`, `Recipe.Feasible` — the two
  source-grounded balance equations (one transferable hydrogen per
  inter-fragment bond; two attachment points per inter-fragment bond) as the
  *only* feasibility hypotheses;
* proved lemmas: `hydrogen_balance` (2·transferableH = attachPoints),
  `n_eq` (n + 2a = 3b + c), `n_parity` (n % 2 = (3b + c) % 2),
  `n_mod_two_eq_one` and `n_eq_nine` for the PL1 quantities;
* final classification theorems `answer_b_n_is_odd`,
  `answer_a_n_even_impossible`, `answer_c_parity_not_free` and
  `t5_a1_answer`, stating that every feasible PL1 assembly has n odd
  (indeed n = 9), so (b) holds and (a), (c) are excluded;
* the witness `pl1_feasible_at_nine` showing satisfiability.

Verification (commands and axiom report) is recorded in `verification.md`;
all final theorems depend only on the standard Lean axioms `propext`,
`Classical.choice`, `Quot.sound`.
