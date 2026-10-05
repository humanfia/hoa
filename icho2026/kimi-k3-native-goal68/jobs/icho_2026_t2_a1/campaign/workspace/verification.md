# Verification log - target `icho_2026_t2_a1` (IChO 2026, T2, question 2.1)

Environment: Lean (version 4.31.0, x86_64-unknown-linux-gnu, commit
68218e876d2a38b1985b8590fff244a83c321783, Release); repository toolchain
`leanprover/lean4:v4.31.0` with pinned Mathlib v4.31.0 (prebuilt under
`.lake/packages/mathlib/.lake/build`).

## Commands run and results

1. Compilation of the deliverable (exact command):

       lake env lean --root=. IChO2026Problems/problem_icho_2026_t2_a1.lean

   Exit code: 0. No errors, no warnings. Output (from the `#print axioms`
   commands at the end of the file):

       'IChO2026.overallBZ_isBalanced' does not depend on any axioms
       'IChO2026.overallBZ_atom_balance' does not depend on any axioms
       'IChO2026.overallBZ_charge_balance' does not depend on any axioms
       'IChO2026.oxidation_half_reaction_balance' does not depend on any axioms
       'IChO2026.reduction_half_reaction_balance' does not depend on any axioms
       'IChO2026.electron_lcm' does not depend on any axioms

   Every final theorem is completely axiom-free: no `sorryAx`, no custom
   axioms, and not even the standard logical axioms `propext`,
   `Classical.choice`, `Quot.sound`. All proof obligations are closed by the
   kernel via `rfl`/`decide`/`List.not_mem_nil`.

2. No-shortcut audit:

       grep -nE "sorry|admit|^axiom|unsafe|set_option" \
         IChO2026Problems/problem_icho_2026_t2_a1.lean

   The only match is the word "axioms" inside a documentation comment
   (line 44). There is no `sorry`, `admit`, `axiom` declaration, `unsafe`
   definition, or `set_option` override in the file.

3. Toolchain version command:

       lake env lean --version

   Output: `Lean (version 4.31.0, ..., Release)`.

## Semantic faithfulness check (independent of the green build)

- Requested output (TASK.json, `requested_outputs[0]`): "overall balanced BZ
  reaction with atoms and charge conserved", kind `formula`,
  reporting `exact_symbolic`.
- The formal `overallBZ` lists reactants `(3, MA)` and `(4, BrO3)` and
  products `(9, CO2)`, `(4, BrIon)`, `(6, H2O)` - i.e. exactly the equation
  written in `answer.md`:

      3 CH2(COOH)2 + 4 BrO3- -> 9 CO2 + 4 Br- + 6 H2O

- `MA` is defined as C3H4O4 (neutral), matching the problem's "CH2(COOH)2";
  `BrO3` carries charge -1, `BrIon` charge -1, `CO2` and `H2O` charge 0, so
  the problem-stated redox partners and the acidic-medium species are encoded
  faithfully.
- `Reaction.IsBalanced` requires per-element conservation for
  C, H, O, Br, charge conservation, and nonzero coefficients; the kernel
  evaluates `elementTotal`/`chargeTotal` on both sides (C: 9 = 9,
  H: 12 = 12, O: 24 = 24, Br: 4 = 4, charge: -4 = -4) - the same arithmetic
  as the hand verification table in `answer.md`.
- The derivation lemmas (`oxidation_half_reaction_balance`,
  `reduction_half_reaction_balance`, `electron_lcm`) prove the half-reaction
  bookkeeping (8 e- released per MA, 6 e- consumed per BrO3-, lcm 24,
  multiplicities 3 and 4) from which the 3 : 4 stoichiometry follows.
- Cerium appears in neither side of `overallBZ`, consistent with the
  problem note "Ce(IV) is a catalyst"; `cerium_is_catalyst_balance` records
  the corresponding (trivial) balance row.

## Source inputs consulted (not modified)

- `TASK.json` (target contract), `GOAL.txt`.
- `icho_2026_source/image/T2_page-1.png` (question 2.1, page Q2-1) and
  `T2_page-2.png` (mechanism, used only as within-problem corroboration).
- `icho_2026_source/raw/theory_problem.pdf` page 15 (question 2.1) and
  page 19 (answer sheet A2-1, blank field for 2.1).

No source input or shared infrastructure file was modified. Only the three
deliverables (`answer.md`,
`IChO2026Problems/problem_icho_2026_t2_a1.lean`, this file) plus
`result.json` were created.
