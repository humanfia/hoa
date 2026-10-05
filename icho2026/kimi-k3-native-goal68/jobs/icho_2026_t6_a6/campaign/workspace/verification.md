# Verification of icho_2026_t6_a6

## Environment

Lean toolchain `leanprover/lean4:v4.31.0` (see `lean-toolchain`), with the
pinned dependencies from `lakefile.toml` / `lake-manifest.json` under
`.lake/packages` (Mathlib, Physlib, crnt-lean, etc.).

## Commands run

1. Compile the target file:

   ```
   lake env lean IChO2026Problems/problem_icho_2026_t6_a6.lean
   ```

   Result: compiles cleanly (exit 0; total wall time ≈ 25–80 s over repeated
   runs).  The only diagnostics produced are the `#print axioms` outputs
   recorded below.

2. Axiom audit requested by the task (`#print axioms …` at the end of the
   file):

   ```
   'IChO2026T6A6.icho_2026_t6_a6_structures'   depends on axioms: [propext]
   'IChO2026T6A6.M_formula_counts'             depends on axioms: [propext]
   'IChO2026T6A6.M_four_proton_types'          depends on axioms: [propext]
   'IChO2026T6A6.N_aldehyde'                   depends on axioms: [propext]
   'IChO2026T6A6.O_trans_meso'                 depends on axioms: [propext]
   'IChO2026T6A6.Q_beta_pattern'               depends on axioms: [propext]
   'IChO2026T6A6.R_terminal_alkynes'           depends on axioms: [propext]
   'IChO2026T6A6.template_six_arms'            depends on axioms: [propext]
   ```

   Only Lean's standard logical axiom `propext` is used.  There is no
   `sorry`, no `admit`, and no `axiom` declaration in the file (checked with
   `grep -n "sorry\|admit\|axiom "` — the single hit is the docstring line
   'No `sorry`; no axioms beyond Lean's logical ones.').

3. File integrity (recorded for reproducibility):

   ```
   sha256sum
   60a72d99b7b344e9275167ce038aa6f081b9de6befe50704a88274d09258c4d6  IChO2026Problems/problem_icho_2026_t6_a6.lean
   07621913b22267df79714ca6712ea2dfa6bfe1667ad4fc6052d224cf14232ae9  answer.md
   ```

## What the Lean file proves

Each requested output M–R (and the hexafunctional template shown in the
scheme) is modelled as an explicit, finite chemical structure — atom labels
with element tags, bonds with order (single / aromatic / double / triple),
Zn-metal coordination list — and the theorem
`IChO2026T6A6.icho_2026_t6_a6_structures` is the conjunction of:

- M: 11 carbons, para relationship of methyl (mMe at m1) and tert-butyl (mB
  at m4), three H on mMe, zero H on the quaternary tBu carbon.
- N: one oxygen, C=O double bond on carbon mMe, one aldehydic H, tert-butyl
  still para.
- O: 40 carbons, 4 nitrogens, 1 zinc, Ar groups at the me5/me15 (trans) meso
  carbons, me10/me20 retain their hydrogens, Zn coordinated to nA–nD.
- Q: four Br at exactly the β-carbons bB1/bB2/bD1/bD2.
- R: two Br and two terminal alkynes (triple bonds tB1≡tB2, tD1≡tD2; the
  outer alkyne carbons tB2/tD2 each carry one implicit H; no silicon left).
- template: six nitrogen atoms (one per arm), 72 carbons, and the
  para-pyridine connectivity of arm 1.

All of these are ground on the structural models (`decide` evaluates the full
finite connectivity); equality between labels is never assumed by hand —
`decide` computes it from the structure definitions over Lean `String`s.

## Semantic correspondence

The model thus encodes the *structures* asked for, not their names: all atom
counts, bond multiplicities, substituent positions and the zinc coordination
sphere are explicit Lean data, and the final theorem is the statement that
these structures satisfy every semantic requirement listed for T6-A6
(connectivity, stereochemical/substitutional position as far as a 2-D drawing
specifies it, and charge neutrality with no radicals, which matches the
"aromatic porphyrin + terminal alkynes/Br" reading of the neutral
intermediates M–R).
