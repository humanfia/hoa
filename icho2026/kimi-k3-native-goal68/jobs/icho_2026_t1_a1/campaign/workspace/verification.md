# Verification — target `icho_2026_t1_a1`

## Environment

- Lean `(version 4.31.0, x86_64-unknown-linux-gnu, commit 68218e876d2a38b1985b8590fff244a83c321783, Release)`
- Lake version 5.0.0-src+68218e8 (Lean version 4.31.0)
- `lean-toolchain`: `leanprover/lean4:v4.31.0`
- Mathlib rev `v4.31.0` (prebuilt in `.lake/packages/mathlib`), resolved via
  the untouched `lakefile.toml` / `lake-manifest.json` of this workspace.

## Files under verification

- `IChO2026Problems/problem_icho_2026_t1_a1.lean` — the formalisation
  (namespace `IChO2026T1A1`).
- `IChO2026Problems/All.lean` — umbrella import
  (`import IChO2026Problems.problem_icho_2026_t1_a1`), created so that the
  fixed workspace umbrella `IChO2026Problems.lean`
  (`import IChO2026Problems.All`) and `lake build` cover the target file.

No source inputs (`icho_2026_source/**`, `TASK.json`, `GOAL.txt`),
`lakefile.toml`, or `.lake/**` were modified.

## Commands and results

### 1. Direct kernel check of the final file

```
$ lake env lean IChO2026Problems/problem_icho_2026_t1_a1.lean
'IChO2026T1A1.t1_a1_answer' depends on axioms: [propext, Quot.sound]
'IChO2026T1A1.t1_a1_answer_compound_numbers' depends on axioms: [propext, Quot.sound]
(exit code 0, no errors, no warnings)
```

### 2. Full project build

```
$ lake build
Build completed successfully (8581 jobs).
(exit code 0)
```

This produces `.lake/build/lib/lean/IChO2026Problems/problem_icho_2026_t1_a1.olean`
and `All.olean`.

### 3. Axiom audit (`#print axioms`, printed by the final file itself)

Both final theorems depend only on the standard Lean logical axioms
`propext` and `Quot.sound`. In particular:

- no `sorryAx` — no `sorry`/`admit` anywhere in the proof;
- no `Classical.choice` — the development is fully constructive/computational
  (all finite checks are kernel `decide`/`Decidable.decide` computations);
- no custom axioms or `axiom` declarations exist in the file: the five
  trusted general laws (`law_mirror`, `law_tetra`, `law_cage`,
  `law_isomer_formula`, `law_ether_cyclisation`) and the two geometric
  premises (`hCageB`, `hCageU`) are explicit hypotheses (function
  arguments) of `t1_a1_answer`, universally quantified in its type, not
  axioms.

## What is proved (theorem inventory, all in `IChO2026T1A1`)

Problem input layer

- `Formula`, `printedFormula : Fin 10 → Formula` — the ten printed formulae,
  compound number minus one as index.
- `formulaC10H18O_carriers` — C₁₀H₁₈O is printed exactly under compounds
  2, 3, 6, 10 (kernel `decide`).
- `shared_formula_class` — two table compounds share a printed formula only
  if equal or both in {2, 3, 6, 10} (kernel `decide`; the formula filter).

Graph model layer (`structure Gr`, symmetric bond-order map `mkBo`,
symmetries `Gr.Valid`/`Gr.ValidN` with `decidableValid`,
forcing lemmas `fixed_of_unique`, `fixed_of_nb`, `inj`)

- `gBorneol` (2), `gCineole` (3), `gLinalool` (6), `gUmbellulone` (10):
  heavy-atom graphs read from the drawings on printed page Q1-2.
- Encoding sanity: `borneol_Ccount/Ocount/Hcount`, `cineole_*`,
  `linalool_*` — each has 10 C, 1 O, 18 H as drawn (matches the printed
  C₁₀H₁₈O); `umbellulone_Ccount/Ocount` plus
  `umbellulone_Hcount_drawn : Hcount gUmbellulone 11 = 16` documenting the
  printed-label vs drawing discrepancy for compound 10.

Symmetry layer

- `cineoleMirror`, `cineoleMirror_valid`, `cineoleMirror_moves`,
  `cineoleMirror_fixed` — compound 3 realises the involution
  (4 5)(7 9)(8 10) (the drawn mirror plane).
- `borneol_sym_cases`, `linalool_sym_cases`, `umbellulone_sym_cases` —
  complete classification of the labelled involutory symmetries of 2, 6, 10
  (identity or the inevitable equivalent-methyl swap), each step discharged
  by kernel-checked uniqueness tables.
- `borneol_no_mirror`, `linalool_no_mirror`, `umbellulone_no_mirror` —
  under `law_cage` (+ cage rigidity premises) resp. `law_tetra`, compounds
  2, 6, 10 cannot have a mirror plane.

Functional-group layer

- `borneol_noCC` (no C=C), `borneol_hasOH`, `linalool_hasOH`,
  `linalool_hasCC`, `umbellulone_noOH`, `cineole_etherO`.

Cyclisation-consistency layer (drawn 6 → 3 reaction)

- `linToCin`, `linToCin_inj`, `cyclisation_preserved`,
  `cyclisation_elements`, `cyclisation_newbond1`, `cyclisation_newbond2`.

Conclusion

- `t1_a1_answer` — given the explicit law hypotheses and the problem data
  (`X ≠ Y`, X isomerises to Y, Y has a mirror plane):
  `X = ⟨5, …⟩ ∧ Y = ⟨2, …⟩ : Fin 10`, i.e. compounds 6 and 3.
- `t1_a1_answer_compound_numbers` — answer-sheet form:
  `X.val = 5 ∧ Y.val = 2` (compound numbers 6 and 3).

## Trusted assumptions (declared, not hidden)

The five laws and two cage-rigidity premises are the only chemistry that is
not mechanically derived from the problem page; they are stated as arguments
of the final theorems (see the header comment of the Lean file and
`result.json → assumptions`). Separating them satisfies the task policy of
distinguishing problem inputs from derived lemmas: everything else —
candidates, symmetries, functional groups, the cyclisation map, the final
case analysis — is kernel-verified from the printed page data.

## Source gap recorded

Compound 10: printed label C₁₀H₁₈O vs drawn skeleton hydrogen count 16
(`umbellulone_Hcount_drawn`). Elimination of 10 is structural and unaffected
by either reading; see `answer.md`, last section.
