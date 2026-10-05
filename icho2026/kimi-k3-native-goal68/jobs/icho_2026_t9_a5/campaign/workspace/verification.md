# Verification — icho_2026_t9_a5

## Environment

* Workspace: `/home/jing/icho-native-goal-kimi68-20260914-01/jobs/icho_2026_t9_a5/campaign/workspace`
* Toolchain: `leanprover/lean4:v4.31.0` (`lean-toolchain`)
* Libraries: Mathlib v4.31.0, Physlib, crnt-lean (prebuilt in `.lake/packages`)

## Exact commands run

### 1. Direct elaboration of the target file (required check)

```
lake env lean IChO2026Problems/problem_icho_2026_t9_a5.lean
```

Result: **exit code 0, no errors, no warnings** (no `sorry`/`admit`/axioms
present in the file; verified by literal grep below).

### 2. Full library build

```
lake build IChO2026Problems
```

Result: `Build completed successfully (8564 jobs).`  The only warning is a
pre-existing style-linter note about a >100-character comment line in the
fixed umbrella `IChO2026Problems.lean`, which is part of the immutable
infrastructure and was not modified.

### 3. Axiom inspection of every final theorem (temporary check file, since deleted)

`IChO2026Problems/AxCheck.lean` was created containing
`import IChO2026Problems.problem_icho_2026_t9_a5` and `#print axioms` for
each of the 24 theorems below, then run with
`lake env lean IChO2026Problems/AxCheck.lean`, then removed (`rm`).

Result — every theorem depends on nothing beyond the standard Lean logical
axioms, none of them on all three, none on anything custom:

| Theorem | Axioms |
|---|---|
| `lTemplate_free_primary_at_1_and_4` | none |
| `lTemplate_protic_at_unit1` | `propext` |
| `lTemplate_secondary_allBn` | none |
| `lTemplate_exactly_two_free_OH` | none |
| `lTemplate_benzyl_count` | none |
| `lTemplate_wellFormed` | none |
| `sinayRule_realised_in_L` | none |
| `sinayRule_forces_3_or_4` | none |
| `sinayRule_unit6_not_chosen` | `propext`, `Quot.sound` |
| `sinayRule_unit3_not_chosen` | `propext`, `Quot.sound` |
| `sinayRule_second_at_4` | `propext`, `Quot.sound` |
| `step2_gives_lTemplate` | none |
| `step2_unique` | `propext` |
| `lTemplate_d7_fixed` | `propext` |
| `lMolecule_formula` | `propext` |
| `lMolecule_formula_consistent` | `propext` |
| `perbenzylBetaCD_formula` | none |
| `betaCDMolecule_formula` | `propext` |
| `betaCDCore_formula` | `propext` |
| `glucoseResidue_formula` | none |
| `benzylation_excess` | none |
| `dibal_substoichiometric` | none |
| `dimerRing_box_counts` | none |
| `dimer_arises_from_L` | none |

All are standard logical axioms (`propext`, `Quot.sound`); **no custom or
unchecked axioms** (`sorryAx` absent everywhere).

### 4. No-cheating grep

```
grep -nE 'sorry|admit|axiom |native_decide|unsafe' IChO2026Problems/problem_icho_2026_t9_a5.lean
```

Result: no matches.

## Semantic-faithfulness audit (independent of the build)

* The requested output is a *structure-drawing* classification: fill every
  box of the β-CD template for L.  `lTemplate` specifies all 7 primary boxes
  in printed unit order (`[H, Bn, Bn, H, Bn, Bn, Bn]`), all 7 secondary
  pairs (`(Bn, Bn)`) and the face box `(Bn, 14)` — nothing is left
  unspecified.
* Connectivity/substituents are bound to explicit atoms: `lMolecule` =
  `betaCDCore` + per-box `substFragment` fragments; `lMolecule_formula`
  proves C₁₇₅H₁₈₄O₃₅ (= C₄₂H₇₀O₃₅ + 19·C₇H₆), cross-checked by
  `l_formula_by_count` / `lMolecule_formula_consistent`.
* The derivation is proved from problem-stated constraints only:
  30 ≥ 21 exhaustive benzylation (`benzylation_excess`), 2 < 7 DIBAL-H
  sub-stoichiometry (`dibal_substoichiometric`), Sinay forward/fallback
  rules quoted from the preamble (`sinayRule_*`), uniqueness of the
  unit-4 second cleavage (`sinayRule_second_at_4`, `step2_unique`), the
  C₇-symmetry justification of the unit-1 anchor (`lTemplate_d7_fixed`),
  and site-wise agreement with the printed dimer
  (`dimerRing_box_counts`, `dimer_arises_from_L`).
* The α-1,4 stereochemistry and all 35 pyranose stereocentres are invariant
  under every reagent on the page and are inherited from the shared-context
  figure; the electing positions (2°,3°,6′) are the only degrees of freedom
  the blank template asks to fill, and they are all fixed by the theorems.

## Source inputs used

T9 pages Q9-1/Q9-2/Q9-3/Q9-4 (images in `icho_2026_source/image/`), the
shared context quoted in TASK.json, and trusted general chemistry laws
(Williamson benzylation; DIBAL-H reductive debenzylation of primary benzyl
ethers; allylation–olefin metathesis–hydrogenation tether logic).  No
official answers, marking schemes, grading reports or answer repositories
were consulted.
