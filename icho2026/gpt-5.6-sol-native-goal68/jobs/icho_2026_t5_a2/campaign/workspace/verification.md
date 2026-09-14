# Verification: `icho_2026_t5_a2`

## Source integrity and inspection

I read `GOAL.txt` and `TASK.json` first.  I then inspected both supplied PNG
pages and rendered the original PDF's Q5-1 and blank Q5-2 student-answer pages
directly (PDF page indices 43 and 44, i.e. file pages 44 and 45 in 1-based
counting).  The source hashes were checked with:

```sh
sha256sum icho_2026_source/image/T5_page-1.png icho_2026_source/image/T5_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result:

```text
4f1688b010a3470a1dec9e211f1577b2eab98b2cd1b9b990ccba4126875b6347  icho_2026_source/image/T5_page-1.png
7f0f35d726d79f8d1ff9b15ee00574efeb89d8b179ab05469b5c297cb147bb96  icho_2026_source/image/T5_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

All three values exactly match `TASK.json`.

## Lean verification

Final command:

```sh
lake env lean IChO2026Problems/problem_icho_2026_t5_a2.lean
```

Exit code: `0`.

The file itself ends with `#print axioms` for both final requested-output
theorems.  Exact output:

```text
'IChO2026Problems.T5A2.structure_pl1' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T5A2.structure_y' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the task.  There are no
custom axiom declarations and no `sorry`, `admit`, `unsafe`, or
`native_decide` proof shortcuts.  Checked with:

```sh
grep -nE '(^|[[:space:]])(sorry|admit|unsafe|native_decide)([[:space:]]|$)' IChO2026Problems/problem_icho_2026_t5_a2.lean
```

Result: no matches (exit code `1`, as expected for `grep` with no matches).

`result.json` was checked with:

```sh
python3 -m json.tool result.json
```

Result: valid JSON, exit code `0`.

## Semantic completion audit

| Requirement | Evidence in the Lean file |
|---|---|
| PL1 constitution | `covalentBonds`, `HasCardiolipinConnectivity`, `pl1R_cardiolipin_connectivity`, `pl1R_inventory`, `pl1R_validValences` |
| Every non-`R` atom, bond order, charge, and radical count | `AtomId`, `AtomState`, `covalentBonds`, `pl1R_all_formal_charges_zero`, `pl1R_closed_shell` |
| Four identical source-authorized `R` residues | the four `AtomId.residue` sites all have `Element.residueR`; `pl1R_inventory` proves count four |
| No peroxide bond | `pl1R_no_peroxide` and `yLeft_no_peroxide` |
| Requested PL1 stereochemistry | `pl1R` has `(R,R)`; `pl1R_pl1S_enantiomers` proves its `(S,S)` mirror differs while `reflection_preserves_pl1_connectivity` proves unchanged constitution |
| Source statement about other diastereomers | `mixed_diastereomers_are_achiral` proves the `(R,S)` and `(S,R)` assignments are reflection-invariant |
| Preceding-part dependency | `printedInventory n` keeps `n` symbolic; `source_constraints_force_n_eq_one` derives `n = 1` from port closure and `preceding_part_n_is_odd` derives odd parity |
| Y composition and charge | `yLeft_inventory`, `yLeft_charge_localization`, `yLeft_stabilized_monoanion` |
| Two explicit stabilizing hydrogen bonds | `hydrogenBonds`, `validHydrogenBond`, `yLeft_stabilized_monoanion` |
| Equivalent left/right forms of Y | `y_canonical_forms_reflected_atom_states` and `y_canonical_forms_reflected_connectivity` |
| Explanation of pKa ordering | `positive_stabilization_raises_second_pKa` proves `pKa1 < pKa2` from positive Y stabilization and the standard free-energy relation; `structure_y` incorporates it into the final certificate |

The task supplies no numerical semantics for `>>`; accordingly, the formal
result proves the strict qualitative ordering and the answer explicitly avoids
claiming an unsupported numerical separation.
