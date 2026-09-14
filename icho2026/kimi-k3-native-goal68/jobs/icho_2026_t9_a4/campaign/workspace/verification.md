# Verification — IChO 2026, subquestion icho_2026_t9_a4 (T9.4)

## Deliverables

- `answer.md` — natural-language solution with source grounding (question page Q9-2,
  source page 85 of `theory_problem.pdf`; answer-sheet template A9-2 of the same PDF).
- `IChO2026Problems/problem_icho_2026_t9_a4.lean` — self-contained Lean 4 file
  (Mathlib v4.31.0, pinned toolchain) formalising the derived structure of Y.

## Exact verification commands and results

Run from the workspace root (which contains `lakefile.toml` / `lake-manifest.json`
against the prebuilt Mathlib):

```
timeout 580 lake env lean IChO2026Problems/problem_icho_2026_t9_a4.lean
```

Result (run 2026-09-14, full output saved in `/tmp/final_build.log`):

- Exit code 0.
- No diagnostics at all except the three requested `#print axioms` outputs:

```
'IChO2026T9A4.icho_2026_t9_a4_structure_of_Y' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T9A4.y_structure_matches_printed_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026T9A4.y_inversion_at_C2_C3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

That is exactly the standard axiom set of Lean's logic; in particular there is **no
`sorryAx`**, no `Classical.choice`-incompatible custom axioms, and no custom unchecked
axiom anywhere in the file.

## Theorem inventory (all proved, no sorry/admit)

Structural core:

- `unit_carbons`, `unit_hydrogens`, `unit_oxygens`, `unit_silicons` — per-unit site
  counts 12 / 22 / 4 / 1 (computational).
- `yUnitFullFormula_eq` — the explicit per-unit formula of the derived unit is
  C12 H22 O4 Si.
- `unitCoordC_eval`, `unitCoordS_eval`, `unitCoordO_eval`, `unitCoordI_eval` — per-unit
  coordinate sums 12, 22, 4, 1.
- `y_formula_decomposes` — the formula of the explicit 102-vertex macrocycle `Y`
  factors as 6 × the per-unit formula, coordinate by coordinate (via
  `Finset.sum_sigma'` over `Fin 6 × UnitV`).
- `y_structure_matches_printed_formula` — **`Y.formula = ⟨72, 132, 24, 6⟩`**, the
  formula printed under the Y arrow on Q9-2 and on the A9-2 template
  (C72H132O24Si6).
- `y_total_c`, `y_total_h`, `y_total_o`, `y_total_si` — the totals elementwise.
- `y_formula_is_six_units` — cross-check `Y.formula = 6 • yUnitFormula`.

Graph well-formedness:

- `y_bond_symm`, `y_bond_irrefl`, `y_bondOrder_pos`, `y_bondOrder_one` — symmetric,
  irreflexive, all bond orders exactly 1 (only single bonds, as drawn).
- `y_vertex_count` — 6 × 17 = 102 vertices.

Chemistry content:

- `y_unit_intrabonds` — pyranose ring bonds, the C2–Oe and C3–Oe epoxide bonds, the
  C4–Og glycosidic arm, and the full C6–Os–Si–(Sm1, Sm2, Sq–{tB1,tB2,tB3}) TBS arm,
  per unit.
- `y_glycosidic_bonds` — the α-1,4 closure `Og(i)–C1(i+1 mod 6)`, both directions.
- `y_epoxide_bridge` — per unit an oxygen `Oe` bonded to the adjacent carbons C2 and
  C3 (which are themselves bonded): a genuine three-membered anhydro ring.
- `y_no_free_OH` — no oxygen vertex carries a hydrogen: no free —OH remains in Y.
- `y_ring_carbon_hydrogens` — C1…C5 each carry exactly one H (tetrahedral
  stereocentres); C6 carries two.
- `y_stereocentre_C2`, `y_stereocentre_C3` — C2 and C3 are stereocentres in the
  operative sense (distinct up/down face substituents).
- `y_inversion_at_C2_C3` — the epoxide oxygen bridges from the **up** face at both C2
  and C3: inversion at both centres relative to α-CD.
- `y_alpha_link_face` — α configuration retained at C1 (predecessor glycosidic oxygen
  on the down face), C4 arm down, C6 arm up.
- `y_silicon_vertices`, `y_silicon_count6` — exactly six silicon sites, one per unit.
- `y_tbs_group` — each Si bears Os, two methyls and the quaternary tert-butyl carbon
  with its three CH3 groups; `Sq` is H-free.
- `yFace_holds` / `yFaceLabels` — the complete per-unit stereochemical reading of the
  answer template.

Deliverable:

- `icho_2026_t9_a4_structure_of_Y` — the conjunction packaging all of the above plus
  the formula fingerprint, `#print axioms`-checked to depend only on
  `[propext, Classical.choice, Quot.sound]`.

## Semantic-faithfulness check (independent)

The theorem states and proves the requested chemistry, mapped conjunct-by-conjunct:

| Problem requirement (answer sheet A9-2, Q9-2 scheme) | Lean witness |
|---|---|
| Complete the **CD template**: six glucopyranose-derived units, cyclic | `Fintype.card YV = 102` (6 × 17) + `y_glycosidic_bonds` (Og(i)–C1(i+1 mod 6)) |
| Correct formula, printed as C72H132O24Si6 | `y_structure_matches_printed_formula` |
| Stereochemistry "unambiguously" | face labels: `y_inversion_at_C2_C3`, `y_alpha_link_face`, `yFace_holds` |
| TBS protecting groups (TBSCl, 6 equiv.) | `y_silicon_count6`, `y_tbs_group` |
| No residual free OH | `y_no_free_OH` |
| 2,3-anhydro linkage per unit (forced by NaH/TsCl sequel → α-cycloaltrin) | `y_epoxide_bridge` + `y_inversion_at_C2_C3` |
| Only single bonds | `y_bondOrder_one` |

No part of the requested output (structure + stereochemistry of Y) is replaced by a
string equality or assumed target: connectivity, element labels, hydrogen counts, bond
orders and face stereochemistry are all explicit data of `Y : Molecule`, and every
required property is a theorem about exactly that graph.

## Notes

- `set_option maxRecDepth 32768 in` is used locally on three proof blocks; it only
  raises the elaborator recursion budget and introduces no axiom (confirmed by the
  `#print axioms` runs above).
- Source inputs (`theory_problem.pdf`, page images) were not modified.
