# Verification for `icho_2026_t8_a4`

Verified on 2026-09-13 UTC from the current workspace.

## Original-source inspection

Command:

```bash
python3 - <<'PY'
import fitz
p = 'icho_2026_source/raw/theory_problem.pdf'
doc = fitz.open(p)
print('pages', doc.page_count)
for index in (71, 72, 78, 79):
    text = ' '.join(doc[index].get_text('text').split())
    print('physical_page', index + 1, text[:240])
PY
```

Result: exit code 0.  It reported a 93-page PDF and identified physical pages
72=`Q8-1`, 73=`Q8-2`, 79=`A8-3`, and 80=`A8-4`.  The extracted A8-3 text
contains `OS = +3, CN = 6` for 11 and `CN = 5` for 12.  A8-4 contains
`OS = +2` for 13 and `VE = 16` for 15.  (PyMuPDF also emitted its API
deprecation warning; this did not affect extraction.)

Command:

```bash
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T8_page-1.png icho_2026_source/image/T8_page-2.png icho_2026_source/image/icho_2026_t8_a4-page-79.png icho_2026_source/image/icho_2026_t8_a4-page-80.png
```

Result: exit code 0.

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
3490231dd64238ab3db32a48d86f92c857f9fef386b510c45ba1b80f483cc843  icho_2026_source/image/T8_page-1.png
cfd3c6fa64d0126843e3cf65a1235337fa3f869db285f36fbb0a18dddebfacee  icho_2026_source/image/T8_page-2.png
7aaf33edb9693cd4c92076a32b764f9405171405319cc8d62377ba0d2699d785  icho_2026_source/image/icho_2026_t8_a4-page-79.png
2e374bd278ead1b3f53725ea2a7a8629a935f9f5754f24c12c714fbebc1efdab  icho_2026_source/image/icho_2026_t8_a4-page-80.png
```

## Lean build and axiom audit

Command:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t8_a4.lean
```

Result: exit code 0.  The `#print axioms` directives in the final file
reported:

```text
'IChO2026Problems.T8A4.all_fragment_graphs_wellFormed' depends on axioms: [propext]
'IChO2026Problems.T8A4.ligand8_has_four_nitrogen_donors' does not depend on any axioms
'IChO2026Problems.T8A4.labile_sites_are_cis' does not depend on any axioms
'IChO2026Problems.T8A4.reconstructed_structures_wellFormed' depends on axioms: [propext]
'IChO2026Problems.T8A4.structure_9' does not depend on any axioms
'IChO2026Problems.T8A4.structure_10' does not depend on any axioms
'IChO2026Problems.T8A4.structure_11' does not depend on any axioms
'IChO2026Problems.T8A4.structure_12' does not depend on any axioms
'IChO2026Problems.T8A4.structure_13' does not depend on any axioms
'IChO2026Problems.T8A4.structure_14' does not depend on any axioms
'IChO2026Problems.T8A4.structure_15' does not depend on any axioms
'IChO2026Problems.T8A4.complex_9_outputs' depends on axioms: [propext]
'IChO2026Problems.T8A4.complex_10_outputs' depends on axioms: [propext]
'IChO2026Problems.T8A4.complex_11_outputs' depends on axioms: [propext]
'IChO2026Problems.T8A4.complex_12_outputs' depends on axioms: [propext]
'IChO2026Problems.T8A4.complex_13_outputs' depends on axioms: [propext]
'IChO2026Problems.T8A4.complex_14_outputs' depends on axioms: [propext]
'IChO2026Problems.T8A4.complex_15_outputs' depends on axioms: [propext]
'IChO2026Problems.T8A4.radical_parities' depends on axioms: [propext]
'IChO2026Problems.T8A4.supplied_answer_sheet_fields_match' depends on axioms: [propext]
'IChO2026Problems.T8A4.catalytic_cycle_closes' does not depend on any axioms
'IChO2026Problems.T8A4.catalytic_cycle_net_reaction' does not depend on any axioms
```

`propext` is a standard Lean logical axiom, expressly allowed by the goal.
There are no custom axioms and no native-evaluation soundness axioms.  An
earlier development build used `native_decide`; its generated native axioms
were detected by this audit and every such proof was replaced by kernel
`decide` before the recorded final build.

Command:

```bash
grep -nE '(^|[[:space:]])(sorry|admit|unsafe)([[:space:]]|$)|^[[:space:]]*axiom[[:space:]]' IChO2026Problems/problem_icho_2026_t8_a4.lean || true
```

Result: exit code 0 with no output.  The final file contains no `sorry`,
`admit`, `unsafe`, or custom `axiom` declaration.

## Semantic completion audit

| Requirement | Evidence in the final state |
|---|---|
| Structures 9-15 | `structure_9` through `structure_15` prove the exact typed fragment and Fe-site inventory derived by successive `applyStep` operations. |
| Explicit connectivity | `fragmentGraph` lists every non-cartoon atom, formal charge, radical count, covalent bond order, Fe donor atom, and stereocentre list. `BoundFragment.donorSites` gives every Fe bond. Ligand 8 is represented at the N4-cartoon resolution required by the question. |
| Geometric consistency | `labile_sites_are_cis` and `reconstructed_structures_wellFormed` prove cis-site placement, correct denticity, valid atom indices, and no duplicate occupied Fe sites. |
| OS, CN, VE, Z for every species | `complex_9_outputs` through `complex_15_outputs` prove all 28 integers from charge conservation, ligand ionic charges, donor counts, and the group-8 electron formula. |
| Supplied answer-sheet data respected | `supplied_answer_sheet_fields_match` proves all five printed constraints simultaneously. |
| Mechanism consistency | `catalytic_cycle_closes` proves exact regeneration of 9; `catalytic_cycle_net_reaction` proves the summed reaction CO2 + 2H+ + 2e- -> CO + H2O. |
| Natural-language answer and grounding | `answer.md` gives the structures, values, derivation, input-page provenance, hashes, and the limited general chemistry conventions used. |

The semantic audit found no unsupported condition and no source gap.  In
particular, the retained aqua ligand in 14 and 15 is required both by the
printed water-addition arrow and by the answer sheet's `VE(15) = 16`; omitting
it would produce a four-coordinate, 14-electron complex and contradict the
source.
