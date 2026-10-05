# Verification record: `icho_2026_t9_a4`

Date: 2026-09-13 (UTC)

## Source inspection

I read `GOAL.txt` and `TASK.json` first. I visually inspected the designated source images `icho_2026_source/image/T9_page-1.png` and `T9_page-2.png`. I also opened the original `theory_problem.pdf` and inspected its problem pages 84–85 and blank student answer-sheet pages 89–90; page 90 contains the blank six-repeat template for 9.4 and prints `Y – C72H132O24Si6`.

Command:

```bash
sha256sum icho_2026_source/image/T9_page-1.png icho_2026_source/image/T9_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
c7f5114e9bb5d3e821a3df76d40c4ab86006fdb550992aa8013bc50b68a90608  icho_2026_source/image/T9_page-1.png
a65b4bf067ff9b1aa03ad40758319abec68f959fce4bf64380bd0e8227bee48f  icho_2026_source/image/T9_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

Command used to inspect the PDF’s text layer and locate both question and answer-sheet pages:

```bash
python3 - <<'PY'
import pymupdf
p='icho_2026_source/raw/theory_problem.pdf'
doc=pymupdf.open(p)
print('page_count:', doc.page_count)
for n in (84, 85, 89, 90):
    text=' '.join(doc[n-1].get_text().split())
    print(f'page {n}:', text[:260])
PY
```

Result (exit code 0): PDF page count 93; page labels were `Q9-1`, `Q9-2`, `A9-1`, and `A9-2`, respectively. The page-90 text was:

```text
Theory A9-2 English (Official) 9.3 (8.0 pt) rs : __________________ sc : __________________ 9.4 (3.0 pt) Y – C72H132O24Si6
```

## Lean verification

Command:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t9_a4.lean
```

Result (exit code 0):

```text
'IChO2026Problems.Icho2026T9A4.structure_y' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.Icho2026T9A4.graph_formula_is_printed_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.Icho2026T9A4.every_atom_has_normal_valence' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The three listed axioms are standard Lean logical/quotient axioms permitted by the goal. There are no target-specific axioms and no generated native-evaluator axioms.

The file itself ends with these exact inspection commands:

```lean
#print axioms structure_y
#print axioms graph_formula_is_printed_formula
#print axioms every_atom_has_normal_valence
```

The proof uses kernel-reduced `decide`, not `native_decide`, for the exhaustive 234-atom graph checks. In particular, it verifies:

- six α-(1→4)-linked repeats;
- complete pyranose, epoxide, O6-TBS, glycosidic, and explicit C-H connectivity;
- 72 C, 132 H, 24 O, and 6 Si atoms;
- normal valence for every atom;
- exclusively single bonds, zero formal charges, and zero radical electrons;
- C1 α/down, C2 epoxide-O up after inversion, C3 epoxide-O up after retention, C4 glycosidic-O down, and C5-CH2OTBS up.

## Shortcut audit

Command:

```bash
if grep -nE '\b(sorry|admit|unsafe)\b' IChO2026Problems/problem_icho_2026_t9_a4.lean; then
  exit 1
fi
```

Result: exit code 0, no matches.

## Semantic audit

The formula is obtained twice and the two derivations agree:

1. direct counting of the complete atom graph; and
2. six glucoses minus six waters for α-CD, plus six net TBS substitutions (`C6H14Si` each), minus six waters for six epoxide closures.

The stereochemical result is not inferred from the formula alone. It follows from O2 activation and intramolecular O3→C2 SN2 closure (C2 inversion, C3 retention), and is checked backward against the problem’s displayed hydrolysis product. The formal statement therefore represents the requested chemistry rather than only a molecular-formula equality.
