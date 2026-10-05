# Verification: IChO 2026 T9-A7

All commands below were run from
`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t9_a7/campaign/workspace`.

## Source integrity

Command:

```text
sha256sum icho_2026_source/image/T9_page-3.png icho_2026_source/image/T9_page-4.png icho_2026_source/raw/theory_problem.pdf
```

Result: exit code 0.

```text
a63869290bd2dcbc80632be3cbf121fab1ffa361f725255f17c191d16df7da4f  icho_2026_source/image/T9_page-3.png
a387cc56150da4c1070f2eb0b61e1e7c130429b1ec58594613fdfdb816476a1d  icho_2026_source/image/T9_page-4.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These values equal those in `TASK.json` and `isolation_manifest.json`.

The original PDF was inspected directly with PyMuPDF because no command-line
PDF text utility is installed.

Command:

```text
python3 - <<'PY'
import pymupdf
pdf = pymupdf.open('icho_2026_source/raw/theory_problem.pdf')
print('page_count:', pdf.page_count)
for page_number in (86, 87, 91):
    text = ' '.join(pdf[page_number - 1].get_text('text').split())
    print(f'page {page_number}:', text[:300])
PY
```

Result: exit code 0. It reports 93 pages; page 86 begins `Theory Q9-3` and
contains the unit-1-to-unit-4 rule, page 87 begins `Theory Q9-4` and contains
T9-A7, and page 91 begins `Theory A9-3` and contains the two blank fields
`[M₁+Na]⁺` and `[M₂+Na]⁺` with no answer values.

## Lean compile and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t9_a7.lean
```

Result: exit code 0. The file itself contains `#print axioms` for every final
result and its supporting formula/count theorems. Exact output:

```text
'IChO2026Problems.T9A7.degradation_arc_counts' depends on axioms: [propext]
'IChO2026Problems.T9A7.first_fragment_formula' depends on axioms: [propext]
'IChO2026Problems.T9A7.second_fragment_formula' depends on axioms: [propext]
'IChO2026Problems.T9A7.first_fragment_mz' depends on axioms: [propext]
'IChO2026Problems.T9A7.second_fragment_mz' depends on axioms: [propext]
'IChO2026Problems.T9A7.t9_a7_answer' depends on axioms: [propext]
```

`propext` is a standard Lean logical axiom permitted by the task. No custom
unchecked axiom occurs.

## Prohibited-shortcut scan

Command:

```text
if grep -nE '(^|[[:space:]])(sorry|admit|unsafe|axiom)([[:space:]]|$)' IChO2026Problems/problem_icho_2026_t9_a7.lean; then exit 1; else echo 'No prohibited declarations found.'; fi
```

Result: exit code 0.

```text
No prohibited declarations found.
```

## Semantic audit

- The Lean source-data namespace records seven β-CD units, deprotected units
  1 and 4, the two formulas printed on Q9-4, the acetoxy end, and integer
  sodium mass separately from all computed results.
- `degradation_arc_counts` proves that the two paths have two and three intact
  residues.
- `first_fragment_formula` and `second_fragment_formula` prove the atom counts
  `C78H84O16` and `C105H112O21` from those components.
- `first_fragment_mz` and `second_fragment_mz` then prove the exact requested
  singly charged sodium-adduct values 1299 and 1731.
- The combined `t9_a7_answer` theorem returns both outputs without adding any
  hypothesis or weakening either equality.

## Result JSON validation

Command:

```text
python3 -m json.tool result.json >/dev/null
```

Result: exit code 0.
