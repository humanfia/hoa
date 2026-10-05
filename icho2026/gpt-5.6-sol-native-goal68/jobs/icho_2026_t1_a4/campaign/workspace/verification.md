# Verification: `icho_2026_t1_a4`

## Source integrity and inspection

The assets named in `TASK.json` were absent from the job directory but were located in the run's immutable seed bundle.  The following exact command verified that they are byte-for-byte the assets authorized by `TASK.json` and `isolation_manifest.json`:

```text
sha256sum /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T1_page-2.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T1_page-3.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

Result: exit code 0.

```text
06f9276f8440fd17bd18f6778d1cc5950d47ffebaa60395b7078b96fcbf4f0cb  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T1_page-2.png
fbdc901fd87b13a184497f3cb922f1cceb63ec8d01f0ff7fc6985d4131e70a17  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T1_page-3.png
af51373f43201cecf68a776068abf216292482dbc8d3d60                    /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

`T1_page-2.png` and `T1_page-3.png` were visually inspected at original detail.  A temporary PDF reader was used outside the workspace because no Poppler/MuPDF command-line reader was installed.  The exact page-audit command was:

```text
PYTHONPATH=/tmp/icho_pdf_tools /usr/bin/python3 - <<'PY'
import pymupdf
p='/home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf'
doc=pymupdf.open(p)
print('PAGES', doc.page_count)
for i,page in enumerate(doc):
    text=' '.join(page.get_text('text').split())
    print(f'{i+1:03d}: {text[:220]}')
PY
```

Result: exit code 0; `PAGES 93`.  The audit located the T1 question on PDF pages 6–9, the T1 blank student sheets on pages 10–14, and specifically T1-A4 on question page 8 (`Q1-3`) with its blank answer fields on page 12 (`A1-3`).  PDF page 5 (`G1-5`) was also rendered and inspected for the supplied atomic masses.

## Lean build and proof checking

Shared library build:

```text
lake build IChO2026Chem
```

Result: exit code 0; `Build completed successfully (8561 jobs).`  The only output was the pre-existing short-copyright-header warning in the two shared infrastructure files; those files were not modified.

Final target compilation and in-file `#print axioms` audit:

```text
lake env lean IChO2026Problems/problem_icho_2026_t1_a4.lean
```

Result: exit code 0.  Exact substantive output:

```text
'IChO2026Problems.T1A4.hydration_number_eq_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T1A4.identify_metal_C_and_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T1A4.metal_q_identity' does not depend on any axioms
'IChO2026Problems.T1A4.hydrated_c_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T1A4.compound_d_formula' does not depend on any axioms
'IChO2026Problems.T1A4.identified_answer_satisfies_problem_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T1A4.bare_arithmetic_does_not_identify_C' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the goal.  No custom unchecked assumptions occur.

Shortcut scan:

```text
if grep -RInE '(^|[[:space:]])(sorry|admit|unsafe|axiom)([[:space:]]|$)' IChO2026Problems/problem_icho_2026_t1_a4.lean; then exit 1; else exit 0; fi
```

Result: exit code 0 with empty output; the guarded scan fails verification if any prohibited token is found.

JSON validation:

```text
jq empty TASK.json result.json
```

Result: exit code 0 with empty output.

## Semantic completion audit

| Requirement | Evidence | Result |
|---|---|---|
| Identify Q | `metal_q_identity`; cryolite industrial classification; 12.85% Al proof | Q = Al |
| Identify C·xH₂O | `sodium_free_precursor_eq_aluminumFluoride`, `hydration_number_eq_three`, and `hydrated_c_formula` | AlF₃·3H₂O |
| Identify D | `compound_d_formula`; 32.85% Na and 12.85% Al proofs | Na₃AlF₆ |
| Check stated conversion | `aluminumFluoride_converts_to_cryolite` | AlF₃ + 3 NaF → Na₃AlF₆ |
| Respect displayed precision | All percentages use `ConsistentMeasurement` with quantum 0.01 | Proven |
| Avoid unjustified finite search | `hydration_number_eq_three` proves the result for arbitrary `x : ℕ` by inequalities | Proven |
| Expose source limitation | `bare_arithmetic_does_not_identify_C` proves the stripped arithmetic admits a distinct formal composition | Gap explicitly represented |

The final theorem is intentionally conditional on the two ordinary-chemistry interpretations that are not spelled out by the paper: the Hall–Héroult cryolite classification and the sodium-free identity of the pH-controlled precipitated metal fluoride.  The arithmetic, reaction balance, and uniqueness of the hydration number under that interpretation are proved, rather than postulated.
