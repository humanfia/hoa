# Verification — `icho_2026_t9_a5`

All commands below were run from
`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t9_a5/campaign/workspace`.

## Source integrity

Command:

```bash
sha256sum icho_2026_source/image/T9_page-3.png icho_2026_source/image/T9_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
a63869290bd2dcbc80632be3cbf121fab1ffa361f725255f17c191d16df7da4f  icho_2026_source/image/T9_page-3.png
a65b4bf067ff9b1aa03ad40758319abec68f959fce4bf64380bd0e8227bee48f  icho_2026_source/image/T9_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These hashes equal the three hashes fixed in `TASK.json`.

The original PDF question page and blank student answer sheet were located
with:

```bash
python3 - <<'PY'
import pymupdf
p = 'icho_2026_source/raw/theory_problem.pdf'
doc = pymupdf.open(p)
print(f'pages={doc.page_count}')
for i, page in enumerate(doc):
    text = page.get_text('text')
    if 'Draw the structure of L' in text or ('A9-3' in text and '9.5 (2.0 pt)' in text):
        header = ' '.join(text.splitlines()[:4])
        print(f'pdf_page={i + 1}: {header}')
PY
```

Result (exit code 0):

```text
pages=93
pdf_page=86: Theory Q9-3 English (Official) In 2000, Sinay et al. demonstrated that a single protic group (NH and OH) at unit 1 directs the next reduc-
pdf_page=91: Theory A9-3 English (Official) 9.5 (2.0 pt)
```

Both designated PNGs and rendered PDF pages 86 and 91 were visually
inspected. Page 86 supplies the reagent sequence, unit numbering, directing
rule, and downstream consistency check. Page 91 supplies the seven primary
boxes and one `(…)14` box of the blank A9-3 template.

The non-target Lean infrastructure was checked against its seed manifest:

```bash
python3 - <<'PY'
import hashlib, json, pathlib
m = json.loads(pathlib.Path('isolation_manifest.json').read_text())
bad = []
for name, expected in m['lake_skeleton_files'].items():
    actual = hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest()
    if actual != expected:
        bad.append((name, expected, actual))
if bad:
    for row in bad:
        print('MISMATCH', *row)
    raise SystemExit(1)
print(f"PASS: all {len(m['lake_skeleton_files'])} generic infrastructure files match their seed hashes")
PY
```

Result (exit code 0):

```text
PASS: all 12 generic infrastructure files match their seed hashes
```

## Lean compilation and axiom audit

The Lean file ends with `#print axioms` commands for the two final structure
theorems, the atom-inventory theorem, and the two primary-oxygen connectivity
theorems.

Command:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t9_a5.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T9A5.requested_structure_L' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T9A5.structure_L_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T9A5.L_primary_has_benzyl_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T9A5.L_primary_has_hydrogen_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T9A5.requested_structure_L_graph' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The axiom set contains only standard Lean logical axioms. There is no custom
or unchecked chemistry axiom.

## Proof-shortcut scan

Command:

```bash
if grep -nE '\b(sorry|admit|unsafe)\b' IChO2026Problems/problem_icho_2026_t9_a5.lean; then echo 'FAIL: forbidden proof shortcut found'; exit 1; else echo 'PASS: no sorry, admit, or unsafe tokens'; fi
```

Result (exit code 0):

```text
PASS: no sorry, admit, or unsafe tokens
```

## Semantic audit

The formal model computes `L` by applying exhaustive benzylation to the
source β-CD state, exposing unit 1, and then applying the printed unit-1 to
unit-4 directing rule. The resulting theorems prove, rather than postulate,
the seven template entries, all fourteen secondary `OBn` entries, two free
primary alcohols, and five primary benzyl ethers.

The graph layer separately expands the shorthand into 19 benzyl attachments,
formula `C175H184O35`, 394 atoms, 420 bonds, and 57 Kekulé double bonds. It
also proves the O6 hydrogen/benzyl attachment classification, explicit
secondary benzyl attachment, zero formal charge and radical count on every
atom, and retention of all 35 α-D-glucopyranoside stereocentres. These checks
cover the requested connectivity, substituents, bond orders, charges,
radicals, and stereochemistry rather than merely proving a label or string.
