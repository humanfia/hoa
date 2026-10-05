# Verification — `icho_2026_t9_a8`

All commands below were run from:

```text
/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t9_a8/campaign/workspace
```

## 1. Source integrity

Command:

```bash
sha256sum TASK.json icho_2026_source/image/T9_page-3.png icho_2026_source/image/T9_page-4.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
831c8c2b64455ec5bf3f4db71a62392d3e70d51ea5ebca88097b0e7e17e23bb4  TASK.json
a63869290bd2dcbc80632be3cbf121fab1ffa361f725255f17c191d16df7da4f  icho_2026_source/image/T9_page-3.png
a387cc56150da4c1070f2eb0b61e1e7c130429b1ec58594613fdfdb816476a1d  icho_2026_source/image/T9_page-4.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

The three problem-asset hashes match `TASK.json` exactly.

## 2. Original PDF and blank answer-sheet inspection

The original PDF pages were rendered and visually inspected during the solve.
PDF page 87 is the original Q9-4 route; PDF pages 92 and 93 are blank answer
sheets A9-4/A9-5 containing all five O–S α-CD templates. The following
read-only text-label check independently confirms those pages:

```bash
python3 - <<'PY'
import fitz
pdf = fitz.open('icho_2026_source/raw/theory_problem.pdf')
print('page_count', len(pdf))
for page_number in (87, 92, 93):
    text = pdf[page_number - 1].get_text('text')
    labels = [line for line in text.splitlines() if line in {'Theory', 'Q9-4', 'A9-4', 'A9-5', '9.8 (18.0 pt)', '9.8 (cont.)'}]
    print(page_number, labels)
PY
```

Result (exit code 0; PyMuPDF also emitted a non-failing API-deprecation
warning):

```text
page_count 93
87 ['Theory', 'Q9-4']
92 ['Theory', 'A9-4', '9.8 (18.0 pt)']
93 ['Theory', 'A9-5', '9.8 (cont.)']
```

## 3. Forbidden-placeholder and custom-axiom scan

Command:

```bash
if grep -RInE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t9_a8.lean; then exit 1; else echo 'No forbidden Lean placeholders or custom axiom declarations found.'; fi
```

Result (exit code 0):

```text
No forbidden Lean placeholders or custom axiom declarations found.
```

## 4. Lean compilation and axiom audit

Command:

```bash
lake env lean IChO2026Problems/problem_icho_2026_t9_a8.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T9A8.structure_o' does not depend on any axioms
'IChO2026Problems.T9A8.structure_p' does not depend on any axioms
'IChO2026Problems.T9A8.structure_q' does not depend on any axioms
'IChO2026Problems.T9A8.structure_r' does not depend on any axioms
'IChO2026Problems.T9A8.structure_s' does not depend on any axioms
'IChO2026Problems.T9A8.structure_q_bridge_connectivity' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T9A8.structure_r_has_NBoc_and_unit6_azide' does not depend on any axioms
'IChO2026Problems.T9A8.structure_s_has_NBn_and_preserves_unit6_azide' does not depend on any axioms
'IChO2026Problems.T9A8.all_requested_structures_fully_specified' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T9A8.requested_outputs' depends on axioms: [propext, Quot.sound]
```

The five requested-output theorems and the two R/S field theorems are
axiom-free. The bridge-list equality, full-specification, and aggregate
theorems use only the standard Lean/Mathlib logical axioms `propext` and
`Quot.sound`; there are no custom unchecked axioms.

## 5. Semantic-fidelity audit

The Lean statements were compared independently with the question image and
blank templates, not merely compiled:

- `alphaCDCore` contains six α-D-glucopyranoside ⁴C₁ stereochemical records,
  six α-(1→4) links, and exactly twelve secondary benzyl ethers.
- Each candidate explicitly fills units 1–6. O and P have no bridge; Q–S have
  a unit-2-N/unit-5-O bridge with connectivity
  `N-CH2-C(=CH2)-CH2-O`.
- O is unit-1 vinyl. P additionally has clockwise unit-2 azide. Q reduces that
  azide, deprotects diametric unit 5, and bridges units 2/5. R uses the
  counterclockwise 1,3 fallback at unit 6, gives unit-6 azide, and has N-Boc.
  S changes only N-Boc to N-Bn.
- Primary fragments and the bridge specify elements, heavy-atom bonds and bond
  orders, formal charges, radical-electron counts, and skeletal-hydrogen
  counts. The azide charge pattern and bridge exocyclic double bond have
  dedicated proved checks.
- Every reaction is a substrate-checking partial function. The five candidate
  structures are separately enumerated, and the proofs show the route computes
  those candidates from source compound N.

No requested output is weakened to a string label or assumed as a premise.

## 6. Artifact syntax and whitespace checks

Commands:

```bash
python3 -m json.tool result.json >/dev/null
if grep -nE '^(<<<<<<<|=======|>>>>>>>)|[[:blank:]]$' answer.md verification.md result.json IChO2026Problems/problem_icho_2026_t9_a8.lean; then exit 1; else echo 'No conflict markers or trailing whitespace found.'; fi
```

Results: both commands exited with code 0. The JSON command intentionally
produced no output; the whitespace command printed:

```text
No conflict markers or trailing whitespace found.
```

`git diff --check` was not used because this isolated workspace has no `.git`
directory; the explicit check above covers the relevant conflict-marker and
trailing-whitespace conditions without changing repository state.

## 7. Generic-infrastructure preservation

Command:

```bash
python3 - <<'PY'
import hashlib, json
manifest = json.load(open('isolation_manifest.json'))
for path, expected in manifest['lake_skeleton_files'].items():
    actual = hashlib.sha256(open(path, 'rb').read()).hexdigest()
    if actual != expected:
        raise SystemExit(f'modified generic infrastructure: {path}')
print('All generic infrastructure files match isolation_manifest.json.')
PY
```

Result (exit code 0):

```text
All generic infrastructure files match isolation_manifest.json.
```
