# Verification record for `icho_2026_t9_a9`

## Source integrity and inspection

Command:

```text
sha256sum icho_2026_source/image/T9_page-5.png icho_2026_source/image/T9_page-4.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
09b3167e89b9156e9bf9040f7a5de68b63a5c688bc43e6f9bb923eba7d4527dd  icho_2026_source/image/T9_page-5.png
a387cc56150da4c1070f2eb0b61e1e7c130429b1ec58594613fdfdb816476a1d  icho_2026_source/image/T9_page-4.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These hashes exactly match `TASK.json`.  The two PNGs were visually inspected.
The original 93-page PDF was also inspected at Q9-4/Q9-5 and at blank student
answer-sheet pages A9-1 through A9-5; A9-5 contains a blank unrestricted box
for 9.9 and no extra instruction.

## Lean compilation and axiom audit

Final command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t9_a9.lean
```

Result (exit code 0):

```text
'IChO2026Problems.T9A9.labelledLinearArrangement_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T9A9.rotateReading_injective' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.T9A9.rotationalReadings_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T9A9.cyclic_orbit_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T9A9.anchored_factorial_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T9A9.arrangement_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T9A9.anchored_count_eq_cyclic_quotient' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The `#print axioms` commands are part of the compiled source.  The reported
dependencies are standard Lean logical axioms; there are no custom axioms.

## Prohibited-shortcut scan

Command:

```text
grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t9_a9.lean
```

Result: no matches (grep exit code 1).  In particular, the proof contains no
`sorry`, `admit`, `unsafe`, or custom `axiom` declaration.

## Semantic audit

- Six sites: grounded by the statement that alpha-CD contains six
  alpha-D-glucopyranoside units and by the restriction to modified primary
  `CH2OH` groups.
- Six pairwise-distinct labels: this is precisely the meaning of
  “hexadifferentiated”.
- Symmetry: rotations only.  Choosing the starting unit does not change a
  cyclic arrangement; reflection reverses the oriented chiral glycosidic
  ring.  Q9-4 independently confirms that the source treats clockwise and
  counterclockwise as different directions.
- Lean correspondence: `LabelledLinearArrangement` has `6! = 720` elements;
  `rotateReading_injective` and `rotationalReadings_count` prove that each
  rotation class has six distinct readings; the anchored representation has
  `5! = 120` elements.  The final `arrangement_count` theorem proves the exact
  requested integer and `anchored_count_eq_cyclic_quotient` proves agreement
  with `720 / 6`.

No source gaps were found.
