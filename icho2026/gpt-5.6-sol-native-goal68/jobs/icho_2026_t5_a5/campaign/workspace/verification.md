# Verification: IChO 2026 T5.5

Verification is rerun from the completed deliverables; the exact final outputs
are recorded below.

## Lean compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t5_a5.lean
```

Expected audited declarations (the file contains explicit `#print axioms`
commands for both):

```text
IChO2026Problems.T5A5.protonatedPL1_phase_is_inverseHexagonal
IChO2026Problems.T5A5.icho_2026_t5_a5
```

Result: exit code `0`.

Verbatim output:

```text
'IChO2026Problems.T5A5.protonatedPL1_phase_is_inverseHexagonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'IChO2026Problems.T5A5.icho_2026_t5_a5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms. There is no custom unchecked axiom and
no `sorryAx`.

## Forbidden-proof scan

Command:

```text
grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t5_a5.lean
```

Result: no output and exit code `1`, meaning no forbidden token was found.

## Source integrity

Command:

```text
sha256sum icho_2026_source/image/T5_page-3.png icho_2026_source/image/T5_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result:

```text
9824f187e7baa6e5929ec0c7cda6c740aee46a1404afdcad974c734b083b86b7  icho_2026_source/image/T5_page-3.png
7f0f35d726d79f8d1ff9b15ee00574efeb89d8b179ab05469b5c297cb147bb96  icho_2026_source/image/T5_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

All three hashes exactly match `TASK.json`.

## Semantic audit

- Requested output: one exact phase classification for fully protonated PL1.
- Natural-language output: option (d), inverse hexagonal.
- Formal output: `protonatedPL1_phase_is_inverseHexagonal` proves existence and
  uniqueness of the phase under the problem-stated dianion/lamellar input;
  `icho_2026_t5_a5` proves that exactly answer choice (d) fits.
- Problem input and general chemistry law are represented separately.
- The proof assigns no numerical molecular geometry and does not require the PL1
  structural formula, consistent with the question's note.
- The blank answer sheet was inspected and supplied no answer information.
