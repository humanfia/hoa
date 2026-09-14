# Verification: IChO 2026 T3-A6

Verification was performed in
`/home/jing/icho-native-goal-gpt68-20260913-01/jobs/icho_2026_t3_a6/campaign/workspace`
with the pinned `leanprover/lean4:v4.31.0` toolchain.

## Source inspection

- Read `GOAL.txt` and `TASK.json` before solving.
- Inspected the original-resolution `T3_page-5.png` and `T3_page-6.png` source
  images.
- Checked the SHA-256 hashes of the PDF and both images; all three equal the
  hashes recorded in `TASK.json`.
- Opened the original 93-page `theory_problem.pdf`, extracted the text of
  question page 30, and rendered and visually inspected question page 30 and
  the dedicated blank answer sheet on page 35 (`Theory A3-4`). Page 35 contains
  the four columns AA, AA′, AB, AB′ and has −67.1 prefilled only under AA′.

## Lean checks

The existing local reporting library was first made available in the build
path:

```text
$ lake build IChO2026Chem
Build completed successfully (8561 jobs).
```

The required direct-file compilation was then run on the final Lean source:

```text
$ lake env lean IChO2026Problems/problem_icho_2026_t3_a6.lean
'IChO2026Problems.T3A6.stacking_energy_aa' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A6.stacking_energy_ab' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A6.stacking_energy_ab_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A6.aa_submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A6.ab_submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T3A6.ab_prime_submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit status: `0`.

The module-level build was also checked:

```text
$ lake build IChO2026Problems.problem_icho_2026_t3_a6
ℹ [8559/8559] Built IChO2026Problems.problem_icho_2026_t3_a6 (34s)
info: IChO2026Problems/problem_icho_2026_t3_a6.lean:203:0: 'IChO2026Problems.T3A6.stacking_energy_aa' depends on axioms: [propext, Classical.choice, Quot.sound]
info: IChO2026Problems/problem_icho_2026_t3_a6.lean:204:0: 'IChO2026Problems.T3A6.stacking_energy_ab' depends on axioms: [propext, Classical.choice, Quot.sound]
info: IChO2026Problems/problem_icho_2026_t3_a6.lean:205:0: 'IChO2026Problems.T3A6.stacking_energy_ab_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
info: IChO2026Problems/problem_icho_2026_t3_a6.lean:206:0: 'IChO2026Problems.T3A6.aa_submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
info: IChO2026Problems/problem_icho_2026_t3_a6.lean:207:0: 'IChO2026Problems.T3A6.ab_submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
info: IChO2026Problems/problem_icho_2026_t3_a6.lean:208:0: 'IChO2026Problems.T3A6.ab_prime_submission_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8559 jobs).
```

Exit status: `0`. The only build warning preceding this excerpt concerned the
pre-existing short copyright header in `IChO2026Chem/Reporting.lean`; it is
unrelated to this target.

The final file itself contains the `#print axioms` commands responsible for the
outputs above. The listed axioms are standard Lean logical axioms, and there is
no `sorryAx` or custom unchecked axiom.

Finally, the forbidden-shortcut scan was run:

```text
$ grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t3_a6.lean
```

It produced no output and exit status `1`, the expected `grep` status for no
matches.

The result manifest was parsed independently:

```text
$ python3 -m json.tool result.json >/dev/null
```

It produced no output and exit status `0`.

## Semantic audit

- The formal inventory proves five aromatic sites: four benzene and one
  triazine.
- The AA and AB overlap enumerations are explicit data derived from the source
  diagrams, not assumptions in theorem hypotheses.
- `aa_prime_matches_stated_energy` independently recovers the problem's
  supplied −67.1 kJ mol⁻¹ value from four slipped b-b contacts and one slipped
  t-t contact.
- The three requested raw-energy theorems prove −38.3, −49.8, and −55.6
  kJ mol⁻¹ exactly.
- The three reporting theorems separately certify those exact raw values at a
  0.1 kJ mol⁻¹ display quantum, which is three significant figures for every
  requested output.
