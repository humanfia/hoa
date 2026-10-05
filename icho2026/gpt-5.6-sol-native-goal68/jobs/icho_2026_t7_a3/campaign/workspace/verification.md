# Verification record

## Source inspection

The following problem-only materials were inspected before solving:

- `GOAL.txt` and `TASK.json`;
- `icho_2026_source/image/T7_page-1.png` and `T7_page-2.png` at original
  resolution;
- page 64 of `icho_2026_source/raw/theory_problem.pdf`, rendered directly from
  the original PDF;
- blank student answer sheet A7-3 on PDF page 69, including its T7-A3 response
  fields.

The source files remained unchanged. This command:

```text
sha256sum icho_2026_source/image/T7_page-1.png icho_2026_source/image/T7_page-2.png icho_2026_source/raw/theory_problem.pdf
```

returned:

```text
ee7fe1adff7ac3aae8701bf684981bd2b1e21b28f1c9e4b21dd9c38c3bdb79ad  icho_2026_source/image/T7_page-1.png
010bf0d38d5f34a4edd184c97a2a3f0f9375e0e6f1326e7d0fbd336d319b97ba  icho_2026_source/image/T7_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These hashes exactly match the values in `TASK.json` and
`isolation_manifest.json`.

## Lean verification

The local shared reporting module first needed its ordinary compiled artifact.
The command

```text
lake build IChO2026Chem.Reporting
```

exited with code 0 and reported:

```text
Built IChO2026Chem.Reporting
Build completed successfully (8558 jobs).
```

It also emitted only the pre-existing style warning that the copyright header
in `IChO2026Chem/Reporting.lean` is short.

The final target command was then run exactly as required:

```text
lake env lean IChO2026Problems/problem_icho_2026_t7_a3.lean
```

It exited with code 0. The two `#print axioms` checks returned:

```text
'IChO2026Problems.T7A3.nitrogen_after_58_cycles' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T7A3.cycles_for_97_percent' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms; there are no custom unchecked axioms.

The command

```text
! grep -nE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t7_a3.lean
```

produced no matches. It was evaluated so that no matches is success (exit code
0); the formalization contains no `sorry`, `admit`, `unsafe`, or custom
`axiom` declaration.

## Artifact checks

```text
python3 -m json.tool result.json
```

exited with code 0, validating the JSON syntax.

```text
! grep -n '[[:blank:]]$' answer.md verification.md result.json IChO2026Problems/problem_icho_2026_t7_a3.lean
```

produced no output and exited with code 0. The supplied workspace is not a Git
repository, so `git diff --check` is unavailable and is not a completion gate.

## Semantic audit

- The recurrence theorem uses a 1 mol nitrogen addition derived from the
  source's 4 mol, 1:3 feed and a retained fraction 17/20 derived from the
  source's 0.150 yield.
- The part (a) theorem proves the exact geometric closed form and the complete
  half-quantum interval needed to round to 5.6662 at quantum 0.0001.
- The part (b) definition is proved equal to converted nitrogen divided by
  cumulative fresh nitrogen. It gives 15.0% at cycle 1.
- The least-cycle theorem proves monotonicity for every positive cycle count,
  proves cycle 188 is below 97.0%, and proves cycle 189 reaches 97.0%.
- No other competition answer, marking scheme, solver agent, or answer
  repository was used. No source gap was found.
