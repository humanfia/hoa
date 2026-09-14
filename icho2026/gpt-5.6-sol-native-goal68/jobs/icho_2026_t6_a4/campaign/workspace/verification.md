# Verification: IChO 2026 T6-A4

## Source inspection

- Read `GOAL.txt` and `TASK.json` first.
- Inspected both task-listed images:
  `icho_2026_source/image/T6_page-1.png` and
  `icho_2026_source/image/T6_page-2.png`.
- Opened the original `icho_2026_source/raw/theory_problem.pdf` (93 pages)
  and inspected T6 question pages Q6-1 through Q6-5 and blank student answer
  sheets A6-1 through A6-6. In particular, Q6-2 is PDF page 53 and the
  worked `591 = [E + H]⁺` answer-table entry is on A6-2, PDF page 58.

The provided-source hashes were checked with:

```text
sha256sum icho_2026_source/image/T6_page-1.png icho_2026_source/image/T6_page-2.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0), matching `TASK.json` and `isolation_manifest.json`:

```text
29fff91c704c94f9e4e9fddba3ab61896375763880aff114baef9318cbdbe6ba  icho_2026_source/image/T6_page-1.png
d9fd1e2d82d0e8a94ab6bcee210a2aee319715da722bbeb8d1df38e35d7d3362  icho_2026_source/image/T6_page-2.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

## Lean verification

Command run from the workspace root:

```text
lake env lean IChO2026Problems/problem_icho_2026_t6_a4.lean
```

Result: exit code 0. Output from the four `#print axioms` commands in the
file:

```text
'IChO2026Problems.T6A4.ion_783_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A4.ion_879_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A4.ion_1174_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T6A4.requested_ion_identities' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard Lean logical axioms permitted by the goal. The file
declares no custom axioms and uses no `sorry`, `admit`, or `unsafe` shortcut.

Additional artifact checks:

```text
grep -RInE '\b(sorry|admit|unsafe|axiom)\b' IChO2026Problems/problem_icho_2026_t6_a4.lean
python3 -m json.tool result.json
```

The grep command returns exit code 1 with no output, which confirms that no
listed forbidden declaration or shortcut occurs. The JSON command returns
exit code 0 and prints the parsed object successfully.
