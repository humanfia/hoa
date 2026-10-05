# Verification for `icho_2026_t7_a6`

Verification date: 2026-09-13 (UTC)

## Source inspection

The required control files `GOAL.txt` and `TASK.json` were read before work on
the answer.  Both supplied images were visually inspected:

- `icho_2026_source/image/T7_page-3.png` contains the complete calibration and
  A--D candidate tables for 7.6.
- `icho_2026_source/image/T7_page-2.png` contains the preceding T7 context.

The original 93-page `icho_2026_source/raw/theory_problem.pdf` was opened with
PyMuPDF.  PDF page 65 reproduces Q7-3, and PDF page 70 is blank student answer
sheet A7-4; its 7.6 response area is an unrestricted box.

The source hashes were checked with:

```text
sha256sum icho_2026_source/raw/theory_problem.pdf icho_2026_source/image/T7_page-2.png icho_2026_source/image/T7_page-3.png icho_2026_source/image/T7_page-4.png
```

Result (exit code 0):

```text
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
010bf0d38d5f34a4edd184c97a2a3f0f9375e0e6f1326e7d0fbd336d319b97ba  icho_2026_source/image/T7_page-2.png
9bc386ab33010a7f8e999035212268ecbeb2ff73ca3a8a108dca96b364e5d47c  icho_2026_source/image/T7_page-3.png
7c6a69f04e438a75d16afb5e92c9d91a1f5c289faffbfc4f93d4f19e2ad8e626  icho_2026_source/image/T7_page-4.png
```

These match `TASK.json` and `isolation_manifest.json`.

## Lean compilation and axiom audit

Exact command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t7_a6.lean
```

Final result: exit code 0.  The `#print axioms` output was:

```text
'IChO2026Problems.T7A6.calibration_reductant_trend' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T7A6.calibration_pKa_trend' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T7A6.calibration_counterion_effect' depends on axioms: [propext]
'IChO2026Problems.T7A6.ammonia_yield_decreasing_order' does not depend on any axioms
'IChO2026Problems.T7A6.ammonia_yield_ranking_is_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T7A6.ammonia_yield_ranking_is_strict' does not depend on any axioms
'IChO2026Problems.T7A6.numerical_ammonia_yields_follow_ranking' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Thus the computed answer theorem and strict-order theorem are axiom-free.  The
remaining listed dependencies are standard Lean logical/quotient axioms; there
are no custom axioms.

## Proof-shortcut and artifact checks

Exact command:

```text
if grep -nE '(^|[[:space:]])(sorry|admit|unsafe)([[:space:]]|$)|^[[:space:]]*axiom[[:space:]]' IChO2026Problems/problem_icho_2026_t7_a6.lean; then exit 1; else echo 'no forbidden proof shortcuts'; fi
```

Result (exit code 0):

```text
no forbidden proof shortcuts
```

Exact JSON validation command:

```text
python3 -m json.tool result.json >/dev/null
```

Result: exit code 0.

Exact whitespace/conflict-marker command:

```text
if grep -nE '[[:blank:]]$|^(<<<<<<<|=======|>>>>>>>)' answer.md verification.md result.json IChO2026Problems/problem_icho_2026_t7_a6.lean; then exit 1; else echo 'no whitespace errors or conflict markers'; fi
```

Result (exit code 0):

```text
no whitespace errors or conflict markers
```

`git diff --check` was also attempted but returned exit code 129 because the
workspace has no `.git` directory.  It was not used as a final gate; the direct
file check above covers the relevant whitespace and conflict-marker conditions.

## Semantic audit

- The four calibration rows and A--D properties in Lean are exact scaled
  transcriptions of Q7-3.
- `computedRanking` is obtained by a generic insertion sort using the named
  empirical rule; it is not defined to be the desired answer list.
- `ammonia_yield_decreasing_order` proves that computation equals
  `[B, C, D, A]`.
- `ammonia_yield_ranking_is_complete` proves the answer is a permutation of all
  four candidates, and `ammonia_yield_ranking_is_strict` proves every earlier
  candidate ranks above every later one under the classifier.
- Because A--D yields are not measured in the source, the stronger theorem
  `numerical_ammonia_yields_follow_ranking` keeps trend compatibility as an
  explicit hypothesis.  No unsupported numerical candidate yields are assumed.
