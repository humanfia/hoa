# Verification for `icho_2026_t2_a6`

Verification date: 2026-09-13 (UTC).

## Source identity

Command:

```sh
sha256sum icho_2026_source/image/T2_page-2.png icho_2026_source/image/T2_page-3.png icho_2026_source/image/T2_page-4.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit 0):

```text
77bd97168be820a9643a8acac845ca1ef8c4c1a4a99f678c78227e6e5e48ef8b  icho_2026_source/image/T2_page-2.png
c3149da1c24d984ae95dea8947243aba8fe833b79e4447761bb04ec17b831260  icho_2026_source/image/T2_page-3.png
b5e103f6fca031d7080e03073c4dad882142bd4e53cc0690f4140eaa4f6dea47  icho_2026_source/image/T2_page-4.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These values exactly match `TASK.json`. Original PDF pages 18 and 19-23 were rendered read-only and visually inspected. Page 18 is Q2-4 containing T2-A6; pages 19-23 are the blank A2-1 through A2-5 student sheets, with the four-row a-e grid on page 23.

## Lean compilation and axiom inspection

Command:

```sh
lake env lean IChO2026Problems/problem_icho_2026_t2_a6.lean
```

Result (exit 0):

```text
'IChO2026Problems.T2A6.action_1_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A6.action_2_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A6.action_3_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A6.action_4_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A6.all_requested_outputs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The five `#print axioms` commands are embedded at the end of the target file. They report only Lean/Mathlib's permitted standard logical axioms; there are no custom unchecked axioms.

## Forbidden-shortcut scan

Command:

```sh
if grep -nE '^[[:space:]]*(axiom|unsafe|sorry|admit)([[:space:]]|$)' IChO2026Problems/problem_icho_2026_t2_a6.lean; then echo 'Forbidden Lean declaration or proof shortcut found.'; exit 1; else echo 'No forbidden Lean declarations or proof shortcuts found.'; fi
```

Result (exit 0):

```text
No forbidden Lean declarations or proof shortcuts found.
```

## Result manifest syntax

Command:

```sh
python3 -m json.tool result.json >/dev/null && echo 'result.json: valid JSON'
```

Result (exit 0):

```text
result.json: valid JSON
```

## Semantic coverage audit

- Action 1 is represented by `action_1_answer`; its certificate proves that any positive Ce(IV) pulse increases the printed Process-C bromide-production rate.
- Action 2 is represented by `action_2_answer`; its certificate proves B-to-A selection when AgBr precipitation takes bromide across the derived critical boundary.
- Action 3 is represented by `action_3_answer`; its certificate proves that a positive bromide pulse increases remaining B duration for any strictly monotone time-to-boundary relation, without assuming constant phase-portrait velocity.
- Action 4 is represented by `action_4_answer`; its certificate proves Process B is invariant for every trajectory maintained above the critical bromide concentration.
- `all_requested_outputs` bundles the exact four classifications in student-sheet order.
- The quantitative pulse sizes and continuous-feed rate are absent from the source. Both `answer.md` and `result.json` record this limitation; the Lean theorem statements expose the required crossing/invariance conditions.
