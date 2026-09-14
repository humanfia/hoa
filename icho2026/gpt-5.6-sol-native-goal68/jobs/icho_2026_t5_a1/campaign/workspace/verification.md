# Verification: IChO 2026 T5-A1

This file records the final verification commands.  They were rerun after all
deliverables were in place; the results below are the captured final-state
checks, not evidence from an official answer.

## Source identity

```text
$ sha256sum icho_2026_source/image/T5_page-1.png icho_2026_source/raw/theory_problem.pdf
4f1688b010a3470a1dec9e211f1577b2eab98b2cd1b9b990ccba4126875b6347  icho_2026_source/image/T5_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These match `TASK.json`.

## Lean elaboration and axiom audit

```text
$ lake env lean IChO2026Problems/problem_icho_2026_t5_a1.lean
'IChO2026Problems.IChO2026T5A1.Derived.completeAssembly_forces_odd' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.IChO2026T5A1.Derived.parityStatement_correct_iff' depends on axioms: [propext, Quot.sound]
'IChO2026Problems.IChO2026T5A1.Derived.connectedAcyclicAssembly_forces_n_eq_one' depends on axioms: [propext,
 Quot.sound]
'IChO2026Problems.IChO2026T5A1.Derived.fragment_parity_statement' depends on axioms: [propext, Quot.sound]
```

Exit status: `0`.

`propext` and `Quot.sound` are standard Lean logical axioms used by Mathlib's
verified tactics.  No custom axiom and no `sorryAx` occurs in the final theorem
audit.

## Proof-shortcut scan

```text
$ if grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t5_a1.lean; then exit 1; else echo 'No forbidden proof shortcuts found.'; fi
No forbidden proof shortcuts found.
```

Exit status: `0`.

## Result manifest syntax

```text
$ python3 -m json.tool result.json >/dev/null && echo 'result.json: valid JSON'
result.json: valid JSON
```

Exit status: `0`.

## Semantic audit

- The formal constants are copied from the source figure: attachment ends per
  `a,b,c,d` fragment are `1,2,3,1`, and multiplicities are `n,2,3,4`.
- `CompleteAssembly` does not assume the answer.  It records only that all open
  ends are paired two per joining bond.
- Lean proves `totalAttachmentEnds n = n + 17`, derives `Odd n`, excludes
  `Even n`, proves that `.odd` is the unique supported choice, and proves that
  the selected classification is `.odd`.
- The separate connected-acyclic refinement proves the stronger `n = 1` from
  the page's one-molecule and acyclic descriptions.
- The no-peroxide statement is not required for the numerical parity
  invariant; omitting it from the arithmetic model neither weakens nor changes
  the requested classification.
