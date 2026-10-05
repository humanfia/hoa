# Verification for `icho_2026_t4_a2`

## Source identity

Command:

```text
sha256sum /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T4_page-1.png /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
f3b21152e21992aaa319cd436ffe893d0dff6634488f27663eee85b3cf81ddcf  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/image/T4_page-1.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  /home/jing/icho-native-goal-gpt68-20260913-01/seed/icho_2026_source/raw/theory_problem.pdf
```

These hashes match `TASK.json` and `isolation_manifest.json`. The question was
read on PDF page 37; the corresponding blank answer sheet A4-1 was read on PDF
page 40 and contains the three fields `(a)`, `(b)`, and `(c)`.

## Lean compilation and axiom audit

Command:

```text
lake env lean IChO2026Problems/problem_icho_2026_t4_a2.lean
```

Result (exit code 0):

```text
'IChO2026Problems.ProblemIChO2026T4A2.reactionA_balanced' depends on axioms: [propext]
'IChO2026Problems.ProblemIChO2026T4A2.reactionB_balanced' depends on axioms: [propext]
'IChO2026Problems.ProblemIChO2026T4A2.reactionC_balanced' depends on axioms: [propext]
'IChO2026Problems.ProblemIChO2026T4A2.nuclear_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIChO2026T4A2.nuclear_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.ProblemIChO2026T4A2.nuclear_c' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The `#print axioms` commands are part of the final Lean file. Every listed
axiom is a standard Lean logical axiom permitted by the goal; there are no
custom unchecked axioms.

## Forbidden-shortcut scan

Command:

```text
perl -ne 'BEGIN{$bad=0} if (/\b(?:sorry|admit|unsafe)\b/) { print "$.:$_"; $bad=1 } END { exit $bad }' IChO2026Problems/problem_icho_2026_t4_a2.lean
```

Result: exit code 0, with no output.

## Semantic audit

The formal species are exactly the isotope labels appearing in the answer:
boron-11 `(11,5)`, alpha `(4,2)`, deuterium `(2,1)`, gamma `(0,0)`,
beryllium-9 `(9,4)`, neutron `(1,0)`, nitrogen-14 `(14,7)`, hydrogen-1
`(1,1)`, and carbon-12 `(12,6)`. `Balanced` independently requires equality
of total mass number and total atomic number. The three `reaction*_balanced`
theorems verify the displayed equations, while `nuclear_a`, `nuclear_b`, and
`nuclear_c` prove that no other residual `(A,Z)` can balance the respective
one-residual-plus-one-neutron channel.
