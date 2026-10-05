# Verification — `icho_2026_t2_a7`

Verified on 2026-09-13 UTC from the problem-only workspace.

## Source integrity and inspection

Command:

```sh
sha256sum icho_2026_source/image/T2_page-4.png icho_2026_source/image/T2_page-3.png icho_2026_source/raw/theory_problem.pdf
```

Result (exit code 0):

```text
b5e103f6fca031d7080e03073c4dad882142bd4e53cc0690f4140eaa4f6dea47  icho_2026_source/image/T2_page-4.png
c3149da1c24d984ae95dea8947243aba8fe833b79e4447761bb04ec17b831260  icho_2026_source/image/T2_page-3.png
af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60  icho_2026_source/raw/theory_problem.pdf
```

These values exactly match `TASK.json`. The two PNGs were visually inspected.
The original 93-page PDF was opened and its T2 blank answer sheets A2-1 through
A2-6 (PDF pages 19–24, one-indexed) were rendered and inspected. A2-6 shows the
six 2.7 choices in a 3-by-2 grid. Its bottom-right red curve stays below zero,
oscillates with a decaying envelope, and tends to zero.

No official solution, marking scheme, grading report, historical answer, or
answer repository was used.

## Lean verification

Command:

```sh
lake env lean IChO2026Problems/problem_icho_2026_t2_a7.lean
```

Result: exit code 0. The file's embedded `#print axioms` commands produced:

```text
'IChO2026Problems.T2A7.stepGibbsRate_nonpositive' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A7.gibbs_tends_to_infimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A7.stepGibbsRate_tends_to_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A7.closed_oscillatory_rate_constraints' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A7.gibbsDerivative_nonpositive' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A7.continuous_gibbs_rate_constraints' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A7.satisfies_constraints_iff_bottomRight' depends on axioms: [propext]
'IChO2026Problems.T2A7.gibbs_rate_graph_answer' depends on axioms: [propext]
'IChO2026Problems.T2A7.closed_oscillatory_system_selects_bottomRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A7.continuous_system_selects_bottomRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'IChO2026Problems.T2A7.selectedGraph_eq_bottomRight' does not depend on any axioms
```

Only standard Lean logical/quotient axioms appear. In particular, no
`sorryAx` or custom unchecked axiom appears.

## Proof-shortcut scan

Command:

```sh
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|unsafe)([^[:alnum:]_]|$)' IChO2026Problems/problem_icho_2026_t2_a7.lean; then echo 'forbidden proof shortcut found'; exit 1; else echo 'no sorry/admit/unsafe proof shortcut found'; fi
```

Result (exit code 0):

```text
no sorry/admit/unsafe proof shortcut found
```

## Result manifest validation

Command:

```sh
python3 -m json.tool result.json
```

Result: exit code 0; the file parsed successfully as JSON and contains the
required target id, status, answer summary, theorem names, assumptions, source
gaps, and verification commands.

## Semantic audit

- Requested output: exactly one qualitative graph choice. The answer is the
  bottom-right box on the original A2-6 sheet.
- Literal derivative: `gibbsDerivative_nonpositive` uses `HasDerivAt` and
  derives nonpositivity from antitonicity of Gibbs energy; the result is not
  encoded as the desired graph constructor.
- Long-time behavior: `gibbs_tends_to_infimum` derives convergence from a
  lower bound and antitonicity, then `stepGibbsRate_tends_to_zero` derives the
  vanishing rate.
- Exhaustiveness: `GibbsRateGraph` has one constructor for each of the six
  visible source boxes; `satisfies_constraints_iff_bottomRight` checks every
  constructor.
- Model-to-output link:
  `continuous_system_selects_bottomRight` combines the literal derivative
  facts and the six-case classification in one uniqueness theorem.
- Scope caveat: the source says “closed” but does not explicitly state fixed
  temperature and pressure/no non-expansion work. Those conditions are needed
  for the Gibbs monotonicity criterion and remain explicit in
  `FixedTPClosedEvolution`,
  `ContinuousFixedTPClosedOscillatoryEvolution`, `answer.md`, and
  `result.json`.
