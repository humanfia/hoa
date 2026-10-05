# Prover result

## Status

Solved. All five `sorry` bodies in
`QAlgFormalized/problem_qalg_QSPParameterTrace_ParityMaximumFejerKernelQSPResponse.lean`
were replaced by kernel-checked proofs without changing any theorem signature.
No `needs_redraft` request is required.

## Proof

- Proved a list-induction invariant for the first column of the ordered QSP
  tail product. The upper entry is represented by a polynomial of degree at
  most the number of signal factors; the lower entry is
  `sqrt (1-a^2)` times a polynomial of the opposite parity.
- In the induction step, used `QAlgBench.sq_sqrt_one_sub_sq` to replace the
  only product of two square-root factors by `1-a^2`. The resulting polynomial
  recurrences preserve the sharp degree bounds and the required parity.
- Multiplied the tail polynomial by the initial diagonal phase to obtain the
  polynomial witness for `qspResponse_isPolynomial`; the same invariant gives
  `qspResponse_parity`.
- Expanded the squared geometric sum as a product of a conjugate sum and an
  ordinary sum. Grouped the resulting index pairs by their integer difference
  and proved that the fiber at `ℓ` has cardinality `k+1-|ℓ|`, including
  separate nonnegative and negative integer cases.
- Used that fiber count to prove the exact Fejér identity. The unit-interval
  bound follows from nonnegativity of `Complex.normSq` and the triangle bound
  on the geometric sum, while the endpoint theorem follows by evaluating all
  exponential terms at angle zero.

## Verification

- `lake env lean
  QAlgFormalized/problem_qalg_QSPParameterTrace_ParityMaximumFejerKernelQSPResponse.lean`
  exits successfully with no diagnostics.
- `lake build` completes successfully (2383 jobs); its messages are pre-existing
  linter warnings in protected Base files.
- Lean verification of all five public theorems reports only `propext`,
  `Classical.choice`, and `Quot.sound`, with no source-scan warnings.
- The assigned file contains no `sorry`, `admit`, new `axiom`, `sorryAx`, or
  `USER` marker, and `git diff --check` passes.
