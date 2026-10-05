# Prover result

## Status

Solved. The sole `sorry` in
`QAlgFormalized/problem_qalg_LinearAlgebra_UnitaryExtensionMarkovChainIsometry.lean`
was replaced by a kernel-checked proof without changing any declaration
header.

## Proof

- Computed the inner products of the coherent row states directly. Distinct
  row labels have disjoint first-register support, while a state's squared
  norm reduces via `Real.sq_sqrt` and the stochastic row sum to one.
- Applied
  `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` to extend the
  prescribed columns indexed by `(i, 0)` to a full orthonormal basis.
- Used
  `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` to obtain the
  required unitary change-of-basis matrix.
- Used `QAlgBench.HilbertOperator.applyVec_ket` and the computational
  orthonormal basis coordinate formula to prove both the ket-action and
  entrywise column conclusions.

## Verification

- `lake env lean QAlgFormalized/problem_qalg_LinearAlgebra_UnitaryExtensionMarkovChainIsometry.lean`
  exited successfully with no output.
- The theorem verification scan reported only the standard foundational
  axioms `propext`, `Classical.choice`, and `Quot.sound`, with no warnings.
- The assigned file contains no `sorry`, `admit`, new `axiom`, or
  `native_decide`.
