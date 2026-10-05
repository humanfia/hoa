# Prover result

## Status

Solved. The sole `sorry` in
`QAlgFormalized/problem_qalg_Circuits_ExactQROMFactorization.lean` was
replaced by a kernel-checked proof without changing the
`dataXTensor_eq_dataXPower` declaration header.

## Proof

- Proved that the benchmark's big-endian `prodEquiv` pairing is exactly
  `BitVec` append and used `BitVec.xor_append` to show that XOR respects this
  register decomposition.
- Proved that tensoring two `dataXPower` permutation gates gives the
  `dataXPower` gate for the paired data word.
- Handled the zero-qubit tensor as the unique permutation on `Fin 1`.
- Identified the final one-bit factor with identity or `Gate.X`, then
  inductively split every successor-width word into its MSB prefix and least
  significant bit. This proves that the explicit ordered tensor has exactly
  the same gate as XOR by the full word.

## Verification

- Lean LSP reported no diagnostics for the assigned file.
- `lake env lean QAlgFormalized/problem_qalg_Circuits_ExactQROMFactorization.lean`
  exited successfully with no output.
- Verification of
  `QAlgFormalized.ExactQROMFactorization.dataXTensor_eq_dataXPower` reported
  only the standard foundational axioms `propext`, `Classical.choice`, and
  `Quot.sound`, with no warnings.
- The assigned file contains no `sorry`, `admit`, new `axiom`,
  `native_decide`, or `sorryAx`.
