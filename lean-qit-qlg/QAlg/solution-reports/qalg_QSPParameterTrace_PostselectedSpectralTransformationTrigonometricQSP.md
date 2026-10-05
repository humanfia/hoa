# Prover result

## Status

Solved. The sole `sorry` in
`QAlgFormalized/problem_qalg_QSPParameterTrace_PostselectedSpectralTransformationTrigonometricQSP.lean`
was replaced by a kernel-checked proof without changing the theorem signature.

## Proof

- Derived the action of the supplied spectral sum on each vector of the
  orthonormal eigenbasis, including the corresponding conjugate-transpose
  eigenvalue.
- Proved that the controlled odd and even signal gates restrict on an
  eigenvector to `phaseGate x` and `phaseGateOnZero (-x)` on the control.
- Used the Base library's phase-gate/`rotZStd` identities and a list-induction
  invariant to show that the `L` positive and `L` negative scalar half-phases
  cancel in the full `2 * L`-signal sequence.
- Identified the projected control-zero block with the QSP amplitude on every
  eigenbasis vector, yielding the spectral-polynomial operator equality.
- Proved the positive- and negative-integer power eigenvalue formulas, expanded
  the finite Laurent sum, and obtained the Laurent-operator equality.
- Rewrote the raw postselection branch by the projected-block identity; the
  required normalized-vector equality then follows directly.

## Verification

- Lean LSP reports no errors in the assigned file.
- `lake env lean
  QAlgFormalized/problem_qalg_QSPParameterTrace_PostselectedSpectralTransformationTrigonometricQSP.lean`
  exits successfully.
- Verification of
  `QAlgFormalized.PostselectedSpectralTransformationTrigonometricQSP.postselected_spectral_transformation`
  reports only `propext`, `Classical.choice`, and `Quot.sound`, with no source
  scan warnings.
- The assigned file contains no `sorry`, `admit`, new `axiom`,
  `native_decide`, or `sorryAx`.
