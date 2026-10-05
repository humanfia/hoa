# Prover result

## Status

Solved. The sole `sorry` in
`QAlgFormalized/problem_qalg_QSPParameterTrace_ThirdMomentTwoControlledSWAPTests.lean`
was replaced by a kernel-checked proof without changing any declaration
header. No `needs_redraft` request is required.

## Proof

- Expanded `U₂U₁` into its four ancilla projector branches, with data
  operators `I`, `S₁₂`, `S₁₃`, and `S₁₃S₁₂`.
- Computed the four one-qubit traces selected by the Pauli-`X` observable.
  Twelve of the sixteen branch pairs vanish; each complementary branch pair
  has coefficient `1/4`.
- Proved that both swap-product orientations are three-cycles and evaluated
  their traces against `ρ ⊗ ρ ⊗ ρ` by explicit finite-sum reindexing. Both
  orientations equal `tr (ρ³)`.
- Used cyclicity of matrix trace to put all four surviving data terms into
  one of those two orientations, after which their average is `tr (ρ³)`.

The density-matrix hypothesis is not needed by the proof because this
permutation-trace identity holds for every square complex matrix `ρ`; the
stated density-matrix theorem follows as a specialization.

## Verification

- `lake env lean QAlgFormalized/problem_qalg_QSPParameterTrace_ThirdMomentTwoControlledSWAPTests.lean`
  exited successfully. Its only message is the expected unused-hypothesis
  linter warning for `hρ`.
- Verification of
  `QAlgFormalized.QSPParameterTrace.ThirdMomentTwoControlledSWAPTests.thirdMoment_twoControlledSWAPTests`
  reported only the standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound`, with no source-scan warnings.
- The assigned file contains no `sorry`, `admit`, new `axiom`,
  `native_decide`, or `sorryAx`.
