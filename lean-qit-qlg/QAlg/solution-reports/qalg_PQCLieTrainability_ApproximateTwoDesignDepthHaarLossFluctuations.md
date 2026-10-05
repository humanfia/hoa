# Prover result — iteration 087

## Status

Solved. Every `sorry` in the assigned Lean file was replaced by a
kernel-checked proof, with all original declaration headers preserved.

## Formalized proofs

- Proved continuity of the two-copy conjugation coordinates and the
  Hilbert--Schmidt orthogonal-complement submodule laws.
- Proved `approximateTwoDesign_of_depth` from the contraction estimate and
  logarithmic depth threshold.
- Proved `inversePolynomialAccuracy_depth_isBigO`, including the eventual
  inverse-polynomial design conclusion and the asymptotic depth estimate.
- Proved continuity of `haarLoss` and of conjugated-state tensor-square
  coordinates.
- Developed the required Haar-functional algebra and special-unitary
  phase/swap symmetries to prove `haarLoss_mean_zero` without assuming a first
  moment formula.
- Proved `haarLoss_variance` from the supplied pure-state two-copy Haar
  identity. The proof expands the squared trace entrywise, applies the
  two-copy expectation, contracts the identity/swap tensors, uses
  tracelessness, and obtains both the exact formula and the
  `1 / (N + 1)` bound.
- Proved `haarLoss_exponential_fluctuation` using `N = 2^n`, monotonicity of
  reciprocal and square root, and the corresponding real-power identities.

## Verification

The exact project command succeeded:

```text
lake env lean QAlgFormalized/problem_qalg_PQCLieTrainability_ApproximateTwoDesignDepthHaarLossFluctuations.lean
```

It exited with code 0 and emitted only lint/deprecation warnings.

Additional checks:

- Lean LSP reports no errors in the file.
- Source scan finds no `sorry`, `admit`, `axiom`, or `native_decide`.
- `lean_verify` on all five requested theorem targets reports only the standard
  axioms `propext`, `Classical.choice`, and `Quot.sound`; the final target's
  source scan reports no warnings.
- `git diff --check` passes for the assigned Lean file.

## Notes

- No other Lean source file or protected file was edited.
