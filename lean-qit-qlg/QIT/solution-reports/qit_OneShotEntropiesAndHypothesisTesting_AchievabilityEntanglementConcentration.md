# Prover result — iteration 106

## Outcome

- Status: solved.
- `QITFormalized.achievability_entanglement_concentration` now has a
  kernel-checked proof with no remaining `sorry`.
- The frozen theorem signature is byte-for-byte unchanged from the iteration
  baseline.
- No other Lean file was edited.
- No `/- USER: ... -/` file-specific hint is present.
## Completed positive-rate construction

The previous proof already established the finite-alphabet weak AEP, the exact
floor-rank coefficient cap, and eventual convex-hull membership of the
normalized good spectrum. This iteration closed the remaining operational and
fidelity layer:

1. Extracted a finite convex decomposition of the normalized good spectrum.
2. Enumerated every fixed-cardinality support by an embedding `Fin M ↪ D`.
3. Used extending permutations to relabel every support to one common output
   subspace.
4. Instantiated the existing complete Nielsen filter, Bob feed-forward
   correction, local compression channels, and explicit two-round
   `FiniteRoundLOCCProtocol`.
5. Proved the channel action on the IID rank-one input branch-by-branch.
   Successful branches yield a uniform entangled vector; fallback branches
   yield correlated basis vectors.
6. Summed the branches to the exact output
   `s • maximallyEntangledDensity M + (1 - s) • correlatedDiagonalDensity M`.
7. Evaluated the matrix-CFC fidelity of this output exactly as
   `sqrt (s + (1 - s) / M)`.
8. Chose these protocols on the eventual AEP set and a valid local discard
   protocol elsewhere, then squeezed the exact fidelity formula to one using
   `iidInformationGoodMass_tendsto_one`.

The zero-rate discard construction remains unchanged and checked.

## Verification

Exact compiler command:

```text
lake env lean QITFormalized/problem_qit_OneShotEntropiesAndHypothesisTesting_AchievabilityEntanglementConcentration.lean
```

Result: exit code `0` (linter warnings only).

Source scan:

- `sorry`: 0
- `admit`: 0
- declared `axiom`: 0
- `native_decide`: 0
- `sorryAx`: 0

`lean_verify` for
`QITFormalized.achievability_entanglement_concentration` reports only:

```text
propext
Classical.choice
Quot.sound
```

No suspicious source patterns were reported.
