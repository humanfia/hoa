# Prover result

## Status

Solved. The sole `sorry` in
`QAlgFormalized/problem_qalg_QSPParameterTrace_SharedParameterShiftRuleRXTensorRZ.lean`
was replaced by a kernel-checked proof without changing the theorem signature.
No `needs_redraft` request is required.

## Proof

- Expanded the inner `R_X(θ) ⊗ R_Z(θ)` operator as a fixed matrix plus
  `cos θ` and `sin θ` times two fixed matrices, using the double-angle
  identities. Tensor bilinearity lifts this decomposition through the
  spectator identity.
- Introduced the trace coefficient
  `Tr[O A ρ B†]` and proved its linearity in `A` and conjugate-linearity in
  `B`.
- Used those laws to express the full loss as a quadratic trigonometric
  polynomial with the six modes
  `1`, `cos θ`, `sin θ`, `cos² θ`, `sin² θ`, and `cos θ sin θ`.
- Proved the ordinary real derivative of that polynomial with Mathlib's
  trigonometric derivative API and converted it to the theorem's custom
  punctured-neighborhood difference quotient.
- Verified the four-shift interpolation formula for the complete quadratic
  trigonometric family using the exact values at `π/4`, the relation
  `3π/4 = π - π/4`, and `(√2)² = 2`.

The density-matrix and observable hypotheses are not needed by the proof:
the parameter-shift identity is algebraic and analytic for arbitrary finite
complex matrices of the stated dimensions.

## Verification

- `lake env lean QAlgFormalized/problem_qalg_QSPParameterTrace_SharedParameterShiftRuleRXTensorRZ.lean`
  exited successfully. Its only messages are the expected unused-hypothesis
  linter warnings for `hρ` and `hO`.
- Verification of
  `QAlgFormalized.SharedParameterShiftRuleRXTensorRZ.sharedParameterShiftRule`
  reported only the standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound`, with no source-scan warnings.
- The assigned file contains no `sorry`, `admit`, new `axiom`,
  `native_decide`, or `sorryAx`.
