# QITFormalized/problem_qit_EntropyCodingAndInformationInequalities_ConvexityQuantumMutualInformation.lean

## Summary

- Added 45 non-private and 3 private axiom-clean declarations. The public
  declarations are `matrix_sandwich_mono`,
  `matrix_conjTranspose_sandwich_mono`,
  `matrix_isometry_rangeProjection_le_one`,
  `matrix_cross_isometry_contraction_le_one`, `ssaMapToTensorMES`,
  `ssaMapToTensorMES_contraction`, `posDef_sqrt_inv_sandwich`,
  `posDef_sqrt_inv_sqrt`, `matrix_reindex_isHermitian`,
  `matrix_reindex_le_reindex_iff`, `matrix_kronecker_isHermitian`,
  `matrix_sandwich_le_iff_of_isUnit_isHermitian`, `ssaVRho`,
  `ssaVRho_apply`, `ssaVRho_isometry`, `matrix_kronecker_isometry`,
  `matrix_reindex_isometry`, `ssaMapFromTensorMES`,
  `ssaMapFromTensorMES_contraction`, `ssaVSigma`, `ssaVSigma_apply`,
  `ssaVSigma_isometry`, `ssaWMatrix`, `ssaSMatrix`,
  `ssaSMatrix_isHermitian`, `ssaSMatrix_isUnit`,
  `ssaWMatrix_sq_eq_sandwich`, `ssaIntermediateRHS`,
  `ssaSMatrix_mul_intermediateRHS_mul_ssaSMatrix`, `ssaWMatrix_apply`,
  `ssaWMatrix_apply_eq_sum_ssaVRho_mul_conjTranspose_ssaVSigma`,
  `ssaU1Matrix`, `ssaU2Matrix`, `ssaU1Matrix_isometry`,
  `ssaU2Matrix_isometry`, `ssaWMatrix_eq_conjTranspose_mul_ssaU`,
  `ssaWMatrix_sq_le_one`, `ssaIntermediate_ineq`,
  `ssaOperatorExtension`, `posDef_cfc_log_inv`,
  `posDef_cfc_log_kronecker`, `posDef_cfc_log_reindex`,
  `ssaLogOperatorInequality`, `ssaLogOperatorInequality_leftAssoc`, and
  `vonNeumannEntropyWeakMonotonicity_posDef`.
- Closed the previously blocked declaration
  `quantumConditionalEntropy_concave` by deriving positive-definite weak
  monotonicity from the Lin--Kim--Hsieh operator extension and feeding it
  through the already-formalized weak-monotonicity-to-SSA reduction.
- Declarations blocked: 0.
- Sorry count in the assigned file: `1 → 0`.
- Standalone verification:
  `lake env lean -o .lake/build/lib/lean/QITFormalized/problem_qit_EntropyCodingAndInformationInequalities_ConvexityQuantumMutualInformation.olean QITFormalized/problem_qit_EntropyCodingAndInformationInequalities_ConvexityQuantumMutualInformation.lean`
  exits 0.
- `lean_verify` was run on all 45 new public declarations and on
  `quantumConditionalEntropy_concave`; every result uses only
  `{propext, Classical.choice, Quot.sound}`.

## Session summary

- Built the rectangular sandwich-order and contraction leaves, then two
  explicit finite-dimensional isometries `ssaVRho` and `ssaVSigma`.
- Factored their cross Gram matrix through an invertible positive sandwich,
  proved the pre-inversion contraction inequality, and used the existing
  positive-definite inverse antitonicity theorem to obtain
  `ssaOperatorExtension`.
- Proved finite-matrix logarithm identities for inverse, Kronecker product,
  and basis reindexing, then applied operator monotonicity of `log`.
- Paired the resulting operator inequality with the tripartite state,
  reduced the four trace terms to marginal spectral-log pairings, and
  rewrote those pairings as von Neumann entropies.
- The implementation follows the operator-extension route in Physlib's
  `QuantumInfo/Entropy/SSA.lean`, adapted to this project's bare `CMatrix`
  representation and existing marginal conventions.
- No informal-agent key was available: `DEEPSEEK`, `MOONSHOT`,
  `OPENROUTER`, `OPENAI`, and `GEMINI` were absent.

## Declarations attempted

### `matrix_sandwich_mono` (line 2371)

- **Approach:** Translate Loewner order to positivity of the difference and
  conjugate by the rectangular matrix.
- **Result:** RESOLVED — axiom-clean.

### `matrix_conjTranspose_sandwich_mono` (line 2389)

- **Approach:** Apply `matrix_sandwich_mono` with the conjugate transpose.
- **Result:** RESOLVED — axiom-clean.

### `matrix_isometry_rangeProjection_le_one` (line 2398)

- **Approach:** Express `I - VVᴴ` as a positive range-complement projection
  using `VᴴV = I`.
- **Result:** RESOLVED — axiom-clean.

### `matrix_cross_isometry_contraction_le_one` (line 2438)

- **Approach:** Sandwich the preceding range-projection inequality by the
  second isometry.
- **Result:** RESOLVED — axiom-clean.

### `ssaMapToTensorMES` (line 2457)

- **Approach:** Define the delta map which inserts a maximally entangled copy
  of the shared basis.
- **Result:** RESOLVED — axiom-clean definition.

### `ssaMapToTensorMES_contraction` (line 2465)

- **Approach:** Expand both matrix products and collapse the delta sums.
- **Result:** RESOLVED — axiom-clean.

### `posDef_sqrt_inv_sandwich` (line 2478)

- **Approach:** Use the CFC square-root identities and nonsingular inverse
  cancellation for a positive-definite matrix.
- **Result:** RESOLVED — axiom-clean.

### `posDef_sqrt_inv_sqrt` (line 2502)

- **Approach:** Specialize the previous sandwich identity.
- **Result:** RESOLVED — axiom-clean.

### `matrix_reindex_isHermitian` (line 2532)

- **Approach:** Expand simultaneous submatrix reindexing and conjugate
  transpose.
- **Result:** RESOLVED — axiom-clean.

### `matrix_reindex_le_reindex_iff` (line 2541)

- **Approach:** Transport positive semidefiniteness in both directions along
  a finite equivalence.
- **Result:** RESOLVED — axiom-clean.

### `matrix_kronecker_isHermitian` (line 2553)

- **Approach:** Rewrite the conjugate transpose of a Kronecker product.
- **Result:** RESOLVED — axiom-clean.

### `matrix_sandwich_le_iff_of_isUnit_isHermitian` (line 2563)

- **Approach:** Cancel an invertible Hermitian sandwich using its unit inverse
  and order-preserving conjugation.
- **Result:** RESOLVED — axiom-clean.

### `ssaVRho` (line 2588)

- **Approach:** Compose the square root of `M`, the tensor-MES map, and the
  inverse square root of `Tr_B M`.
- **Result:** RESOLVED — axiom-clean definition.

### `ssaVRho_apply` (line 2593)

- **Approach:** Expand the two matrix multiplications and the delta map.
- **Result:** RESOLVED — axiom-clean.

### `ssaVRho_isometry` (line 2606)

- **Approach:** Collapse the MES sandwich to `Tr_B M` and cancel it against
  its inverse square roots.
- **Result:** RESOLVED — axiom-clean.

### `matrix_kronecker_isometry` (line 2647)

- **Approach:** Use `mul_kronecker_mul` and the two factor isometry equations.
- **Result:** RESOLVED — axiom-clean.

### `matrix_reindex_isometry` (line 2663)

- **Approach:** Transport the Gram matrix through simultaneous reindexing.
- **Result:** RESOLVED — axiom-clean.

### `ssaMapFromTensorMES` (line 2676)

- **Approach:** Define the complementary delta contraction for the second
  SSA isometry.
- **Result:** RESOLVED — axiom-clean definition.

### `ssaMapFromTensorMES_contraction` (line 2687)

- **Approach:** Expand the two products and collapse finite delta sums.
- **Result:** RESOLVED — axiom-clean.

### `ssaVSigma` (line 2702)

- **Approach:** Construct the second isometry from `sqrt N`,
  `(Tr_A N)⁻¹/²`, the MES contraction, and associator reindexing.
- **Result:** RESOLVED — axiom-clean definition.

### `ssaVSigma_apply` (line 2709)

- **Approach:** Expand the construction entrywise.
- **Result:** RESOLVED — axiom-clean.

### `ssaVSigma_isometry` (line 2723)

- **Approach:** Reduce to the complementary MES contraction and cancel the
  reduced density matrix against its inverse square roots.
- **Result:** RESOLVED — axiom-clean.

### `ssaWMatrix` (line 2765)

- **Approach:** Define the square-root-normalized cross operator in the
  Lin--Kim--Hsieh factorization.
- **Result:** RESOLVED — axiom-clean definition.

### `ssaSMatrix` (line 2776)

- **Approach:** Define the positive square-root sandwich used to cancel the
  cross-operator inequality.
- **Result:** RESOLVED — axiom-clean definition.

### `ssaSMatrix_isHermitian` (line 2785)

- **Approach:** Combine Hermiticity of CFC square roots and Kronecker
  products.
- **Result:** RESOLVED — axiom-clean.

### `ssaSMatrix_isUnit` (line 2797)

- **Approach:** Use positive definiteness of the Kronecker factors and the
  square-root functional calculus.
- **Result:** RESOLVED — axiom-clean.

### `ssaWMatrix_sq_eq_sandwich` (line 2826)

- **Approach:** Expand `WᴴW`, commute compatible spectral factors, and reduce
  the middle product to the two SSA isometries.
- **Result:** RESOLVED — axiom-clean.

### `ssaIntermediateRHS` (line 2863)

- **Approach:** Define the associator-reindexed reduced-matrix product that
  appears before inversion.
- **Result:** RESOLVED — axiom-clean definition.

### `ssaSMatrix_mul_intermediateRHS_mul_ssaSMatrix` (line 2873)

- **Approach:** Expand and cancel square-root/inverse-square-root factors.
- **Result:** RESOLVED — axiom-clean.

### `ssaWMatrix_apply` (line 2907)

- **Approach:** Expand the normalized cross operator entrywise.
- **Result:** RESOLVED — axiom-clean.

### `ssaWMatrix_apply_eq_sum_ssaVRho_mul_conjTranspose_ssaVSigma` (line 2923)

- **Approach:** Match the entry expansion with the cross Gram matrix of the
  two isometries by finite-sum reassociation.
- **Result:** RESOLVED — axiom-clean.

### `ssaU1Matrix` (line 2961)

- **Approach:** Tensor `ssaVRho` with the identity needed for a common
  codomain.
- **Result:** RESOLVED — axiom-clean definition.

### `ssaU2Matrix` (line 2972)

- **Approach:** Reindex and tensor `ssaVSigma` into the same codomain.
- **Result:** RESOLVED — axiom-clean definition.

### `ssaU1Matrix_isometry` (line 2979)

- **Approach:** Apply `matrix_kronecker_isometry` to `ssaVRho_isometry`.
- **Result:** RESOLVED — axiom-clean.

### `ssaU2Matrix_isometry` (line 2990)

- **Approach:** Apply the Kronecker and reindexing isometry lemmas to
  `ssaVSigma_isometry`.
- **Result:** RESOLVED — axiom-clean.

### `ssaWMatrix_eq_conjTranspose_mul_ssaU` (line 3001)

- **Approach:** Use the entrywise cross-Gram identity.
- **Result:** RESOLVED — axiom-clean.

### `ssaWMatrix_sq_le_one` (line 3021)

- **Approach:** Invoke `matrix_cross_isometry_contraction_le_one` on
  `ssaU1Matrix` and `ssaU2Matrix`.
- **Result:** RESOLVED — axiom-clean.

### `ssaIntermediate_ineq` (line 3033)

- **Approach:** Rewrite `WᴴW ≤ I` as equal invertible `S` sandwiches and
  cancel `S`.
- **Result:** RESOLVED — axiom-clean.

### `ssaOperatorExtension` (line 3052)

- **Approach:** Apply positive-definite inverse antitonicity to the
  intermediate inequality, simplify inverses of Kronecker products and
  reindexing, and transport back through the associator.
- **Result:** RESOLVED — axiom-clean.

### `matrix_cfc_isHermitian` (private, line 3108)

- **Approach:** Rewrite the finite spectral CFC to Mathlib's generic CFC and
  apply `IsSelfAdjoint.cfc`.
- **Result:** RESOLVED — axiom-clean.

### `posDef_cfc_log_inv` (line 3118)

- **Approach:** Show `exp (-log M) = M⁻¹`, then use `CFC.log_exp`.
- **Result:** RESOLVED — axiom-clean.

### `posDef_cfc_log_kronecker` (line 3141)

- **Approach:** Exponentiate the commuting tensor-factor logarithms and use
  uniqueness through `CFC.log_exp`.
- **Result:** RESOLVED — axiom-clean.

### `posDef_cfc_log_reindex` (line 3207)

- **Approach:** Commute matrix exponential with the reindex algebra
  equivalence, then apply `CFC.log_exp`.
- **Result:** RESOLVED — axiom-clean.

### `ssaLogOperatorInequality` (line 3238)

- **Approach:** Apply `Matrix.PosDef.cfc_log_mono` to
  `ssaOperatorExtension` and normalize both sides with the three logarithm
  identities.
- **Result:** RESOLVED — axiom-clean.

### `ssaLogOperatorInequality_leftAssoc` (line 3287)

- **Approach:** Reindex both sides by the inverse associator and identify the
  four tensor lifts entrywise.
- **Result:** RESOLVED — axiom-clean.

### `re_trace_mul_ssaLiftAMatrix` (private, line 3339)

- **Approach:** Apply the existing `AB` lift trace identity and then trace
  out `B`.
- **Result:** RESOLVED — axiom-clean.

### `re_trace_mul_ssaLiftCMatrix` (private, line 3361)

- **Approach:** Apply
  `partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right`.
- **Result:** RESOLVED — axiom-clean.

### `vonNeumannEntropyWeakMonotonicity_posDef` (line 3865)

- **Approach:** Pair `ssaLogOperatorInequality_leftAssoc` with `tau.pos`,
  rewrite the four lifted trace pairings as marginal pairings, and replace
  each spectral-log pairing by negative von Neumann entropy.
- **Result:** RESOLVED — axiom-clean.

### `quantumConditionalEntropy_concave` (line 4570)

- **Approach 1:** The pre-existing direct Lieb three-matrix branch was
  retained during scouting; Mathlib has no ready theorem for its remaining
  integral inequality.
- **Approach 2:** Completed the alternative Lin--Kim--Hsieh operator
  extension, derived positive-definite weak monotonicity, and supplied it to
  `vonNeumannEntropyStrongSubadditivity_of_posDef_weakMonotonicity`.
- **Result:** RESOLVED — the original statement and signature are unchanged,
  its proof is axiom-clean, and the final `sorry` was removed.
- **Dead end:** Do not restore the direct Lieb-integral placeholder. The
  operator-extension route now proves the unconditional theorem completely.

## Needs blueprint entry

The blueprint chapter is protected read-only in this prover run, so I could
not add `\leanok` or auxiliary nodes. The existing environment for
`quantumConditionalEntropy_concave` should be marked `\leanok`. Add one
`lean_aux` entry for each new public declaration below; every declaration is
in
`QITFormalized/problem_qit_EntropyCodingAndInformationInequalities_ConvexityQuantumMutualInformation.lean`.

- `matrix_sandwich_mono` — relies on `Matrix.le_iff` and PSD conjugation.
- `matrix_conjTranspose_sandwich_mono` — relies on
  `matrix_sandwich_mono`.
- `matrix_isometry_rangeProjection_le_one` — relies on isometry
  cancellation and PSD range-complement projection.
- `matrix_cross_isometry_contraction_le_one` — relies on the preceding two
  sandwich/range lemmas.
- `ssaMapToTensorMES` — delta-map definition.
- `ssaMapToTensorMES_contraction` — relies on finite delta-sum collapse.
- `posDef_sqrt_inv_sandwich` — relies on CFC square-root identities and
  nonsingular inverse cancellation.
- `posDef_sqrt_inv_sqrt` — relies on `posDef_sqrt_inv_sandwich`.
- `matrix_reindex_isHermitian` — relies on conjugate transpose of submatrix.
- `matrix_reindex_le_reindex_iff` — relies on PSD submatrix transport.
- `matrix_kronecker_isHermitian` — relies on
  `Matrix.conjTranspose_kronecker`.
- `matrix_sandwich_le_iff_of_isUnit_isHermitian` — relies on
  `matrix_sandwich_mono` and unit cancellation.
- `ssaVRho` — relies on matrix square roots, `ssaMapToTensorMES`, and
  `partialTraceB`.
- `ssaVRho_apply` — relies on `ssaVRho` and finite matrix multiplication.
- `ssaVRho_isometry` — relies on `ssaMapToTensorMES_contraction`,
  `posDef_sqrt_inv_sandwich`, and partial-trace identities.
- `matrix_kronecker_isometry` — relies on `Matrix.mul_kronecker_mul`.
- `matrix_reindex_isometry` — relies on algebraic reindexing.
- `ssaMapFromTensorMES` — complementary delta-map definition.
- `ssaMapFromTensorMES_contraction` — relies on finite delta-sum collapse.
- `ssaVSigma` — relies on `ssaMapFromTensorMES`, square roots, and
  associator reindexing.
- `ssaVSigma_apply` — relies on `ssaVSigma` and finite matrix multiplication.
- `ssaVSigma_isometry` — relies on `ssaMapFromTensorMES_contraction`,
  `posDef_sqrt_inv_sandwich`, and partial-trace identities.
- `ssaWMatrix` — normalized cross-operator definition.
- `ssaSMatrix` — positive sandwich-factor definition.
- `ssaSMatrix_isHermitian` — relies on CFC square-root and Kronecker
  Hermiticity.
- `ssaSMatrix_isUnit` — relies on positive-definite Kronecker products and
  CFC square-root invertibility.
- `ssaWMatrix_sq_eq_sandwich` — relies on `ssaVRho_isometry`,
  `ssaVSigma_isometry`, and spectral-factor commutation.
- `ssaIntermediateRHS` — associator-reindexed reduced-matrix definition.
- `ssaSMatrix_mul_intermediateRHS_mul_ssaSMatrix` — relies on square-root
  inverse cancellation.
- `ssaWMatrix_apply` — relies on the definition of `ssaWMatrix`.
- `ssaWMatrix_apply_eq_sum_ssaVRho_mul_conjTranspose_ssaVSigma` — relies on
  `ssaVRho_apply`, `ssaVSigma_apply`, and finite-sum reassociation.
- `ssaU1Matrix` — tensor extension of `ssaVRho`.
- `ssaU2Matrix` — reindexed tensor extension of `ssaVSigma`.
- `ssaU1Matrix_isometry` — relies on `ssaVRho_isometry` and
  `matrix_kronecker_isometry`.
- `ssaU2Matrix_isometry` — relies on `ssaVSigma_isometry`,
  `matrix_kronecker_isometry`, and `matrix_reindex_isometry`.
- `ssaWMatrix_eq_conjTranspose_mul_ssaU` — relies on the cross-Gram entry
  identity.
- `ssaWMatrix_sq_le_one` — relies on
  `matrix_cross_isometry_contraction_le_one`.
- `ssaIntermediate_ineq` — relies on `ssaWMatrix_sq_le_one`,
  `ssaWMatrix_sq_eq_sandwich`, and invertible sandwich cancellation.
- `ssaOperatorExtension` — relies on `ssaIntermediate_ineq`,
  `posDef_nonsingInv_antitone`, inverse-Kronecker simplification, and
  reindex order transport.
- `posDef_cfc_log_inv` — relies on `CFC.exp_log`, `CFC.log_exp`, and matrix
  exponential of negation.
- `posDef_cfc_log_kronecker` — relies on commuting matrix exponentials,
  Kronecker multiplication, `CFC.exp_log`, and `CFC.log_exp`.
- `posDef_cfc_log_reindex` — relies on
  `normedSpace_exp_matrix_reindex`, `CFC.exp_log`, and `CFC.log_exp`.
- `ssaLogOperatorInequality` — relies on `ssaOperatorExtension`,
  `Matrix.PosDef.cfc_log_mono`, and all three CFC-log identities.
- `ssaLogOperatorInequality_leftAssoc` — relies on
  `ssaLogOperatorInequality` and associator reindex transport.
- `vonNeumannEntropyWeakMonotonicity_posDef` — relies on
  `ssaLogOperatorInequality_leftAssoc`,
  `Matrix.PosSemidef.re_trace_mul_mono_right`, partial-trace pairing
  identities, and
  `vonNeumannEntropy_eq_neg_re_trace_mul_spectralLogMatrix`.

## Why I stopped

- **Real progress:** 45 new axiom-clean public declarations were added at
  lines 2371–3326 and 3865; all are named in the Summary and individually
  logged above.
- **Target progress:** `quantumConditionalEntropy_concave` is fully proved at
  line 4570, and the assigned file now contains no `sorry`.
- **Partial progress:** none.
- **Blocked declarations:** none.
- **Approaches written but not attempted:** none. The direct Lieb branch was
  scouted and the operator-extension alternative was fully attempted and
  completed.
- **Verification:** standalone compilation succeeds; axiom audits for every
  new public declaration and the target show only the three allowed axioms.
- Stopped because the assigned objective is complete. The only remaining
  work is blueprint bookkeeping, which is outside this run's write
  permissions.
