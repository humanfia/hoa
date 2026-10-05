# QITFormalized/problem_qit_OneShotEntropiesAndHypothesisTesting_ConverseEntanglementConcentration.lean

## Session summary

- Added 18 axiom-clean declarations: 17 private IID Schmidt-decomposition
  helpers (lines 960–1439) and one reusable public one-shot LOCC truncation
  theorem (lines 1548–1684).
- Closed `converse_entanglement_concentration` (line 1692) by replacing the
  arbitrary tensor-spectrum indexing obligation with an explicit tensor
  product of one-copy marginal Schmidt components.
- The retained components are indexed directly by
  `iidLowInformationSupport`; their total LOCC maximally-entangled overlap is
  at most support-cardinality divided by target rank, while orthogonality
  identifies the discarded squared norm exactly with
  `iidHighInformationMass`.
- Full assigned-file compilation exits 0 with no warnings and no `sorry`.
## `iidSchmidtLeftAmplitude` (line 960)

- **Approach:** Defined the Alice factor of an IID Schmidt component as the
  recursive tensor product of the one-copy marginal eigenvectors.
- **Result:** RESOLVED — private, axiom-clean through the public truncation
  theorem.

## `iidSchmidtRightAmplitude` (line 971)

- **Approach:** Defined the Bob factor recursively from the projections of
  the one-copy amplitude onto Alice's marginal eigenvectors.
- **Result:** RESOLVED — private, axiom-clean through the public truncation
  theorem.

## `iidSchmidtComponent` (line 985)

- **Approach:** Formed each bipartite IID Schmidt component as the product of
  its recursive Alice and Bob amplitudes.
- **Result:** RESOLVED — private, axiom-clean through the public truncation
  theorem.

## `sum_iidSchmidtComponent` (line 995)

- **Approach:** Inducted on blocklength, used
  `sum_marginalEigenvectorAmplitude` for the one-copy factor, and factored the
  finite product sum with `Finset.sum_mul_sum`.
- **Result:** RESOLVED — private, axiom-clean.

## `marginalEigenvectorBasis_amplitudeSquaredNorm` (line 1056)

- **Approach:** Converted `amplitudeSquaredNorm` to the Euclidean-space norm
  and used orthonormality of `Matrix.IsHermitian.eigenvectorBasis`.
- **Result:** RESOLVED — private, axiom-clean.

## `iidSchmidtLeftAmplitude_amplitudeSquaredNorm` (line 1076)

- **Approach:** Inducted over tensor length and applied
  `amplitudeSquaredNorm_product`; every Alice tensor factor has norm one.
- **Result:** RESOLVED — private, axiom-clean.

## `iidSchmidtRightAmplitude_amplitudeSquaredNorm` (line 1102)

- **Approach:** Inducted over tensor length, using
  `marginalEigenvector_projected_amplitudeSquaredNorm` and
  `amplitudeSquaredNorm_product`.
- **Result:** RESOLVED — the resulting norm is exactly
  `iidSpectrumWeight`.

## `iidSchmidtComponent_amplitudeSquaredNorm` (line 1171)

- **Approach:** Factored the bipartite component norm into its Alice and Bob
  norms, then used the preceding two results.
- **Result:** RESOLVED — private, axiom-clean.

## `dotProduct_product` (line 1192)

- **Approach:** Expanded the finite dot product on a product type and factored
  the double sum with `Finset.sum_mul_sum`.
- **Result:** RESOLVED — private, axiom-clean.

## `marginalEigenvectorBasis_dotProduct_eq_zero` (line 1208)

- **Approach:** Identified the coordinate dot product with the Euclidean inner
  product and used orthonormality for distinct marginal eigenvectors.
- **Result:** RESOLVED — private, axiom-clean.

## `iidSchmidtLeftAmplitude_dotProduct_eq_zero` (line 1230)

- **Approach:** Inducted on the IID string. A first-letter mismatch uses
  one-copy eigenvector orthogonality; otherwise the induction hypothesis
  handles the tail.
- **Result:** RESOLVED — private, axiom-clean.

## `iidSchmidtComponent_dotProduct_eq_zero` (line 1271)

- **Approach:** Factored the bipartite component dot product and killed its
  Alice factor using the preceding IID orthogonality theorem.
- **Result:** RESOLVED — private, axiom-clean.

## `iidSchmidtTruncation` (line 1293)

- **Approach:** Defined truncation as the finite sum of explicit IID Schmidt
  components over an arbitrary support finset.
- **Result:** RESOLVED — private, axiom-clean through the public truncation
  theorem.

## `iidSchmidtTruncation_add_compl` (line 1302)

- **Approach:** Used `Finset.sum_sdiff` and
  `sum_iidSchmidtComponent` to split the full amplitude into retained and
  complementary component sums.
- **Result:** RESOLVED — private, axiom-clean.

## `iidSchmidtTruncation_amplitudeSquaredNorm` (line 1324)

- **Approach:** Inducted over the support finset, applied orthogonal norm
  additivity, and rewrote every component norm as its IID spectral weight.
- **Result:** RESOLVED — private, axiom-clean.

## `iidSpectrumWeight_sum_compl_lowInformationSupport` (line 1388)

- **Approach:** Rewrote the complement sum as a sum of membership conditionals
  and split on positive weight and the information threshold. Zero-weight
  strings contribute zero on both sides.
- **Result:** RESOLVED — the complement mass is exactly
  `iidHighInformationMass`.

## `iidSchmidtTruncation_compl_amplitudeSquaredNorm` (line 1419)

- **Approach:** Combined truncation norm additivity with the complement-mass
  identity, using `stateEigenvalues_isProbabilityDistribution`.
- **Result:** RESOLVED — private, axiom-clean.

## `LOCCProtocol.sqrt_sum_branch_maximallyEntangled_overlap_sq_le_iidTruncation` (line 1548)

- **Approach:** Applied
  `LOCCProtocol.sum_branch_maximallyEntangled_overlap_sq_sum_product_le` to
  the explicitly retained product components, bounded their total mass by
  one, and combined the retained and discarded parts via
  `LOCCProtocol.sqrt_sum_branch_overlap_sq_add_le`.
- **Result:** RESOLVED — public and axiom-clean.
- **Axioms:** `{propext, Classical.choice, Quot.sound}`.

## `converse_entanglement_concentration` (line 1692)

- **Approach 1:** Searched Mathlib for a theorem identifying eigenvalues of a
  Hermitian Kronecker product with pairwise products. LeanSearch returned
  Kronecker determinant and algebra lemmas but no tensor-spectrum theorem.
- **Approach 2:** Avoided arbitrary sorted eigenvalue indices by constructing
  the tensor-power Schmidt decomposition explicitly from the one-copy
  marginal eigenbasis.
- **Approach 3:** Fed the resulting one-shot IID truncation estimate into the
  already-proved vanishing spectral envelope and asymptotic-rate reduction.
- **Result:** RESOLVED — the former sole `sorry` is removed.
- **Axioms:** `{propext, Classical.choice, Quot.sound}`.
- **Dead end:** Do not reintroduce a pointwise equality between Mathlib's
  sorted tensor-marginal eigenvalue function and `iidSpectrumWeight`; the
  indexing need not align. The explicit component decomposition is
  index-stable and avoids that false strengthening.

## Verification

- `lake env lean
  QITFormalized/problem_qit_OneShotEntropiesAndHypothesisTesting_ConverseEntanglementConcentration.lean`
  exits 0 with no diagnostics.
- `lean_verify` on
  `LOCCProtocol.sqrt_sum_branch_maximallyEntangled_overlap_sq_le_iidTruncation`
  reports exactly `{propext, Classical.choice, Quot.sound}`.
- `lean_verify` on `converse_entanglement_concentration` reports exactly
  `{propext, Classical.choice, Quot.sound}`.
- Source scan finds no `sorry`, `admit`, `axiom`, or `native_decide`.
- `git diff --check` passes for the assigned Lean file.
- No `DEEPSEEK`, `MOONSHOT`, `OPENROUTER`, `OPENAI`, or `GEMINI` key was
  present. The informal agent was not needed because the direct proof closed.
## Summary

- Declarations added: 18 — `iidSchmidtLeftAmplitude`,
  `iidSchmidtRightAmplitude`, `iidSchmidtComponent`,
  `sum_iidSchmidtComponent`,
  `marginalEigenvectorBasis_amplitudeSquaredNorm`,
  `iidSchmidtLeftAmplitude_amplitudeSquaredNorm`,
  `iidSchmidtRightAmplitude_amplitudeSquaredNorm`,
  `iidSchmidtComponent_amplitudeSquaredNorm`, `dotProduct_product`,
  `marginalEigenvectorBasis_dotProduct_eq_zero`,
  `iidSchmidtLeftAmplitude_dotProduct_eq_zero`,
  `iidSchmidtComponent_dotProduct_eq_zero`, `iidSchmidtTruncation`,
  `iidSchmidtTruncation_add_compl`,
  `iidSchmidtTruncation_amplitudeSquaredNorm`,
  `iidSpectrumWeight_sum_compl_lowInformationSupport`,
  `iidSchmidtTruncation_compl_amplitudeSquaredNorm`, and
  `LOCCProtocol.sqrt_sum_branch_maximallyEntangled_overlap_sq_le_iidTruncation`.
- Declarations blocked: 0.
- Existing target declaration closed: 1 —
  `converse_entanglement_concentration`.
- Assigned-file sorry count: 1 → 0.

## Needs blueprint entry

- `QITFormalized.OneShotEntropiesAndHypothesisTesting.ConverseEntanglementConcentration.LOCCProtocol.sqrt_sum_branch_maximallyEntangled_overlap_sq_le_iidTruncation`
  — file
  `QITFormalized/problem_qit_OneShotEntropiesAndHypothesisTesting_ConverseEntanglementConcentration.lean`,
  line 1548. Its proof relies on the explicit IID Schmidt-component
  reconstruction and orthogonality developed privately in this file,
  `iidSpectrumWeight_sum`, `stateEigenvalues_isProbabilityDistribution`,
  `LOCCProtocol.sum_branch_maximallyEntangled_overlap_sq_sum_product_le`, and
  `LOCCProtocol.sqrt_sum_branch_overlap_sq_add_le`.

The protected blueprint chapter also needs `\leanok` on the existing target
environment now that `converse_entanglement_concentration` is closed; this
prover could not edit the protected chapter.

## Why I stopped

- **Real progress:** 18 axiom-clean declarations added (lines 960–1684), and
  the main theorem closed at line 1692.
- **Partial progress:** none.
- **Approaches written but not attempted:** none.
- **Blocked — alternatives exhausted:** not applicable; the proof is complete.
- **Infrastructure already exists:** the imported foundation supplied the
  product-Kraus overlap and Minkowski-style truncation inequalities. Mathlib
  did not supply the Kronecker-spectrum identification, so the explicit IID
  Schmidt decomposition was proved project-locally.
