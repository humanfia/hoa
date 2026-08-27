# Physics LeanExplore Grounding Log

- Target Lean file: `QITFormalized/problem_qit_NormFidelityAndContinuityTools_GentleMeasurementLemmaNormalizedPostMeasurementState.lean`
- Blueprint chapter: `blueprint/src/chapters/QITFormalized_problem_qit_NormFidelityAndContinuityTools_GentleMeasurementLemmaNormalizedPostMeasurementState.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:50e095a38013772ee71d805834aeefb9ba20f66851242aac4cf5898f24529978
- Packages searched: Mathlib, QITBench

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `QITBench.OneShot.matrixSqrt` | module `QITBench.Base.OneShot` | package QITBench | Matrix square root used in finite-dimensional fidelity.
- `QITBench.OneShot.traceNorm` | module `QITBench.Base.OneShot` | package QITBench | Trace norm through the matrix-CFC square root.
- `QITBench.MatrixMap.exists_kraus_of_choi_psd` | module `QITBench.Base.Map` | package QITBench | Choi-positive maps have a finite Kraus representation [Wilde2011Qst, qit-notes.tex:8242-8262].

### Query: `Quantum Information formalization target`
- `QITBench.OneShot.quantumFidelity` | module `QITBench.Base.OneShot` | package QITBench | Unsquared quantum fidelity `Tr sqrt(sqrt(ρ) σ sqrt(ρ))`.
- `QITBench.OneShot.targetRankAtRate` | module `QITBench.Base.OneShot` | package QITBench | The rate-`R` target Schmidt rank `⌊2^(nR)⌋`.
- `QITBench.Channel.TensorPower` | module `QITBench.Base.Channel` | package QITBench | An `n`-use channel surface between recursive tensor-power systems.

## Grounded Mathlib/PhysLean names

- `QITBench.OneShot.matrixSqrt` (QITBench)
- `QITBench.OneShot.traceNorm` (QITBench)
- `QITBench.MatrixMap.exists_kraus_of_choi_psd` (QITBench)
- `QITBench.OneShot.quantumFidelity` (QITBench)
- `QITBench.OneShot.targetRankAtRate` (QITBench)
- `QITBench.Channel.TensorPower` (QITBench)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
