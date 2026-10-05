# Physics LeanExplore Grounding Log

- Target Lean file: `QITFormalized/problem_qit_NormFidelityAndContinuityTools_VariationalCharacterizationTraceNorm.lean`
- Blueprint chapter: `blueprint/src/chapters/QITFormalized_problem_qit_NormFidelityAndContinuityTools_VariationalCharacterizationTraceNorm.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7c115a84f7ea712aaf3fd53ca92588af2db2b363952d7ee17a47223623c7ea5f
- Packages searched: Mathlib, QITBench

## LeanExplore queries/candidates actually used

### Query: `Quantum Information formalization target`
- `QITBench.OneShot.quantumFidelity` | module `QITBench.Base.OneShot` | package QITBench | Unsquared quantum fidelity `Tr sqrt(sqrt(ρ) σ sqrt(ρ))`.
- `QITBench.OneShot.targetRankAtRate` | module `QITBench.Base.OneShot` | package QITBench | The rate-`R` target Schmidt rank `⌊2^(nR)⌋`.
- `QITBench.Channel.TensorPower` | module `QITBench.Base.Channel` | package QITBench | An `n`-use channel surface between recursive tensor-power systems.

## Grounded Mathlib/PhysLean names

- `QITBench.OneShot.quantumFidelity` (QITBench)
- `QITBench.OneShot.targetRankAtRate` (QITBench)
- `QITBench.Channel.TensorPower` (QITBench)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
