# Physics LeanExplore Grounding Log

- Target Lean file: `QITFormalized/problem_qit_ChannelsAndChoiRepresentations_FixedPointEveryTracePreservingQuantumOperation.lean`
- Blueprint chapter: `blueprint/src/chapters/QITFormalized_problem_qit_ChannelsAndChoiRepresentations_FixedPointEveryTracePreservingQuantumOperation.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:78595164c1d800c51438c2b4f4285cb632a76fc888fb4a0efbae9ecfd9527afa
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
