# Physics LeanExplore Grounding Log

- Target Lean file: `QITFormalized/problem_qit_NormFidelityAndContinuityTools_ChannelFidelityGateFidelityPureInputState.lean`
- Blueprint chapter: `blueprint/src/chapters/QITFormalized_problem_qit_NormFidelityAndContinuityTools_ChannelFidelityGateFidelityPureInputState.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:a2b5350932ff31a4af460b23451bc1ffc23379953ed028cc9500c4b92a030900
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
