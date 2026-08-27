---
license: apache-2.0
language:
- en
pretty_name: QIT Humanize-Physic Formalizations and Proofs
task_categories:
- text-generation
tags:
- lean
- theorem-proving
- quantum-information
- autoformalization
- formal-verification
size_categories:
- n<1K
configs:
- config_name: default
  data_files:
  - split: train
    path: data/qit_formalized.jsonl
---

# QIT Humanize-Physic Formalizations and Proofs

QIT (Quantum Information Theory) is a blind benchmark for formalizing theorems in quantum information. It evaluates whether an AI agent can faithfully translate natural-language and TeX problem statements into Lean 4 theorems and then construct formal proofs checked by the Lean kernel. Its 40 tasks cover quantum channels and Choi representations, entropy and coding, mixed-unitary obstructions and symmetry, norm and fidelity tools, and one-shot entropies and hypothesis testing. Each run receives only the natural-language problem and the `QITBench.Base` library, without official per-task Lean files, hints, or answers.

This dataset publishes all 40 natural-language QIT benchmark tasks together with the Lean 4 formalizations, proof artifacts, and final Review status produced by the blind Humanize-Physic run. The run used only the public TeX statements and the benchmark-local `QITBench.Base` library; official per-task Lean files, hints, and solutions were excluded.

## Final results

| Metric | Result | Pass rate |
|---|---:|---:|
| Generated and compilable formalizations | 40/40 | 100% |
| Formalization semantic review passed | 40/40 | 100% |
| Lean files free of `sorry` and `admit` | 40/40 | 100% |
| Formal Proof Review passed | 40/40 | 100% |
| End-to-end passed | 40/40 | **100%** |
| Conditional proof rate after semantic acceptance | 40/40 | 100% |
| Full `lake build` | Passed | 100% |

Being `sorry`-free is an important mechanical guarantee. In Lean, `sorry` is a placeholder that lets an unfinished proof compile by relying on the `sorryAx` escape hatch. A `sorry`-free file therefore contains complete proof terms instead of unproved claims hidden behind placeholders. Semantic review remains a separate requirement because a mechanically complete proof can still formalize the wrong statement.

## Review rounds

| Review stage | Maximum rounds per task | Observed distribution across 40 tasks |
|---|---:|---|
| Formalization semantic review | 5 | 1 round: 38 tasks; 2 rounds: 2 tasks |
| Proof Review | 5 | 1 round: 35 tasks; 2 rounds: 3 tasks; 3 rounds: 1 task; 5 rounds: 1 task |

The `formalization_review_count` and `proof_review_attempts` fields record the actual number of rounds for each task. Complete gate histories are stored in `metadata/`. These counts describe the final post-repair lifecycle of the pipeline.

## Foundation-build rounds

Two of the three most difficult final tasks triggered a task-local Foundation Build:

| Target | Foundation Build | Final status |
|---|---:|---|
| `ConvexityQuantumMutualInformation` | 6 rounds | Materialized; Proof Review solved |
| `ConverseEntanglementConcentration` | 2 rounds | Materialized; Proof Review solved |

For QMI convexity, the project reconstructed the operator extensions, isometries, inverse square roots, matrix logarithms, and trace-to-entropy dependency chain required for finite-dimensional strong subadditivity and weak monotonicity over its bare `CMatrix` representation. The converse task avoided unstable tensor-spectrum sorting indices by explicitly reconstructing the IID Schmidt decomposition, orthogonal truncation, and an LOCC overlap bound. The corresponding foundation sources are available in `foundations/` and in `lean-project/QITFoundations/` within the reproducible project.

The semantic score is the final automated reviewer result after automatic repair, not an independent external human blind audit. A compiling Lean file may still contain `sorry`, and a `sorry`-free file can still be rejected for an unfaithful theorem contract. Each row therefore exposes the mechanical and reviewer-based fields separately. All 40 final rows now pass both gates and contain no active proof placeholders.

## Results by topic

| Topic | Tasks | Semantic Review | Proof Review |
|---|---:|---:|---:|
| Channels and Choi representations | 11 | 11/11 | 11/11 |
| Entropy, coding, and information inequalities | 9 | 9/9 | 9/9 |
| Mixed-unitary obstructions and symmetry | 7 | 7/7 | 7/7 |
| Norm, fidelity, and continuity tools | 10 | 10/10 | 10/10 |
| One-shot entropies and hypothesis testing | 3 | 3/3 | 3/3 |
| **Total** | **40** | **40/40** | **40/40** |

## Contents

- `data/qit_formalized.jsonl`: Dataset Viewer table with the natural-language problem, source TeX, complete generated Lean code, Review status, and solution report.
- `lean/`: one generated, placeholder-free Lean file per task.
- `foundations/`: project-local dependency layers synthesized for the two Foundation Build targets.
- `sources/`: unchanged public TeX statements.
- `solution-reports/`: final per-task proof reports when available.
- `lean-project/`: reproducible Lean 4 project containing `QITBench.Base`, `QITFoundations`, and all generated files.
- `metadata/`: source manifest, final Formalization/Foundation/Proof Review gates, aggregate metrics, and topic metrics.

## Provenance

- Pinned source commit: `e4f0230e14c35da9c658b58c8663b3e6825e6663`
- Lean toolchain: `leanprover/lean4:v4.30.0`
- License: Apache-2.0

Generated formalizations and proofs are clearly separated from the unchanged public source statements. No official per-task Lean answer, hidden hint, agent session transcript, credential, runtime log, or cache is included.
