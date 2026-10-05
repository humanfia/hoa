---
license: apache-2.0
language:
- en
pretty_name: QAlg Humanize-Physic Formalizations and Proofs
task_categories:
- text-generation
tags:
- lean
- theorem-proving
- quantum-computing
- autoformalization
- formal-verification
size_categories:
- n<1K
configs:
- config_name: default
  data_files:
  - split: train
    path: data/qalg_formalized.jsonl
---

# QAlg Humanize-Physic Formalizations and Proofs

QAlg (Quantum Algorithms) is a blind benchmark for formalizing theorems in quantum algorithms. It evaluates whether an AI agent can faithfully translate natural-language and TeX problem statements into Lean 4 theorems and then construct formal proofs checked by the Lean kernel. Its 36 tasks cover quantum circuits, linear algebra, the quantum Fourier transform, Hamiltonian simulation, hidden subgroups, QSP/QSVT, and parameterized quantum circuits. Each run receives only the natural-language problem and the `QAlgBench.Base` library, without official per-task Lean answers. The benchmark therefore evaluates formalization accuracy, semantic fidelity, theorem-proving ability, and automatic repair.

This dataset publishes the 36 natural-language QAlg benchmark tasks together with the Lean 4 formalizations and kernel-checked proofs produced by the blind Humanize-Physic run. The run used only the public TeX statements and the benchmark-local `QAlgBench.Base` library; official per-task Lean files, hints, and solutions were excluded.

## Final results

| Metric | Result | Rate |
|---|---:|---:|
| Compilable formalizations | 36/36 | 100% |
| Final semantic review passed | 36/36 | 100% |
| Proofs completed and accepted by the Lean kernel | 36/36 | 100% |
| Lean files free of `sorry` and `admit` | 36/36 | 100% |
| Formal Proof Review certificate coverage | 35/36 | 97.2% |
| Pass rate among tasks that entered Proof Review | 35/35 | 100% |
| Full `lake build` | Passed | 100% |

Formal Proof Review certificate coverage of 35/36 does not mean that one proof is incorrect. `HadamardTensorHadamardMatrix` was already free of `sorry`, compiled successfully, and passed formalization semantic review twice before the proof stage, so it was not routed through the separate Proof Review gate. All 36 Lean files were accepted by the Lean kernel.

Being `sorry`-free is an important mechanical guarantee. In Lean, `sorry` is a placeholder that lets an unfinished proof compile by relying on the `sorryAx` escape hatch. A `sorry`-free file therefore contains complete proof terms instead of unproved claims hidden behind placeholders. Semantic review remains a separate requirement because a mechanically complete proof can still formalize the wrong statement.

The semantic score is the final automated reviewer result after automatic repair, not an independent external human blind audit. The objective mechanical claims are zero `sorry`/`admit`, successful target compilation, and a successful full `lake build`.

## Contents

- `data/qalg_formalized.jsonl`: Dataset Viewer table with natural-language problem, source TeX, complete Lean code, review status, and solution report.
- `lean/`: one completed Lean file per task.
- `sources/`: the immutable public TeX statements.
- `solution-reports/`: final per-task proof reports when available.
- `lean-project/`: a reproducible Lean 4 project containing `QAlgBench.Base` and all completed files.
- `metadata/`: source manifest, final review gates, and aggregate metrics.

## Provenance

- Lean toolchain: `leanprover/lean4:v4.31.0`
- License: Apache-2.0

Generated formalizations and proofs are clearly separated from the unchanged public source statements. No official per-task Lean answer, hidden hint, agent session transcript, credential, or runtime cache is included.
