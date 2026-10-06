# HOA: Humanize Olympic Agents

> [!NOTE]
> HOA is part of the RSI effort at NVIDIA Research. [Humanize](https://github.com/humanfia/humanize)
> is an open agent-loop framework led by [NVIDIA Research](https://www.nvidia.com/en-us/research),
> [UCLA PolyArch](https://polyarch.cs.ucla.edu), and [MIT HAN Lab](https://hanlab.mit.edu),
> together with open-source community members. The project page is
> [humanfia.ai/projects/hoa](https://humanfia.ai/projects/hoa).

HOA is a unified, reproducible archive of Humanfia's agent work on major
international competitions, formal-reasoning benchmarks, and verified
scientific libraries. It brings together IMO, IPhO, IChO, IOI, IBO,
PutnamBench, QIT, QAlg, and Chemlib without flattening their histories or
reducing them to a list of external links.

The repository covers several kinds of reasoning:

- mathematical proof construction and Lean 4 verification;
- natural-language physics, chemistry, and biology problem solving;
- competitive-programming solutions evaluated by an external judge;
- quantum-information and quantum-algorithm formalization;
- reusable, machine-checked mathematical chemistry;
- answer-blind agent experiments, independent review, and reproducibility;
- checksums, grading reports, manifests, and provenance for auditing results.

Each collection retains its release files and source history. Monorepo-specific
README edits only adapt clone commands, relative links, and paths to this layout;
the problem material, solutions, proof sources, and verification tools remain
with the histories they came from.

## Results at a glance

| Collection | Scope | Reported result | Main evidence |
| --- | --- | --- | --- |
| **IMO 2026** | 6 mathematics problems | **6/6 solved** by both released agent configurations | Complete Lean 4 proofs, structural validation, and external AXLE verification workflow |
| **IPhO 2026** | 3 theory problems | **30.00/30.00** in source-level grading audits for both natural-language solution sets | Natural-language answers, independent grading reports, and Lean formalizations for 41 subparts |
| **IChO 2026** | 9 theory problems, 68 numbered targets | **68/68 formalization coverage** in the complete releases | Standalone Lean projects, checksums, experiment records, and semantic-review reports |
| **IOI 2026** | 6 programming tasks | **6/6 full-score submissions** | Submission-ready C++20, annotated solutions, public-package replay, and Codeforces results |
| **PutnamBench** | 672 formalized Putnam problems | **672/672 verified**, reported joint #1 | Lean kernel checking, statement preservation, Comparator, AXLE, and an independent post-run audit |
| **IBO 2024** | 100 theory tasks, 400 statement verdicts | **100/100 tasks; 400/400 verdict agreement** | Worked solutions, official-answer mapping, reviewed-solution hashes, and offline validation |
| **QAlg + QIT** | 36 quantum-algorithm and 40 quantum-information tasks | **76/76 formalized and Lean-verified** | Original TeX, dataset records, generated Lean proofs, build projects, and review metadata |
| **Chemlib** | Mathematical chemistry library plus AFPS2017 | **Verified Lean library and 22-module AFPS2017 extension** | Pinned Lake project, source-grounded models, manifests, and verification certificates |

These rows summarize the claims and scope documented by the imported releases.
They are not directly comparable model benchmarks: the competitions use
different task formats, grading methods, toolchains, and experiment protocols.
The collection-specific grading reports are the authoritative source for the
precise meaning and limitations of each result.

## What is included

HOA is intended to preserve the work needed to understand a result, not only
the final answer. Depending on the competition, the collection includes:

1. **Inputs and task definitions** — formal statements, public problem
   packages, contestant interfaces, or pinned benchmark data.
2. **Final outputs** — Lean proofs, natural-language solutions, and C++
   submissions.
3. **Agent workflows** — plans, prompts, launchers, worker/reviewer loops,
   isolation helpers, and result-collection scripts.
4. **Verification** — pinned Lean projects, local validators, checksums,
   manifests, Comparator integration, AXLE clients, and judge evidence.
5. **Audits and provenance** — grading reports, experiment records, source
   revisions, artifact inventories, and disclosed scope limitations.

No single root build command is provided because the eight collections use
different languages, Lean versions, dependency sets, and verification models.
Each collection remains self-contained.

## The collections

### IMO — formal mathematics

`imo2026/` contains the Humanfia IMO 2026 release for all six problems. It includes
the formal problem skeletons, complete solution sets from GPT-5.6 Sol and
Kimi-K3, reusable agent plans, worker/reviewer launchers, structural validators,
and an AXLE verification client.

The project is pinned to Lean 4.31.0 and Mathlib v4.31.0. The released proof
files are designed to preserve the original theorem statements and to avoid
`sorry`, `admit`, custom axioms, and other proof escapes. The two solution sets
can be checked independently in the pinned environment.

Key paths:

- `imo2026/base/IMO2026/` — formal statements for Questions 1–6;
- `imo2026/gpt-5.6-solution/` — six GPT-5.6 Sol proof files;
- `imo2026/kimi-solution/` — six Kimi-K3 proof files;
- `imo2026/scripts/` — validation, verification, and experiment launchers;
- `imo2026/tools/lean4export/` — bundled declaration-export tooling.

### IPhO — physics reasoning and formalization

`ipho2026/` contains the theory-problem release for the 56th International Physics
Olympiad. The primary result is answer-blind natural-language problem solving:
both released solution sets answered all 23 scored theory subparts and received
30.00/30.00 in separate source-level grading audits. These are audit scores,
not official jury adjudications.

The collection also contains optional Lean 4 formalizations for all 41 modeled
subparts. The GPT formalization project uses Lean 4.32.0 with pinned Mathlib and
PhysLean dependencies; the Kimi project carries its own pinned environment.

Key paths:

- `ipho2026/NaturalLanguage/` — GPT-5.6 Sol answers and grading report;
- `ipho2026/Kimi/NaturalLanguage/` — Kimi-K3 answers and grading report;
- `ipho2026/Ipho2026Gpt56solBlind/` — GPT Lean formalizations;
- `ipho2026/Kimi/Ipho2026KimiK3Blind32/` — Kimi Lean formalizations;
- `ipho2026/scripts/run-natural-language-experiment.sh` — clean answer-blind
  experiment launcher.

### IChO — chemistry solutions, baselines, and full formalization

`icho2026/` preserves the theoretical portion of the IChO 2026 work: nine theory
problems and 68 numbered subquestions. It contains natural-language worked
solutions, answer-blind formalizations, complete formalization projects, and
native Codex `/goal` baselines for both GPT-5.6 Sol and Kimi-K3.

The headline 68/68 figures mean formalization completion under the scopes
declared by the individual releases. They do **not** mean that every answer
received full official chemistry credit. The repository keeps formal proof
acceptance, semantic review, and official-rubric answer scoring as separate
measurements so that those claims are not conflated.

Key paths:

- `icho2026/gpt-5.6-sol-full68-formalization/` — complete GPT formalization release;
- `icho2026/gpt-5.6-sol-answer-blind/` — earlier 32-target answer-blind run;
- `icho2026/kimi-k3-answer-blind/` and
  `icho2026/kimi-k3-nl-36-formalization/` — Kimi's combined 68-target coverage;
- `icho2026/gpt-5.6-sol-native-goal68/` and
  `icho2026/kimi-k3-native-goal68/` — separate native `/goal` baselines;
- `icho2026/gpt-5.6-sol-max/` and `icho2026/kimi-k3-max/` — worked solution sets.

The practical laboratory examination is outside the scope of these preserved
runs.

### IOI — competitive programming

`ioi2026/` contains six IOI 2026 tasks: Ball Machine, Monuments, Tiling Game,
Classroom Game, Magic City, and Partition. All six released C++ submissions are
reported as full-score Codeforces submissions.

This collection includes more than source files. It preserves public problem
packages, contestant interfaces, annotated explanations, per-task immutable
plans, isolated Humanize worker launchers, monitoring and collection scripts,
and a one-command public verification gate. The local gate validates the
manifest, builds every solution, replays all released Day 1 examples, and
strictly compiles the Day 2 artifacts. Hidden judge tests remain external.

Key paths:

- `ioi2026/problems/` — released Day 1 and Day 2 problem material;
- `ioi2026/submissions/` — the six judged submission files;
- `ioi2026/solutions/` — annotated C++20 solutions;
- `ioi2026/orchestration/` — plans and six-worker experiment tooling;
- `ioi2026/MANIFEST.sha256` and `ioi2026/verify.sh` — integrity and reproduction gate.

### Putnam — the complete PutnamBench campaign

`putnambench/` contains the solver, pinned statements, verification environment,
campaign controller, and evidence for the Humanfia PutnamBench result. The
release reports 672 verified proofs out of 672 formal statements and a joint #1
leaderboard result.

A candidate is counted only after passing statement-preservation checks,
forbidden-marker checks, Lean compilation, Comparator and kernel replay, AXLE,
and an independent post-hoc audit. The worker and reviewer environments are
separated, and the benchmark statements and major tool revisions are pinned.

At the PutnamBench authors' request, the full set of proof files is not included
in this Git repository. The collection instead contains the complete solving
and verification pipeline, retained audit evidence, and instructions for
checking the separately published proof preview and dataset.

Key paths:

- `putnambench/inputs/putnam_bench.jsonl` — 672 pinned formal statements;
- `putnambench/humanize/` — vendored agent and verification workflow;
- `putnambench/solve-all-putnambench.sh` — campaign controller;
- `putnambench/reproduce.sh` — integrity, bootstrap, and workspace preparation;
- `putnambench/reference/` — retained reports and audit evidence;
- `putnambench/provenance/` — source revisions and packaging notes.

### IBO — biology answers and source-grounded validation

`ibo2024/` contains the Humanfia release for all 100 theory tasks from the IBO
2024 Theoretical Exam. The result reports 100/100 completed tasks and exact
agreement with all 400 official true/false statement verdicts. The collection
includes individual worked solutions, consolidated Theory A and Theory B
volumes, the official-answer mapping, worker assignments, generation plans,
reviewed-solution hashes, and deterministic validation scripts.

The reported score is answer-key agreement, not an official Olympiad points
calculation. Practical examinations are outside the release. The official exam
PDFs are also not redistributed: source-grounded reproduction requires users to
provide the two official English PDFs locally, after which the included tools
extract and validate the relevant text without web access.

Key paths:

- `ibo2024/solutions/part-a/` and `ibo2024/solutions/part-b/` — 100 individual
  worked solutions;
- `ibo2024/theory-a-solutions.md` and `ibo2024/theory-b-solutions.md` — ordered
  consolidated volumes;
- `ibo2024/official-answers.tsv` and `ibo2024/task-map.tsv` — answer patterns
  and source-grounded task identities;
- `ibo2024/reviewed-solutions.sha256` — reviewed-corpus integrity lock;
- `ibo2024/scripts/` — deterministic builder, validator, tests, and isolated
  experiment launcher.

### QIT and QAlg — detailed quantum benchmark statements and proofs

`lean-qit-qlg/` combines two formalization datasets: 36 Quantum Algorithms
tasks and 40 Quantum Information Theory tasks. All 76 releases contain complete
Lean proofs, compile in their pinned projects, and contain no `sorry` or
`admit`. The final semantic-review pass rates reported by both datasets are
100%; those semantic reviews were automated rather than an independent human
blind audit.

This collection includes the problem material needed to inspect the
formalization boundary rather than only the final Lean theorem: original public
TeX statements, JSONL dataset records, generated Lean sources, reproducible Lake
projects, metadata, manifests, proof reports, and QIT foundation modules. QAlg
is pinned to Lean 4.31.0; QIT is pinned to Lean 4.30.0.

Key paths:

- `lean-qit-qlg/QAlg/sources/` and `lean-qit-qlg/QIT/sources/` — original
  public TeX statements;
- `lean-qit-qlg/QAlg/data/` and `lean-qit-qlg/QIT/data/` — dataset tables;
- `lean-qit-qlg/QAlg/lean/` and `lean-qit-qlg/QIT/lean/` — generated proof
  sources;
- `lean-qit-qlg/QAlg/lean-project/` and `lean-qit-qlg/QIT/lean-project/` —
  independently buildable pinned projects;
- `lean-qit-qlg/QAlg/metadata/` and `lean-qit-qlg/QIT/metadata/` — review and
  provenance records.

### Chemlib — verified mathematical chemistry

`chemlib/` is a reusable Lean 4 library for mathematical chemistry. It also
contains AFPS2017, a source-grounded formalization of selected sequence, flow,
yield, and analytical claims from the automated flow peptide synthesis work of
Mijalis et al. (2017). The AFPS extension contains 22 modules across sequence
assembly, flow accounting, observations, and scalar-composition models.

The formalization proves typed models and source-addressed arithmetic. It does
not infer molecular identity, purity, experimental success, reactor
performance, or a complete chemical mechanism unless those conclusions are
provided as explicit hypotheses. The project uses Lean 4.31.0 with pinned
Mathlib and Physlib dependencies and retains its verification certificates and
campaign metadata.

Key paths:

- `chemlib/chemlib/Chemlib/` and `chemlib/chemlib/Chemlib.lean` — general
  chemistry library;
- `chemlib/chemlib/AFPS2017/` and `chemlib/chemlib/AFPS2017.lean` — AFPS2017
  formalization;
- `chemlib/chemlib/campaign/` — verification evidence and release
  certificates;
- `chemlib/reproduce.sh` and `chemlib/REPRODUCE.md` — clean-build workflow.

## Repository layout

```text
hoa-qed/
├── README.md       # This overview
├── imo2026/        # Formal mathematics: six Lean-verified problems
├── ipho2026/       # Physics: natural-language solutions and Lean proofs
├── icho2026/       # Chemistry: solutions, baselines, and formalizations
├── ioi2026/        # Programming: problems, C++ solutions, and harnesses
├── putnambench/    # PutnamBench: 672-problem solver and verification stack
├── ibo2024/        # Biology: 100 tasks and source-grounded validation
├── lean-qit-qlg/   # QIT + QAlg: 76 detailed statements and Lean proofs
└── chemlib/        # Reusable chemistry library and AFPS2017 formalization
```

All collection directories use the canonical lowercase names established by
this monorepo. Inside every directory, the release layout remains self-contained,
and build instructions and downstream dependency declarations use these paths.

## Quick start

Clone the combined repository:

```bash
git clone https://github.com/humanfia/hoa-qed.git
cd hoa-qed
```

The repository is immediately browsable without additional setup. To run the
verification workflows, choose the collection that matches your environment.

### Verify the IOI public bundle

Requires Bash, Python 3, `sha256sum`, and a C++20-capable compiler:

```bash
(cd ioi2026 && ./verify.sh)
```

### Check the Putnam package integrity

This check does not download dependencies or make model calls:

```bash
(cd putnambench && ./reproduce.sh check)
```

### Check the IChO release checksums

```bash
for run in \
  gpt-5.6-sol-answer-blind \
  kimi-k3-answer-blind \
  kimi-k3-nl-36-formalization \
  gpt-5.6-sol-native-goal68 \
  kimi-k3-native-goal68; do
  (cd "icho2026/$run" && sha256sum -c CHECKSUMS.sha256)
done
```

### Build the IPhO Lean formalizations

Install Elan first; the project selects its pinned toolchain automatically:

```bash
(
  cd ipho2026
  lake exe cache get
  lake build
)
```

### Check an IMO proof

Install Elan, fetch the pinned Mathlib cache, and run Lean from the base
project:

```bash
(
  cd imo2026/base
  lake exe cache get
  lake env lean ../gpt-5.6-solution/IMO2026Q1.lean
  lake env lean ../kimi-solution/IMO2026Q1.lean
)
```

### Validate the published IBO collection

The committed collection can be checked without model calls. Full
source-grounded regeneration additionally requires the two official PDFs at the
paths documented in `ibo2024/README.md`.

```bash
(
  cd ibo2024
  sha256sum --check reviewed-solutions.sha256
  python3 scripts/build.py --check
)
```

### Verify all QIT and QAlg proofs

Install Elan first. `--with-cache` downloads the appropriate precompiled
Mathlib cache for each pinned project:

```bash
(cd lean-qit-qlg && ./scripts/verify.sh --with-cache)
```

### Build Chemlib and AFPS2017

```bash
(cd chemlib && ./reproduce.sh)
```

The full agent experiments require additional model credentials, API quota,
Linux isolation support, and substantially more compute. Review the relevant
collection's own README before launching them; several scripts intentionally
require an explicit start flag to prevent accidental quota consumption.

## Verification philosophy

The collections use different verification mechanisms, but they share several
principles:

- **Preserve the task.** Formal-statement validators reject modified or weakened
  theorem signatures.
- **Separate generation from judgment.** Worker outputs are checked by tools,
  reviewers, external judges, or post-run audits that do not rely on the
  generating model's self-assessment.
- **Pin the environment.** Lean versions, Mathlib revisions, problem inputs,
  tool revisions, and packaged files are pinned or checksummed where possible.
- **Retain failures and limitations.** Baseline rejections, conditional results,
  grading distinctions, and incomplete public artifacts are disclosed rather
  than silently folded into headline numbers.
- **Make evidence inspectable.** Reports, manifests, scripts, and provenance are
  stored beside the outputs they support.

Formal verification proves that a theorem follows from its encoded statement;
it does not by itself prove that the encoding perfectly captures the original
natural-language question. For that reason, several releases combine Lean
checking with statement audits, semantic review, or official-rubric grading.

## Provenance and source statements

The collection histories are preserved in this monorepo. Use path-limited Git
logs to inspect how each release was assembled and updated:

```bash
git log -- imo2026/
git log -- ipho2026/
git log -- icho2026/
git log -- ioi2026/
git log -- putnambench/
git log -- ibo2024/
git log -- lean-qit-qlg/
git log -- chemlib/
```

The detailed problem and statement sources have different redistribution
boundaries:

- `imo2026/base/IMO2026/` contains the formal Lean statements derived from the
  AxiomMath IMO 2026 release.
- `ioi2026/problems/` contains the released official IOI problem packages and
  public examples; hidden judge data is not included.
- `putnambench/inputs/putnam_bench.jsonl` pins all 672 PutnamBench formal
  statements.
- `lean-qit-qlg/QAlg/sources/` and `lean-qit-qlg/QIT/sources/` preserve the
  original public TeX statements alongside their generated formalizations.
- IBO worked solutions, task identities, and official-answer patterns are
  included, but the official exam PDFs are not redistributed. Full validation
  requires locally supplied copies as described in `ibo2024/README.md`.
- IPhO and IChO source, grading, and formalization boundaries are documented in
  their collection READMEs and reports.

Third-party problem material remains under its owners' terms. [NOTICE](NOTICE)
records the source and licensing boundary for each included collection.

## Citation

[CITATION.cff](CITATION.cff) provides the repository title, authorship,
keywords, project URL, and preferred citation metadata.

## License

Code and Lean proofs are licensed under [Apache-2.0](LICENSE).
Natural-language solutions, write-ups, and grading reports are licensed under
[CC-BY-4.0](LICENSE-CC-BY-4.0). Third-party problem statements, benchmark
inputs, official packages, and vendored tools retain their original terms as
listed in [NOTICE](NOTICE).

For exact experimental parameters, detailed grading, and collection-specific
limitations, continue from the README inside the relevant top-level directory.
