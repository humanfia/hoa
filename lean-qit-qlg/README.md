# Lean QIT + QAlg formalization datasets

This repository mirrors and combines the Humanfia Lab QAlg (Quantum Algorithms) and QIT (Quantum Information Theory) proof datasets with reproducible Lean 4 build environments. It preserves the dataset tables, original TeX statements, generated Lean formalizations and proofs, review metadata, and proof reports.

> [!IMPORTANT]
> **100% final semantic-review pass rate and verified proof completion — 76/76 tasks across QAlg and QIT.**
>
> All 36 QAlg tasks and all 40 QIT tasks produced compilable formalizations, passed final semantic review, contain complete Lean proofs with no `sorry` or `admit`, and are included in successful full `lake build`s.

## Accuracy highlights

| Benchmark | Compilable formalizations | Final semantic review | Proof verification | `sorry`/`admit`-free |
|---|---:|---:|---:|---:|
| [QAlg](https://huggingface.co/datasets/humanfia-lab/QAlg#final-results) | 36/36 (100%) | 36/36 (100%) | 36/36 Lean-kernel accepted (100%) | 36/36 (100%) |
| [QIT](https://huggingface.co/datasets/humanfia-lab/QIT#final-results) | 40/40 (100%) | 40/40 (100%) | 40/40 Formal Proof Review and end-to-end passed (100%) | 40/40 (100%) |

These are the final post-repair results reported in the linked dataset cards. The semantic scores come from automated review rather than an independent external human blind audit; compilation, placeholder-free status, and the full `lake build` provide separate mechanical checks.

## Contents

| Directory | Dataset | Tasks | Lean toolchain | Included build environment |
|---|---|---:|---|---|
| `QAlg/` | [humanfia-lab/QAlg](https://huggingface.co/datasets/humanfia-lab/QAlg) | 36 | Lean 4.31.0 | `QAlgBench`, generated `QAlgFormalized` proofs, pinned Mathlib and CSLib |
| `QIT/` | [humanfia-lab/QIT](https://huggingface.co/datasets/humanfia-lab/QIT) | 40 | Lean 4.30.0 | `QITBench`, generated `QITFormalized` proofs, two generated `QITFoundations` modules, pinned Mathlib |

Each dataset directory contains:

- `data/*.jsonl`: the Hugging Face dataset table;
- `lean/`: standalone generated proof sources;
- `lean-project/`: the reproducible Lake project used for verification;
- `sources/`: the original public TeX statements;
- `metadata/`: manifests, review gates, and aggregate metrics;
- `solution-reports/`: proof reports when available;
- `foundations/`: generated QIT foundation sources, where applicable.

## Verify all proofs

Install [elan](https://github.com/leanprover/elan), then run:

```bash
./scripts/verify.sh --with-cache
```

The optional `--with-cache` flag downloads Mathlib's precompiled cache first. Without it, Lake may compile dependencies from source:

```bash
./scripts/verify.sh
```

The `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` files in each project pin the compiler and dependency revisions. The root verification script enters each project separately, so elan automatically selects the correct Lean version. Local `.lake/` build products are intentionally excluded from Git.

To verify only one dataset:

```bash
cd QAlg/lean-project && lake exe cache get && lake build
cd QIT/lean-project && lake exe cache get && lake build
```

The Lake defaults in this mirror include the generated proof libraries, not only the benchmark base libraries. Therefore `lake build` checks all 36 QAlg proofs and all 40 QIT proofs, including the two generated QIT foundation modules.

## Snapshot provenance

- QAlg dataset snapshot: `447a94117eb5e35ccdc4cb415d1bf91451002525`
- QIT dataset snapshot: `5c9eeef6ad82b1383b70baa65e3938485b64e2f2`
- QAlg benchmark source commit: `7f964d2b34a63c8ea7cae87937ede7740abe7dda`
- QIT benchmark source commit: `e4f0230e14c35da9c658b58c8663b3e6825e6663`

Dataset-specific descriptions, generation methodology, review caveats, and detailed provenance remain in [`QAlg/README.md`](QAlg/README.md) and [`QIT/README.md`](QIT/README.md).

## License

Apache License 2.0. See `LICENSE` and the dataset-local license files.
