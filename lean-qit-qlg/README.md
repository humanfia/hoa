# Lean QIT + QAlg formalization datasets

本仓库镜像并整合了 Humanfia Lab 发布的 QAlg（量子算法）与 QIT（量子信息论）证明数据，同时保留可复现的 Lean 4 编译环境。数据、TeX 原题、生成的 Lean 形式化与证明、审查元数据和证明报告均完整保留。

This repository mirrors the Humanfia Lab QAlg and QIT proof datasets and includes the pinned Lean 4 projects needed to kernel-check all generated formalizations and proofs.

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
