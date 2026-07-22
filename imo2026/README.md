# IMO 2026 Lean Formalizations

Lean 4 formalizations of the six IMO 2026 problems, together with two sets of
machine-generated proof solutions and the scripts used to validate and
reproduce the experiments.

The project is pinned to **Lean 4.31.0** and **Mathlib v4.31.0**.

## Repository layout

| Path | Description |
| --- | --- |
| `base/IMO2026/Q1` … `Q6` | Public Lean problem skeletons. Their proof bodies contain `sorry` intentionally. |
| `gpt-5.6-solution/` | Complete solution files produced by GPT-5.6. |
| `kimi-solution/` | Complete solution files produced by Kimi. |
| `base/formalization.yaml` | Formalization metadata, theorem inventory, and fidelity notes. |
| `scripts/validate-imo2026-output.py` | Local structural validator for candidate solutions. |
| `scripts/verify-imo2026-axle.py` | Remote proof verification through the AXLE API. |
| `scripts/run-imo2026.sh` | GPT-5.6 worker/reviewer experiment harness. |
| `scripts/run-imo2026-kimi.sh` | Kimi compatibility wrapper and experiment entry point. |
| `comparator-smoke/` | Minimal project for testing a Comparator installation. |
| `tools/lean4export/` | Bundled Lean declaration exporter source. |

## Quick start

### Prerequisites

- Git
- [Elan](https://github.com/leanprover/elan), which provides Lean and Lake
- Python 3 for the validation and AXLE scripts
- A C/C++ build toolchain required by Lean dependencies
- Internet access during the first Mathlib setup

### Clone the repository

```bash
git clone https://github.com/humanfia/imo-2026-lean-solutions.git
cd imo-2026-lean-solutions
```

### Install the Lean dependencies

From the repository root:

```bash
(
  cd base
  lake update
  lake exe cache get
  lake build
)
```

The `lean-toolchain` file makes Elan select Lean 4.31.0 automatically. The
Mathlib cache step avoids compiling all of Mathlib from source.

### Check one solution

Run Lean from the `base` project so it uses the pinned Mathlib environment:

```bash
(cd base && lake env lean ../gpt-5.6-solution/IMO2026Q1.lean)
```

To check the corresponding Kimi solution:

```bash
(cd base && lake env lean ../kimi-solution/IMO2026Q1.lean)
```

Lean normally prints nothing when a file succeeds. A compilation error causes
a non-zero exit status.

### Check every included solution

```bash
cd base

for solution_dir in ../gpt-5.6-solution ../kimi-solution; do
  for solution in "$solution_dir"/*.lean; do
    echo "Checking $solution"
    lake env lean "$solution"
  done
done
```

`lake build` alone does not compile the files in the two solution directories,
so use the explicit `lake env lean` commands above.

## Validate a candidate solution

The local validator checks that a candidate:

- preserves the original definitions, theorem signatures, theorem order, and
  protected docstrings;
- contains none of `sorry`, `admit`, `axiom`, or `native_decide`;
- retains the required namespace terminator for Q3 and Q4.

It is a structural check, not a replacement for Lean type-checking.

### Validate one file

Run this command from the repository root:

```bash
python3 scripts/validate-imo2026-output.py \
  --problem imo2026_q1 \
  --original base/IMO2026/Q1/problem.lean \
  --candidate gpt-5.6-solution/IMO2026Q1.lean
```

### Validate all included files

```bash
for solution_dir in gpt-5.6-solution kimi-solution; do
  for question in 1 2 3 4 5 6; do
    python3 scripts/validate-imo2026-output.py \
      --problem "imo2026_q${question}" \
      --original "base/IMO2026/Q${question}/problem.lean" \
      --candidate "${solution_dir}/IMO2026Q${question}.lean"
  done
done
```

## Work on your own proof

Copy a problem skeleton, replace its proof placeholders, and keep the original
declarations and theorem headers unchanged:

```bash
cp base/IMO2026/Q1/problem.lean /tmp/IMO2026Q1.lean
${EDITOR:-vi} /tmp/IMO2026Q1.lean
```

Then run both local checks:

```bash
python3 scripts/validate-imo2026-output.py \
  --problem imo2026_q1 \
  --original base/IMO2026/Q1/problem.lean \
  --candidate /tmp/IMO2026Q1.lean

(cd base && lake env lean /tmp/IMO2026Q1.lean)
```

Change `q1`, `Q1`, and `IMO2026Q1.lean` consistently for another problem.

## Verify with AXLE

The AXLE verifier sends the original statement and candidate proof to the
configured AXLE verification endpoint and writes a JSON report.

```bash
python3 scripts/verify-imo2026-axle.py \
  --problem imo2026_q1 \
  --original base/IMO2026/Q1/problem.lean \
  --candidate gpt-5.6-solution/IMO2026Q1.lean \
  --output reports/gpt-5.6-q1.json
```

This step requires outbound HTTPS access. The defaults are a 900-second request
timeout and four retries. Exit status `0` means AXLE returned `okay: true`, `1`
means the proof was rejected, and `2` means verification or input handling
failed.

## Comparator tooling

`Comparator` and `Landrun` binaries are not included in this repository. If you
already have them, first build the bundled `lean4export` binary:

```bash
(cd tools/lean4export && lake build)
```

Then test the three tools with the smoke project:

```bash
COMPARATOR_BIN=/path/to/comparator \
LEAN4EXPORT_BIN="$PWD/tools/lean4export/.lake/build/bin/lean4export" \
LANDRUN_BIN=/path/to/landrun \
bash comparator-smoke/tools/check-with-comparator.sh
```

The smoke test uses `comparator-smoke/comparator.json` and should accept the
proof in `comparator-smoke/Solution.lean` against the challenge declaration.

## Reproduce the model experiments

The experiment harness is separate from ordinary proof checking. It was built
for a pre-provisioned Linux environment and is **not** a portable one-command
runner for macOS or a fresh Linux installation.

The harness expects:

- Linux utilities including `proot`, `setpriv`, `getent`, `flock`, `jq`, `rg`,
  a C compiler, and GNU `timeout`;
- a working Codex binary and Codex configuration/authentication directory;
- a populated `base/.lake/packages` Mathlib checkout;
- an external Comparator binary and Landrun binary;
- a runtime template containing Lean, Mathlib, Comparator, Landrun, and
  `lean4export`;
- `/mathlib-packages` linked to the pinned package cache;
- isolated users named `humanize-imo-q1` through `humanize-imo-q6`, unless
  `HUMANIZE_USER_PREFIX` is changed.

The default runtime template layout is:

```text
/tmp/imo2026-humanize-runtime-v431/
├── root/.elan/bin/lake
├── mathlib-packages/mathlib/
├── checker-tools/lean4export
└── comparator-tools/
    ├── comparator
    └── landrun
```

The checked-in scripts do not have executable file modes, while the harness
requires its Comparator wrapper to be executable. Prepare them once with:

```bash
chmod +x scripts/*.sh scripts/*.py comparator-smoke/tools/*.sh
```

### GPT-5.6 run

After provisioning the environment, run one problem first:

```bash
BASE_CODEX_HOME=/path/to/codex-home \
CODEX_BIN=/path/to/codex \
LOCAL_RUNTIME_TEMPLATE=/tmp/imo2026-humanize-runtime-v431 \
bash scripts/run-imo2026.sh \
  --problem imo2026_q1 \
  --jobs 1 \
  --fallback-jobs 1 \
  --probe-count 1
```

This runner is fixed to the `gpt-5.6-sol` model and rejects another
`CODEX_MODEL` value.

### Kimi run

The Kimi wrapper starts a local compatibility proxy and then launches the same
worker/reviewer workflow:

```bash
KIMI_CODEX_HOME=/path/to/kimi-codex-home \
KIMI_KEY_FILE=/path/to/kimi-api-key \
KIMI_CODEX_BIN=/path/to/compatible/codex \
LOCAL_RUNTIME_TEMPLATE=/tmp/imo2026-humanize-runtime-v431 \
bash scripts/run-imo2026-kimi.sh \
  --problem imo2026_q1 \
  --jobs 1 \
  --fallback-jobs 1 \
  --probe-count 1
```

Use `bash scripts/run-imo2026.sh --help` for the GPT runner options. To inspect
the shared Kimi options without first configuring Kimi credentials, run
`bash scripts/run-imo2026-kimi-core.sh --help`.

Useful options include:

- `--problem imo2026_qN` — select a problem; repeat to select several;
- `--max-turns N` — set the worker/reviewer turn limit;
- `--prepare-only` — create and audit isolated workspaces without starting a
  model;
- `--resume-prepared`, `--resume-worker-only`, and `--resume-review-only` —
  continue an existing run;
- `--run-id ID` and `--out-root PATH` — control result locations.

Even `--dry-run` performs the harness prerequisite checks.

## Experiment outputs

Runs are written under `runs/<RUN_ID>/`. Important artifacts include:

- `RUN.md` — run configuration and provenance;
- `jobs/` — per-problem status, hashes, and local-check logs;
- `metrics.tsv` — final per-job status and timing;
- `codex-sessions.tsv` — worker/reviewer session records;
- `workspaces` and `agent-homes` — links to the isolated runtime directories;
- rate-limit and transport-failure logs when those conditions occur.

Workers have network access blocked. Reviewers receive network access only for
the prompted AXLE verification step. Existing solution directories are not
mounted into either model namespace.
