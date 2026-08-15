# Six-worker Humanize reproduction

This launcher reconstructs the process that produced the six IOI 2026
artifacts. It creates six independent Git repositories from the bundled
official problems, copies the corresponding immutable Humanize plans, and
starts six concurrent Codex workers. Every worker runs its own native-hook
Humanize RLCR implementation/review loop.

The worker seeds do **not** contain `../submissions/`. On Linux, the default
Landlock boundary also prevents a worker and its nested reviewers from reading
the bundle, sibling workers, or other workspace repositories.

## Prerequisites

- Linux with Landlock support (or explicitly use `--no-isolation`)
- authenticated Codex CLI with native hooks support
- Bash, Python 3, Git, jq, a C compiler, and the task toolchain
- the Humanize skill installed locally

Six `gpt-5.6-sol:max` runs can consume substantial quota. Nothing starts unless
`--start` is supplied.

## Commands

```sh
# Validate configuration without writing or launching anything
./orchestration/launch-six.sh --dry-run

# Prepare and launch six detached workers
./orchestration/launch-six.sh --start

# Prepare, launch, and wait for all workers
./orchestration/launch-six.sh --start --wait

# Inspect the latest run
./orchestration/monitor.sh

# Restart workers that are stopped, failed, or not yet started
./orchestration/resume-six.sh

# Copy six completed artifacts into that run's results directory
./orchestration/collect-results.sh
```

Every command accepts an explicit run directory where applicable. The launcher
prints the created directory and updates `runs/latest` to point to it.

Configuration can be overridden with `--model`, `--effort`, `--max`, and
`--codex-timeout`. `HUMANIZE_ROOT_OVERRIDE` and `CODEX_AUTH_FILE_OVERRIDE`
select non-default installations without copying credentials into this bundle.

## Output layout

```text
runs/<run-id>/
├── run.json
├── runtime/
├── workers/
│   ├── ballmachine/
│   ├── monuments/
│   ├── tiling/
│   ├── classroom/
│   ├── magiccity/
│   └── partition/
└── results/                 # created by collect-results.sh
```

Each worker retains its commits, `.humanize/` review ledger, JSONL Codex event
stream, final message, validation log, and status JSON.
