#!/usr/bin/env bash

set -euo pipefail
IFS=$'\n\t'

usage() {
  printf '%s\n' \
    'Usage:' \
    '  scripts/run-natural-language-experiment.sh PROBLEM INPUT_DIR RUN_DIR [BUILDER] [REVIEWER]' \
    '' \
    'Arguments:' \
    '  PROBLEM    T1, T2, or T3.' \
    '  INPUT_DIR  Directory containing only that problem statement and its figures.' \
    '  RUN_DIR    New or empty directory outside this release checkout.' \
    '  BUILDER    Optional Humanize agent (default: codex/gpt-5.6-sol:max).' \
    '  REVIEWER   Optional Humanize agent (default: same as BUILDER).' \
    '' \
    'Example:' \
    '  scripts/run-natural-language-experiment.sh T1 /path/to/T1-input ../ipho2026-runs/T1'
}

if [[ "${1:-}" == '--help' || "${1:-}" == '-h' ]]; then
  usage
  exit 0
fi

if (( $# < 3 || $# > 5 )); then
  usage >&2
  exit 2
fi

problem=$1
input_dir=$2
run_dir=$3
builder=${4:-codex/gpt-5.6-sol:max}
reviewer=${5:-$builder}

case "$problem" in
  T1|T2|T3) ;;
  *)
    printf 'error: PROBLEM must be T1, T2, or T3; got %s\n' "$problem" >&2
    exit 2
    ;;
esac

for command_name in git hmz; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    printf 'error: required command not found: %s\n' "$command_name" >&2
    exit 127
  fi
done

if [[ ! -d "$input_dir" ]]; then
  printf 'error: input directory does not exist: %s\n' "$input_dir" >&2
  exit 2
fi

if [[ -d "$input_dir/.git" ]]; then
  printf 'error: INPUT_DIR must contain problem materials, not a Git repository\n' >&2
  exit 2
fi

if [[ -z "$(find "$input_dir" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
  printf 'error: input directory is empty: %s\n' "$input_dir" >&2
  exit 2
fi

linked_input=$(find "$input_dir" -type l -print -quit)
if [[ -n "$linked_input" ]]; then
  printf 'error: symbolic links are not allowed in INPUT_DIR: %s\n' "$linked_input" >&2
  exit 2
fi

forbidden_input=$(find "$input_dir" -type f \( \
  -iname '*answer*' -o \
  -iname '*grading*' -o \
  -iname '*marking*' -o \
  -iname '*rubric*' -o \
  -iname '*solution*' \
  \) -print -quit)
if [[ -n "$forbidden_input" ]]; then
  printf 'error: possible answer material found in INPUT_DIR: %s\n' "$forbidden_input" >&2
  exit 2
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
release_root=$(CDPATH= cd -- "$script_dir/.." && pwd -P)
input_root=$(CDPATH= cd -- "$input_dir" && pwd -P)

if [[ -e "$run_dir" && ! -d "$run_dir" ]]; then
  printf 'error: RUN_DIR exists and is not a directory: %s\n' "$run_dir" >&2
  exit 2
fi

mkdir -p -- "$run_dir"
run_root=$(CDPATH= cd -- "$run_dir" && pwd -P)

case "$run_root/" in
  "$release_root/"*)
    printf 'error: RUN_DIR must be outside the release checkout to prevent result leakage\n' >&2
    exit 2
    ;;
esac

case "$run_root/" in
  "$input_root/"*)
    printf 'error: RUN_DIR must not be inside INPUT_DIR\n' >&2
    exit 2
    ;;
esac

if [[ -n "$(find "$run_root" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
  printf 'error: RUN_DIR must be new or empty: %s\n' "$run_root" >&2
  exit 2
fi

cp -a -- "$input_root/." "$run_root/"
mkdir -p -- "$run_root/docs"

cat >"$run_root/docs/plan.md" <<EOF
# IPhO 2026 $problem answer-blind natural-language solution

## Objective

Solve every part of the supplied $problem statement and write the final,
self-contained contest solution to \`solution.md\`.

## Acceptance criteria

1. Cover every subpart in the supplied statement.
2. Show rigorous derivations, units, numerical work, and requested figures.
3. Include independent dimensional, limiting-case, and numerical checks where applicable.
4. Make the final answers easy to locate and match to the statement's numbering.
5. Do not use official solutions, marking schemes, previous submissions, or web sources.

## Isolation rules

Use only files in this workspace. Do not read outside it. Do not use the network.
Do not weaken these rules or modify this plan.
EOF

git -C "$run_root" init --initial-branch=main --quiet
git -C "$run_root" config user.name 'IPhO Humanize Experiment'
git -C "$run_root" config user.email 'ipho-humanize@localhost'
git -C "$run_root" add -- .
git -C "$run_root" commit --quiet -m "Seed answer-blind IPhO 2026 $problem workspace"

export HUMANIZE_SENTRY=${HUMANIZE_SENTRY:-off}

printf 'Starting Humanize RLCR for %s in %s\n' "$problem" "$run_root"
(
  cd -- "$run_root"
  hmz exec -f official/humanize1:rlcr \
    -a "$builder" \
    -a "$reviewer" \
    "IPhO 2026 $problem answer-blind natural-language experiment"
)

if [[ ! -s "$run_root/solution.md" ]]; then
  printf 'error: Humanize exited without producing solution.md\n' >&2
  exit 1
fi

printf 'Experiment complete: %s\n' "$run_root/solution.md"
