#!/usr/bin/env bash

set -euo pipefail
IFS=$'\n\t'

script_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$script_root/common.sh"

usage() {
  cat <<'EOF'
Usage: launch-six.sh --dry-run | --prepare-only | --start [options]

Modes:
  --dry-run       Check all prerequisites; do not create or launch a run.
  --prepare-only  Create six clean worker repositories; do not launch Codex.
  --start         Create and launch all six Humanize workers.

Options:
  --wait                    Wait for all launched workers to exit.
  --run-id ID               Use a specific safe run identifier.
  --model MODEL             Worker and reviewer model (gpt-5.6-sol).
  --effort LEVEL            max, xhigh, high, medium, or low (max).
  --max N                   Maximum Humanize rounds (42).
  --codex-timeout SECONDS   Per-review timeout (5400).
  --no-isolation            Disable the Linux Landlock read boundary.
  -h, --help                Show this help.
EOF
}

mode=
wait_for_workers=false
isolation=true
run_id=
model="${IOI_HUMANIZE_MODEL:-gpt-5.6-sol}"
effort="${IOI_HUMANIZE_EFFORT:-max}"
max_iterations="${IOI_HUMANIZE_MAX:-42}"
codex_timeout="${IOI_HUMANIZE_CODEX_TIMEOUT:-5400}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --dry-run|--prepare-only|--start)
      [[ -z "$mode" ]] || { printf 'choose exactly one mode\n' >&2; exit 2; }
      mode=${1#--}
      shift
      ;;
    --wait) wait_for_workers=true; shift ;;
    --no-isolation) isolation=false; shift ;;
    --run-id|--model|--effort|--max|--codex-timeout)
      [[ -n "${2:-}" ]] || { printf '%s requires a value\n' "$1" >&2; exit 2; }
      case "$1" in
        --run-id) run_id=$2 ;;
        --model) model=$2 ;;
        --effort) effort=$2 ;;
        --max) max_iterations=$2 ;;
        --codex-timeout) codex_timeout=$2 ;;
      esac
      shift 2
      ;;
    -h|--help) usage; exit 0 ;;
    *) printf 'unknown option: %s\n' "$1" >&2; usage >&2; exit 2 ;;
  esac
done

[[ -n "$mode" ]] || { usage >&2; exit 2; }
[[ "$wait_for_workers" == false || "$mode" == start ]] || {
  printf '%s\n' '--wait requires --start' >&2
  exit 2
}
[[ "$effort" =~ ^(max|xhigh|high|medium|low)$ ]] || {
  printf 'invalid effort: %s\n' "$effort" >&2
  exit 2
}
[[ "$max_iterations" =~ ^[1-9][0-9]*$ ]] || {
  printf 'invalid --max value: %s\n' "$max_iterations" >&2
  exit 2
}
[[ "$codex_timeout" =~ ^[1-9][0-9]*$ ]] || {
  printf 'invalid --codex-timeout value: %s\n' "$codex_timeout" >&2
  exit 2
}

for command_name in bash codex git jq python3 sha256sum setsid; do
  command -v "$command_name" >/dev/null 2>&1 || {
    printf 'missing prerequisite: %s\n' "$command_name" >&2
    exit 1
  }
done
if [[ "$isolation" == true ]]; then
  command -v cc >/dev/null 2>&1 || {
    printf '%s\n' 'missing prerequisite for isolation: cc' >&2
    exit 1
  }
fi

humanize_root="$(find_humanize_root)" || {
  printf '%s\n' 'Humanize runtime not found; set HUMANIZE_ROOT_OVERRIDE' >&2
  exit 1
}
auth_file="$(find_auth_file)" || {
  printf '%s\n' 'Codex auth file not found; set CODEX_AUTH_FILE_OVERRIDE' >&2
  exit 1
}
codex_real="$(readlink -f -- "$(command -v codex)")"
[[ -x "$codex_real" ]] || { printf 'invalid Codex executable: %s\n' "$codex_real" >&2; exit 1; }
codex features list 2>/dev/null | grep -Eq '^(hooks|codex_hooks)[[:space:]]' || {
  printf '%s\n' 'this Codex CLI does not expose native hooks support' >&2
  exit 1
}

for task in "${ioi_tasks[@]}"; do
  [[ -f "$orchestration_root/plans/$task.md" ]] || {
    printf 'missing plan for %s\n' "$task" >&2
    exit 1
  }
  [[ -d "$(task_problem_source "$task")" ]] || {
    printf 'missing problem material for %s\n' "$task" >&2
    exit 1
  }
done

printf 'model:             %s:%s\n' "$model" "$effort"
printf 'Humanize runtime:  %s\n' "$humanize_root"
printf 'Codex executable:  %s\n' "$codex_real"
printf 'filesystem guard:  %s\n' "$isolation"
printf 'worker count:      %s\n' "${#ioi_tasks[@]}"

if [[ "$mode" == dry-run ]]; then
  printf '%s\n' 'DRY RUN PASS: six-worker launch prerequisites are ready'
  exit 0
fi

if [[ -z "$run_id" ]]; then
  run_id="$(date -u +%Y%m%dT%H%M%SZ)-$$"
fi
[[ "$run_id" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]] || {
  printf 'unsafe run id: %s\n' "$run_id" >&2
  exit 2
}

runs_root="$bundle_root/runs"
run_root="$runs_root/$run_id"
[[ ! -e "$run_root" ]] || { printf 'run already exists: %s\n' "$run_root" >&2; exit 1; }
mkdir -p -- "$run_root/workers" "$run_root/runtime/pids"

landlock_binary=
if [[ "$isolation" == true ]]; then
  landlock_binary="$run_root/runtime/landlock-exec"
  cc -std=c11 -O2 -Wall -Wextra -Werror \
    "$orchestration_root/landlock_exec.c" -o "$landlock_binary"
  "$landlock_binary" --ro /usr --ro /etc --rw /dev --ro /proc --ro /sys \
    --rw /run -- /usr/bin/true
fi

python3 - "$run_root/run.json" "$run_id" "$model" "$effort" \
  "$max_iterations" "$codex_timeout" "$isolation" "$humanize_root" \
  "$auth_file" "$codex_real" "$landlock_binary" <<'PY'
import datetime
import json
import pathlib
import sys

(path, run_id, model, effort, maximum, timeout, isolation, humanize,
 auth, codex, landlock) = sys.argv[1:]
payload = {
    "run_id": run_id,
    "created_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "model": model,
    "effort": effort,
    "max_iterations": int(maximum),
    "codex_timeout": int(timeout),
    "isolation": isolation == "true",
    "humanize_root": humanize,
    "auth_file": auth,
    "codex_real": codex,
    "landlock_binary": landlock,
}
pathlib.Path(path).write_text(json.dumps(payload, indent=2) + "\n")
PY

for task in "${ioi_tasks[@]}"; do
  worker="$run_root/workers/$task"
  problem_target="$worker/$(task_problem_directory "$task")"
  mkdir -p -- "$problem_target"
  cp -a -- "$(task_problem_source "$task")/." "$problem_target/"
  cp -a -- "$orchestration_root/plans/$task.md" "$worker/plan.md"
  cp -a -- "$orchestration_root/worker-AGENTS.md" "$worker/AGENTS.md"
  cp -a -- "$orchestration_root/worker.gitignore" "$worker/.gitignore"
  git -C "$worker" init --initial-branch=main --quiet
  git -C "$worker" config user.name 'IOI Humanize Reproducer'
  git -C "$worker" config user.email 'ioi-humanize@localhost'
  git -C "$worker" add -- .
  git -C "$worker" commit --quiet -m "Seed $task from official problem material"
  [[ -z "$(git -C "$worker" status --porcelain=v1 --untracked-files=all)" ]] || {
    printf 'prepared worker is dirty: %s\n' "$worker" >&2
    exit 1
  }
done

mkdir -p -- "$runs_root"
if [[ -L "$runs_root/latest" ]]; then
  unlink -- "$runs_root/latest"
elif [[ -e "$runs_root/latest" ]]; then
  printf 'refusing to replace non-symlink: %s\n' "$runs_root/latest" >&2
  exit 1
fi
ln -s -- "$run_id" "$runs_root/latest"

printf 'prepared run: %s\n' "$run_root"
if [[ "$mode" == prepare-only ]]; then
  printf 'start it with: %s %q\n' "$orchestration_root/resume-six.sh" "$run_root"
  exit 0
fi

printf '%s\n' 'Starting six detached max-effort Humanize RLCR workers.'
printf '%s\n' 'This can consume substantial model quota.'
pids=()
for task in "${ioi_tasks[@]}"; do
  setsid bash "$orchestration_root/run-worker.sh" "$run_root" "$task" \
    >"$run_root/runtime/$task.launch.log" 2>&1 < /dev/null &
  pid=$!
  pids+=("$pid")
  printf '%s\n' "$pid" >"$run_root/runtime/pids/$task.pid"
  printf 'launched %-12s pid=%s\n' "$task" "$pid"
done

if [[ "$wait_for_workers" == true ]]; then
  failures=0
  for pid in "${pids[@]}"; do
    if ! wait "$pid"; then
      failures=$((failures + 1))
    fi
  done
  "$orchestration_root/monitor.sh" "$run_root"
  printf 'all workers exited; failures=%s\n' "$failures"
  exit "$failures"
fi

printf 'monitor with: %s %q\n' "$orchestration_root/monitor.sh" "$run_root"
