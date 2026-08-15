#!/usr/bin/env bash

set -euo pipefail

script_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$script_root/common.sh"

[[ $# -le 1 ]] || { printf 'usage: %s [RUN_ROOT]\n' "$0" >&2; exit 2; }
run_root="$(resolve_run_root "${1:-}")" || {
  printf '%s\n' 'no valid run found; pass RUN_ROOT or create runs/latest' >&2
  exit 1
}
results_root="$run_root/results"
[[ ! -e "$results_root" ]] || {
  printf 'refusing to overwrite existing results: %s\n' "$results_root" >&2
  exit 1
}

for task in "${ioi_tasks[@]}"; do
  worker="$run_root/workers/$task"
  status_path="$worker/runtime/status.json"
  state="$(python3 - "$status_path" <<'PY'
import json
import sys
try:
    print(json.load(open(sys.argv[1], encoding="utf-8")).get("state", "missing"))
except (FileNotFoundError, json.JSONDecodeError):
    print("missing")
PY
)"
  [[ "$state" == complete ]] || {
    printf 'worker is not complete: %s (state=%s)\n' "$task" "$state" >&2
    exit 1
  }
  solution="$worker/$(task_solution_path "$task")"
  [[ -f "$solution" ]] || { printf 'missing solution: %s\n' "$solution" >&2; exit 1; }
done

mkdir -p -- "$results_root"
for task in "${ioi_tasks[@]}"; do
  cp -a -- "$run_root/workers/$task/$(task_solution_path "$task")" \
    "$results_root/$task.cpp"
done
(
  cd -- "$results_root"
  sha256sum ./*.cpp >SHA256SUMS
)
printf 'collected six solutions: %s\n' "$results_root"
