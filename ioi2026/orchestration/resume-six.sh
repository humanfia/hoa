#!/usr/bin/env bash

set -euo pipefail

script_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$script_root/common.sh"

[[ $# -le 1 ]] || { printf 'usage: %s [RUN_ROOT]\n' "$0" >&2; exit 2; }
run_root="$(resolve_run_root "${1:-}")" || {
  printf '%s\n' 'no valid run found; pass RUN_ROOT or create runs/latest' >&2
  exit 1
}

launched=0
for task in "${ioi_tasks[@]}"; do
  status_path="$run_root/workers/$task/runtime/status.json"
  readarray -t worker_state < <(
    python3 - "$status_path" <<'PY'
import json
import os
import sys

try:
    data = json.load(open(sys.argv[1], encoding="utf-8"))
except (FileNotFoundError, json.JSONDecodeError):
    data = {}
pid = data.get("pid")
alive = False
if isinstance(pid, int):
    try:
        os.kill(pid, 0)
        alive = True
    except OSError:
        pass
print(data.get("state", "not-started"))
print(str(alive).lower())
PY
  )
  if [[ "${worker_state[0]}" == complete ]]; then
    printf 'skip %-12s already complete\n' "$task"
    continue
  fi
  if [[ "${worker_state[1]}" == true ]]; then
    printf 'skip %-12s already running\n' "$task"
    continue
  fi
  setsid bash "$orchestration_root/run-worker.sh" "$run_root" "$task" \
    >"$run_root/runtime/$task.resume.log" 2>&1 < /dev/null &
  pid=$!
  printf '%s\n' "$pid" >"$run_root/runtime/pids/$task.pid"
  printf 'launched %-12s pid=%s\n' "$task" "$pid"
  launched=$((launched + 1))
done

printf 'launched workers: %s\n' "$launched"
printf 'monitor with: %s %q\n' "$orchestration_root/monitor.sh" "$run_root"
