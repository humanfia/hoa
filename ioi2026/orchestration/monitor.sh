#!/usr/bin/env bash

set -euo pipefail

script_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$script_root/common.sh"

[[ $# -le 1 ]] || { printf 'usage: %s [RUN_ROOT]\n' "$0" >&2; exit 2; }
run_root="$(resolve_run_root "${1:-}")" || {
  printf '%s\n' 'no valid run found; pass RUN_ROOT or create runs/latest' >&2
  exit 1
}

python3 - "$run_root" "${ioi_tasks[@]}" <<'PY'
import json
import os
import pathlib
import re
import sys

run = pathlib.Path(sys.argv[1])
print(f"run: {run}")
print(f"{'task':<13} {'state':<12} {'alive':<6} {'round':<7} {'complete':<9} message")
for task in sys.argv[2:]:
    worker = run / "workers" / task
    status_path = worker / "runtime" / "status.json"
    try:
        status = json.loads(status_path.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        status = {"state": "not-started", "pid": None, "message": ""}
    pid = status.get("pid")
    alive = False
    if isinstance(pid, int):
        try:
            os.kill(pid, 0)
            alive = True
        except OSError:
            pass
    loops = sorted((worker / ".humanize" / "rlcr").glob("*"))
    current_round = "-"
    complete = False
    if loops:
        loop = loops[-1]
        complete = (loop / "complete-state.md").is_file()
        state_file = loop / "state.md"
        if state_file.is_file():
            match = re.search(r"^current_round:\s*(\d+)", state_file.read_text(), re.M)
            if match:
                current_round = match.group(1)
    print(
        f"{task:<13} {status.get('state', 'unknown'):<12} "
        f"{str(alive).lower():<6} {current_round:<7} "
        f"{str(complete).lower():<9} {status.get('message', '')}"
    )
PY
