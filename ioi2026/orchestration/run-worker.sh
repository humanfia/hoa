#!/usr/bin/env bash

set -euo pipefail
IFS=$'\n\t'

script_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$script_root/common.sh"

[[ $# -eq 2 ]] || { printf 'usage: %s RUN_ROOT TASK\n' "$0" >&2; exit 2; }
run_root="$(resolve_run_root "$1")" || { printf 'invalid run: %s\n' "$1" >&2; exit 1; }
task=$2
require_task "$task"
worker_root="$run_root/workers/$task"
[[ -d "$worker_root/.git" ]] || { printf 'worker repository missing: %s\n' "$worker_root" >&2; exit 1; }

status_path="$worker_root/runtime/status.json"
mkdir -p -- "$worker_root/runtime"

write_status() {
  local state=$1
  local message=${2:-}
  python3 - "$status_path" "$task" "$state" "$$" "$message" <<'PY'
import datetime
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
try:
    data = json.loads(path.read_text())
except (FileNotFoundError, json.JSONDecodeError):
    data = {}
data.update({
    "task": sys.argv[2],
    "state": sys.argv[3],
    "pid": int(sys.argv[4]),
    "message": sys.argv[5],
    "updated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
})
temporary = path.with_suffix(".json.tmp")
temporary.write_text(json.dumps(data, indent=2) + "\n")
temporary.replace(path)
PY
}

on_error() {
  local exit_status=$?
  local failed_line=$1
  set +e
  write_status failed "runner error at line $failed_line (exit $exit_status)"
  exit "$exit_status"
}
trap 'on_error "$LINENO"' ERR

mapfile -t run_configuration < <(
  python3 - "$run_root/run.json" <<'PY'
import json
import sys

data = json.load(open(sys.argv[1], encoding="utf-8"))
for key in (
    "model", "effort", "max_iterations", "codex_timeout", "isolation",
    "humanize_root", "auth_file", "codex_real", "landlock_binary",
):
    value = data[key]
    print(str(value).lower() if isinstance(value, bool) else value)
PY
)
model=${run_configuration[0]}
effort=${run_configuration[1]}
max_iterations=${run_configuration[2]}
codex_timeout=${run_configuration[3]}
isolation=${run_configuration[4]}
humanize_root=${run_configuration[5]}
auth_file=${run_configuration[6]}
codex_real=${run_configuration[7]}
landlock_binary=${run_configuration[8]}

[[ -x "$humanize_root/scripts/setup-rlcr-loop.sh" ]]
[[ -x "$humanize_root/hooks/loop-codex-stop-hook.sh" ]]
[[ -r "$auth_file" ]]
[[ -x "$codex_real" ]]
if [[ "$isolation" == true ]]; then
  [[ -x "$landlock_binary" ]]
fi

runtime_home="$worker_root/.codex-runtime"
runtime_bin="$worker_root/runtime/bin"
private_tmp="$worker_root/runtime/tmp"
mkdir -p -- "$runtime_home" "$runtime_bin" "$private_tmp"

python3 - "$runtime_home" "$worker_root" "$humanize_root" "$model" \
  "$effort" "$auth_file" "$codex_real" "$runtime_bin/codex" <<'PY'
import json
import pathlib
import shlex
import sys

home = pathlib.Path(sys.argv[1])
worker = pathlib.Path(sys.argv[2])
humanize = pathlib.Path(sys.argv[3])
model = sys.argv[4]
effort = sys.argv[5]
auth = pathlib.Path(sys.argv[6])
codex = pathlib.Path(sys.argv[7])
wrapper = pathlib.Path(sys.argv[8])

def toml_string(value: str) -> str:
    return json.dumps(value)

config = f'''model = {toml_string(model)}
review_model = {toml_string(model)}
model_reasoning_effort = {toml_string(effort)}
disable_response_storage = true
network_access = "disabled"
web_search = "disabled"

[features]
hooks = true
plugins = false
skill_search = false
standalone_web_search = false
web_search_cached = false
web_search_request = false

[projects.{toml_string(str(worker))}]
trust_level = "trusted"
'''
home.mkdir(parents=True, exist_ok=True)
(home / "config.toml").write_text(config)

hooks = {
    "description": "IOI reproduction Humanize native Stop hook",
    "hooks": {
        "Stop": [{
            "hooks": [{
                "type": "command",
                "command": str(humanize / "hooks" / "loop-codex-stop-hook.sh"),
                "timeout": 7200,
                "statusMessage": "Humanize RLCR stop hook",
            }]
        }]
    },
}
(home / "hooks.json").write_text(json.dumps(hooks, indent=2) + "\n")

auth_link = home / "auth.json"
if auth_link.is_symlink():
    if auth_link.resolve() != auth.resolve():
        raise SystemExit(f"unexpected auth symlink: {auth_link}")
elif auth_link.exists():
    raise SystemExit(f"refusing to replace auth path: {auth_link}")
else:
    auth_link.symlink_to(auth)

wrapper.write_text(
    "#!/usr/bin/env bash\nset -euo pipefail\nexec "
    + shlex.quote(str(codex)) + " \"$@\"\n"
)
wrapper.chmod(0o755)
PY

export CODEX_HOME="$runtime_home"
export HUMANIZE_ROOT="$humanize_root"
export CLAUDE_PROJECT_DIR="$worker_root"
export TMPDIR="$private_tmp"
export TMP="$private_tmp"
export TEMP="$private_tmp"
export XDG_CACHE_HOME="$worker_root/runtime/xdg-cache"
export PYTHONDONTWRITEBYTECODE=1
export PATH="$runtime_bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
mkdir -p -- "$XDG_CACHE_HOME"

write_status preparing 'configuring Humanize loop'
loop_root=
if [[ -d "$worker_root/.humanize/rlcr" ]]; then
  loop_root="$(find "$worker_root/.humanize/rlcr" -mindepth 1 -maxdepth 1 \
    -type d -print | LC_ALL=C sort | tail -n 1)"
fi

if [[ -z "$loop_root" ]]; then
  (cd -- "$worker_root" && \
    bash "$humanize_root/scripts/setup-rlcr-loop.sh" plan.md \
      --track-plan-file \
      --base-branch main \
      --max "$max_iterations" \
      --codex-model "$model:$effort" \
      --codex-timeout "$codex_timeout" \
      --full-review-round 5 \
      --yolo \
      --privacy) \
    >"$worker_root/runtime/humanize-setup.log" 2>&1
  loop_root="$(find "$worker_root/.humanize/rlcr" -mindepth 1 -maxdepth 1 \
    -type d -print | LC_ALL=C sort | tail -n 1)"
fi
[[ -n "$loop_root" && -d "$loop_root" ]]

solution_path="$(task_solution_path "$task")"
worker_prompt="$worker_root/runtime/worker-prompt.md"
cat >"$worker_prompt" <<EOF
You are the implementation worker for IOI 2026 task "$(task_title "$task")".
This is an active Humanize RLCR run, not a one-shot answer.

First read AGENTS.md, immutable plan.md, and the current authoritative prompt
under ${loop_root#"$worker_root/"}. Follow them exactly. Implement and validate
the complete contestant solution at $solution_path using only the official
problem material in this repository and tests you author here.

Work through every Humanize round. Commit each round, write the exact summary
requested by the current prompt, and then stop normally so the native Stop hook
can review it. If the hook blocks, read its feedback and continue. Do not edit
state/reviewer files, bypass the hook, cancel the loop, use the network, or read
outside this repository. Continue until Humanize itself creates complete-state.md.
EOF

events="$worker_root/runtime/codex-events.jsonl"
errors="$worker_root/runtime/codex-stderr.log"
final_message="$worker_root/runtime/codex-final.md"
codex_command=(
  "$runtime_bin/codex"
  exec
  --cd "$worker_root"
  --model "$model"
  -c "model_reasoning_effort=\"$effort\""
  -c 'network_access="disabled"'
  -c 'web_search="disabled"'
  -c 'disable_response_storage=true'
  --sandbox workspace-write
  --dangerously-bypass-hook-trust
  --json
  --output-last-message "$final_message"
  -
)

execution=("${codex_command[@]}")
if [[ "$isolation" == true ]]; then
  execution=(
    "$landlock_binary"
    --rw "$worker_root"
    --ro "$auth_file"
    --ro "$codex_real"
    --ro "$humanize_root"
    --ro /usr
    --ro /etc
    --rw /dev
    --ro /proc
    --ro /sys
    --rw /run
  )
  if [[ -f "${HOME}/.gitconfig" ]]; then
    execution+=(--ro "${HOME}/.gitconfig")
  fi
  execution+=(-- "${codex_command[@]}")
fi

write_status running "Humanize RLCR with $model:$effort"
set +e
"${execution[@]}" <"$worker_prompt" >>"$events" 2>>"$errors"
codex_exit=$?
set -e
if [[ $codex_exit -ne 0 ]]; then
  write_status failed "Codex exited with status $codex_exit"
  exit "$codex_exit"
fi

complete_state="$(find "$loop_root" -maxdepth 1 -type f -name complete-state.md -print -quit)"
if [[ -z "$complete_state" ]]; then
  write_status stopped 'Codex exited before Humanize completion; use resume-six.sh'
  exit 1
fi

[[ -f "$worker_root/$solution_path" ]] || {
  write_status failed "missing solution artifact: $solution_path"
  exit 1
}
[[ -x "$worker_root/test.sh" ]] || {
  write_status failed 'missing executable test.sh'
  exit 1
}

write_status validating 'running worker test.sh after Humanize completion'
set +e
(cd -- "$worker_root" && ./test.sh) \
  >"$worker_root/runtime/final-validation.log" 2>&1
validation_exit=$?
set -e
if [[ $validation_exit -ne 0 ]]; then
  write_status failed "final test.sh exited with status $validation_exit"
  exit "$validation_exit"
fi
if [[ -n "$(git -C "$worker_root" status --porcelain=v1 --untracked-files=all)" ]]; then
  write_status failed 'worker repository is dirty after final validation'
  exit 1
fi

write_status complete 'Humanize complete and final validation passed'
trap - ERR
printf 'COMPLETE %s\n' "$task"
