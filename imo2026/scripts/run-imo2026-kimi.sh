#!/usr/bin/env bash
set -Eeuo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HUMANIZE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
WORKSPACE_ROOT="${WORKSPACE_ROOT:-$HUMANIZE_ROOT}"
MATH_FLOW_BENCH_ROOT="${MATH_FLOW_BENCH_ROOT:-$WORKSPACE_ROOT/base}"
IMO2026_SOURCE_ROOT="${IMO2026_SOURCE_ROOT:-$WORKSPACE_ROOT/base/IMO2026}"
FAILURE_FILE="${FAILURE_FILE:-$WORKSPACE_ROOT/inputs/problems.md}"
BASE_KIMI_HOME="${BASE_KIMI_HOME:-/root/.kimi-code}"
BASE_CODEX_HOME="${BASE_CODEX_HOME:-/root/.codex}"
OUT_ROOT="${OUT_ROOT:-$WORKSPACE_ROOT/runs}"
COMPARATOR_TOOLS_ROOT="${COMPARATOR_TOOLS_ROOT:-$WORKSPACE_ROOT/tools}"
LOCAL_RUNTIME_TEMPLATE="${LOCAL_RUNTIME_TEMPLATE:-/tmp/imo2026-humanize-runtime-v431}"
LOCAL_RUNS_ROOT="${LOCAL_RUNS_ROOT:-/tmp/imo2026-humanize-kimi-worker-codex-reviewer-runs}"
COMPARATOR_BIN="${COMPARATOR_BIN:-$LOCAL_RUNTIME_TEMPLATE/comparator-tools/comparator}"
LEAN4EXPORT_BIN="${LEAN4EXPORT_BIN:-$LOCAL_RUNTIME_TEMPLATE/checker-tools/lean4export}"
LANDRUN_BIN="${LANDRUN_BIN:-$LOCAL_RUNTIME_TEMPLATE/comparator-tools/landrun}"
KIMI_BIN="${KIMI_BIN:-/root/.kimi-code/bin/kimi}"
HUMANIZE_USER_PREFIX="${HUMANIZE_USER_PREFIX:-humanize-imo}"

KIMI_MODEL="kimi-for-coding/k3"
CODEX_MODEL="${CODEX_MODEL:-gpt-5.5}"
CODEX_REASONING_EFFORT="${CODEX_REASONING_EFFORT:-xhigh}"
MAX_TURNS="${MAX_TURNS:-50}"
JOBS="${JOBS:-6}"
FALLBACK_JOBS="${FALLBACK_JOBS:-6}"
PROBE_COUNT="${PROBE_COUNT:-4}"
WORKER_TIMEOUT_SECONDS="${WORKER_TIMEOUT_SECONDS:-14400}"
REVIEW_TIMEOUT_SECONDS="${REVIEW_TIMEOUT_SECONDS:-7200}"
KIMI_RATE_RETRIES="${KIMI_RATE_RETRIES:-6}"
CODEX_RATE_RETRIES="${CODEX_RATE_RETRIES:-6}"
REVIEW_INFRA_RETRIES="${REVIEW_INFRA_RETRIES:-0}"
RUN_ID="${RUN_ID:-imo2026-humanize-kimi-worker-codex-reviewer-comparator-$(date -u +%Y%m%dT%H%M%SZ)}"

DRY_RUN=0
PREPARE_ONLY=0
RESUME_PREPARED=0
RESUME_REVIEW_ONLY=0
RESUME_WORKER_ONLY=0
MAX_PROBLEMS=0
PROBLEMS=()

usage() {
  cat <<'EOF'
Usage:
  bash scripts/run-imo2026.sh [options]

Runs blind Kimi Code IMO 2026 proof workers and isolated Codex AXLE-backed
reviewers for Q1-Q6.
Each problem gets at most 50
worker/reviewer turns by default. Solver shell commands are network-blocked.
Workers must self-check with Comparator before review. Reviewers may use the
network only for the required AXLE verification call.

Options:
  --problem ID                 Run only this problem; repeatable.
  --max-problems N             Limit parsed problems. Default: all.
  --jobs N                     Main concurrency after a clean probe. Default: 6.
  --fallback-jobs N            Concurrency after 429/529. Default: 6.
  --probe-count N              One-turn jobs before ramp-up. Default: 4.
  --max-turns N                Worker/reviewer turns per problem. Default: 50.
  --worker-timeout-seconds N   Timeout per worker Kimi Code call. Default: 7200.
  --review-timeout-seconds N   Timeout per reviewer Codex call. Default: 7200.
  --run-id ID                  Override timestamped run ID.
  --failure-file PATH          Markdown problem list.
  --source-root PATH           Root containing Q1/problem.lean through Q6/problem.lean.
  --base-kimi-home PATH        Kimi Code auth/config source. Default: /root/.kimi-code.
  --base-codex-home PATH       Codex auth/config source. Default: workspace .codex.
  --out-root PATH              Output parent directory.
  --prepare-only               Build and audit sanitized workspaces; run no models.
  --resume-prepared            Reuse an existing run and launch only jobs whose
                               status is `prepared` or `pending`; never rewrite workspaces.
  --resume-review-only         Resume a terminal reviewer failure against the
                               unchanged candidate; never rerun the worker first.
  --resume-worker-only         Resume a terminal worker failure from its current
                               turn without rewriting the prepared workspace.
  --dry-run                    Print selected IDs and checks; write nothing.
  -h, --help                   Show this help.

Environment defaults:
  KIMI_MODEL=kimi-for-coding/k3 (fixed)
  CODEX_MODEL=gpt-5.5
  CODEX_REASONING_EFFORT=xhigh
  MAX_TURNS=50
  JOBS=6
  BASE_KIMI_HOME=/root/.kimi-code
  COMPARATOR_TOOLS_ROOT=<package>/tools
EOF
}

log() {
  printf '[imo2026-humanize] %s\n' "$*"
}

die() {
  printf '[imo2026-humanize] ERROR: %s\n' "$*" >&2
  exit 1
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --problem) PROBLEMS+=("$2"); shift 2 ;;
    --max-problems) MAX_PROBLEMS="$2"; shift 2 ;;
    --jobs) JOBS="$2"; shift 2 ;;
    --fallback-jobs) FALLBACK_JOBS="$2"; shift 2 ;;
    --probe-count) PROBE_COUNT="$2"; shift 2 ;;
    --max-turns) MAX_TURNS="$2"; shift 2 ;;
    --worker-timeout-seconds) WORKER_TIMEOUT_SECONDS="$2"; shift 2 ;;
    --review-timeout-seconds) REVIEW_TIMEOUT_SECONDS="$2"; shift 2 ;;
    --run-id) RUN_ID="$2"; shift 2 ;;
    --failure-file) FAILURE_FILE="$2"; shift 2 ;;
    --source-root) IMO2026_SOURCE_ROOT="$2"; shift 2 ;;
    --base-kimi-home) BASE_KIMI_HOME="$2"; shift 2 ;;
    --base-codex-home) BASE_CODEX_HOME="$2"; shift 2 ;;
    --out-root) OUT_ROOT="$2"; shift 2 ;;
    --prepare-only) PREPARE_ONLY=1; shift ;;
    --resume-prepared) RESUME_PREPARED=1; shift ;;
    --resume-review-only) RESUME_REVIEW_ONLY=1; shift ;;
    --resume-worker-only) RESUME_WORKER_ONLY=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) die "unknown option: $1" ;;
  esac
done

for name in MAX_PROBLEMS JOBS FALLBACK_JOBS PROBE_COUNT MAX_TURNS \
  WORKER_TIMEOUT_SECONDS REVIEW_TIMEOUT_SECONDS KIMI_RATE_RETRIES \
  CODEX_RATE_RETRIES REVIEW_INFRA_RETRIES; do
  value="${!name}"
  [[ "$value" =~ ^[0-9]+$ ]] || die "$name must be a non-negative integer"
done
[[ "$JOBS" -ge 1 ]] || die "JOBS must be at least 1"
[[ "$FALLBACK_JOBS" -ge 1 ]] || die "FALLBACK_JOBS must be at least 1"
[[ "$MAX_TURNS" -ge 1 ]] || die "MAX_TURNS must be at least 1"
[[ "$WORKER_TIMEOUT_SECONDS" -ge 60 ]] || die "worker timeout must be at least 60"
[[ "$REVIEW_TIMEOUT_SECONDS" -ge 60 ]] || die "review timeout must be at least 60"
[[ "$REVIEW_INFRA_RETRIES" -eq 0 || "$REVIEW_INFRA_RETRIES" -ge 1 ]] || \
  die "REVIEW_INFRA_RETRIES must be 0 (unlimited) or at least 1"
[[ $((PREPARE_ONLY + RESUME_PREPARED + RESUME_REVIEW_ONLY + RESUME_WORKER_ONLY)) -le 1 ]] || \
  die "prepare/resume modes are mutually exclusive"

RUN_ROOT="$OUT_ROOT/$RUN_ID"
PROOT_ROOT="${PROOT_ROOT:-$LOCAL_RUNS_ROOT/$RUN_ID}"
WORKSPACES_ROOT="$PROOT_ROOT/workspaces"
KIMI_RUN_HOME="$PROOT_ROOT/agent-homes"
CODEX_RUN_HOME="$PROOT_ROOT/codex-homes"
IDENTITY_TAG="$(printf '%s' "$RUN_ID" | tr -c '[:alnum:]_.-' '-')"
PRIVATE_WORKSPACES_LINK="/kimi-k3-${IDENTITY_TAG}-v2-workspaces"
PRIVATE_AGENT_HOMES_LINK="/kimi-k3-${IDENTITY_TAG}-v2-agent-homes"
PRIVATE_CODEX_HOMES_LINK="/codex-${IDENTITY_TAG}-review-homes"
PRIVATE_CHECKER_TOOLS_LINK="/kimi-k3-${IDENTITY_TAG}-v2-checker-tools"
RATE_FLAG="$RUN_ROOT/rate-limit.detected"
RATE_LOG="$RUN_ROOT/rate-limit-events.tsv"
QUOTA_FLAG="$RUN_ROOT/quota-exhausted.detected"
QUOTA_LOG="$RUN_ROOT/quota-exhausted-events.tsv"
INFRA_FLAG="$RUN_ROOT/transport-failure.detected"
INFRA_LOG="$RUN_ROOT/transport-failures.tsv"
METRICS="$RUN_ROOT/metrics.tsv"
KIMI_SESSIONS="$RUN_ROOT/kimi-sessions.tsv"
CODEX_SESSIONS="$RUN_ROOT/codex-sessions.tsv"
LOOP_STAMP="$(date -u +%Y-%m-%d_%H-%M-%S)"
NO_NET_BASH="$RUN_ROOT/no-net-bash"

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || die "missing required command: $1"
}

module_name() {
  printf 'IMO2026%s\n' "$(printf '%s' "${1#imo2026_}" | tr '[:lower:]' '[:upper:]')"
}

safe_name() {
  printf '%s' "$1" | tr -c '[:alnum:]_.-' '-'
}

parse_failed_problems() {
  if [[ "${#PROBLEMS[@]}" -gt 0 ]]; then
    printf '%s\n' "${PROBLEMS[@]}"
  else
    rg -o 'imo2026_q[1-6]' "$FAILURE_FILE" | sort -u
  fi | awk -v max="$MAX_PROBLEMS" 'NF && !seen[$0]++ { print; n++; if (max > 0 && n >= max) exit }'
}

validate_kimi_model_config() {
  python3 - "$BASE_KIMI_HOME/config.toml" "$KIMI_MODEL" <<'PY'
import sys
import tomllib
from pathlib import Path

config = tomllib.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
alias = sys.argv[2]
model = (config.get("models") or {}).get(alias)
if not isinstance(model, dict):
    raise SystemExit(f"Kimi model alias is not configured: {alias}")
if model.get("model") != "k3":
    raise SystemExit(f"Kimi alias {alias} does not resolve to model id k3")
if not ((config.get("thinking") or {}).get("enabled") is True):
    raise SystemExit("Kimi thinking mode must be enabled in the base config")
PY
}

codex_binary() {
  readlink -f "$(command -v codex)"
}

node_binary() {
  readlink -f "$(command -v node)"
}

codex_base_url() {
  awk -F= '/^[[:space:]]*base_url[[:space:]]*=/{gsub(/[ "\r]/, "", $2); print $2; exit}' \
    "$BASE_CODEX_HOME/config.toml"
}

write_codex_config() {
  local output="$1"
  local provider_url
  provider_url="$(codex_base_url)"
  cat > "$output" <<EOF
model = "$CODEX_MODEL"
review_model = "$CODEX_MODEL"
model_reasoning_effort = "$CODEX_REASONING_EFFORT"
disable_response_storage = true
network_access = "enabled"
windows_wsl_setup_acknowledged = true
approvals_reviewer = "user"
service_tier = "default"
EOF

  if [[ -n "$provider_url" ]]; then
    cat >> "$output" <<EOF
model_provider = "OpenAI"

[model_providers.OpenAI]
name = "OpenAI"
base_url = "$provider_url"
wire_api = "responses"
requires_openai_auth = true
EOF
  fi
}

hydrate_codex_home() {
  local output="$1"
  mkdir -p "$output/sessions" "$output/shell_snapshots" "$output/tmp"
  # Each isolated reviewer home otherwise decides independently that an old
  # `last_refresh` timestamp requires token rotation.  Besides causing a
  # refresh storm across six concurrent reviewers, the configured gateway can
  # reject the newly rotated token even while the base access token remains
  # valid.  Pin the still-valid base token for this fresh isolated invocation;
  # if it is near expiry, retain the original timestamp and let Codex refresh.
  python3 - "$BASE_CODEX_HOME/auth.json" "$output/auth.json" <<'PY'
import base64
import datetime as dt
import json
import os
import sys
import time
from pathlib import Path

source, destination = map(Path, sys.argv[1:])
data = json.loads(source.read_text(encoding="utf-8"))
token = ((data.get("tokens") or {}).get("access_token") or "")
try:
    encoded = token.split(".")[1]
    encoded += "=" * ((4 - len(encoded) % 4) % 4)
    expires = int(json.loads(base64.urlsafe_b64decode(encoded))["exp"])
except (IndexError, KeyError, TypeError, ValueError, json.JSONDecodeError):
    expires = 0
if expires > int(time.time()) + 3600:
    data["last_refresh"] = dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")
temporary = destination.with_name(destination.name + ".tmp")
fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
with os.fdopen(fd, "w", encoding="utf-8") as handle:
    json.dump(data, handle, separators=(",", ":"))
    handle.write("\n")
os.replace(temporary, destination)
PY
  write_codex_config "$output/config.toml"
  chmod -R go-rwx "$output"
}

hydrate_kimi_home() {
  local output="$1"
  local role="$2"
  local tmp="$output/config.toml.tmp"
  : "$role"
  mkdir -p "$output/credentials" "$output/oauth" "$output/sessions" \
    "$output/tmp" "$output/empty-skills"

  awk '
    BEGIN { inserted = 0 }
    /^(default_permission_mode|merge_all_available_skills|telemetry)[[:space:]]*=/ { next }
    /^\[/ && !inserted {
      print "default_permission_mode = \"auto\""
      print "merge_all_available_skills = false"
      print "telemetry = false"
      print ""
      inserted = 1
    }
    { print }
    END {
      if (!inserted) {
        print "default_permission_mode = \"auto\""
        print "merge_all_available_skills = false"
        print "telemetry = false"
      }
    }
  ' "$BASE_KIMI_HOME/config.toml" > "$tmp"
  cat >> "$tmp" <<'EOF'

[[permission.rules]]
decision = "deny"
pattern = "WebSearch"
reason = "Blind proof workers and reviewers may not search the web."

[[permission.rules]]
decision = "deny"
pattern = "FetchURL"
reason = "External HTTP access is reserved for the AXLE verifier script."

[[permission.rules]]
decision = "deny"
pattern = "Agent"
reason = "Nested model workers are disabled for this benchmark."

[[permission.rules]]
decision = "deny"
pattern = "AgentSwarm"
reason = "Nested model workers are disabled for this benchmark."

[[permission.rules]]
decision = "deny"
pattern = "Skill"
reason = "The runner, not the terminal agent, owns the Humanize workflow."
EOF
  mv "$tmp" "$output/config.toml"

  [[ -f "$BASE_KIMI_HOME/device_id" ]] && \
    cp "$BASE_KIMI_HOME/device_id" "$output/device_id"
  [[ -d "$BASE_KIMI_HOME/credentials" ]] && \
    cp -a "$BASE_KIMI_HOME/credentials/." "$output/credentials/"
  [[ -d "$BASE_KIMI_HOME/oauth" ]] && \
    cp -a "$BASE_KIMI_HOME/oauth/." "$output/oauth/"
  chmod -R go-rwx "$output"
}

compile_no_net_bash() {
  local source="${NO_NET_BASH}.c"
  cat > "$source" <<'EOF'
#define _GNU_SOURCE
#include <errno.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <fcntl.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <unistd.h>

#define DENY_SYSCALL(nr) \
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (nr), 0, 1), \
  BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EACCES)

static void install_no_network_filter(void) {
  struct sock_filter filter[] = {
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
#ifdef __NR_socket
    DENY_SYSCALL(__NR_socket),
#endif
#ifdef __NR_connect
    DENY_SYSCALL(__NR_connect),
#endif
#ifdef __NR_accept
    DENY_SYSCALL(__NR_accept),
#endif
#ifdef __NR_accept4
    DENY_SYSCALL(__NR_accept4),
#endif
#ifdef __NR_bind
    DENY_SYSCALL(__NR_bind),
#endif
#ifdef __NR_listen
    DENY_SYSCALL(__NR_listen),
#endif
#ifdef __NR_socketpair
    DENY_SYSCALL(__NR_socketpair),
#endif
#ifdef __NR_sendto
    DENY_SYSCALL(__NR_sendto),
#endif
#ifdef __NR_recvfrom
    DENY_SYSCALL(__NR_recvfrom),
#endif
#ifdef __NR_sendmsg
    DENY_SYSCALL(__NR_sendmsg),
#endif
#ifdef __NR_recvmsg
    DENY_SYSCALL(__NR_recvmsg),
#endif
#ifdef __NR_getsockname
    DENY_SYSCALL(__NR_getsockname),
#endif
#ifdef __NR_getpeername
    DENY_SYSCALL(__NR_getpeername),
#endif
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
  };
  struct sock_fprog prog = {
    .len = (unsigned short)(sizeof(filter) / sizeof(filter[0])),
    .filter = filter,
  };
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) exit(126);
  if (prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog) != 0) exit(126);
}

int main(int argc, char **argv) {
  (void)argc;
  const char *audit = getenv("HUMANIZE_SHELL_AUDIT");
  if (audit != NULL && *audit != '\0') {
    int fd = open(audit, O_WRONLY | O_CREAT | O_APPEND, 0600);
    if (fd >= 0) {
      dprintf(fd, "%ld\n", (long)getpid());
      close(fd);
    }
  }
  install_no_network_filter();
  execv("/usr/bin/bash", argv);
  perror("execv(/usr/bin/bash)");
  return 127;
}
EOF
  cc -O2 -Wall -Wextra -o "$NO_NET_BASH" "$source"
  mkdir -p "$PROOT_ROOT/worker-shell"
  cc -O2 -Wall -Wextra -shared -fPIC \
    -o "$PROOT_ROOT/worker-shell/libhumanize-nonet.so" \
    "$HUMANIZE_ROOT/scripts/nonet-preload.c"
  cc -O2 -Wall -Wextra \
    -o "$PROOT_ROOT/worker-shell/bash" \
    "$HUMANIZE_ROOT/scripts/nonet-shell.c"
  cp /usr/bin/bash "$PROOT_ROOT/worker-shell/bash.real"
  : > "$PROOT_ROOT/worker-shell/invocations.log"
  chmod 0666 "$PROOT_ROOT/worker-shell/invocations.log"
}

clone_runtime_template() {
  [[ -d "$LOCAL_RUNTIME_TEMPLATE" ]] || \
    die "local runtime template missing: $LOCAL_RUNTIME_TEMPLATE"
  [[ -x "$LOCAL_RUNTIME_TEMPLATE/root/.elan/bin/lake" ]] || \
    die "local runtime template has no executable Lake"
  [[ -d "$LOCAL_RUNTIME_TEMPLATE/mathlib-packages/mathlib" ]] || \
    die "local runtime template has no Mathlib package"
  [[ -x "$LOCAL_RUNTIME_TEMPLATE/checker-tools/lean4export" ]] || \
    die "local runtime template has no lean4export"
  [[ -x "$LOCAL_RUNTIME_TEMPLATE/comparator-tools/comparator" ]] || \
    die "local runtime template has no Comparator"
  [[ -x "$LOCAL_RUNTIME_TEMPLATE/comparator-tools/landrun" ]] || \
    die "local runtime template has no Landrun"
  [[ ! -e "$PROOT_ROOT" ]] || die "local run root already exists: $PROOT_ROOT"
  mkdir -p "$LOCAL_RUNS_ROOT"
  cp -al "$LOCAL_RUNTIME_TEMPLATE" "$PROOT_ROOT"
  mkdir -p "$WORKSPACES_ROOT" "$KIMI_RUN_HOME" "$CODEX_RUN_HOME" \
    "$PROOT_ROOT/worker-shell"
  chmod 1777 "$PROOT_ROOT/tmp"
}

ensure_symlink() {
  local target="$1" link="$2"
  if [[ -L "$link" ]]; then
    [[ "$(readlink -f "$link")" == "$(readlink -f "$target")" ]] || \
      die "private identity path already points elsewhere: $link"
    return 0
  fi
  [[ ! -e "$link" ]] || die "private identity path is occupied: $link"
  ln -s "$target" "$link"
}

ensure_guest_directory() {
  local path="$1"
  [[ ! -L "$path" ]] || die "private guest bind point is a symbolic link: $path"
  mkdir -p "$path"
  [[ -d "$path" ]] || die "private guest bind point is unavailable: $path"
}

activate_private_identity_paths() {
  local workspace_name agent_name codex_name checker_name
  workspace_name="${PRIVATE_WORKSPACES_LINK#/}"
  agent_name="${PRIVATE_AGENT_HOMES_LINK#/}"
  codex_name="${PRIVATE_CODEX_HOMES_LINK#/}"
  checker_name="${PRIVATE_CHECKER_TOOLS_LINK#/}"

  ensure_symlink "$WORKSPACES_ROOT" "$PRIVATE_WORKSPACES_LINK"
  ensure_symlink "$KIMI_RUN_HOME" "$PRIVATE_AGENT_HOMES_LINK"
  ensure_symlink "$CODEX_RUN_HOME" "$PRIVATE_CODEX_HOMES_LINK"
  ensure_symlink "$PROOT_ROOT/checker-tools" "$PRIVATE_CHECKER_TOOLS_LINK"
  ensure_guest_directory "$PROOT_ROOT/$workspace_name"
  ensure_guest_directory "$PROOT_ROOT/$agent_name"
  ensure_guest_directory "$PROOT_ROOT/$codex_name"
  ensure_guest_directory "$PROOT_ROOT/$checker_name"
}

install_lake_workspace_wrapper() {
  local lake_bin="$PROOT_ROOT/root/.elan/bin/lake"
  local real_lake="$PROOT_ROOT/root/.elan/bin/lake.elan-shim"
  if [[ ! -e "$real_lake" ]]; then
    mv "$lake_bin" "$real_lake"
  fi
  if ! cmp -s "$HUMANIZE_ROOT/scripts/lake-workspace-wrapper.sh" "$lake_bin"; then
    cp "$HUMANIZE_ROOT/scripts/lake-workspace-wrapper.sh" "$lake_bin"
  fi
  chmod 0755 "$lake_bin" "$real_lake"
}

extract_problem_statement() {
  local problem="$1"
  local output="$2"
  local question
  question="$(printf '%s' "${problem#imo2026_}" | tr '[:lower:]' '[:upper:]')"
  cp "$IMO2026_SOURCE_ROOT/$question/problem.lean" "$output"
}

write_plan_files() {
  local workspace="$1"
  local problem="$2"
  local module="$3"
  local loop_dir="$workspace/.humanize/rlcr/$LOOP_STAMP"
  mkdir -p "$workspace/docs/humanize" "$loop_dir"
  cat > "$workspace/docs/humanize/active-imo2026-plan.md" <<EOF
# Blind Humanize IMO 2026 Proof: $problem

## Goal

Solve every theorem hole in the exact IMO 2026 statement snapshot in
\`MathFlowBench/$module.lean\` without consulting prior solutions.

## Acceptance Criteria

- AC-1: Original declarations, theorem signatures, and docstrings are preserved.
- AC-2: The candidate contains no \`sorry\`, \`admit\`, \`axiom\`, or \`native_decide\`.
- AC-3: \`lake env lean MathFlowBench/$module.lean\` succeeds.
- AC-4: \`bash tools/check-with-comparator.sh\` ends with \`Your solution is okay!\`.
- AC-5: The isolated AXLE reviewer returns Boolean \`okay: true\` against the
  exact upstream problem statement using the Lean 4.31.0 AXLE environment.

## Constraints

- The worker may read only this sanitized workspace and the mounted Mathlib tree.
- The worker must not use the Internet, prior attempts, session archives, or existing solutions.
- The reviewer must not edit the candidate. Its only permitted external network call is AXLE verification.
- The worker uses Kimi Code with model \`$KIMI_MODEL\` and thinking enabled.
- The independent reviewer uses Codex model \`$CODEX_MODEL\` with
  \`$CODEX_REASONING_EFFORT\` reasoning effort.
- Stop after at most $MAX_TURNS worker/reviewer turns.
EOF
  cat > "$loop_dir/goal-tracker.md" <<EOF
# Goal Tracker

## IMMUTABLE SECTION

Ultimate Goal: Produce complete Lean proofs for every theorem hole in $problem.

Acceptance Criteria: AC-1 through AC-5 in the active plan.

## MUTABLE SECTION

Active task: solve and independently verify \`MathFlowBench/$module.lean\`.
Completed: none.
Blocking side issues: none.
Queued side issues: none.
EOF
}

prepare_workspace() {
  local index="$1"
  local problem="$2"
  local module="$3"
  local safe workspace job_dir worker_home reviewer_home user
  safe="$(safe_name "$problem")"
  workspace="$WORKSPACES_ROOT/j${index}-${safe}"
  job_dir="$RUN_ROOT/jobs/j${index}-${safe}"
  worker_home="$KIMI_RUN_HOME/j${index}-${safe}/worker"
  reviewer_home="$CODEX_RUN_HOME/j${index}-${safe}/reviewer"

  mkdir -p "$workspace/MathFlowBench" "$workspace/source/lean4/src" \
    "$workspace/scripts" "$workspace/tools" "$workspace/.lake/build" \
    "$workspace/home" "$job_dir" \
    "$worker_home" "$reviewer_home"
  ln -s /mathlib-packages "$workspace/.lake/packages"
  cat > "$workspace/home/.gitconfig" <<'EOF'
[safe]
	directory = *
EOF

  cp "$MATH_FLOW_BENCH_ROOT/lakefile.lean" "$workspace/lakefile.lean"
  cp "$MATH_FLOW_BENCH_ROOT/lake-manifest.json" "$workspace/lake-manifest.json"
  cp "$MATH_FLOW_BENCH_ROOT/lean-toolchain" "$workspace/lean-toolchain"
  cp "$HUMANIZE_ROOT/scripts/validate-imo2026-output.py" \
    "$workspace/scripts/validate-imo2026-output.py"
  cp "$HUMANIZE_ROOT/scripts/verify-imo2026-axle.py" \
    "$workspace/tools/verify-imo2026-axle.py"
  cp "$HUMANIZE_ROOT/scripts/check-with-comparator.sh" \
    "$workspace/tools/check-with-comparator.sh"
  chmod +x "$workspace/tools/check-with-comparator.sh"

  extract_problem_statement "$problem" "$workspace/source/lean4/src/$problem.lean"
  cp "$workspace/source/lean4/src/$problem.lean" "$workspace/MathFlowBench/$module.lean"
  cp "$workspace/source/lean4/src/$problem.lean" "$workspace/ComparatorChallenge.lean"
  cat >> "$workspace/lakefile.lean" <<'EOF'

lean_lib ComparatorChallenge
EOF
  python3 - "$workspace/ComparatorChallenge.lean" "$workspace/comparator.json" \
    "$problem" "$module" <<'PY'
import json
from pathlib import Path
import sys

output = Path(sys.argv[2])
problem = sys.argv[3]
module = sys.argv[4]
theorem_names = {
    "imo2026_q1": [
        "statement_a_termination", "statement_a_unique_large",
        "statement_b_invariance", "terminal_value_eq_Mval", "Mval_gt_one",
    ],
    "imo2026_q2": ["main_theorem"],
    "imo2026_q3": [
        "LiuBangXiangYu.pieceLengths_sum",
        "LiuBangXiangYu.pieceLengths_length",
        "LiuBangXiangYu.L_mem_Icc", "LiuBangXiangYu.V_eq",
        "LiuBangXiangYu.lower_bound", "LiuBangXiangYu.upper_bound",
    ],
    "imo2026_q4": ["TriangleGame.main_theorem"],
    "imo2026_q5": ["main_theorem"],
    "imo2026_q6": ["main_theorem"],
}
config = {
    "challenge_module": "ComparatorChallenge",
    "solution_module": f"MathFlowBench.{module}",
    "theorem_names": theorem_names[problem],
    "definition_names": [],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": False,
}
output.write_text(json.dumps(config, indent=2) + "\n")
PY
  printf 'import MathFlowBench.%s\n' "$module" > "$workspace/MathFlowBench.lean"
  write_plan_files "$workspace" "$problem" "$module"

  hydrate_kimi_home "$worker_home" worker
  hydrate_codex_home "$reviewer_home"

  git -C "$workspace" init -q
  git -C "$workspace" config core.fileMode false
  git -C "$workspace" config user.name "Blind IMO2026 Runner"
  git -C "$workspace" config user.email "runner@localhost"
  git -C "$workspace" add MathFlowBench MathFlowBench.lean ComparatorChallenge.lean \
    comparator.json source scripts tools docs lakefile.lean lake-manifest.json lean-toolchain
  git -C "$workspace" commit -q -m "Initialize sanitized $problem skeleton"

  user="${HUMANIZE_USER_PREFIX}-$(printf '%s' "${problem#imo2026_}" | tr '[:upper:]' '[:lower:]')"
  chown -R root:root "$workspace"
  chown "$user:$user" "$workspace/.lake"
  chown -R "$user:$user" "$workspace/MathFlowBench" "$workspace/.humanize" \
    "$workspace/.lake/build" "$workspace/home" \
    "$KIMI_RUN_HOME/j${index}-${safe}" "$CODEX_RUN_HOME/j${index}-${safe}"
  chmod 0755 "$workspace"
  chmod 0700 "$KIMI_RUN_HOME/j${index}-${safe}" "$CODEX_RUN_HOME/j${index}-${safe}"
  chmod 0444 "$workspace/ComparatorChallenge.lean" "$workspace/comparator.json" \
    "$workspace/lakefile.lean" "$workspace/lake-manifest.json" \
    "$workspace/lean-toolchain" "$workspace/tools/check-with-comparator.sh"
  chmod -R a-w "$workspace/source" "$workspace/scripts" "$workspace/tools"

  sha256sum "$workspace/source/lean4/src/$problem.lean" > "$job_dir/original.sha256"
  printf '%s\n' "$problem" > "$job_dir/problem.txt"
  printf '%s\n' "$module" > "$job_dir/module.txt"
  printf '%s\n' "$workspace" > "$job_dir/workspace.txt"
  printf '%s\n' "$worker_home" > "$job_dir/worker-kimi-home.txt"
  printf '%s\n' "$reviewer_home" > "$job_dir/reviewer-codex-home.txt"
  printf '1\n' > "$job_dir/next-turn.txt"
  printf 'prepared\n' > "$job_dir/status.txt"
}

write_worker_prompt() {
  local workspace="$1"
  local problem="$2"
  local module="$3"
  local turn="$4"
  local feedback="$5"
  local loop_dir="$workspace/.humanize/rlcr/$LOOP_STAMP"
  local prompt="$loop_dir/round-${turn}-prompt.md"
  if [[ -z "$feedback" && "$turn" -eq 1 && -s "$loop_dir/seed-review.md" ]]; then
    feedback="$loop_dir/seed-review.md"
  fi
  cat > "$prompt" <<EOF
You are the blind Lean proof worker in Humanize round $turn of at most $MAX_TURNS.

Problem: $problem
Only editable proof file: \`MathFlowBench/$module.lean\`
Upstream formal-statement snapshot: \`source/lean4/src/$problem.lean\`

Hard isolation and blindness rules:
- Work only inside this sanitized workspace and mounted Mathlib.
- Never inspect existing solutions, other worktrees, prior experiment outputs,
  Kimi Code session archives, or paths outside this workspace.
- Do not use the Internet, web search, curl, wget, sockets, or network resources.
- Do not launch nested model workers.
- Treat the snapshot as authoritative and preserve it exactly apart from filling proof holes.
- Tool calls may receive different ephemeral \`/tmp\` namespaces. Keep any
  reusable analysis scratch under \`\$HOME/scratch\` instead of \`/tmp\` so it
  survives across tool calls, and keep such scratch outside the candidate tree.
- On a recovered worker call, inspect and reuse any existing
  \`\$HOME/scratch\` artifacts before rebuilding experiments or certificates.

Proof rules:
- Preserve the theorem statement, binders, hypotheses, theorem name, and docstring exactly.
- Replace every theorem-body placeholder in the candidate.
- Preserve every original definition, inductive, namespace, theorem signature,
  declaration name, and docstring. Additional helper declarations are allowed.
- Never use \`sorry\`, \`admit\`, \`axiom\`, \`native_decide\`, unsound declarations, or theorem weakening.
- AXLE rejects \`native_decide\` because it depends on \`Lean.ofReduceBool\` and
  \`Lean.trustCompiler\`. Use kernel-checked alternatives such as \`decide\`,
  \`norm_num\`, \`omega\`, or an explicit proof.
- Edit only \`MathFlowBench/$module.lean\`.

Required local checks:
- \`rg -n '\\b(sorry|admit|axiom|native_decide)\\b' MathFlowBench/$module.lean\`
- \`python3 scripts/validate-imo2026-output.py --problem $problem --original source/lean4/src/$problem.lean --candidate MathFlowBench/$module.lean\`
- \`lake env lean MathFlowBench/$module.lean\`
- \`bash tools/check-with-comparator.sh\`

Comparator gate (mandatory before handing the proof to the reviewer):
- The wrapper compares the protected \`ComparatorChallenge.lean\` against
  \`MathFlowBench/$module.lean\` using \`comparator.json\`.
- It verifies every protected theorem statement,
  rejects unpermitted axioms, and replays the proof through the Lean kernel.
- Do not edit \`ComparatorChallenge.lean\`, \`comparator.json\`, the Lake files,
  or \`tools/check-with-comparator.sh\`. Fix only the candidate proof.
- Attempt the wrapper once after Lean succeeds. If it reaches Comparator, a pass
  must end with both \`Lean default kernel accepts the solution\` and
  \`Your solution is okay!\`. If it reports an ordinary proof diagnostic,
  repair the candidate and rerun it.
- On this host, Landrun invoked inside PRoot can instead fail immediately with
  \`permission denied\`, even for a valid executable. Do not bypass, replace, or
  repeatedly debug Landrun in that case. Report the infrastructure failure and
  leave the best Lean-compiling candidate in place. The root runner always
  executes the unchanged real Landrun-backed wrapper after the worker exits and
  will not launch a reviewer unless that authoritative Comparator gate passes.
- Use the supplied real Landrun-backed wrapper. Do not use fake Landrun or
  bypass Comparator.

Do not run a full \`lake build\`; compile only the target file. Leave the best
useful candidate in place even if this round is incomplete.
EOF
  if [[ -n "$feedback" && -s "$feedback" ]]; then
    cat >> "$prompt" <<EOF

## Previous Independent Review

Read and address this review. The reviewer cannot edit the proof:

EOF
    cat "$feedback" >> "$prompt"
  fi
}

run_comparator_local_check() {
  local workspace="$1"
  (
    builtin cd "$workspace"
    ELAN_HOME="${ELAN_HOME:-$HOME/.elan}" \
      COMPARATOR_BIN="$COMPARATOR_BIN" \
      LEAN4EXPORT_BIN="$LEAN4EXPORT_BIN" \
      LANDRUN_BIN="$LANDRUN_BIN" \
      bash tools/check-with-comparator.sh
  )
}

local_checks() {
  local workspace="$1"
  local problem="$2"
  local module="$3"
  local log_file="$4"
  local code=0
  {
    printf '## forbidden markers\n'
    if rg -n '\b(sorry|admit|axiom|native_decide)\b' "$workspace/MathFlowBench/$module.lean"; then
      printf 'FAIL: forbidden marker found\n'
      code=20
    else
      printf 'PASS\n'
    fi
    printf '\n## statement validator\n'
    if python3 "$workspace/scripts/validate-imo2026-output.py" \
      --problem "$problem" \
      --original "$workspace/source/lean4/src/$problem.lean" \
      --candidate "$workspace/MathFlowBench/$module.lean"; then
      printf 'PASS\n'
    else
      printf 'FAIL\n'
      [[ "$code" -eq 0 ]] && code=21
    fi
    printf '\n## Lean target compilation\n'
    if (cd "$workspace" && lake env lean "MathFlowBench/$module.lean"); then
      printf 'PASS\n'
    else
      printf 'FAIL\n'
      [[ "$code" -eq 0 ]] && code=22
    fi
    printf '\n## Comparator self-check\n'
    if run_comparator_local_check "$workspace"; then
      printf 'PASS\n'
    else
      printf 'FAIL\n'
      [[ "$code" -eq 0 ]] && code=23
    fi
  } > "$log_file" 2>&1
  return "$code"
}

write_summary() {
  local workspace="$1"
  local problem="$2"
  local module="$3"
  local turn="$4"
  local check_code="$5"
  local check_log="$6"
  local worker_final="$7"
  local summary="$workspace/.humanize/rlcr/$LOOP_STAMP/round-${turn}-summary.md"
  cat > "$summary" <<EOF
# Round $turn Worker Summary

Problem: \`$problem\`
Candidate: \`MathFlowBench/$module.lean\`
Local check exit: \`$check_code\`

## Worker Final Message

$(sed -n '1,240p' "$worker_final" 2>/dev/null || true)

## Deterministic Local Checks

\`\`\`
$(sed -n '1,320p' "$check_log" 2>/dev/null || true)
\`\`\`

The runner, not the worker, generated this summary from isolated artifacts.
EOF
}

render_review_prompt() {
  local workspace="$1"
  local problem="$2"
  local module="$3"
  local turn="$4"
  local template="$HUMANIZE_ROOT/humanize/prompt-template/kimi/regular-review.md"
  local loop_dir="$workspace/.humanize/rlcr/$LOOP_STAMP"
  local output="$loop_dir/round-${turn}-review-prompt.md"
  TEMPLATE="$template" WORKSPACE="$workspace" GUEST_WORKSPACES_ROOT="$PRIVATE_WORKSPACES_LINK" \
    PROBLEM="$problem" MODULE="$module" \
    TURN="$turn" LOOP_STAMP="$LOOP_STAMP" OUTPUT="$output" python3 - <<'PY'
from pathlib import Path
import os
import subprocess

workspace = Path(os.environ["WORKSPACE"])
guest_workspace = Path(os.environ["GUEST_WORKSPACES_ROOT"]) / workspace.name
problem = os.environ["PROBLEM"]
module = os.environ["MODULE"]
turn = int(os.environ["TURN"])
stamp = os.environ["LOOP_STAMP"]
loop_host = workspace / ".humanize" / "rlcr" / stamp
loop_chroot = guest_workspace / ".humanize" / "rlcr" / stamp
summary = (loop_host / f"round-{turn}-summary.md").read_text()
try:
    history = subprocess.run(
        ["git", "-c", f"safe.directory={workspace}", "-C", str(workspace),
         "log", "--oneline", "--reverse"],
        check=True, text=True, stdout=subprocess.PIPE,
    ).stdout.strip()
except Exception:
    history = "(git history unavailable)"

values = {
    "CURRENT_ROUND": str(turn),
    "PLAN_FILE": str(guest_workspace / "docs/humanize/active-imo2026-plan.md"),
    "PROMPT_FILE": str(loop_chroot / f"round-{turn}-prompt.md"),
    "SUMMARY_CONTENT": summary,
    "GOAL_TRACKER_FILE": str(loop_chroot / "goal-tracker.md"),
    "DOCS_PATH": str(guest_workspace / "docs"),
    "GOAL_TRACKER_UPDATE_SECTION": (
        "The goal tracker is runner-managed. You may update its mutable section, "
        "but you must not edit the candidate proof or immutable acceptance criteria."
    ),
    "COMMIT_HISTORY_SECTION": "## Development History\n\n```\n" + history + "\n```",
    "COMPLETED_ITERATIONS": str(turn),
    "LOOP_TIMESTAMP": stamp,
    "PREV_ROUND": str(max(0, turn - 1)),
    "PREV_PREV_ROUND": str(max(0, turn - 2)),
    "AXLE_VERIFIER": str(guest_workspace / "tools/verify-imo2026-axle.py"),
    "ORIGINAL_FILE": str(guest_workspace / "source/lean4/src" / f"{problem}.lean"),
    "REVIEW_RESULT_FILE": str(loop_chroot / f"round-{turn}-review-result.md"),
}

text = Path(os.environ["TEMPLATE"]).read_text()
for key, value in values.items():
    text = text.replace("{{" + key + "}}", value)
text = text.replace("<candidate-file>", f"MathFlowBench/{module}.lean")
text = text.replace("PROBLEM_ID", problem)
prefix = f"""# Isolated Blind IMO 2026 Reviewer\n\n
You are Codex reviewing `{problem}` in a sanitized filesystem. References to
the worker in the inherited Humanize template mean the blind Kimi Code proof worker.

- Use Codex model $CODEX_MODEL with $CODEX_REASONING_EFFORT reasoning effort.
- Do not inspect Kimi or Codex sessions, prior experiments, other worktrees, or existing solutions.
- Do not use web search or any external network resource except the AXLE call
  made by `{guest_workspace}/tools/verify-imo2026-axle.py`.
- The proof file is mounted read-only. Never modify it.
- Compile with `cd {guest_workspace} && lake env lean MathFlowBench/{module}.lean`.
- The original is `{guest_workspace}/source/lean4/src/{problem}.lean`.
- AXLE evidence is valid only when `{guest_workspace}/tools/verify-imo2026-axle.py` reports
  a Boolean `okay: true` for the exact candidate and original hashes.

"""
Path(os.environ["OUTPUT"]).write_text(prefix + text)
PY
}

kimi_error_text() {
  local file="$1"
  if [[ "$file" == *.jsonl ]]; then
    jq -r '
      select(.role == "error" or .type == "error" or .type == "turn.failed") |
      .message // .content // .error.message // .item.message // empty
    ' "$file" 2>/dev/null
  else
    cat "$file"
  fi
}

rate_error_in() {
  local file
  for file in "$@"; do
    [[ -f "$file" ]] || continue
    if kimi_error_text "$file" | rg -qi "(HTTP([[:space:]_-]+status)?[^0-9]{0,20}(429|529)|status(_code)?[\\\"':= ]+(429|529)|too many requests|rate[ _-]*limit|request rate limit|upstream.*overload|overloaded.*(429|529))"; then
      return 0
    fi
  done
  return 1
}

quota_error_in() {
  local file
  for file in "$@"; do
    [[ -f "$file" ]] || continue
    if kimi_error_text "$file" | rg -qi \
      "(HTTP[^0-9]{0,20}403|status(_code)?[\"':= ]+403).*(usage limit|billing cycle|quota|purchase extra usage|upgrade your plan)|(usage limit|billing cycle|quota exhausted).*(403|purchase extra usage|upgrade your plan)"; then
      return 0
    fi
  done
  return 1
}

transient_error_in() {
  local file
  for file in "$@"; do
    [[ -f "$file" ]] || continue
    if kimi_error_text "$file" | rg -qi "(stream disconnected|error sending request|connection (reset|closed|refused)|temporar(il)?y unavailable|timed? out|selected model is at capacity|model[^.\n]{0,40}at capacity|HTTP[^0-9]{0,20}(408|500|502|503|504)|status(_code)?[\\\"':= ]+(408|500|502|503|504))"; then
      return 0
    fi
  done
  return 1
}

record_rate_error() {
  local problem="$1" role="$2" turn="$3" attempt="$4"
  touch "$RATE_FLAG"
  {
    flock 9
    printf '%s\t%s\t%s\t%s\t%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      "$problem" "$role" "$turn" "$attempt" >> "$RATE_LOG"
  } 9>"$RUN_ROOT/rate.lock"
}

record_quota_error() {
  local problem="$1" role="$2" turn="$3" attempt="$4"
  touch "$QUOTA_FLAG"
  {
    flock 9
    if [[ ! -s "$QUOTA_LOG" ]]; then
      printf 'timestamp\tproblem\trole\tturn\tattempt\n' > "$QUOTA_LOG"
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      "$problem" "$role" "$turn" "$attempt" >> "$QUOTA_LOG"
  } 9>"$RUN_ROOT/quota.lock"
}

record_transport_failure() {
  local problem="$1" role="$2" turn="$3" attempt="$4" code="$5"
  touch "$INFRA_FLAG"
  {
    flock 9
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      "$problem" "$role" "$turn" "$attempt" "$code" >> "$INFRA_LOG"
  } 9>"$RUN_ROOT/infra.lock"
}

record_sessions() {
  local job_dir="$1" problem="$2" role="$3" turn="$4" attempt="$5"
  local kimi_home="$6" marker="$7" events="$8" final="$9"
  local thread_id session_file
  thread_id="$(jq -r '
    select(.role == "meta" and .type == "session.resume_hint") |
    .session_id // empty
  ' "$events" 2>/dev/null | head -n 1)"
  [[ -n "$thread_id" ]] || \
    thread_id="$(jq -r 'select(.type == "thread.started") | .thread_id // empty' "$events" 2>/dev/null | head -n 1)"
  [[ -n "$thread_id" ]] || thread_id="$(rg -o 'session id: [0-9a-f-]+' "$events" 2>/dev/null | head -n1 | awk '{print $3}')"
  [[ -n "$thread_id" ]] || thread_id="unknown"

  mapfile -t new_sessions < <(find "$kimi_home/sessions" -type f -name '*.jsonl' -newer "$marker" -print 2>/dev/null | sort)
  if [[ "${#new_sessions[@]}" -eq 0 ]]; then
    new_sessions=("")
  fi
  for session_file in "${new_sessions[@]}"; do
    {
      flock 9
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$problem" "$role" "$turn" "$attempt" \
        "$thread_id" "$events" "$final" "$session_file" >> "$KIMI_SESSIONS"
      printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$role" "$turn" "$attempt" \
        "$thread_id" "$events" "$session_file" >> "$job_dir/sessions.tsv"
    } 9>"$RUN_ROOT/sessions.lock"
  done
}

run_kimi_namespace_once() {
  local role="$1" workspace="$2" kimi_home="$3" prompt_rel="$4"
  local events="$5" stderr_log="$6" final_rel="$7" nsroot="$8"
  local module="$9" timeout_seconds="${10}"
  local user guest_workspace guest_kimi_home kimi_home_rel prompt_text exit_code=0
  local -a proot_args
  : "$nsroot" "$module"
  user="${HUMANIZE_USER_PREFIX}-$(printf '%s' "${module#IMO2026}" | tr '[:upper:]' '[:lower:]')"
  guest_workspace="$PRIVATE_WORKSPACES_LINK/$(basename "$workspace")"
  kimi_home_rel="${kimi_home#"$KIMI_RUN_HOME"/}"
  [[ "$kimi_home_rel" != "$kimi_home" ]] || die "Kimi home is outside this run: $kimi_home"
  guest_kimi_home="$PRIVATE_AGENT_HOMES_LINK/$kimi_home_rel"
  prompt_text="$(<"$workspace/$prompt_rel")"

  chown "$user:$user" "$workspace/.lake"
  chown -R "$user:$user" \
    "$workspace/.humanize" "$workspace/.lake/build" "$workspace/home" "$kimi_home"
  if [[ "$role" == worker ]]; then
    chown -R "$user:$user" "$workspace/MathFlowBench"
  else
    chown -R root:root "$workspace/MathFlowBench"
    chmod 0755 "$workspace/MathFlowBench"
    chmod 0644 "$workspace/MathFlowBench/$module.lean"
  fi

  proot_args=(
    -r "$PROOT_ROOT"
    -b /usr -b /etc -b /dev -b /proc -b /sys
    -b "$KIMI_BIN:/usr/local/bin/kimi!"
    -b "$WORKSPACES_ROOT:$PRIVATE_WORKSPACES_LINK!"
    -b "$KIMI_RUN_HOME:$PRIVATE_AGENT_HOMES_LINK!"
    -b "$PROOT_ROOT/checker-tools:$PRIVATE_CHECKER_TOOLS_LINK!"
    -w "$guest_workspace"
  )
  if [[ "$role" == worker ]]; then
    proot_args+=(-b "$PROOT_ROOT/worker-shell/bash:/bin/bash!")
  fi

  (
    cd "$workspace"
    setpriv --reuid="$user" --regid="$user" --init-groups \
      /usr/bin/proot "${proot_args[@]}" \
      /usr/bin/env -i \
        HOME="$guest_workspace/home" USER="$user" KIMI_CODE_HOME="$guest_kimi_home" \
        ELAN_HOME=/root/.elan PATH=/root/.elan/bin:/usr/local/bin:/usr/bin:/bin \
        SHELL=/bin/bash TMPDIR="$guest_kimi_home/tmp" TERM=dumb \
        HUMANIZE_SHELL_AUDIT=/worker-shell/invocations.log \
        HUMANIZE_NONET_LIB=/worker-shell/libhumanize-nonet.so \
        HUMANIZE_REAL_BASH=/worker-shell/bash.real \
        HUMANIZE_WORKSPACE="$guest_workspace" \
        COMPARATOR_BIN=/comparator-tools/comparator \
        LEAN4EXPORT_BIN="$PRIVATE_CHECKER_TOOLS_LINK/lean4export" \
        LANDRUN_BIN=/comparator-tools/landrun \
        PYTHONDONTWRITEBYTECODE=1 \
      timeout --foreground "$timeout_seconds" \
        /usr/local/bin/kimi \
          --model "$KIMI_MODEL" \
          --skills-dir "$guest_kimi_home/empty-skills" \
          --prompt "$prompt_text" \
          --output-format stream-json \
          > "$events" 2> "$stderr_log"
  ) || exit_code="$?"

  jq -rs -r '
    [.[] | select(.role == "assistant") | .content] |
    last // "" |
    if type == "string" then . else tostring end
  ' "$events" > "$workspace/$final_rel" 2>/dev/null || :

  if [[ "$role" == worker ]]; then
    chown -R root:root "$workspace/MathFlowBench"
    chmod 0755 "$workspace/MathFlowBench"
    chmod 0644 "$workspace/MathFlowBench/$module.lean"
  fi
  return "$exit_code"
}

run_kimi_with_retries() {
  local role="$1" workspace="$2" kimi_home="$3" prompt_rel="$4"
  local final_rel="$5" job_dir="$6" problem="$7" module="$8" turn="$9"
  local timeout_seconds="${10}"
  local attempt attempt_base retry_index events stderr_log marker code delay nsroot
  attempt_base="$(find "$job_dir" -maxdepth 1 -type f \
    -name "round-${turn}-${role}-attempt-*.stderr.log" -printf '%f\n' 2>/dev/null | \
    sed -nE 's/.*-attempt-([0-9]+)\.stderr\.log/\1/p' | sort -n | tail -n 1)"
  attempt_base="${attempt_base:-0}"
  for ((retry_index = 1; retry_index <= KIMI_RATE_RETRIES + 1; retry_index++)); do
    attempt=$((attempt_base + retry_index))
    events="$job_dir/round-${turn}-${role}-attempt-${attempt}.events.jsonl"
    stderr_log="$job_dir/round-${turn}-${role}-attempt-${attempt}.stderr.log"
    marker="$job_dir/round-${turn}-${role}-attempt-${attempt}.session-marker"
    nsroot="$RUN_ROOT/nsroot/$(basename "$job_dir")-$role"
    touch "$marker"
    code=0
    run_kimi_namespace_once "$role" "$workspace" "$kimi_home" "$prompt_rel" \
      "$events" "$stderr_log" "$final_rel" "$nsroot" "$module" "$timeout_seconds" || code="$?"
    record_sessions "$job_dir" "$problem" "$role" "$turn" "$attempt" \
      "$kimi_home" "$marker" "$events" "$workspace/$final_rel"
    if quota_error_in "$events" "$stderr_log"; then
      record_quota_error "$problem" "$role" "$turn" "$attempt"
      return 76
    fi
    if rate_error_in "$events" "$stderr_log"; then
      record_rate_error "$problem" "$role" "$turn" "$attempt"
      if [[ "$retry_index" -le "$KIMI_RATE_RETRIES" ]]; then
        delay=$((30 * (2 ** (retry_index - 1))))
        [[ "$delay" -gt 600 ]] && delay=600
        log "$problem $role turn $turn hit 429/529; retrying in ${delay}s"
        sleep "$delay"
        continue
      fi
      return 75
    fi
    if [[ "$code" -ne 0 ]] && transient_error_in "$events" "$stderr_log"; then
      if [[ "$retry_index" -le "$KIMI_RATE_RETRIES" ]]; then
        delay=$((30 * (2 ** (retry_index - 1))))
        [[ "$delay" -gt 600 ]] && delay=600
        log "$problem $role turn $turn hit a transient transport failure; retrying in ${delay}s"
        sleep "$delay"
        continue
      fi
      record_transport_failure "$problem" "$role" "$turn" "$attempt" "$code"
      return "$code"
    fi
    if [[ "$code" -ne 0 ]]; then
      record_transport_failure "$problem" "$role" "$turn" "$attempt" "$code"
    fi
    return "$code"
  done
  return 75
}

codex_error_text() {
  local file="$1"
  if [[ "$file" == *.jsonl ]]; then
    jq -r '
      select(.type == "error" or .type == "turn.failed") |
      .message // .error.message // .item.message // empty
    ' "$file" 2>/dev/null
  else
    cat "$file"
  fi
}

codex_rate_error_in() {
  local file
  for file in "$@"; do
    [[ -f "$file" ]] || continue
    if codex_error_text "$file" | rg -qi "(HTTP([[:space:]_-]+status)?[^0-9]{0,20}(429|529)|status(_code)?[\\\"':= ]+(429|529)|too many requests|rate[ _-]*limit|request rate limit|upstream.*overload|overloaded.*(429|529))"; then
      return 0
    fi
  done
  return 1
}

codex_transient_error_in() {
  local file
  for file in "$@"; do
    [[ -f "$file" ]] || continue
    if codex_error_text "$file" | rg -qi "(stream disconnected|error sending request|connection (reset|closed|refused)|temporar(il)?y unavailable|timed? out|selected model is at capacity|model[^.\n]{0,40}at capacity|HTTP[^0-9]{0,20}(408|500|502|503|504)|status(_code)?[\\\"':= ]+(408|500|502|503|504))"; then
      return 0
    fi
  done
  return 1
}

record_codex_sessions() {
  local job_dir="$1" problem="$2" role="$3" turn="$4" attempt="$5"
  local codex_home="$6" marker="$7" events="$8" final="$9"
  local thread_id session_file
  thread_id="$(jq -r 'select(.type == "thread.started") | .thread_id // empty' \
    "$events" 2>/dev/null | head -n 1)"
  [[ -n "$thread_id" ]] || thread_id="unknown"

  mapfile -t new_sessions < <(find "$codex_home/sessions" -type f \
    -name '*.jsonl' -newer "$marker" -print 2>/dev/null | sort)
  if [[ "${#new_sessions[@]}" -eq 0 ]]; then
    new_sessions=("")
  fi
  for session_file in "${new_sessions[@]}"; do
    {
      flock 9
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$problem" "$role" "$turn" "$attempt" \
        "$thread_id" "$events" "$final" "$session_file" >> "$CODEX_SESSIONS"
      printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$role" "$turn" "$attempt" \
        "$thread_id" "$events" "$session_file" >> "$job_dir/codex-sessions.tsv"
    } 9>"$RUN_ROOT/sessions.lock"
  done
}

run_codex_namespace_once() {
  local workspace="$1" codex_home="$2" prompt_rel="$3"
  local events="$4" stderr_log="$5" final_rel="$6" module="$7"
  local timeout_seconds="$8"
  local user guest_workspace guest_codex_home codex_home_rel codex_js node_bin
  local -a proot_args
  user="${HUMANIZE_USER_PREFIX}-$(printf '%s' "${module#IMO2026}" | tr '[:upper:]' '[:lower:]')"
  guest_workspace="$PRIVATE_WORKSPACES_LINK/$(basename "$workspace")"
  codex_home_rel="${codex_home#"$CODEX_RUN_HOME"/}"
  [[ "$codex_home_rel" != "$codex_home" ]] || die "Codex home is outside this run: $codex_home"
  guest_codex_home="$PRIVATE_CODEX_HOMES_LINK/$codex_home_rel"
  codex_js="$(codex_binary)"
  node_bin="$(node_binary)"

  chown -R "$user:$user" "$workspace/.humanize" "$workspace/.lake/build" \
    "$workspace/home" "$codex_home"
  chown -R root:root "$workspace/MathFlowBench"
  chmod 0755 "$workspace/MathFlowBench"
  chmod 0444 "$workspace/MathFlowBench/$module.lean"

  proot_args=(
    -r "$PROOT_ROOT"
    -b /usr -b /etc -b /dev -b /proc -b /sys
    -b "$WORKSPACES_ROOT:$PRIVATE_WORKSPACES_LINK!"
    -b "$CODEX_RUN_HOME:$PRIVATE_CODEX_HOMES_LINK!"
    -b "$PROOT_ROOT/checker-tools:$PRIVATE_CHECKER_TOOLS_LINK!"
    -w "$guest_workspace"
  )

  (
    cd "$workspace"
    setpriv --reuid="$user" --regid="$user" --init-groups \
      /usr/bin/proot "${proot_args[@]}" \
      /usr/bin/env -i \
        HOME="$guest_workspace/home" USER="$user" CODEX_HOME="$guest_codex_home" \
        ELAN_HOME=/root/.elan \
        PATH=/root/.elan/bin:/usr/local/share/nvm/versions/node/v24.18.0/bin:/usr/local/bin:/usr/bin:/bin \
        SHELL=/bin/bash TMPDIR="$guest_codex_home/tmp" TERM=dumb \
        PYTHONDONTWRITEBYTECODE=1 \
      timeout --foreground "$timeout_seconds" \
        "$node_bin" "$codex_js" --ask-for-approval never exec \
          --cd "$guest_workspace" --skip-git-repo-check --model "$CODEX_MODEL" \
          --sandbox danger-full-access --json \
          --disable browser_use \
          --disable browser_use_external \
          --disable browser_use_full_cdp_access \
          --disable in_app_browser \
          --disable search_tool \
          --disable standalone_web_search \
          --disable hooks \
          -c model_reasoning_effort="\"$CODEX_REASONING_EFFORT\"" \
          -c network_access='"enabled"' \
          -c disable_response_storage=true \
          -c shell_environment_policy.inherit='"all"' \
          -o "$guest_workspace/$final_rel" \
          - < "$workspace/$prompt_rel"
  ) > "$events" 2> "$stderr_log"
}

run_codex_with_retries() {
  local workspace="$1" codex_home="$2" prompt_rel="$3" final_rel="$4"
  local job_dir="$5" problem="$6" module="$7" turn="$8" timeout_seconds="$9"
  local attempt attempt_base retry_index events stderr_log marker code delay
  attempt_base="$(find "$job_dir" -maxdepth 1 -type f \
    -name "round-${turn}-reviewer-attempt-*.stderr.log" -printf '%f\n' 2>/dev/null | \
    sed -nE 's/.*-attempt-([0-9]+)\.stderr\.log/\1/p' | sort -n | tail -n 1)"
  attempt_base="${attempt_base:-0}"
  for ((retry_index = 1; retry_index <= CODEX_RATE_RETRIES + 1; retry_index++)); do
    attempt=$((attempt_base + retry_index))
    events="$job_dir/round-${turn}-reviewer-attempt-${attempt}.events.jsonl"
    stderr_log="$job_dir/round-${turn}-reviewer-attempt-${attempt}.stderr.log"
    marker="$job_dir/round-${turn}-reviewer-attempt-${attempt}.session-marker"
    touch "$marker"
    code=0
    run_codex_namespace_once "$workspace" "$codex_home" "$prompt_rel" \
      "$events" "$stderr_log" "$final_rel" "$module" "$timeout_seconds" || code="$?"
    record_codex_sessions "$job_dir" "$problem" reviewer "$turn" "$attempt" \
      "$codex_home" "$marker" "$events" "$workspace/$final_rel"
    if codex_rate_error_in "$events" "$stderr_log"; then
      record_rate_error "$problem" reviewer "$turn" "$attempt"
      if [[ "$retry_index" -le "$CODEX_RATE_RETRIES" ]]; then
        delay=$((30 * (2 ** (retry_index - 1))))
        [[ "$delay" -gt 600 ]] && delay=600
        log "$problem Codex reviewer turn $turn hit 429/529; retrying in ${delay}s"
        sleep "$delay"
        continue
      fi
      return 75
    fi
    if [[ "$code" -ne 0 ]] && codex_transient_error_in "$events" "$stderr_log"; then
      if [[ "$retry_index" -le "$CODEX_RATE_RETRIES" ]]; then
        delay=$((30 * (2 ** (retry_index - 1))))
        [[ "$delay" -gt 600 ]] && delay=600
        log "$problem Codex reviewer turn $turn hit a transient failure; retrying in ${delay}s"
        sleep "$delay"
        continue
      fi
      record_transport_failure "$problem" reviewer "$turn" "$attempt" "$code"
      return "$code"
    fi
    if [[ "$code" -ne 0 ]]; then
      record_transport_failure "$problem" reviewer "$turn" "$attempt" "$code"
    fi
    return "$code"
  done
  return 75
}

commit_candidate_round() {
  local workspace="$1" problem="$2" turn="$3"
  if [[ -n "$(git -c safe.directory="$workspace" -C "$workspace" status --porcelain -- MathFlowBench)" ]]; then
    git -c safe.directory="$workspace" -C "$workspace" add MathFlowBench
    git -c safe.directory="$workspace" -C "$workspace" commit -q -m "Round $turn candidate for $problem"
  fi
}

review_is_complete() {
  local workspace="$1" turn="$2"
  local loop_dir="$workspace/.humanize/rlcr/$LOOP_STAMP"
  local result="$loop_dir/round-${turn}-review-result.md"
  local axle="$result.axle.json"
  local candidate original candidate_sha original_sha
  [[ -s "$result" ]] || return 1
  [[ "$(awk 'NF{line=$0} END{print line}' "$result")" == "COMPLETE" ]] || return 1
  candidate="$(find "$workspace/MathFlowBench" -maxdepth 1 -type f \
    -name 'IMO2026Q*.lean' -print -quit)"
  original="$(find "$workspace/source/lean4/src" -maxdepth 1 -type f \
    -name 'imo2026_q*.lean' -print -quit)"
  [[ -n "$candidate" && -n "$original" ]] || return 1
  candidate_sha="$(sha256sum "$candidate" | awk '{print $1}')"
  original_sha="$(sha256sum "$original" | awk '{print $1}')"
  jq -e --arg candidate_sha "$candidate_sha" --arg original_sha "$original_sha" '
    .all_okay == true and
    (.results | length > 0) and
    all(.results[];
      .okay == true and
      .status == "correct" and
      .http_status == 200 and
      (.request_id | type == "string" and length > 0) and
      .environment == "lean-4.31.0" and
      .candidate_sha256 == $candidate_sha and
      .original_sha256 == $original_sha
    )
  ' "$axle" >/dev/null 2>&1
}

axle_infrastructure_failed() {
  local workspace="$1" turn="$2"
  local result="$workspace/.humanize/rlcr/$LOOP_STAMP/round-${turn}-review-result.md"
  local axle="$result.axle.json"
  [[ -f "$axle" ]] || return 0
  jq -e 'any(.results[]?; .status == "api_error")' "$axle" >/dev/null 2>&1
}

run_job() {
  local index="$1" problem="$2" end_turn="$3"
  local module safe workspace job_dir worker_home reviewer_home loop_dir
  local turn feedback worker_prompt_rel worker_final_rel check_log check_code
  local review_prompt_rel review_final_rel review_result review_try code status start end
  module="$(module_name "$problem")"
  safe="$(safe_name "$problem")"
  workspace="$WORKSPACES_ROOT/j${index}-${safe}"
  job_dir="$RUN_ROOT/jobs/j${index}-${safe}"
  worker_home="$KIMI_RUN_HOME/j${index}-${safe}/worker"
  reviewer_home="$CODEX_RUN_HOME/j${index}-${safe}/reviewer"
  loop_dir="$workspace/.humanize/rlcr/$LOOP_STAMP"

  if [[ "$(cat "$job_dir/status.txt" 2>/dev/null || true)" == passed ]]; then
    return 0
  fi
  turn="$(cat "$job_dir/next-turn.txt")"
  feedback=""
  if [[ "$turn" -gt 1 ]]; then
    local previous_review="$loop_dir/round-$((turn - 1))-review-result.md"
    local previous_summary="$loop_dir/round-$((turn - 1))-summary.md"
    if [[ -s "$previous_review" ]]; then
      feedback="$previous_review"
    elif [[ -s "$previous_summary" ]]; then
      # A worker-only recovery can resume the same turn after quota, timeout,
      # or transport failure without a Codex review ever having run. Preserve
      # the deterministic worker summary instead of silently dropping the
      # previous round's mathematical and local-check context.
      feedback="$previous_summary"
    fi
  fi
  start="$(date +%s)"
  status="pending"

  while [[ "$turn" -le "$end_turn" && "$turn" -le "$MAX_TURNS" ]]; do
    printf 'worker_turn_%s\n' "$turn" > "$job_dir/status.txt"
    write_worker_prompt "$workspace" "$problem" "$module" "$turn" "$feedback"
    worker_prompt_rel=".humanize/rlcr/$LOOP_STAMP/round-${turn}-prompt.md"
    worker_final_rel=".humanize/rlcr/$LOOP_STAMP/round-${turn}-worker-final.md"
    code=0
    run_kimi_with_retries worker "$workspace" "$worker_home" "$worker_prompt_rel" \
      "$worker_final_rel" "$job_dir" "$problem" "$module" "$turn" \
      "$WORKER_TIMEOUT_SECONDS" || code="$?"
    if [[ "$code" -eq 75 ]]; then
      status="worker_rate_limited"
      break
    fi
    if [[ "$code" -eq 76 ]]; then
      status="worker_quota_exhausted"
      break
    fi
    if [[ "$code" -eq 124 ]]; then
      status="worker_timeout"
      break
    elif [[ "$code" -ne 0 ]]; then
      status="worker_transport_failed"
      break
    fi

    commit_candidate_round "$workspace" "$problem" "$turn"
    check_log="$job_dir/round-${turn}-local-checks.log"
    check_code=0
    local_checks "$workspace" "$problem" "$module" "$check_log" || check_code="$?"
    write_summary "$workspace" "$problem" "$module" "$turn" "$check_code" \
      "$check_log" "$workspace/$worker_final_rel"

    # The reviewer only evaluates candidates that have passed every deterministic
    # local gate, including the real Landrun-backed Comparator replay.
    if [[ "$check_code" -ne 0 ]]; then
      feedback="$loop_dir/round-${turn}-summary.md"
      turn=$((turn + 1))
      printf '%s\n' "$turn" > "$job_dir/next-turn.txt"
      status="pending"
      continue
    fi

    printf 'review_turn_%s\n' "$turn" > "$job_dir/status.txt"
    render_review_prompt "$workspace" "$problem" "$module" "$turn"
    review_prompt_rel=".humanize/rlcr/$LOOP_STAMP/round-${turn}-review-prompt.md"
    review_final_rel=".humanize/rlcr/$LOOP_STAMP/round-${turn}-reviewer-final.md"
    review_result="$loop_dir/round-${turn}-review-result.md"
    review_try=1
    while [[ "$REVIEW_INFRA_RETRIES" -eq 0 || "$review_try" -le "$REVIEW_INFRA_RETRIES" ]]; do
      code=0
      run_codex_with_retries "$workspace" "$reviewer_home" "$review_prompt_rel" \
        "$review_final_rel" "$job_dir" "$problem" "$module" "$turn" \
        "$REVIEW_TIMEOUT_SECONDS" || code="$?"
      if [[ ! -s "$review_result" && -s "$workspace/$review_final_rel" ]]; then
        cp "$workspace/$review_final_rel" "$review_result"
      fi
      if [[ "$code" -eq 75 ]]; then
        status="reviewer_rate_limited"
        break 2
      fi
      if [[ "$code" -eq 76 ]]; then
        status="reviewer_quota_exhausted"
        break 2
      fi
      if [[ "$code" -eq 124 ]]; then
        status="reviewer_timeout"
        break 2
      elif [[ "$code" -ne 0 ]]; then
        status="reviewer_transport_failed"
        break 2
      fi
      if axle_infrastructure_failed "$workspace" "$turn"; then
        if [[ "$REVIEW_INFRA_RETRIES" -eq 0 || "$review_try" -lt "$REVIEW_INFRA_RETRIES" ]]; then
          local review_delay=$((60 * review_try))
          [[ "$review_delay" -gt 600 ]] && review_delay=600
          log "$problem reviewer turn $turn has unavailable AXLE result; retrying review"
          sleep "$review_delay"
          review_try=$((review_try + 1))
          continue
        fi
        status="review_infrastructure_failed"
        break 2
      fi
      break
    done

    if [[ "$check_code" -eq 0 ]] && review_is_complete "$workspace" "$turn"; then
      status="passed"
      printf 'passed\n' > "$job_dir/status.txt"
      printf '%s\n' "$turn" > "$job_dir/completed-turn.txt"
      sha256sum "$workspace/MathFlowBench/$module.lean" > "$job_dir/candidate.sha256"
      break
    fi

    feedback="$review_result"
    turn=$((turn + 1))
    printf '%s\n' "$turn" > "$job_dir/next-turn.txt"
    status="pending"
  done

  if [[ "$status" == pending && "$turn" -gt "$MAX_TURNS" ]]; then
    status="max_turns_reached"
  fi
  printf '%s\n' "$status" > "$job_dir/status.txt"
  end="$(date +%s)"
  {
    flock 9
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$RUN_ID" "j${index}-${safe}" \
      "$problem" "$module" "$status" "$turn" "$((end - start))" >> "$METRICS"
  } 9>"$RUN_ROOT/metrics.lock"
  [[ "$status" == passed || "$status" == pending ]]
}

resume_worker_job() {
  local problem="$1"
  local safe job_dir job_name index current_status worker_home reviewer_home
  safe="$(safe_name "$problem")"
  job_dir="$(find "$RUN_ROOT/jobs" -mindepth 1 -maxdepth 1 -type d \
    -name "*-$safe" -print -quit)"
  [[ -n "$job_dir" ]] || die "worker recovery job not found for $problem"
  job_name="$(basename "$job_dir")"
  index="${job_name%%-*}"
  index="${index#j}"
  worker_home="$KIMI_RUN_HOME/$job_name/worker"
  reviewer_home="$CODEX_RUN_HOME/$job_name/reviewer"
  if [[ ! -s "$worker_home/config.toml" ]]; then
    hydrate_kimi_home "$worker_home" worker
  fi
  # Recovery can happen after the base Codex credential has been refreshed.
  # Always rehydrate the dormant reviewer home so retries do not retain an
  # obsolete account indefinitely.  This preserves sessions and only replaces
  # runner-managed authentication/configuration files.
  hydrate_codex_home "$reviewer_home"
  current_status="$(head -1 "$job_dir/status.txt" 2>/dev/null || true)"
  case "$current_status" in
    worker_rate_limited|worker_quota_exhausted|worker_timeout|worker_transport_failed)
      ;;
    *) die "$problem is not in a recoverable worker state: $current_status" ;;
  esac

  log "worker-only recovery for $problem from turn $(cat "$job_dir/next-turn.txt")"
  run_job "$index" "$problem" "$MAX_TURNS"
}

resume_review_job() {
  local problem="$1"
  local safe module job_dir job_name index workspace reviewer_home loop_dir turn
  local current_status review_prompt_rel review_final_rel review_result review_try
  local review_delay code status check_log check_code start end
  safe="$(safe_name "$problem")"
  module="$(module_name "$problem")"
  job_dir="$(find "$RUN_ROOT/jobs" -mindepth 1 -maxdepth 1 -type d \
    -name "*-$safe" -print -quit)"
  [[ -n "$job_dir" ]] || die "review recovery job not found for $problem"
  job_name="$(basename "$job_dir")"
  index="${job_name%%-*}"
  index="${index#j}"
  workspace="$WORKSPACES_ROOT/$job_name"
  reviewer_home="$CODEX_RUN_HOME/$job_name/reviewer"
  # See resume_worker_job: recovery must use the current configured Codex
  # identity, rather than whichever credential happened to seed this run.
  hydrate_codex_home "$reviewer_home"
  loop_dir="$workspace/.humanize/rlcr/$LOOP_STAMP"
  current_status="$(head -1 "$job_dir/status.txt" 2>/dev/null || true)"
  case "$current_status" in
    review_infrastructure_failed|reviewer_timeout|reviewer_transport_failed|reviewer_rate_limited|reviewer_quota_exhausted)
      ;;
    review_turn_[0-9]*)
      ;;
    *) die "$problem is not in a recoverable reviewer state: $current_status" ;;
  esac

  turn="$(cat "$job_dir/next-turn.txt")"
  review_prompt_rel=".humanize/rlcr/$LOOP_STAMP/round-${turn}-review-prompt.md"
  review_final_rel=".humanize/rlcr/$LOOP_STAMP/round-${turn}-reviewer-final.md"
  review_result="$loop_dir/round-${turn}-review-result.md"
  [[ -s "$workspace/$review_prompt_rel" ]] || \
    die "review recovery prompt missing for $problem turn $turn"
  [[ -s "$loop_dir/round-${turn}-summary.md" ]] || \
    die "review recovery summary missing for $problem turn $turn"

  # Revalidate before a recovered reviewer is launched. Older runner versions
  # could enter review recovery even when the local Comparator gate had failed.
  check_log="$job_dir/round-${turn}-local-checks.log"
  check_code=0
  local_checks "$workspace" "$problem" "$module" "$check_log" || check_code="$?"
  write_summary "$workspace" "$problem" "$module" "$turn" "$check_code" \
    "$check_log" "$loop_dir/round-${turn}-worker-final.md"
  if [[ "$check_code" -ne 0 ]]; then
    turn=$((turn + 1))
    printf '%s\n' "$turn" > "$job_dir/next-turn.txt"
    log "$problem failed the local gate during review recovery; resuming worker turn $turn"
    run_job "$index" "$problem" "$MAX_TURNS"
    return $?
  fi

  start="$(date +%s)"
  status="pending"
  review_try=1
  printf 'review_turn_%s\n' "$turn" > "$job_dir/status.txt"
  while [[ "$REVIEW_INFRA_RETRIES" -eq 0 || "$review_try" -le "$REVIEW_INFRA_RETRIES" ]]; do
    code=0
    run_codex_with_retries "$workspace" "$reviewer_home" "$review_prompt_rel" \
      "$review_final_rel" "$job_dir" "$problem" "$module" "$turn" \
      "$REVIEW_TIMEOUT_SECONDS" || code="$?"
    if [[ ! -s "$review_result" && -s "$workspace/$review_final_rel" ]]; then
      cp "$workspace/$review_final_rel" "$review_result"
    fi
    if [[ "$code" -eq 75 ]]; then
      status="reviewer_rate_limited"
      break
    elif [[ "$code" -eq 76 ]]; then
      status="reviewer_quota_exhausted"
      break
    elif [[ "$code" -eq 124 ]]; then
      status="reviewer_timeout"
      break
    elif [[ "$code" -ne 0 ]]; then
      status="reviewer_transport_failed"
      break
    fi
    if axle_infrastructure_failed "$workspace" "$turn"; then
      if [[ "$REVIEW_INFRA_RETRIES" -eq 0 || "$review_try" -lt "$REVIEW_INFRA_RETRIES" ]]; then
        review_delay=$((60 * review_try))
        [[ "$review_delay" -gt 600 ]] && review_delay=600
        log "$problem reviewer turn $turn remains unavailable; retrying unchanged candidate"
        sleep "$review_delay"
        review_try=$((review_try + 1))
        continue
      fi
      status="review_infrastructure_failed"
    fi
    break
  done

  if [[ "$status" != pending ]]; then
    printf '%s\n' "$status" > "$job_dir/status.txt"
    return 1
  fi

  check_log="$job_dir/round-${turn}-local-checks.log"
  check_code=0
  local_checks "$workspace" "$problem" "$module" "$check_log" || check_code="$?"
  if [[ "$check_code" -eq 0 ]] && review_is_complete "$workspace" "$turn"; then
    status="passed"
    printf 'passed\n' > "$job_dir/status.txt"
    printf '%s\n' "$turn" > "$job_dir/completed-turn.txt"
    sha256sum "$workspace/MathFlowBench/$module.lean" > "$job_dir/candidate.sha256"
    end="$(date +%s)"
    {
      flock 9
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$RUN_ID" "$job_name" \
        "$problem" "$module" "$status" "$turn" "$((end - start))" >> "$METRICS"
    } 9>"$RUN_ROOT/metrics.lock"
    return 0
  fi

  turn=$((turn + 1))
  printf '%s\n' "$turn" > "$job_dir/next-turn.txt"
  log "$problem review recovery returned a Boolean rejection; resuming worker turn $turn"
  run_job "$index" "$problem" "$MAX_TURNS"
}

write_run_manifest() {
  local count="$1" source_sha kimi_version codex_version
  source_sha="$(sha256sum "$IMO2026_SOURCE_ROOT"/Q[1-6]/problem.lean | sha256sum | awk '{print $1}')"
  kimi_version="$("$KIMI_BIN" --version)"
  codex_version="$(codex --version)"
  cat > "$RUN_ROOT/RUN.md" <<EOF
# IMO 2026 Humanize + Comparator + AXLE Run

- Run ID: \`$RUN_ID\`
- Failure source: \`$FAILURE_FILE\`
- Problems: $count
- Problem source: \`$IMO2026_SOURCE_ROOT/Q1..Q6/problem.lean\`
- Combined problem-source SHA-256: \`$source_sha\`
- Upstream repository commit: \`c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2\`
- Worker: \`Kimi Code CLI $kimi_version\`, model \`$KIMI_MODEL\`
- Worker model ID: \`k3\`; thinking mode: enabled
- Reviewer: \`$codex_version\`, model \`$CODEX_MODEL\`,
  reasoning effort \`$CODEX_REASONING_EFFORT\`
- Maximum turns: $MAX_TURNS
- Requested main concurrency: $JOBS
- Rate-limited fallback concurrency: $FALLBACK_JOBS
- Base Kimi Code home: \`$BASE_KIMI_HOME\`
- Per-job Kimi Code homes: \`$KIMI_RUN_HOME\`
- Base Codex home: \`$BASE_CODEX_HOME\`
- Per-job Codex reviewer homes: \`$CODEX_RUN_HOME\`
- Run-scoped guest workspace path: \`$PRIVATE_WORKSPACES_LINK\`
- Run-scoped guest Kimi home path: \`$PRIVATE_AGENT_HOMES_LINK\`
- Run-scoped guest Codex home path: \`$PRIVATE_CODEX_HOMES_LINK\`
- Solver network: blocked by the enforced socket-denial worker shell
- Worker self-check: current Comparator, target-version lean4export, and real Landrun
- Reviewer network: permitted only for the prompted AXLE verifier call
- Existing solutions: not mounted into either model namespace

All prompts, event streams, final messages, session paths, reviews, compilation
logs, Comparator output, AXLE JSON, hashes, and status files are retained under this run directory.
EOF
}

main() {
  local command selected problem index missing active limit total probe_n user question
  for command in awk bash cc chmod chown cmp codex date find flock getent git jq lake node proot ps python3 readlink rg setpriv sha256sum timeout; do
    need_cmd "$command"
  done
  [[ -f "$FAILURE_FILE" ]] || die "failure file not found: $FAILURE_FILE"
  [[ -d "$IMO2026_SOURCE_ROOT" ]] || die "IMO2026 source root not found: $IMO2026_SOURCE_ROOT"
  [[ -f "$BASE_KIMI_HOME/config.toml" ]] || die "Kimi Code config missing: $BASE_KIMI_HOME/config.toml"
  [[ -f "$BASE_CODEX_HOME/config.toml" ]] || die "Codex config missing: $BASE_CODEX_HOME/config.toml"
  [[ -f "$BASE_CODEX_HOME/auth.json" ]] || die "Codex auth missing: $BASE_CODEX_HOME/auth.json"
  [[ -d "$MATH_FLOW_BENCH_ROOT/.lake/packages" ]] || die "Mathlib packages missing"
  [[ -f "$HUMANIZE_ROOT/humanize/prompt-template/kimi/regular-review.md" ]] || die "new review template missing"
  [[ -x "$COMPARATOR_BIN" ]] || die "Comparator binary missing or not executable: $COMPARATOR_BIN"
  [[ -x "$LEAN4EXPORT_BIN" ]] || die "lean4export binary missing or not executable: $LEAN4EXPORT_BIN"
  [[ -x "$LANDRUN_BIN" ]] || die "Landrun binary missing or not executable: $LANDRUN_BIN"
  [[ -x "$HUMANIZE_ROOT/scripts/check-with-comparator.sh" ]] || \
    die "Comparator wrapper missing or not executable"
  [[ -f "$HUMANIZE_ROOT/scripts/validate-imo2026-output.py" ]] || die "statement validator missing"
  [[ -f "$HUMANIZE_ROOT/scripts/verify-imo2026-axle.py" ]] || die "AXLE verifier missing"
  [[ -x "$KIMI_BIN" ]] || die "Kimi Code binary missing or not executable: $KIMI_BIN"
  [[ -d "$LOCAL_RUNTIME_TEMPLATE" ]] || die "local runtime template missing: $LOCAL_RUNTIME_TEMPLATE"
  [[ -d /mathlib-packages ]] || die "/mathlib-packages is not linked to the pinned package cache"
  for question in q1 q2 q3 q4 q5 q6; do
    user="${HUMANIZE_USER_PREFIX}-${question}"
    getent passwd "$user" >/dev/null || die "missing isolated worker account: $user"
  done
  [[ "$KIMI_MODEL" == "kimi-for-coding/k3" ]] || die "this run requires KIMI_MODEL=kimi-for-coding/k3"
  validate_kimi_model_config
  mapfile -t selected < <(parse_failed_problems)
  [[ "${#selected[@]}" -gt 0 ]] || die "no failed problems parsed"
  missing=0
  for problem in "${selected[@]}"; do
    if ! [[ "$problem" =~ ^imo2026_q[1-6]$ ]]; then
      printf 'invalid problem id: %s\n' "$problem" >&2
      missing=$((missing + 1))
    elif [[ ! -s "$IMO2026_SOURCE_ROOT/$(printf '%s' "${problem#imo2026_}" | tr '[:lower:]' '[:upper:]')/problem.lean" ]]; then
      printf 'missing nonempty upstream problem source: %s\n' "$problem" >&2
      missing=$((missing + 1))
    fi
  done
  [[ "$missing" -eq 0 ]] || die "$missing selected IMO2026 problems are unavailable"

  log "run id: $RUN_ID"
  log "selected problems: ${#selected[@]}"
  log "worker: Kimi Code CLI $("$KIMI_BIN" --version), model $KIMI_MODEL, thinking enabled"
  log "reviewer: $(codex --version), model $CODEX_MODEL, effort $CODEX_REASONING_EFFORT"
  log "max turns: $MAX_TURNS"
  if [[ "$DRY_RUN" -eq 1 ]]; then
    printf '%s\n' "${selected[@]}"
    return 0
  fi

  if [[ "$RESUME_WORKER_ONLY" -eq 1 ]]; then
    local existing_stamp
    [[ "${#selected[@]}" -eq 1 ]] || die "worker-only recovery requires exactly one problem"
    [[ -d "$RUN_ROOT/jobs" && -d "$WORKSPACES_ROOT" ]] || \
      die "cannot recover worker in missing run: $RUN_ROOT"
    activate_private_identity_paths
    install_lake_workspace_wrapper
    existing_stamp="$(find "$WORKSPACES_ROOT" -mindepth 4 -maxdepth 4 \
      -type d -path '*/.humanize/rlcr/*' -printf '%f\n' | sort -u | head -n 1)"
    [[ -n "$existing_stamp" ]] || die "cannot locate existing Humanize loop stamp"
    LOOP_STAMP="$existing_stamp"
    log "worker-only recovery for $RUN_ID using loop $LOOP_STAMP"
    resume_worker_job "${selected[0]}"
    return 0
  fi

  if [[ "$RESUME_REVIEW_ONLY" -eq 1 ]]; then
    local existing_stamp
    [[ "${#selected[@]}" -eq 1 ]] || die "review-only recovery requires exactly one problem"
    [[ -d "$RUN_ROOT/jobs" && -d "$WORKSPACES_ROOT" ]] || \
      die "cannot recover review in missing run: $RUN_ROOT"
    activate_private_identity_paths
    install_lake_workspace_wrapper
    existing_stamp="$(find "$WORKSPACES_ROOT" -mindepth 4 -maxdepth 4 \
      -type d -path '*/.humanize/rlcr/*' -printf '%f\n' | sort -u | head -n 1)"
    [[ -n "$existing_stamp" ]] || die "cannot locate existing Humanize loop stamp"
    LOOP_STAMP="$existing_stamp"
    log "review-only recovery for $RUN_ID using loop $LOOP_STAMP"
    resume_review_job "${selected[0]}"
    return 0
  fi

  if [[ "$RESUME_PREPARED" -eq 1 ]]; then
    local existing_stamp status_file job_dir job_name pid current_status stale_active
    local worker_home reviewer_home
    local -a resume_pids=()
    [[ -d "$RUN_ROOT/jobs" && -d "$WORKSPACES_ROOT" ]] || \
      die "cannot resume missing run: $RUN_ROOT"
    activate_private_identity_paths
    install_lake_workspace_wrapper
    existing_stamp="$(find "$WORKSPACES_ROOT" -mindepth 4 -maxdepth 4 \
      -type d -path '*/.humanize/rlcr/*' -printf '%f\n' | sort -u | head -n 1)"
    [[ -n "$existing_stamp" ]] || die "cannot locate existing Humanize loop stamp"
    LOOP_STAMP="$existing_stamp"
    log "resume-prepared for run $RUN_ID using loop $LOOP_STAMP"

    # A controller/model migration can leave worker_turn_* behind after the old
    # process tree has exited. Normalize only that stale state; never take over a
    # workspace while an old PRoot worker is still live.
    stale_active=0
    for problem in "${selected[@]}"; do
      job_dir="$(find "$RUN_ROOT/jobs" -mindepth 1 -maxdepth 1 -type d \
        -name "*-$(safe_name "$problem")" -print -quit)"
      [[ -n "$job_dir" ]] || die "prepared job not found for $problem"
      current_status="$(cat "$job_dir/status.txt" 2>/dev/null || true)"
      [[ "$current_status" =~ ^worker_turn_[0-9]+$ ]] && stale_active=1
    done
    if [[ "$stale_active" -eq 1 ]]; then
      if ps -eo comm=,args= | awk -v root="$PROOT_ROOT" \
          '$1 == "proot" && index($0, root) { found = 1 } END { exit !found }'; then
        die "cannot recover stale worker_turn state while an old PRoot worker is active"
      fi
      for problem in "${selected[@]}"; do
        job_dir="$(find "$RUN_ROOT/jobs" -mindepth 1 -maxdepth 1 -type d \
          -name "*-$(safe_name "$problem")" -print -quit)"
        status_file="$job_dir/status.txt"
        current_status="$(cat "$status_file" 2>/dev/null || true)"
        if [[ "$current_status" =~ ^worker_turn_[0-9]+$ ]]; then
          log "normalizing interrupted $current_status for $problem"
          printf 'pending\n' > "$status_file"
        fi
      done
    fi

    active=0
    for problem in "${selected[@]}"; do
      job_dir="$(find "$RUN_ROOT/jobs" -mindepth 1 -maxdepth 1 -type d \
        -name "*-$(safe_name "$problem")" -print -quit)"
      [[ -n "$job_dir" ]] || die "prepared job not found for $problem"
      job_name="$(basename "$job_dir")"
      index="${job_name%%-*}"
      index="${index#j}"
      status_file="$job_dir/status.txt"
      current_status="$(cat "$status_file" 2>/dev/null || true)"
      if [[ "$current_status" =~ ^(prepared|pending|worker_rate_limited|worker_quota_exhausted|worker_timeout|worker_transport_failed)$ ]]; then
        worker_home="$KIMI_RUN_HOME/$job_name/worker"
        reviewer_home="$CODEX_RUN_HOME/$job_name/reviewer"
        hydrate_kimi_home "$worker_home" worker
        hydrate_codex_home "$reviewer_home"
        while [[ "$(find "$RUN_ROOT/jobs" -name status.txt -type f -exec cat {} + 2>/dev/null | \
            awk '/^(worker_turn_|review_turn_)/ { n++ } END { print n + 0 }')" -ge "$JOBS" ]]; do
          sleep 5
        done
        run_job "$index" "$problem" "$MAX_TURNS" &
        resume_pids+=("$!")
        active=$((active + 1))
        sleep 0.2
      fi
    done
    log "resume-prepared launched $active jobs"
    for pid in "${resume_pids[@]}"; do
      wait "$pid" || true
    done
    log "resume-prepared jobs finished: $RUN_ROOT"
    return 0
  fi

  mkdir -p "$RUN_ROOT"/{jobs,nsroot}
  clone_runtime_template
  activate_private_identity_paths
  install_lake_workspace_wrapper
  ln -sfn "$WORKSPACES_ROOT" "$RUN_ROOT/workspaces"
  ln -sfn "$KIMI_RUN_HOME" "$RUN_ROOT/agent-homes"
  ln -sfn "$CODEX_RUN_HOME" "$RUN_ROOT/codex-homes"
  printf 'timestamp\tproblem\trole\tturn\tattempt\n' > "$RATE_LOG"
  printf 'timestamp\tproblem\trole\tturn\tattempt\n' > "$QUOTA_LOG"
  printf 'timestamp\tproblem\trole\tturn\tattempt\texit_code\n' > "$INFRA_LOG"
  printf 'timestamp\tproblem\trole\tturn\tattempt\tthread_id\tevents\tfinal\tsession_file\n' > "$KIMI_SESSIONS"
  printf 'timestamp\tproblem\trole\tturn\tattempt\tthread_id\tevents\tfinal\tsession_file\n' > "$CODEX_SESSIONS"
  printf 'timestamp\trun_id\tjob\tproblem\tmodule\tstatus\tturn\telapsed_seconds\n' > "$METRICS"
  write_run_manifest "${#selected[@]}"
  compile_no_net_bash

  index=0
  for problem in "${selected[@]}"; do
    prepare_workspace "$index" "$problem" "$(module_name "$problem")"
    index=$((index + 1))
  done
  log "prepared and provenance-audited ${#selected[@]} sanitized workspaces"
  if [[ "$PREPARE_ONLY" -eq 1 ]]; then
    log "prepare-only complete: $RUN_ROOT"
    return 0
  fi

  probe_n="$PROBE_COUNT"
  [[ "$probe_n" -gt "${#selected[@]}" ]] && probe_n="${#selected[@]}"
  log "starting $probe_n one-turn probe jobs"
  active=0
  for ((index = 0; index < probe_n; index++)); do
    run_job "$index" "${selected[$index]}" 1 &
    active=$((active + 1))
  done
  while [[ "$active" -gt 0 ]]; do
    wait -n || true
    active=$((active - 1))
  done

  if [[ -f "$RATE_FLAG" ]]; then
    limit="$FALLBACK_JOBS"
    log "probe detected HTTP 429/529; using fallback concurrency $limit"
  elif [[ -f "$INFRA_FLAG" ]]; then
    limit="$FALLBACK_JOBS"
    log "probe had transport failures; withholding full ramp and using $limit"
  else
    limit="$JOBS"
    log "probe clean: launching up to $limit parallel problem workers"
  fi
  printf '%s\n' "$limit" > "$RUN_ROOT/selected-concurrency.txt"

  total="${#selected[@]}"
  active=0
  index=0
  while [[ "$index" -lt "$total" || "$active" -gt 0 ]]; do
    if [[ -f "$RATE_FLAG" ]]; then
      limit="$FALLBACK_JOBS"
    fi
    while [[ "$index" -lt "$total" && "$active" -lt "$limit" ]]; do
      run_job "$index" "${selected[$index]}" "$MAX_TURNS" &
      index=$((index + 1))
      active=$((active + 1))
      sleep 0.2
    done
    if [[ "$active" -gt 0 ]]; then
      wait -n || true
      active=$((active - 1))
    fi
  done
  log "all jobs finished: $RUN_ROOT"
}

main "$@"
