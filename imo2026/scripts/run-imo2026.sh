#!/usr/bin/env bash
set -Eeuo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HUMANIZE_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
WORKSPACE_ROOT="${WORKSPACE_ROOT:-$HUMANIZE_ROOT}"
MATH_FLOW_BENCH_ROOT="${MATH_FLOW_BENCH_ROOT:-$WORKSPACE_ROOT/base}"
IMO2026_SOURCE_ROOT="${IMO2026_SOURCE_ROOT:-$WORKSPACE_ROOT/base/IMO2026}"
FAILURE_FILE="${FAILURE_FILE:-$WORKSPACE_ROOT/inputs/problems.md}"
PROMPT_FILE="${PROMPT_FILE:-}"
QUESTION_FILE="${QUESTION_FILE:-}"
BASE_CODEX_HOME="${BASE_CODEX_HOME:-/root/storage/zhengyang-workspace/.codex}"
OUT_ROOT="${OUT_ROOT:-$WORKSPACE_ROOT/runs}"
COMPARATOR_TOOLS_ROOT="${COMPARATOR_TOOLS_ROOT:-$WORKSPACE_ROOT/tools}"
LOCAL_RUNTIME_TEMPLATE="${LOCAL_RUNTIME_TEMPLATE:-/tmp/imo2026-humanize-runtime-v431}"
LOCAL_RUNS_ROOT="${LOCAL_RUNS_ROOT:-/tmp/imo2026-humanize-runs}"
COMPARATOR_BIN="${COMPARATOR_BIN:-$LOCAL_RUNTIME_TEMPLATE/comparator-tools/comparator}"
LEAN4EXPORT_BIN="${LEAN4EXPORT_BIN:-$LOCAL_RUNTIME_TEMPLATE/checker-tools/lean4export}"
LANDRUN_BIN="${LANDRUN_BIN:-$LOCAL_RUNTIME_TEMPLATE/comparator-tools/landrun}"
CODEX_BIN="${CODEX_BIN:-/usr/local/share/nvm/versions/node/v24.18.0/lib/node_modules/@openai/codex/node_modules/@openai/codex-linux-x64/vendor/x86_64-unknown-linux-musl/bin/codex}"
HUMANIZE_USER_PREFIX="${HUMANIZE_USER_PREFIX:-humanize-imo}"

CODEX_MODEL="gpt-5.6-sol"
MAX_TURNS="${MAX_TURNS:-50}"
JOBS="${JOBS:-6}"
FALLBACK_JOBS="${FALLBACK_JOBS:-6}"
PROBE_COUNT="${PROBE_COUNT:-4}"
WORKER_TIMEOUT_SECONDS="${WORKER_TIMEOUT_SECONDS:-7200}"
REVIEW_TIMEOUT_SECONDS="${REVIEW_TIMEOUT_SECONDS:-7200}"
CODEX_RATE_RETRIES="${CODEX_RATE_RETRIES:-6}"
REVIEW_INFRA_RETRIES="${REVIEW_INFRA_RETRIES:-0}"
RUN_ID="${RUN_ID:-imo2026-humanize-axle-comparator-$(date -u +%Y%m%dT%H%M%SZ)}"

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

Runs blind IMO 2026 proof workers and isolated AXLE-backed reviewers for Q1-Q6.
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
  --worker-timeout-seconds N   Timeout per worker Codex call. Default: 7200.
  --review-timeout-seconds N   Timeout per reviewer Codex call. Default: 7200.
  --run-id ID                  Override timestamped run ID.
  --failure-file PATH          Markdown problem list.
  --prompt PATH                User plan appended to the mandatory proof instructions.
  --question-file PATH         Exact Lean statement for one selected problem.
  --source-root PATH           Root containing Q1/problem.lean through Q6/problem.lean.
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
  CODEX_MODEL=gpt-5.6-sol (fixed)
  MAX_TURNS=50
  JOBS=6
  BASE_CODEX_HOME=/root/storage/zhengyang-workspace/.codex
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
    --prompt) PROMPT_FILE="$2"; shift 2 ;;
    --question-file) QUESTION_FILE="$2"; shift 2 ;;
    --source-root) IMO2026_SOURCE_ROOT="$2"; shift 2 ;;
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
  WORKER_TIMEOUT_SECONDS REVIEW_TIMEOUT_SECONDS CODEX_RATE_RETRIES REVIEW_INFRA_RETRIES; do
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
CODEX_RUN_HOME="$PROOT_ROOT/agent-homes"
RATE_FLAG="$RUN_ROOT/rate-limit.detected"
RATE_LOG="$RUN_ROOT/rate-limit-events.tsv"
INFRA_FLAG="$RUN_ROOT/transport-failure.detected"
INFRA_LOG="$RUN_ROOT/transport-failures.tsv"
METRICS="$RUN_ROOT/metrics.tsv"
SESSIONS="$RUN_ROOT/codex-sessions.tsv"
LOOP_STAMP="$(date -u +%Y-%m-%d_%H-%M-%S)"
NO_NET_BASH="$RUN_ROOT/no-net-bash"

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || die "missing required command: $1"
}

module_name() {
  printf 'IMO2026%s\n' "$(printf '%s' "${1#imo2026_}" | tr '[:lower:]' '[:upper:]')"
}

problem_source_file() {
  local problem="$1"
  local question
  if [[ -n "$QUESTION_FILE" ]]; then
    printf '%s\n' "$QUESTION_FILE"
    return
  fi
  question="$(printf '%s' "${problem#imo2026_}" | tr '[:lower:]' '[:upper:]')"
  printf '%s/%s/problem.lean\n' "$IMO2026_SOURCE_ROOT" "$question"
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

codex_binary() {
  readlink -f "$(command -v codex)"
}

codex_runtime() {
  local binary
  binary="$(codex_binary)"
  (cd "$(dirname "$binary")/.." && pwd)
}

base_url() {
  awk -F= '/^[[:space:]]*base_url[[:space:]]*=/{gsub(/[ "\r]/, "", $2); print $2; exit}' \
    "$BASE_CODEX_HOME/config.toml"
}

write_codex_config() {
  local output="$1"
  local role="$2"
  local network="disabled"
  local provider_url
  [[ "$role" == reviewer ]] && network="enabled"
  provider_url="$(base_url)"
  cat > "$output" <<EOF
model = "$CODEX_MODEL"
review_model = "$CODEX_MODEL"
model_reasoning_effort = "max"
disable_response_storage = true
network_access = "$network"
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

activate_identity_paths() {
  local link target
  for link in /workspaces /agent-homes /checker-tools; do
    case "$link" in
      /workspaces) target="$WORKSPACES_ROOT" ;;
      /agent-homes) target="$CODEX_RUN_HOME" ;;
      /checker-tools) target="$PROOT_ROOT/checker-tools" ;;
    esac
    if [[ -e "$link" && ! -L "$link" ]]; then
      die "required PRoot identity path is occupied by a real path: $link"
    fi
    ln -sfn "$target" "$link"
  done
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
  mkdir -p "$WORKSPACES_ROOT" "$CODEX_RUN_HOME" "$PROOT_ROOT/worker-shell"
  activate_identity_paths
}

extract_problem_statement() {
  local problem="$1"
  local output="$2"
  cp "$(problem_source_file "$problem")" "$output"
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
- Both worker and reviewer use \`$CODEX_MODEL\` with \`max\` reasoning effort.
- Stop after at most $MAX_TURNS worker/reviewer turns.
EOF
  if [[ -n "$PROMPT_FILE" ]]; then
    cp "$PROMPT_FILE" "$workspace/docs/humanize/user-plan.md"
    {
      printf '\n## User-Supplied Plan\n\n'
      cat "$workspace/docs/humanize/user-plan.md"
      printf '\n'
    } >> "$workspace/docs/humanize/active-imo2026-plan.md"
  fi
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
  worker_home="$CODEX_RUN_HOME/j${index}-${safe}/worker"
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

  cp "$BASE_CODEX_HOME/auth.json" "$worker_home/auth.json"
  cp "$BASE_CODEX_HOME/auth.json" "$reviewer_home/auth.json"
  write_codex_config "$worker_home/config.toml" worker
  write_codex_config "$reviewer_home/config.toml" reviewer
  mkdir -p "$worker_home/sessions" "$worker_home/shell_snapshots" "$worker_home/tmp"
  mkdir -p "$reviewer_home/sessions" "$reviewer_home/shell_snapshots" "$reviewer_home/tmp"

  git -C "$workspace" init -q
  git -C "$workspace" config user.name "Blind IMO2026 Runner"
  git -C "$workspace" config user.email "runner@localhost"
  git -C "$workspace" add MathFlowBench MathFlowBench.lean ComparatorChallenge.lean \
    comparator.json source scripts tools docs lakefile.lean lake-manifest.json lean-toolchain
  git -C "$workspace" commit -q -m "Initialize sanitized $problem skeleton"

  user="${HUMANIZE_USER_PREFIX}-$(printf '%s' "${problem#imo2026_}" | tr '[:upper:]' '[:lower:]')"
  chown "$user:$user" "$workspace" "$CODEX_RUN_HOME/j${index}-${safe}"
  chmod 0700 "$workspace" "$CODEX_RUN_HOME/j${index}-${safe}"

  sha256sum "$workspace/source/lean4/src/$problem.lean" > "$job_dir/original.sha256"
  printf '%s\n' "$problem" > "$job_dir/problem.txt"
  printf '%s\n' "$module" > "$job_dir/module.txt"
  printf '%s\n' "$workspace" > "$job_dir/workspace.txt"
  printf '%s\n' "$worker_home" > "$job_dir/worker-codex-home.txt"
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
  Codex session archives, or paths outside this workspace.
- Do not use the Internet, web search, curl, wget, sockets, or network resources.
- Do not launch nested model workers.
- Treat the snapshot as authoritative and preserve it exactly apart from filling proof holes.

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
  if [[ -s "$workspace/docs/humanize/user-plan.md" ]]; then
    {
      printf '\n## User-Supplied Plan\n\n'
      cat "$workspace/docs/humanize/user-plan.md"
      printf '\n'
    } >> "$prompt"
  fi
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
  local template="$HUMANIZE_ROOT/humanize/prompt-template/codex/regular-review.md"
  local loop_dir="$workspace/.humanize/rlcr/$LOOP_STAMP"
  local output="$loop_dir/round-${turn}-review-prompt.md"
  TEMPLATE="$template" WORKSPACE="$workspace" PROOT_ROOT="$PROOT_ROOT" PROBLEM="$problem" MODULE="$module" \
    TURN="$turn" LOOP_STAMP="$LOOP_STAMP" OUTPUT="$output" python3 - <<'PY'
from pathlib import Path
import os
import subprocess

workspace = Path(os.environ["WORKSPACE"])
proot_root = Path(os.environ["PROOT_ROOT"])
guest_workspace = Path("/") / workspace.relative_to(proot_root)
problem = os.environ["PROBLEM"]
module = os.environ["MODULE"]
turn = int(os.environ["TURN"])
stamp = os.environ["LOOP_STAMP"]
loop_host = workspace / ".humanize" / "rlcr" / stamp
loop_chroot = guest_workspace / ".humanize" / "rlcr" / stamp
summary = (loop_host / f"round-{turn}-summary.md").read_text()
try:
    history = subprocess.run(
        ["git", "-C", str(workspace), "log", "--oneline", "--reverse"],
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
You are reviewing `{problem}` in a sanitized filesystem. References to Claude
in the inherited Humanize template mean the blind Codex proof worker.

- Use model gpt-5.6-sol with max reasoning effort.
- Do not inspect Codex sessions, prior experiments, other worktrees, or existing solutions.
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

rate_error_in() {
  local file
  for file in "$@"; do
    [[ -f "$file" ]] || continue
    if codex_error_text "$file" | rg -qi "(HTTP([[:space:]_-]+status)?[^0-9]{0,20}(429|529)|status(_code)?[\\\"':= ]+(429|529)|too many requests|rate[ _-]*limit|request rate limit|upstream.*overload|overloaded.*(429|529))"; then
      return 0
    fi
  done
  return 1
}

transient_error_in() {
  local file
  for file in "$@"; do
    [[ -f "$file" ]] || continue
    if codex_error_text "$file" | rg -qi "(stream disconnected|error sending request|connection (reset|closed|refused)|temporar(il)?y unavailable|timed? out|selected model is at capacity|model[^.\n]{0,40}at capacity|HTTP[^0-9]{0,20}(408|500|502|503|504)|status(_code)?[\\\"':= ]+(408|500|502|503|504))"; then
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
  local codex_home="$6" marker="$7" events="$8" final="$9"
  local thread_id session_file
  thread_id="$(jq -r 'select(.type == "thread.started") | .thread_id // empty' "$events" 2>/dev/null | head -n 1)"
  [[ -n "$thread_id" ]] || thread_id="$(rg -o 'session id: [0-9a-f-]+' "$events" 2>/dev/null | head -n1 | awk '{print $3}')"
  [[ -n "$thread_id" ]] || thread_id="unknown"

  mapfile -t new_sessions < <(find "$codex_home/sessions" -type f -name '*.jsonl' -newer "$marker" -print 2>/dev/null | sort)
  if [[ "${#new_sessions[@]}" -eq 0 ]]; then
    new_sessions=("")
  fi
  for session_file in "${new_sessions[@]}"; do
    {
      flock 9
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$problem" "$role" "$turn" "$attempt" \
        "$thread_id" "$events" "$final" "$session_file" >> "$SESSIONS"
      printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$role" "$turn" "$attempt" \
        "$thread_id" "$events" "$session_file" >> "$job_dir/sessions.tsv"
    } 9>"$RUN_ROOT/sessions.lock"
  done
}

run_codex_namespace_once() {
  local role="$1" workspace="$2" codex_home="$3" prompt_rel="$4"
  local events="$5" stderr_log="$6" final_rel="$7" nsroot="$8"
  local module="$9" timeout_seconds="${10}"
  local network_mode user guest_workspace guest_codex_home exit_code=0
  local -a proot_args
  : "$nsroot" "$module"
  network_mode="disabled"
  user="${HUMANIZE_USER_PREFIX}-$(printf '%s' "${module#IMO2026}" | tr '[:upper:]' '[:lower:]')"
  guest_workspace="${workspace#"$PROOT_ROOT"}"
  guest_codex_home="${codex_home#"$PROOT_ROOT"}"
  if [[ "$role" == reviewer ]]; then
    network_mode="enabled"
  fi
  chown -R "$user:$user" \
    "$workspace/.humanize" "$workspace/.lake/build" "$workspace/home" "$codex_home"
  chown "$user:$user" "$workspace/.lake"
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
        HOME="$guest_workspace/home" USER="$user" CODEX_HOME="$guest_codex_home" \
        ELAN_HOME=/root/.elan PATH=/root/.elan/bin:/usr/local/bin:/usr/bin:/bin \
        SHELL=/bin/bash TMPDIR="$guest_codex_home/tmp" TERM=dumb \
        HUMANIZE_SHELL_AUDIT=/worker-shell/invocations.log \
        HUMANIZE_NONET_LIB=/worker-shell/libhumanize-nonet.so \
        HUMANIZE_REAL_BASH=/worker-shell/bash.real \
        COMPARATOR_BIN=/comparator-tools/comparator \
        LEAN4EXPORT_BIN=/checker-tools/lean4export \
        LANDRUN_BIN=/comparator-tools/landrun \
        PYTHONDONTWRITEBYTECODE=1 \
      timeout --foreground "$timeout_seconds" \
        "$CODEX_BIN" --ask-for-approval never exec \
          --cd "$guest_workspace" --skip-git-repo-check --model "$CODEX_MODEL" \
          --sandbox danger-full-access --json \
          --disable browser_use \
          --disable browser_use_external \
          --disable browser_use_full_cdp_access \
          --disable in_app_browser \
          --disable search_tool \
          --disable standalone_web_search \
          --disable hooks \
          -c model_reasoning_effort='"max"' \
          -c network_access="\"$network_mode\"" \
          -c disable_response_storage=true \
          -c shell_environment_policy.inherit='"all"' \
          -o "$guest_workspace/$final_rel" \
          - < "$workspace/$prompt_rel" \
          > "$events" 2> "$stderr_log"
  ) || exit_code="$?"

  if [[ "$role" == worker ]]; then
    chown -R root:root "$workspace/MathFlowBench"
    chmod 0755 "$workspace/MathFlowBench"
    chmod 0644 "$workspace/MathFlowBench/$module.lean"
  fi
  return "$exit_code"
}

run_codex_with_retries() {
  local role="$1" workspace="$2" codex_home="$3" prompt_rel="$4"
  local final_rel="$5" job_dir="$6" problem="$7" module="$8" turn="$9"
  local timeout_seconds="${10}"
  local attempt events stderr_log marker code delay nsroot
  for ((attempt = 1; attempt <= CODEX_RATE_RETRIES + 1; attempt++)); do
    events="$job_dir/round-${turn}-${role}-attempt-${attempt}.events.jsonl"
    stderr_log="$job_dir/round-${turn}-${role}-attempt-${attempt}.stderr.log"
    marker="$job_dir/round-${turn}-${role}-attempt-${attempt}.session-marker"
    nsroot="$RUN_ROOT/nsroot/$(basename "$job_dir")-$role"
    touch "$marker"
    code=0
    run_codex_namespace_once "$role" "$workspace" "$codex_home" "$prompt_rel" \
      "$events" "$stderr_log" "$final_rel" "$nsroot" "$module" "$timeout_seconds" || code="$?"
    record_sessions "$job_dir" "$problem" "$role" "$turn" "$attempt" \
      "$codex_home" "$marker" "$events" "$workspace/$final_rel"
    if rate_error_in "$events" "$stderr_log"; then
      record_rate_error "$problem" "$role" "$turn" "$attempt"
      if [[ "$attempt" -le "$CODEX_RATE_RETRIES" ]]; then
        delay=$((30 * (2 ** (attempt - 1))))
        [[ "$delay" -gt 600 ]] && delay=600
        log "$problem $role turn $turn hit 429/529; retrying in ${delay}s"
        sleep "$delay"
        continue
      fi
      return 75
    fi
    if [[ "$code" -ne 0 ]] && transient_error_in "$events" "$stderr_log"; then
      if [[ "$attempt" -le "$CODEX_RATE_RETRIES" ]]; then
        delay=$((30 * (2 ** (attempt - 1))))
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

commit_candidate_round() {
  local workspace="$1" problem="$2" turn="$3"
  if [[ -n "$(git -C "$workspace" status --porcelain -- MathFlowBench)" ]]; then
    git -C "$workspace" add MathFlowBench
    git -C "$workspace" commit -q -m "Round $turn candidate for $problem"
  fi
}

review_is_complete() {
  local workspace="$1" turn="$2"
  local loop_dir="$workspace/.humanize/rlcr/$LOOP_STAMP"
  local result="$loop_dir/round-${turn}-review-result.md"
  local axle="$result.axle.json"
  [[ -s "$result" ]] || return 1
  [[ "$(awk 'NF{line=$0} END{print line}' "$result")" == "COMPLETE" ]] || return 1
  jq -e '.all_okay == true and (.results | length > 0) and all(.results[]; .okay == true)' \
    "$axle" >/dev/null 2>&1
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
  worker_home="$CODEX_RUN_HOME/j${index}-${safe}/worker"
  reviewer_home="$CODEX_RUN_HOME/j${index}-${safe}/reviewer"
  loop_dir="$workspace/.humanize/rlcr/$LOOP_STAMP"

  if [[ "$(cat "$job_dir/status.txt" 2>/dev/null || true)" == passed ]]; then
    return 0
  fi
  turn="$(cat "$job_dir/next-turn.txt")"
  feedback=""
  if [[ "$turn" -gt 1 ]]; then
    feedback="$loop_dir/round-$((turn - 1))-review-result.md"
  fi
  start="$(date +%s)"
  status="pending"

  while [[ "$turn" -le "$end_turn" && "$turn" -le "$MAX_TURNS" ]]; do
    printf 'worker_turn_%s\n' "$turn" > "$job_dir/status.txt"
    write_worker_prompt "$workspace" "$problem" "$module" "$turn" "$feedback"
    worker_prompt_rel=".humanize/rlcr/$LOOP_STAMP/round-${turn}-prompt.md"
    worker_final_rel=".humanize/rlcr/$LOOP_STAMP/round-${turn}-worker-final.md"
    code=0
    run_codex_with_retries worker "$workspace" "$worker_home" "$worker_prompt_rel" \
      "$worker_final_rel" "$job_dir" "$problem" "$module" "$turn" \
      "$WORKER_TIMEOUT_SECONDS" || code="$?"
    if [[ "$code" -eq 75 ]]; then
      status="worker_rate_limited"
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
      run_codex_with_retries reviewer "$workspace" "$reviewer_home" "$review_prompt_rel" \
        "$review_final_rel" "$job_dir" "$problem" "$module" "$turn" \
        "$REVIEW_TIMEOUT_SECONDS" || code="$?"
      if [[ ! -s "$review_result" && -s "$workspace/$review_final_rel" ]]; then
        cp "$workspace/$review_final_rel" "$review_result"
      fi
      if [[ "$code" -eq 75 ]]; then
        status="reviewer_rate_limited"
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
  local safe job_dir job_name index current_status
  safe="$(safe_name "$problem")"
  job_dir="$(find "$RUN_ROOT/jobs" -mindepth 1 -maxdepth 1 -type d \
    -name "*-$safe" -print -quit)"
  [[ -n "$job_dir" ]] || die "worker recovery job not found for $problem"
  job_name="$(basename "$job_dir")"
  index="${job_name%%-*}"
  index="${index#j}"
  current_status="$(head -1 "$job_dir/status.txt" 2>/dev/null || true)"
  case "$current_status" in
    worker_rate_limited|worker_timeout|worker_transport_failed)
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
  loop_dir="$workspace/.humanize/rlcr/$LOOP_STAMP"
  current_status="$(head -1 "$job_dir/status.txt" 2>/dev/null || true)"
  case "$current_status" in
    review_infrastructure_failed|reviewer_timeout|reviewer_transport_failed|reviewer_rate_limited)
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
    run_codex_with_retries reviewer "$workspace" "$reviewer_home" "$review_prompt_rel" \
      "$review_final_rel" "$job_dir" "$problem" "$module" "$turn" \
      "$REVIEW_TIMEOUT_SECONDS" || code="$?"
    if [[ ! -s "$review_result" && -s "$workspace/$review_final_rel" ]]; then
      cp "$workspace/$review_final_rel" "$review_result"
    fi
    if [[ "$code" -eq 75 ]]; then
      status="reviewer_rate_limited"
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
  local count="$1" source_sha source_label prompt_sha prompt_label
  if [[ -n "$QUESTION_FILE" ]]; then
    source_label="$QUESTION_FILE"
    source_sha="$(sha256sum "$QUESTION_FILE" | awk '{print $1}')"
  else
    source_label="$IMO2026_SOURCE_ROOT/Q1..Q6/problem.lean"
    source_sha="$(sha256sum "$IMO2026_SOURCE_ROOT"/Q[1-6]/problem.lean | sha256sum | awk '{print $1}')"
  fi
  if [[ -n "$PROMPT_FILE" ]]; then
    prompt_label="$PROMPT_FILE"
    prompt_sha="$(sha256sum "$PROMPT_FILE" | awk '{print $1}')"
  else
    prompt_label="built-in mandatory proof plan"
    prompt_sha="n/a"
  fi
  cat > "$RUN_ROOT/RUN.md" <<EOF
# IMO 2026 Humanize + Comparator + AXLE Run

- Run ID: \`$RUN_ID\`
- Failure source: \`$FAILURE_FILE\`
- Problems: $count
- Problem source: \`$source_label\`
- Combined problem-source SHA-256: \`$source_sha\`
- User prompt: \`$prompt_label\`
- User-prompt SHA-256: \`$prompt_sha\`
- Upstream repository commit: \`c5a6a089d06d3619afe7ff45c5ccab9e2a30d5d2\`
- Worker/reviewer model: \`$CODEX_MODEL\`
- Reasoning effort: \`max\`
- Maximum turns: $MAX_TURNS
- Requested main concurrency: $JOBS
- Rate-limited fallback concurrency: $FALLBACK_JOBS
- Base Codex home: \`$BASE_CODEX_HOME\`
- Per-job Codex homes: \`$CODEX_RUN_HOME\`
- Solver network: blocked by the enforced socket-denial worker shell
- Worker self-check: current Comparator, target-version lean4export, and real Landrun
- Reviewer network: permitted only for the prompted AXLE verifier call
- Existing solutions: not mounted into either model namespace

All prompts, event streams, final messages, session paths, reviews, compilation
logs, Comparator output, AXLE JSON, hashes, and status files are retained under this run directory.
EOF
}

main() {
  local command selected problem index missing active limit total probe_n user source_file
  for command in awk bash cc chown chmod date find flock getent git jq lake proot python3 readlink rg setpriv sha256sum timeout; do
    need_cmd "$command"
  done
  if [[ -n "$PROMPT_FILE" ]]; then
    [[ -s "$PROMPT_FILE" ]] || die "prompt file missing or empty: $PROMPT_FILE"
    PROMPT_FILE="$(readlink -f "$PROMPT_FILE")"
  fi
  if [[ -n "$QUESTION_FILE" ]]; then
    [[ -s "$QUESTION_FILE" ]] || die "question file missing or empty: $QUESTION_FILE"
    [[ "${#PROBLEMS[@]}" -eq 1 ]] || \
      die "--question-file requires exactly one --problem"
    QUESTION_FILE="$(readlink -f "$QUESTION_FILE")"
  fi
  if [[ "${#PROBLEMS[@]}" -eq 0 ]]; then
    [[ -f "$FAILURE_FILE" ]] || die "failure file not found: $FAILURE_FILE"
  fi
  if [[ -z "$QUESTION_FILE" ]]; then
    [[ -d "$IMO2026_SOURCE_ROOT" ]] || die "IMO2026 source root not found: $IMO2026_SOURCE_ROOT"
  fi
  [[ -f "$BASE_CODEX_HOME/auth.json" ]] || die "Codex auth missing: $BASE_CODEX_HOME/auth.json"
  [[ -f "$BASE_CODEX_HOME/config.toml" ]] || die "Codex config missing: $BASE_CODEX_HOME/config.toml"
  [[ -f "$HUMANIZE_ROOT/humanize/prompt-template/codex/regular-review.md" ]] || die "new review template missing"
  [[ -x "$COMPARATOR_BIN" ]] || die "Comparator binary missing or not executable: $COMPARATOR_BIN"
  [[ -x "$LEAN4EXPORT_BIN" ]] || die "lean4export binary missing or not executable: $LEAN4EXPORT_BIN"
  [[ -x "$LANDRUN_BIN" ]] || die "Landrun binary missing or not executable: $LANDRUN_BIN"
  [[ -f "$HUMANIZE_ROOT/scripts/check-with-comparator.sh" ]] || \
    die "Comparator wrapper missing"
  [[ -f "$HUMANIZE_ROOT/scripts/validate-imo2026-output.py" ]] || die "statement validator missing"
  [[ -f "$HUMANIZE_ROOT/scripts/verify-imo2026-axle.py" ]] || die "AXLE verifier missing"
  [[ -x "$CODEX_BIN" ]] || die "Codex binary missing or not executable: $CODEX_BIN"
  [[ -d "$LOCAL_RUNTIME_TEMPLATE" ]] || die "local runtime template missing: $LOCAL_RUNTIME_TEMPLATE"
  [[ -d /mathlib-packages ]] || die "/mathlib-packages is not linked to the pinned package cache"
  [[ "$CODEX_MODEL" == "gpt-5.6-sol" ]] || die "this run requires CODEX_MODEL=gpt-5.6-sol"
  mapfile -t selected < <(parse_failed_problems)
  [[ "${#selected[@]}" -gt 0 ]] || die "no failed problems parsed"
  missing=0
  for problem in "${selected[@]}"; do
    if ! [[ "$problem" =~ ^imo2026_q[1-6]$ ]]; then
      printf 'invalid problem id: %s\n' "$problem" >&2
      missing=$((missing + 1))
      continue
    fi
    source_file="$(problem_source_file "$problem")"
    if [[ ! -s "$source_file" ]]; then
      printf 'missing nonempty upstream problem source: %s\n' "$problem" >&2
      missing=$((missing + 1))
    fi
    user="${HUMANIZE_USER_PREFIX}-${problem#imo2026_}"
    getent passwd "$user" >/dev/null || die "missing isolated worker account: $user"
  done
  [[ "$missing" -eq 0 ]] || die "$missing selected IMO2026 problems are unavailable"

  log "run id: $RUN_ID"
  log "selected problems: ${#selected[@]}"
  log "model: $CODEX_MODEL; effort: max; max turns: $MAX_TURNS"
  if [[ "$DRY_RUN" -eq 1 ]]; then
    printf '%s\n' "${selected[@]}"
    return 0
  fi

  if [[ "$RESUME_WORKER_ONLY" -eq 1 ]]; then
    local existing_stamp
    [[ "${#selected[@]}" -eq 1 ]] || die "worker-only recovery requires exactly one problem"
    [[ -d "$RUN_ROOT/jobs" && -d "$WORKSPACES_ROOT" ]] || \
      die "cannot recover worker in missing run: $RUN_ROOT"
    activate_identity_paths
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
    activate_identity_paths
    existing_stamp="$(find "$WORKSPACES_ROOT" -mindepth 4 -maxdepth 4 \
      -type d -path '*/.humanize/rlcr/*' -printf '%f\n' | sort -u | head -n 1)"
    [[ -n "$existing_stamp" ]] || die "cannot locate existing Humanize loop stamp"
    LOOP_STAMP="$existing_stamp"
    log "review-only recovery for $RUN_ID using loop $LOOP_STAMP"
    resume_review_job "${selected[0]}"
    return 0
  fi

  if [[ "$RESUME_PREPARED" -eq 1 ]]; then
    local existing_stamp status_file job_dir job_name pid
    local -a resume_pids=()
    [[ -d "$RUN_ROOT/jobs" && -d "$WORKSPACES_ROOT" ]] || \
      die "cannot resume missing run: $RUN_ROOT"
    activate_identity_paths
    existing_stamp="$(find "$WORKSPACES_ROOT" -mindepth 4 -maxdepth 4 \
      -type d -path '*/.humanize/rlcr/*' -printf '%f\n' | sort -u | head -n 1)"
    [[ -n "$existing_stamp" ]] || die "cannot locate existing Humanize loop stamp"
    LOOP_STAMP="$existing_stamp"
    log "resume-prepared for run $RUN_ID using loop $LOOP_STAMP"
    active=0
    for problem in "${selected[@]}"; do
      job_dir="$(find "$RUN_ROOT/jobs" -mindepth 1 -maxdepth 1 -type d \
        -name "*-$(safe_name "$problem")" -print -quit)"
      [[ -n "$job_dir" ]] || die "prepared job not found for $problem"
      job_name="$(basename "$job_dir")"
      index="${job_name%%-*}"
      index="${index#j}"
      status_file="$job_dir/status.txt"
      if [[ "$(cat "$status_file" 2>/dev/null || true)" =~ ^(prepared|pending)$ ]]; then
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
  ln -sfn "$WORKSPACES_ROOT" "$RUN_ROOT/workspaces"
  ln -sfn "$CODEX_RUN_HOME" "$RUN_ROOT/agent-homes"
  printf 'timestamp\tproblem\trole\tturn\tattempt\n' > "$RATE_LOG"
  printf 'timestamp\tproblem\trole\tturn\tattempt\texit_code\n' > "$INFRA_LOG"
  printf 'timestamp\tproblem\trole\tturn\tattempt\tthread_id\tevents\tfinal\tsession_file\n' > "$SESSIONS"
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
