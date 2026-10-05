#!/usr/bin/env bash

set -euo pipefail

orchestration_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
bundle_root="$(CDPATH= cd -- "$orchestration_root/.." && pwd -P)"

readonly orchestration_root bundle_root
readonly -a ioi_tasks=(
  ballmachine
  monuments
  tiling
  classroom
  magiccity
  partition
)

task_title() {
  case "$1" in
    ballmachine) printf '%s\n' 'Ball Machine' ;;
    monuments) printf '%s\n' 'Monuments' ;;
    tiling) printf '%s\n' 'Tiling Game' ;;
    classroom) printf '%s\n' 'Classroom Game' ;;
    magiccity) printf '%s\n' 'Magic City' ;;
    partition) printf '%s\n' 'Partition' ;;
    *) return 1 ;;
  esac
}

task_problem_source() {
  case "$1" in
    ballmachine|monuments|tiling)
      printf '%s\n' "$bundle_root/problems/day1/$1"
      ;;
    classroom|magiccity|partition)
      printf '%s\n' "$bundle_root/problems/day2/$1"
      ;;
    *) return 1 ;;
  esac
}

task_problem_directory() {
  case "$1" in
    ballmachine) printf '%s\n' 'source' ;;
    monuments|tiling|classroom|magiccity|partition) printf '%s\n' 'problem' ;;
    *) return 1 ;;
  esac
}

task_solution_path() {
  case "$1" in
    ballmachine) printf '%s\n' 'solutions/01-ballmachine/solution.cpp' ;;
    monuments) printf '%s\n' 'solutions/02-monuments/solution.cpp' ;;
    tiling) printf '%s\n' 'solutions/03-tiling/solution.cpp' ;;
    classroom) printf '%s\n' 'solutions/01-classroom/solution.cpp' ;;
    magiccity) printf '%s\n' 'solutions/02-magiccity/solution.cpp' ;;
    partition) printf '%s\n' 'solutions/03-partition/solution.cpp' ;;
    *) return 1 ;;
  esac
}

require_task() {
  local candidate=$1
  local task
  for task in "${ioi_tasks[@]}"; do
    [[ "$candidate" == "$task" ]] && return 0
  done
  printf 'unknown IOI task: %s\n' "$candidate" >&2
  return 1
}

find_humanize_root() {
  local candidate
  if [[ -n "${HUMANIZE_ROOT_OVERRIDE:-}" ]]; then
    candidate=$HUMANIZE_ROOT_OVERRIDE
  elif [[ -d "$bundle_root/../.codex/skills/humanize" ]]; then
    candidate="$bundle_root/../.codex/skills/humanize"
  else
    candidate="${HOME}/.codex/skills/humanize"
  fi
  candidate="$(CDPATH= cd -- "$candidate" 2>/dev/null && pwd -P)" || return 1
  [[ -x "$candidate/scripts/setup-rlcr-loop.sh" ]] || return 1
  [[ -x "$candidate/hooks/loop-codex-stop-hook.sh" ]] || return 1
  printf '%s\n' "$candidate"
}

find_auth_file() {
  local candidate="${CODEX_AUTH_FILE_OVERRIDE:-${HOME}/.codex/auth.json}"
  [[ -r "$candidate" ]] || return 1
  readlink -f -- "$candidate"
}

resolve_run_root() {
  local requested=${1:-}
  local resolved
  if [[ -n "$requested" ]]; then
    resolved="$(CDPATH= cd -- "$requested" 2>/dev/null && pwd -P)" || return 1
  elif [[ -L "$bundle_root/runs/latest" ]]; then
    resolved="$(CDPATH= cd -- "$bundle_root/runs/latest" && pwd -P)" || return 1
  else
    return 1
  fi
  [[ -f "$resolved/run.json" ]] || return 1
  printf '%s\n' "$resolved"
}
