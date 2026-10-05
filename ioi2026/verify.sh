#!/usr/bin/env bash

set -euo pipefail
IFS=$'\n\t'

bundle_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
cd -- "$bundle_root"
cxx="${CXX:-g++}"

fail() {
  printf 'verify.sh: %s\n' "$*" >&2
  exit 1
}

for required_command in sha256sum mktemp awk cmp python3 "$cxx"; do
  command -v "$required_command" >/dev/null 2>&1 ||
    fail "required command is unavailable: $required_command"
done

sha256sum -c MANIFEST.sha256

for orchestration_script in orchestration/*.sh; do
  bash -n "$orchestration_script"
done
for task_plan in ballmachine monuments tiling classroom magiccity partition; do
  [[ -s "orchestration/plans/$task_plan.md" ]] ||
    fail "missing orchestration plan: $task_plan"
done

build_dir="$(mktemp -d "${TMPDIR:-/tmp}/ioi-2026-clean.XXXXXXXXXX")"
cleanup() {
  local exit_status=$?
  if [[ -n "${build_dir:-}" && -d "$build_dir" ]]; then
    find "$build_dir" -type f -exec unlink -- {} \;
    find "$build_dir" -depth -mindepth 1 -type d -exec rmdir -- {} +
    rmdir -- "$build_dir"
  fi
  return "$exit_status"
}
trap cleanup EXIT

strict_flags=(
  -std=c++20
  -O2
  -Wall
  -Wextra
  -Wpedantic
  -Wconversion
  -Wshadow
  -Werror
)

compile_day1() {
  local task=$1
  local attachment="problems/day1/$task/attachment/cpp"
  "$cxx" "${strict_flags[@]}" -I"$attachment" \
    "$attachment/grader.cpp" "submissions/$task.cpp" \
    -o "$build_dir/$task"
}

for task in ballmachine monuments tiling; do
  compile_day1 "$task"
done

ballmachine_input="problems/day1/ballmachine/attachment/examples/01.in"
ballmachine_actual="$build_dir/ballmachine-01.out"
"$build_dir/ballmachine" <"$ballmachine_input" >"$ballmachine_actual"
python3 tools/validate_ballmachine.py \
  "$ballmachine_input" "$ballmachine_actual"

for input_path in problems/day1/monuments/attachment/examples/*.in; do
  example_name="$(basename -- "${input_path%.in}")"
  actual_path="$build_dir/monuments-$example_name.out"
  "$build_dir/monuments" <"$input_path" >"$actual_path"
  cmp "${input_path%.in}.out" "$actual_path"
done

tiling_input="problems/day1/tiling/attachment/examples/01.in"
tiling_actual="$build_dir/tiling-01.out"
"$build_dir/tiling" <"$tiling_input" >"$tiling_actual"
cmp "${tiling_input%.in}.out" "$tiling_actual"

"$cxx" "${strict_flags[@]}" -Iinterfaces \
  -c submissions/classroom.cpp -o "$build_dir/classroom.o"
"$cxx" "${strict_flags[@]}" \
  -c submissions/magiccity.cpp -o "$build_dir/magiccity.o"
"$cxx" "${strict_flags[@]}" \
  -c submissions/partition.cpp -o "$build_dir/partition.o"

printf '%s\n' 'PASS: IOI 2026 clean bundle verified'
