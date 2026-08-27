#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
use_mathlib_cache=false

if [[ "${1:-}" == "--with-cache" ]]; then
  use_mathlib_cache=true
elif [[ $# -ne 0 ]]; then
  echo "usage: $0 [--with-cache]" >&2
  exit 2
fi

for dataset in QAlg QIT; do
  project_dir="${repo_root}/${dataset}/lean-project"
  echo "==> Verifying ${dataset} in ${project_dir}"
  if [[ "${use_mathlib_cache}" == true ]]; then
    (cd "${project_dir}" && lake exe cache get)
  fi
  (cd "${project_dir}" && lake build)
done

echo "==> QAlg and QIT verification completed successfully"
