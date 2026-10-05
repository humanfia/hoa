#!/usr/bin/env bash

set -Eeuo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
repo_root="$(CDPATH= cd -- "$script_dir/.." && pwd -P)"

prompt_file=
model="${CODEX_MODEL:-gpt-5.6-sol}"
effort="${CODEX_EFFORT:-max}"
run_root=
dry_run=false

usage() {
  cat <<'EOF'
Usage:
  bash scripts/run-ibo2024.sh --prompt PLAN.md [options]

Options:
  --model MODEL    Codex model (default: gpt-5.6-sol)
  --effort LEVEL   Codex reasoning effort (default: max)
  --out DIR        Create the isolated run at DIR (default: a /tmp directory)
  --dry-run        Validate inputs and print configuration without launching
  -h, --help       Show this help

Authentication is read from CODEX_HOME. To use another provider or account,
point CODEX_HOME at a Codex home containing the corresponding auth.json.
EOF
}

die() {
  printf '[ibo2024] ERROR: %s\n' "$*" >&2
  exit 1
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --prompt|--model|--effort|--out)
      [[ $# -ge 2 ]] || die "$1 requires a value"
      case "$1" in
        --prompt) prompt_file=$2 ;;
        --model) model=$2 ;;
        --effort) effort=$2 ;;
        --out) run_root=$2 ;;
      esac
      shift 2
      ;;
    --dry-run)
      dry_run=true
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
done

[[ -n "$prompt_file" ]] || die "--prompt is required"
[[ -s "$prompt_file" ]] || die "prompt file missing or empty: $prompt_file"
[[ -n "$model" ]] || die "--model must not be empty"
[[ -n "$effort" ]] || die "--effort must not be empty"

prompt_file="$(readlink -f -- "$prompt_file")"
source_a="$repo_root/source/IBO2024 Theory A.pdf"
source_b="$repo_root/source/IBO2024 Theory B.pdf"
[[ -s "$source_a" ]] || die "official source PDF missing: $source_a"
[[ -s "$source_b" ]] || die "official source PDF missing: $source_b"

codex_bin="${CODEX_BIN:-$(command -v codex || true)}"
[[ -n "$codex_bin" && -x "$codex_bin" ]] || die "Codex executable not found"

printf 'model:   %s:%s\n' "$model" "$effort"
printf 'prompt:  %s\n' "$prompt_file"
printf 'source A: %s\n' "$source_a"
printf 'source B: %s\n' "$source_b"

if [[ "$dry_run" == true ]]; then
  printf '%s\n' 'DRY RUN PASS: reproduction inputs are ready'
  exit 0
fi

if [[ -z "$run_root" ]]; then
  run_root="$(mktemp -d "${TMPDIR:-/tmp}/ibo2024-reproduction.XXXXXXXX")"
else
  [[ ! -e "$run_root" ]] || die "output path already exists: $run_root"
  mkdir -p -- "$run_root"
  run_root="$(readlink -f -- "$run_root")"
fi

mkdir -p -- "$run_root/source"
cp -- "$source_a" "$source_b" "$run_root/source/"
cp -- "$repo_root/AGENTS.md" "$repo_root/.gitignore" "$run_root/"
cp -- "$prompt_file" "$run_root/plan.md"

git -C "$run_root" init --initial-branch=main --quiet
git -C "$run_root" config user.name 'IBO Reproducer'
git -C "$run_root" config user.email 'ibo-reproducer@localhost'
git -C "$run_root" add -- .
git -C "$run_root" commit --quiet -m 'Seed blind IBO 2024 reproduction'

printf 'workspace: %s\n' "$run_root"
"$codex_bin" exec \
  -C "$run_root" \
  --model "$model" \
  -c "model_reasoning_effort=\"$effort\"" \
  -c 'network_access="disabled"' \
  -c 'web_search="disabled"' \
  --sandbox workspace-write \
  - < "$run_root/plan.md"

printf 'completed workspace: %s\n' "$run_root"
