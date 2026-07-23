#!/usr/bin/env bash
set -Eeuo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ENGINE="${IMO2026_GPT_ENGINE:-$SCRIPT_DIR/run-imo2026.sh}"
PROMPT=""
QUESTION=""
FORWARD_ARGS=()

usage() {
  cat <<'EOF'
Usage:
  bash scripts/run-imo2026-gpt-5-6.sh --prompt PLAN.md --question QUESTION.lean [runner options]

Examples:
  bash scripts/run-imo2026-gpt-5-6.sh \
    --prompt gpt_plan.md \
    --question problem/2026-q1.lean

  bash scripts/run-imo2026-gpt-5-6.sh \
    --prompt gpt_plan.md \
    --question base/IMO2026/Q1/problem.lean \
    --dry-run

The question path must identify Q1 through Q6. If the path does not exist but
its name identifies a question, the corresponding canonical statement under
base/IMO2026 is used. Remaining options are forwarded to the internal runner.
EOF
}

die() {
  printf '[imo2026-gpt-5.6] ERROR: %s\n' "$*" >&2
  exit 1
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --prompt)
      [[ $# -ge 2 ]] || die "--prompt requires a path"
      PROMPT="$2"
      shift 2
      ;;
    --question)
      [[ $# -ge 2 ]] || die "--question requires a path"
      QUESTION="$2"
      shift 2
      ;;
    --problem|--failure-file|--source-root|--question-file)
      die "$1 is managed by this entrypoint"
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      FORWARD_ARGS+=("$1")
      shift
      ;;
  esac
done

[[ -n "$PROMPT" ]] || die "--prompt is required"
[[ -s "$PROMPT" ]] || die "prompt file missing or empty: $PROMPT"
[[ -n "$QUESTION" ]] || die "--question is required"
[[ -f "$ENGINE" ]] || die "internal runner missing: $ENGINE"

PROMPT="$(readlink -f "$PROMPT")"
question_hint="${QUESTION,,}"
question_number=""
if [[ "$question_hint" =~ (^|[/_.-])q([1-6])([/_.-]|$) ]]; then
  question_number="${BASH_REMATCH[2]}"
fi

if [[ -s "$QUESTION" ]]; then
  QUESTION="$(readlink -f "$QUESTION")"
  if [[ -z "$question_number" ]]; then
    for candidate_number in 1 2 3 4 5 6; do
      candidate="$ROOT/base/IMO2026/Q${candidate_number}/problem.lean"
      if cmp -s "$QUESTION" "$candidate"; then
        question_number="$candidate_number"
        break
      fi
    done
  fi
else
  [[ -n "$question_number" ]] || die "question file missing: $QUESTION"
  canonical="$ROOT/base/IMO2026/Q${question_number}/problem.lean"
  [[ -s "$canonical" ]] || die "canonical Q${question_number} statement missing"
  printf '[imo2026-gpt-5.6] using canonical question: %s\n' "$canonical" >&2
  QUESTION="$canonical"
fi

[[ -n "$question_number" ]] || \
  die "cannot determine Q1-Q6 from question: $QUESTION"

exec bash "$ENGINE" \
  --prompt "$PROMPT" \
  --question-file "$QUESTION" \
  --problem "imo2026_q${question_number}" \
  --jobs 1 \
  --fallback-jobs 1 \
  --probe-count 1 \
  "${FORWARD_ARGS[@]}"
