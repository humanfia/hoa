#!/usr/bin/env bash
set -Eeuo pipefail

if [[ "$#" -ne 2 ]]; then
  printf 'usage: %s RUN_ID PAUSED_CONTROLLER_PID\n' "$0" >&2
  exit 2
fi

RUN_ID="$1"
MAIN_PID="$2"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUNNER="$SCRIPT_DIR/run-imo2026.sh"
RUN_DIR="$(cd "$SCRIPT_DIR/.." && pwd)/runs/$RUN_ID"

while true; do
  active=0
  for index in 0 1 2; do
    status_file="$(find "$RUN_DIR/jobs" -mindepth 2 -maxdepth 2 -type f \
      -path "*/j${index}-*/status.txt" -print -quit)"
    status="$(cat "$status_file" 2>/dev/null || true)"
    case "$status" in
      worker_turn_*|review_turn_*) active=1 ;;
    esac
  done
  [[ "$active" -eq 0 ]] && break
  sleep 5
done

kill -KILL "$MAIN_PID" 2>/dev/null || true

exec env \
  MAX_TURNS=50 JOBS=6 FALLBACK_JOBS=6 PROBE_COUNT=0 \
  WORKER_TIMEOUT_SECONDS=7200 REVIEW_TIMEOUT_SECONDS=7200 \
  CODEX_RATE_RETRIES=6 REVIEW_INFRA_RETRIES=0 \
  BASE_CODEX_HOME=/root/storage/zhengyang-workspace/.codex \
  bash "$RUNNER" --run-id "$RUN_ID" --resume-prepared \
    --problem imo2026_q1 --problem imo2026_q2 --problem imo2026_q3 \
    --jobs 6 --fallback-jobs 6 --probe-count 0
