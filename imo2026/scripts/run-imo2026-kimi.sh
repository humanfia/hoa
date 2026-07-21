#!/usr/bin/env bash
set -Eeuo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KIMI_CODEX_HOME="${KIMI_CODEX_HOME:-/root/storage/zhengyang-workspace/.codex-kimi}"
KIMI_KEY_FILE="${KIMI_KEY_FILE:-$KIMI_CODEX_HOME/kimi-api-key}"
KIMI_CODEX_BIN="${KIMI_CODEX_BIN:-$KIMI_CODEX_HOME/runtime/node_modules/@openai/codex/vendor/x86_64-unknown-linux-musl/codex/codex}"
KIMI_PROXY_SCRIPT="$SCRIPT_DIR/kimi-chat-proxy.py"

[[ -r "$KIMI_KEY_FILE" ]] || {
  printf '[imo2026-humanize-kimi] ERROR: Kimi key file is unreadable: %s\n' "$KIMI_KEY_FILE" >&2
  exit 1
}
[[ -x "$KIMI_CODEX_BIN" ]] || {
  printf '[imo2026-humanize-kimi] ERROR: compatible Codex binary is missing: %s\n' "$KIMI_CODEX_BIN" >&2
  exit 1
}
[[ -r "$KIMI_PROXY_SCRIPT" ]] || {
  printf '[imo2026-humanize-kimi] ERROR: Kimi compatibility proxy is missing: %s\n' "$KIMI_PROXY_SCRIPT" >&2
  exit 1
}

export BASE_CODEX_HOME="$KIMI_CODEX_HOME"
export CODEX_BIN="$KIMI_CODEX_BIN"
export CODEX_GUEST_BIN=/codex-bin/codex
export CODEX_MODEL="${CODEX_MODEL:-kimi-for-coding}"
export CODEX_REASONING_EFFORT="${CODEX_REASONING_EFFORT:-high}"
export CODEX_MODEL_CONTEXT_WINDOW="${CODEX_MODEL_CONTEXT_WINDOW:-262144}"
export CODEX_PROVIDER="${CODEX_PROVIDER:-kimi}"
export CODEX_PROVIDER_NAME="${CODEX_PROVIDER_NAME:-Kimi Code}"
export CODEX_WIRE_API="${CODEX_WIRE_API:-chat}"
export CODEX_ENV_KEY=KIMI_API_KEY
export CODEX_REQUIRES_OPENAI_AUTH=false
export CODEX_SERVICE_TIER=""
export CODEX_DISABLE_FEATURES=""
export RUN_ID="${RUN_ID:-imo2026-humanize-kimi-$(date -u +%Y%m%dT%H%M%SZ)}"

proxy_runtime="$(mktemp -d /tmp/imo2026-kimi-proxy.XXXXXX)"
proxy_ready="$proxy_runtime/ready"
proxy_log="$SCRIPT_DIR/../runs/$RUN_ID/kimi-proxy.jsonl"
proxy_stderr="$SCRIPT_DIR/../runs/$RUN_ID/kimi-proxy.stderr.log"
mkdir -p "$(dirname "$proxy_log")"

python3 "$KIMI_PROXY_SCRIPT" \
  --key-file "$KIMI_KEY_FILE" \
  --ready-file "$proxy_ready" \
  --audit-log "$proxy_log" \
  --tool-reminder-groups "${KIMI_TOOL_REMINDER_GROUPS:-1000}" \
  --max-tool-groups "${KIMI_MAX_TOOL_GROUPS:-16}" \
  --max-tokens "${KIMI_MAX_TOKENS:-8192}" \
  --max-continuations "${KIMI_MAX_CONTINUATIONS:-3}" \
  > /dev/null 2> "$proxy_stderr" &
proxy_pid="$!"

cleanup_proxy() {
  if kill -0 "$proxy_pid" 2>/dev/null; then
    kill "$proxy_pid" 2>/dev/null || true
    wait "$proxy_pid" 2>/dev/null || true
  fi
  rm -f "$proxy_ready"
  rmdir "$proxy_runtime" 2>/dev/null || true
}
trap cleanup_proxy EXIT
trap 'exit 130' INT
trap 'exit 143' TERM HUP

for _ in $(seq 1 200); do
  [[ -s "$proxy_ready" ]] && break
  kill -0 "$proxy_pid" 2>/dev/null || {
    printf '[imo2026-humanize-kimi] ERROR: compatibility proxy exited during startup\n' >&2
    exit 1
  }
  sleep 0.05
done
[[ -s "$proxy_ready" ]] || {
  printf '[imo2026-humanize-kimi] ERROR: compatibility proxy did not become ready\n' >&2
  exit 1
}

IFS= read -r CODEX_BASE_URL < "$proxy_ready"
export CODEX_BASE_URL
export KIMI_API_KEY=local-kimi-proxy-credential

bash "$SCRIPT_DIR/run-imo2026-kimi-core.sh" "$@"
