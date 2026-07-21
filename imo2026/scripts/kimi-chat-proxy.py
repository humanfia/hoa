#!/usr/bin/env python3
"""Compatibility proxy for Codex chat history sent to the Kimi API."""

from __future__ import annotations

import argparse
import copy
import http.client
import json
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit


def tool_call_ids(message: dict) -> list[str]:
    calls = message.get("tool_calls")
    if not isinstance(calls, list):
        return []
    return [call["id"] for call in calls if isinstance(call, dict) and isinstance(call.get("id"), str)]


def normalize_messages(messages: list[dict]) -> tuple[list[dict], int]:
    """Move matching tool results directly behind each assistant tool call."""
    normalized: list[dict] = []
    reordered_groups = 0
    index = 0
    while index < len(messages):
        message = copy.deepcopy(messages[index])
        expected = tool_call_ids(message) if message.get("role") == "assistant" else []
        if not expected:
            normalized.append(message)
            index += 1
            continue

        found: dict[str, tuple[int, dict]] = {}
        scan = index + 1
        while scan < len(messages) and len(found) < len(expected):
            candidate = messages[scan]
            call_id = candidate.get("tool_call_id") if candidate.get("role") == "tool" else None
            if call_id in expected and call_id not in found:
                found[call_id] = (scan, copy.deepcopy(candidate))
            scan += 1

        if len(found) != len(expected):
            normalized.append(message)
            index += 1
            continue

        selected_positions = {position for position, _ in found.values()}
        deferred = [
            copy.deepcopy(messages[position])
            for position in range(index + 1, scan)
            if position not in selected_positions
        ]
        originally_adjacent = list(range(index + 1, index + 1 + len(expected)))
        actual_positions = [found[call_id][0] for call_id in expected]
        if actual_positions != originally_adjacent:
            reordered_groups += 1

        normalized.append(message)
        normalized.extend(found[call_id][1] for call_id in expected)
        if deferred:
            normalized_deferred, nested_reorders = normalize_messages(deferred)
            normalized.extend(normalized_deferred)
            reordered_groups += nested_reorders
        index = scan

    return normalized, reordered_groups


def history_shape(messages: list[dict]) -> list[dict]:
    shape = []
    for message in messages:
        item = {"role": message.get("role")}
        calls = tool_call_ids(message)
        if calls:
            item["tool_calls"] = calls
        if isinstance(message.get("tool_call_id"), str):
            item["tool_call_id"] = message["tool_call_id"]
        shape.append(item)
    return shape


def response_shape(body: bytes, content_type: str) -> dict:
    summary: dict = {
        "bytes": len(body),
        "content_chars": 0,
        "reasoning_chars": 0,
        "tool_call_chunks": 0,
        "finish_reasons": [],
    }
    if "text/event-stream" not in content_type:
        return summary
    usage = None
    for line in body.decode("utf-8", errors="replace").splitlines():
        if not line.startswith("data:"):
            continue
        data = line[5:].strip()
        if not data or data == "[DONE]":
            continue
        try:
            event = json.loads(data)
        except json.JSONDecodeError:
            continue
        if isinstance(event.get("usage"), dict):
            usage = event["usage"]
        choices = event.get("choices")
        if not isinstance(choices, list):
            continue
        for choice in choices:
            if not isinstance(choice, dict):
                continue
            delta = choice.get("delta")
            if isinstance(delta, dict):
                content = delta.get("content")
                if isinstance(content, str):
                    summary["content_chars"] += len(content)
                for key in ("reasoning_content", "reasoning"):
                    reasoning = delta.get(key)
                    if isinstance(reasoning, str):
                        summary["reasoning_chars"] += len(reasoning)
                calls = delta.get("tool_calls")
                if isinstance(calls, list):
                    summary["tool_call_chunks"] += len(calls)
            finish_reason = choice.get("finish_reason")
            if isinstance(finish_reason, str) and finish_reason not in summary["finish_reasons"]:
                summary["finish_reasons"].append(finish_reason)
    if usage is not None:
        summary["usage"] = usage
    return summary


def streamed_assistant_state(body: bytes, content_type: str) -> dict:
    state = {"content": "", "reasoning_content": "", "has_tool_calls": False}
    if "text/event-stream" not in content_type:
        return state
    content_parts: list[str] = []
    reasoning_parts: list[str] = []
    for line in body.decode("utf-8", errors="replace").splitlines():
        if not line.startswith("data:"):
            continue
        data = line[5:].strip()
        if not data or data == "[DONE]":
            continue
        try:
            event = json.loads(data)
        except json.JSONDecodeError:
            continue
        choices = event.get("choices")
        if not isinstance(choices, list):
            continue
        for choice in choices:
            if not isinstance(choice, dict) or not isinstance(choice.get("delta"), dict):
                continue
            delta = choice["delta"]
            if isinstance(delta.get("content"), str):
                content_parts.append(delta["content"])
            for key in ("reasoning_content", "reasoning"):
                if isinstance(delta.get(key), str):
                    reasoning_parts.append(delta[key])
                    break
            if isinstance(delta.get("tool_calls"), list) and delta["tool_calls"]:
                state["has_tool_calls"] = True
    state["content"] = "".join(content_parts)
    state["reasoning_content"] = "".join(reasoning_parts)
    return state


def graceful_turn_stop(
    model: str,
    content_type: str,
    message: str = (
        "The bounded reasoning slice ended before a tool call. End this worker turn "
        "so the proof harness can retry with fresh context."
    ),
) -> tuple[bytes, str]:
    created = int(time.time())
    response_id = f"chatcmpl-kimi-proxy-{created}"
    if "text/event-stream" in content_type:
        first = {
            "id": response_id,
            "object": "chat.completion.chunk",
            "created": created,
            "model": model,
            "choices": [{
                "index": 0,
                "delta": {"role": "assistant", "content": message},
                "finish_reason": None,
            }],
        }
        final = {
            "id": response_id,
            "object": "chat.completion.chunk",
            "created": created,
            "model": model,
            "choices": [{"index": 0, "delta": {}, "finish_reason": "stop"}],
        }
        body = (
            f"data: {json.dumps(first, separators=(',', ':'))}\n\n"
            f"data: {json.dumps(final, separators=(',', ':'))}\n\n"
            "data: [DONE]\n\n"
        ).encode("utf-8")
        return body, "text/event-stream"

    body = json.dumps({
        "id": response_id,
        "object": "chat.completion",
        "created": created,
        "model": model,
        "choices": [{
            "index": 0,
            "message": {"role": "assistant", "content": message},
            "finish_reason": "stop",
        }],
    }, separators=(",", ":")).encode("utf-8")
    return body, "application/json"


class ProxyServer(ThreadingHTTPServer):
    daemon_threads = True

    def __init__(
        self,
        address,
        handler,
        upstream,
        api_key: str,
        audit_log: Path,
        tool_reminder_groups: int,
        max_tool_groups: int,
        max_tokens: int,
        max_continuations: int,
    ):
        super().__init__(address, handler)
        self.upstream = upstream
        self.api_key = api_key
        self.audit_log = audit_log
        self.tool_reminder_groups = tool_reminder_groups
        self.max_tool_groups = max_tool_groups
        self.max_tokens = max_tokens
        self.max_continuations = max_continuations
        self.audit_lock = threading.Lock()

    def audit(self, record: dict) -> None:
        with self.audit_lock:
            with self.audit_log.open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(record, separators=(",", ":")) + "\n")


class ProxyHandler(BaseHTTPRequestHandler):
    server: ProxyServer
    protocol_version = "HTTP/1.1"

    def log_message(self, _format: str, *_args) -> None:
        return

    def do_GET(self) -> None:
        if self.path != "/healthz":
            self.send_error(404)
            return
        body = b"ok\n"
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_POST(self) -> None:
        try:
            length = int(self.headers.get("Content-Length", "0"))
            raw_body = self.rfile.read(length)
            payload = json.loads(raw_body)
            request_controls = {
                "max_tokens": payload.get("max_tokens"),
                "max_completion_tokens": payload.get("max_completion_tokens"),
                "reasoning_effort": payload.pop("reasoning_effort", None),
                "reasoning": payload.pop("reasoning", None),
                "thinking": payload.get("thinking"),
                "stream": payload.get("stream"),
            }
            if payload.get("max_tokens") is None and payload.get("max_completion_tokens") is None:
                payload["max_completion_tokens"] = self.server.max_tokens
            request_controls["applied_max_completion_tokens"] = payload.get(
                "max_completion_tokens"
            )
            messages = payload.get("messages")
            reordered = 0
            before_shape = []
            after_shape = []
            if isinstance(messages, list) and all(isinstance(message, dict) for message in messages):
                before_shape = history_shape(messages)
                payload["messages"], reordered = normalize_messages(messages)
                after_shape = history_shape(payload["messages"])
            prior_tool_groups = sum(
                1
                for message in payload.get("messages", [])
                if isinstance(message, dict) and tool_call_ids(message)
            )
            add_tool_reminder = (
                isinstance(payload.get("tools"), list)
                and bool(payload["tools"])
                and prior_tool_groups < self.server.tool_reminder_groups
            )
            original_tool_choice = payload.get("tool_choice")
            if add_tool_reminder:
                if prior_tool_groups < 2:
                    reminder = (
                        "Agent-loop control: Call an available tool now. Inspect only the target "
                        "statement and candidate needed to begin the proof; do not give a final "
                        "answer or a long private derivation."
                    )
                else:
                    reminder = (
                        "Agent-loop control: You have enough context. Your next response must call "
                        "the shell to edit only the candidate theorem proof body, or compile that "
                        "candidate and fix its Lean errors. Never write sorry, admit, an axiom, or "
                        "another placeholder, and never increase the candidate's placeholder count; "
                        "a real tactic attempt that fails compilation is better. Do not run cat, "
                        "head, tail, sed -n, rg, grep, find, which, or ls. The shell command must "
                        "mutate MathFlowBench/*.lean, or compile a candidate already mutated in this "
                        "turn and fix its errors. Do not rewrite the protected prefix, read support "
                        "files, explain, or give a final answer in this response. Do not write helper files under "
                        "/tmp; edit the candidate directly or use a uniquely named file inside the "
                        "current workspace."
                    )
                payload["messages"].append(
                    {
                        "role": "user",
                        "content": reminder,
                    }
                )
            request_controls["original_tool_choice"] = original_tool_choice
            request_controls["tool_reminder_added"] = add_tool_reminder
            request_controls["prior_tool_groups"] = prior_tool_groups
            request_controls["max_tool_groups"] = self.server.max_tool_groups
            if self.server.max_tool_groups and prior_tool_groups >= self.server.max_tool_groups:
                requested_type = (
                    "text/event-stream" if payload.get("stream") else "application/json"
                )
                response_body, response_type = graceful_turn_stop(
                    str(payload.get("model", "kimi-for-coding")),
                    requested_type,
                    (
                        "This worker turn reached its tool-cycle boundary. End the turn now so "
                        "the proof harness can run deterministic checks and continue with fresh "
                        "context."
                    ),
                )
                response_metrics = response_shape(response_body, response_type)
                self.send_response(200)
                self.send_header("Content-Type", response_type)
                self.send_header("Content-Length", str(len(response_body)))
                self.send_header("Connection", "close")
                self.end_headers()
                self.wfile.write(response_body)
                self.close_connection = True
                self.server.audit({
                    "path": self.path,
                    "status": 200,
                    "reordered_groups": reordered,
                    "request_controls": request_controls,
                    "response": response_metrics,
                    "continuations": 0,
                    "forced_turn_stop": True,
                    "forced_turn_stop_reason": "tool_group_limit",
                    "response_attempts": [],
                    "before": before_shape,
                    "after": after_shape,
                })
                return
            upstream_path = self.path
            if self.server.upstream.path and not upstream_path.startswith(self.server.upstream.path):
                upstream_path = self.server.upstream.path.rstrip("/") + "/" + upstream_path.lstrip("/")
            headers = {
                "Authorization": f"Bearer {self.server.api_key}",
                "Content-Type": self.headers.get("Content-Type", "application/json"),
                "Accept": self.headers.get("Accept", "text/event-stream"),
                "Accept-Encoding": "identity",
                "User-Agent": self.headers.get("User-Agent", "codex-kimi-proxy"),
                "Connection": "close",
            }
            continuation_count = 0
            response_attempts = []
            forced_turn_stop = False
            while True:
                request_body = json.dumps(payload, separators=(",", ":")).encode("utf-8")
                connection = http.client.HTTPSConnection(
                    self.server.upstream.hostname,
                    self.server.upstream.port or 443,
                    timeout=7200,
                )
                connection.request("POST", upstream_path, body=request_body, headers=headers)
                response = connection.getresponse()
                response_body = response.read()
                response_type = response.getheader("Content-Type", "application/octet-stream")
                request_id = response.getheader("X-Request-Id")
                response_metrics = response_shape(response_body, response_type)
                response_attempts.append(response_metrics)
                assistant_state = streamed_assistant_state(response_body, response_type)
                should_continue = (
                    response.status == 200
                    and "length" in response_metrics["finish_reasons"]
                    and not assistant_state["has_tool_calls"]
                    and bool(assistant_state["reasoning_content"])
                    and continuation_count < self.server.max_continuations
                )
                connection.close()
                if not should_continue:
                    exhausted_response = (
                        response.status == 200
                        and "length" in response_metrics["finish_reasons"]
                    )
                    if exhausted_response:
                        response_body, response_type = graceful_turn_stop(
                            str(payload.get("model", "kimi-for-coding")), response_type
                        )
                        response_metrics = response_shape(response_body, response_type)
                        forced_turn_stop = True
                    break

                for message in payload.get("messages", []):
                    if isinstance(message, dict) and message.get("role") == "assistant":
                        message.setdefault("reasoning_content", "")
                partial_message = {
                    "role": "assistant",
                    "reasoning_content": assistant_state["reasoning_content"],
                }
                if assistant_state["content"]:
                    partial_message["content"] = assistant_state["content"]
                payload["messages"].append(partial_message)
                payload["messages"].append(
                    {
                        "role": "user",
                        "content": (
                            "Continue directly from the preserved reasoning. Do not restart or "
                            "summarize it. Call the shell tool now to edit the candidate proof or "
                            "compile and fix the current candidate; do not give a final answer. "
                            "Do not use /tmp for helper files."
                        ),
                    }
                )
                thinking = payload.get("thinking")
                if not isinstance(thinking, dict):
                    thinking = {}
                payload["thinking"] = {**thinking, "keep": "all"}
                continuation_count += 1

            self.send_response(response.status, response.reason)
            self.send_header("Content-Type", response_type)
            self.send_header("Content-Length", str(len(response_body)))
            if request_id:
                self.send_header("X-Request-Id", request_id)
            self.send_header("Connection", "close")
            self.end_headers()
            self.wfile.write(response_body)
            self.close_connection = True

            self.server.audit(
                {
                    "path": self.path,
                    "status": response.status,
                    "reordered_groups": reordered,
                    "request_controls": request_controls,
                    "response": response_metrics,
                    "continuations": continuation_count,
                    "forced_turn_stop": forced_turn_stop,
                    "response_attempts": response_attempts,
                    "before": before_shape,
                    "after": after_shape,
                }
            )
        except Exception as exc:  # noqa: BLE001 - return a useful gateway error to Codex.
            body = json.dumps({"error": {"message": f"Kimi proxy failure: {exc}"}}).encode("utf-8")
            self.send_response(502)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Connection", "close")
            self.end_headers()
            self.wfile.write(body)
            self.close_connection = True
            self.server.audit({"path": self.path, "proxy_error": type(exc).__name__})


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--listen", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=0)
    parser.add_argument("--upstream", default="https://api.kimi.com")
    parser.add_argument("--key-file", type=Path, required=True)
    parser.add_argument("--ready-file", type=Path, required=True)
    parser.add_argument("--audit-log", type=Path, required=True)
    parser.add_argument("--tool-reminder-groups", type=int, default=1000)
    parser.add_argument("--max-tool-groups", type=int, default=16)
    parser.add_argument("--max-tokens", type=int, default=8192)
    parser.add_argument("--max-continuations", type=int, default=3)
    args = parser.parse_args()

    api_key = args.key_file.read_text(encoding="utf-8").strip()
    if not api_key:
        raise SystemExit("Kimi key file is empty")
    upstream = urlsplit(args.upstream)
    if upstream.scheme != "https" or not upstream.hostname:
        raise SystemExit("Kimi upstream must be an HTTPS URL")

    args.audit_log.parent.mkdir(parents=True, exist_ok=True)
    if args.tool_reminder_groups < 0:
        raise SystemExit("tool reminder groups must be nonnegative")
    if args.max_tool_groups < 0:
        raise SystemExit("max tool groups must be nonnegative")
    if args.max_tokens <= 0:
        raise SystemExit("max tokens must be positive")
    if args.max_continuations < 0:
        raise SystemExit("max continuations must be nonnegative")
    server = ProxyServer(
        (args.listen, args.port),
        ProxyHandler,
        upstream,
        api_key,
        args.audit_log,
        args.tool_reminder_groups,
        args.max_tool_groups,
        args.max_tokens,
        args.max_continuations,
    )
    host, port = server.server_address
    args.ready_file.write_text(f"http://{host}:{port}/coding/v1\n", encoding="utf-8")
    args.ready_file.chmod(0o600)
    server.serve_forever(poll_interval=0.2)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
