#!/usr/bin/env python3
"""Verify an IMO 2026 Lean candidate against its public problem skeleton."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any


API_URL = "https://axle.axiommath.ai/api/v1/verify_proof"


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def compact(response: dict[str, Any]) -> dict[str, Any]:
    return {
        key: response[key]
        for key in ("failed_declarations", "lean_messages", "tool_messages", "timings", "info")
        if key in response
    }


def post(payload: dict[str, Any], timeout: int, retries: int) -> tuple[dict[str, Any], int]:
    encoded = json.dumps(payload).encode()
    last_error: Exception | None = None
    for attempt in range(retries + 1):
        request = urllib.request.Request(
            API_URL,
            data=encoded,
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        try:
            with urllib.request.urlopen(request, timeout=timeout) as reply:
                response = json.loads(reply.read())
                status = reply.status
            if not isinstance(response, dict) or not isinstance(response.get("okay"), bool):
                raise ValueError("AXLE response lacks a Boolean okay field")
            return response, status
        except urllib.error.HTTPError as exc:
            body = exc.read().decode(errors="replace")
            last_error = RuntimeError(f"HTTP {exc.code}: {body[:2000]}")
            if exc.code != 429 and exc.code < 500:
                break
        except (TimeoutError, urllib.error.URLError, json.JSONDecodeError, ValueError) as exc:
            last_error = exc
        if attempt < retries:
            time.sleep(min(30, 2**attempt))
    assert last_error is not None
    raise last_error


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--problem", required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--original", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--retries", type=int, default=4)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    base = {
        "problem": args.problem,
        "candidate_path": str(args.candidate.resolve()),
        "original_path": str(args.original.resolve()),
        "api_url": API_URL,
        "environment": "lean-4.31.0",
    }
    try:
        candidate = args.candidate.read_text(encoding="utf-8")
        original = args.original.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        result = {**base, "status": "input_error", "okay": None, "error": str(exc)}
    else:
        hashes = {"candidate_sha256": sha256(candidate), "original_sha256": sha256(original)}
        payload = {
            "formal_statement": original,
            "content": candidate,
            "mathlib_options": False,
            "use_def_eq": True,
            "verify_negation": False,
            "ignore_imports": True,
            "environment": "lean-4.31.0",
            "timeout_seconds": 900,
        }
        try:
            response, http_status = post(payload, args.timeout, args.retries)
        except Exception as exc:
            result = {
                **base,
                **hashes,
                "status": "api_error",
                "okay": None,
                "error": f"{type(exc).__name__}: {exc}",
            }
        else:
            okay = response["okay"]
            result = {
                **base,
                **hashes,
                "status": "correct" if okay else "incorrect",
                "okay": okay,
                "http_status": http_status,
                "request_id": (response.get("info") or {}).get("request_id"),
                "response": compact(response),
            }

    report = {"all_okay": result.get("okay") is True, "results": [result]}
    rendered = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    if result["status"] in {"api_error", "input_error"}:
        return 2
    return 0 if result.get("okay") is True else 1


if __name__ == "__main__":
    sys.exit(main())
