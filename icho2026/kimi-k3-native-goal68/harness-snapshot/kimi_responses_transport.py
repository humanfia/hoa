"""Responses relay: put same-turn assistant prose before pending tool calls.

NVIDIA's Kimi converter otherwise loses tool-name resolution. No messages,
tool arguments, outputs or images are removed. Logs contain structure only.
"""
import hmac
import json
import threading
import time
import random
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import requests


class RequestPacer:
    def __init__(self, spacing=2.0, clock=time.monotonic, sleep=time.sleep):
        self.spacing, self.clock, self.sleep = spacing, clock, sleep
        self.lock = threading.Lock()
        self.next_start = 0.0
        self.cooldown_until = 0.0

    def wait(self):
        while True:
            with self.lock:
                now = self.clock()
                delay = max(self.next_start, self.cooldown_until) - now
                if delay <= 0:
                    self.next_start = now + self.spacing
                    return
            self.sleep(min(delay, 1.0))

    def defer(self, seconds):
        with self.lock:
            self.cooldown_until = max(self.cooldown_until, self.clock() + seconds)


def post_with_backoff(send, pacer, audit, attempts=6):
    """Retry only rejected HTTP requests, never a partially consumed SSE stream."""
    for attempt in range(attempts):
        pacer.wait()
        response = send()
        audit({'event':'upstream_attempt','attempt':attempt+1,'status':response.status_code})
        if response.status_code not in (429,503) or attempt == attempts-1:
            return response
        try:
            delay = float(response.headers.get('Retry-After', '60'))
        except ValueError:
            # Non-numeric provider guidance is forwarded rather than shortened.
            return response
        if delay > 180:
            return response
        delay = max(60.0, delay)
        pacer.defer(delay)
        audit({'event':'shared_cooldown','seconds':delay})
        response.close()


def normalize_items(items):
    """Keep pending tool calls adjacent to their results, after assistant prose."""
    changes = 0
    for i in range(len(items)-1, -1, -1):
        if items[i].get('type') == 'message' and items[i].get('role') == 'assistant':
            j = i
            while j > 0 and items[j-1].get('type') in ('function_call', 'custom_tool_call'):
                j -= 1
            if j != i:
                items.insert(j, items.pop(i))
                changes += 1
    return changes


def start_relay(key, audit_path):
    lock = threading.Lock()
    request_slots = threading.BoundedSemaphore(8)
    pacer = RequestPacer()

    def audit(value):
        with lock, audit_path.open('a') as log:
            log.write(json.dumps(dict(at=time.time(), **value)) + '\n')

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def do_POST(self):
            if not hmac.compare_digest(self.headers.get('Authorization', ''), 'Bearer ' + key):
                self.send_error(401)
                return
            if self.path != '/v1/responses':
                self.send_error(404)
                return
            body = self.rfile.read(int(self.headers.get('Content-Length', '0')))
            try:
                data = json.loads(body)
                reordered = normalize_items(data.get('input', []))
                body = json.dumps(data).encode()
                structure = []
                for item in data.get('input', []):
                    if not isinstance(item, dict):
                        continue
                    meta = {k:item[k] for k in ('type', 'role', 'call_id', 'name') if k in item}
                    output = item.get('output')
                    if isinstance(output, list):
                        meta['output_types'] = [x.get('type') for x in output if isinstance(x, dict)]
                    structure.append(meta)
                audit({'event':'request', 'items':structure, 'reordered':reordered, 'stream':data.get('stream'),
                       'tool_types':[x.get('type') for x in data.get('tools', [])]})
                request_slots.acquire()
                try:
                    response = post_with_backoff(lambda: requests.post('https://inference-api.nvidia.com/v1/responses',
                        headers={'Authorization':'Bearer '+key, 'Content-Type':'application/json'},
                        data=body, stream=True, timeout=(30, 600)), pacer, audit)
                except Exception:
                    request_slots.release()
                    raise
                try:
                    audit({'event':'response', 'status':response.status_code})
                    self.send_response(response.status_code)
                    self.send_header('Content-Type', response.headers.get('Content-Type', 'application/json'))
                    self.send_header('Connection', 'close')
                    if response.status_code in (429,503):
                        # Keep provider guidance; otherwise use a conservative cooldown.
                        retry_after = response.headers.get('Retry-After', str(60 + random.randrange(30)))
                        self.send_header('Retry-After', retry_after)
                        audit({'event':'retry_guidance','status':response.status_code,'retry_after':retry_after})
                    self.end_headers()
                    for chunk in response.iter_content(chunk_size=4096):
                        self.wfile.write(chunk)
                        self.wfile.flush()
                finally:
                    response.close()
                    request_slots.release()
            except (BrokenPipeError, ConnectionResetError):
                audit({'event':'client_disconnected'})
            except Exception as exc:
                audit({'event':'transport_error', 'exception_type':type(exc).__name__})
                self.close_connection = True

    server = ThreadingHTTPServer(('127.0.0.1', 0), Handler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    return server
