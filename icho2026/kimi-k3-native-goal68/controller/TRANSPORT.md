# Kimi native-goal transport compatibility

This fresh 68-subquestion answer-blind experiment uses native Codex 0.153.4
persisted goals and NVIDIA model `nvidia/moonshotai/kimi-k3`, maximum 32 jobs.
It does not use the Humanize review/redraft loop or old generated answers.

Preflight 08 passed image reading, shell/patch tools, Lean compilation, native
goal completion, and an independent Lean check. Earlier failed preflights are
retained separately; no formal solver job ran during those diagnostics.

The NVIDIA Responses gateway rejected native requests where assistant prose
appeared between pending tool calls and their results. A controlled diagnostic
of the failing request returned HTTP 200 after moving that same-turn prose
before the calls; removing custom tool definitions, reasoning, or IDs did not
fix it. Adding names to tool results also did not fix it.

A loopback-only authenticated relay now applies that ordering normalization.
It preserves original messages, tool arguments, outputs, images and reasoning,
and otherwise forwards Responses/SSE. It does not invent tool results or alter
scientific conditions. Structural audit logs exclude headers and message bodies.
The credential is held in process environments/memory, not in this release.

An explicit model catalog enables text and image input. The client context
limit is conservatively 128000. Requested reasoning effort is xhigh; provider
interpretation is not assumed equivalent to GPT's effort settings. The base
coding-agent instruction template is inherited from the available public Codex
model metadata with the model identity changed to Kimi-K3.

Solver goal completion and Lean compilation are not semantic certification or
official-answer accuracy. Independent validation and scoring remain separate.

## Rate-limit recoveries

Two provider-wide 429 interruptions required resuming the same native threads.
All original status snapshots are retained in `transport-recovery-*` folders;
the solver answers and proofs were not edited by the controller. Only audited
429/503 retry-exhaustion blockers are eligible for this recovery, never a
scientific/source blocker. Completed goals are left untouched.

The first recovery limited upstream concurrency to 8 and spaced starts by one
second, forwarding Retry-After guidance. A later burst of 429 responses still
exhausted native retries. The second recovery spaces starts by two seconds and
adds a shared cooldown of at least 60 seconds, with at most six attempts of an
HTTP-rejected request. Partially consumed successful streams are never replayed
by this adapter. The solver job cap remains 32; effective provider throughput
is lower and is not equivalent to unconstrained 32-request concurrency.

Each recovery receipt records its exact adapter snapshot and target list.
These transport interruptions are not chemical proof failures and are not
grounds for reporting successful semantic certification.
