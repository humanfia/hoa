# Code Review - Round {{CURRENT_ROUND}}

Read the implementation plan at @{{PLAN_FILE}}, the worker prompt at
@{{PROMPT_FILE}}, the goal tracker at @{{GOAL_TRACKER_FILE}}, and the candidate.
The worker cannot declare success; independently decide whether every acceptance
criterion is satisfied.

## Worker Summary

{{SUMMARY_CONTENT}}

## Deterministic Runner Gate

The runner launches this review only after the forbidden-marker scan, source
preservation validator, Lean target compilation, and real Landrun-backed
Comparator replay all pass. Treat the embedded logs as evidence, but rerun the
target Lean compilation before the AXLE call. Do not rerun Comparator.

{{COMMIT_HISTORY_SECTION}}

## Mandatory AXLE Verification

The candidate is `<candidate-file>`. Verify it against its original statement
using the same-round output artifact:

```bash
axle_status=2
for axle_delay in 0 30 120; do
  if [ "$axle_delay" -gt 0 ]; then sleep "$axle_delay"; fi
  if python3 "{{AXLE_VERIFIER}}" \
      --candidate <candidate-file> \
      --original "{{ORIGINAL_FILE}}" \
      --problem PROBLEM_ID \
      --retries 4 \
      --output "{{REVIEW_RESULT_FILE}}.axle.json"; then
    axle_status=0
  else
    axle_status=$?
  fi
  if [ "$axle_status" -ne 2 ]; then break; fi
done
test "$axle_status" -eq 0
```

The rendered reviewer prefix identifies `PROBLEM_ID`; replace both placeholders
with that exact identifier before running the command. Exit `0` is verified,
exit `1` is a real AXLE rejection, and exit `2` is unavailable infrastructure.
Retry only exit `2`. A completed same-round artifact may be reused only when its
candidate and original SHA-256 values match the current files and `okay` is a
Boolean.

Use Lean 4.31.0 AXLE settings: `mathlib_options=false`, `use_def_eq=true`,
`verify_negation=false`, `ignore_imports=true`, and `timeout_seconds=900`.
Do not use web search or any network resource except this AXLE call. Never edit
the candidate.

## Review Result

Write the review to @{{REVIEW_RESULT_FILE}}. Include:

- Mainline Gaps
- Blocking Side Issues
- Queued Side Issues
- `Mainline Progress Verdict: ADVANCED / STALLED / REGRESSED`
- `ACs: X/5 addressed | Forgotten items: N | Unjustified deferrals: N`
- AXLE candidate/original paths, hashes, status, Boolean `okay`, and request ID

If any proof hole, local failure, AXLE rejection/unavailability, deferral, or
pending task remains, give concrete feedback for the next worker round and do
not output `COMPLETE`.

Only when all five acceptance criteria pass, end @{{REVIEW_RESULT_FILE}} with a
separate final line containing exactly:

```text
COMPLETE
```
