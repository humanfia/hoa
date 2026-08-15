# Tiling Game Full-Score Implementation Plan

## Goal Description

Implement and rigorously justify a deterministic online strategy for the unrestricted Tiling Game with `1 <= N, M <= 100`. The implementation must expose exactly the contestant API

```cpp
void init(int N, int M);
std::pair<int, int> receive_block(int TL, int TR, int BL, int BR);
```

and must place every unrotated block immediately, using every even-aligned `2 x 2` board position exactly once, while ensuring that no all-black `2 x 2` cell square ever appears. The solution must not depend on future blocks, grading examples, hidden tests, network resources, randomness, undefined behavior, or grader adaptivity.

Only the supplied English statement, supplied contestant attachment, public sample in that attachment, and tests created inside this repository may be used as problem evidence.

## Acceptance Criteria

- AC-1: Exact contestant artifact and API
  - Positive Tests (expected to PASS):
    - `solutions/03-tiling/solution.cpp` compiles under GNU C++20 when linked to a harness declaring the exact two required procedures.
    - The file has no `main`, performs no input/output, and returns a `std::pair<int, int>` for every block.
  - Negative Tests (expected to FAIL):
    - A compile check rejects missing, renamed, overloaded-only, or incorrectly typed API procedures.
    - A static check rejects a submitted `main` or direct stdin/stdout interaction in the solution artifact.

- AC-2: Legal online placement for all dimensions and calls
  - Positive Tests (expected to PASS):
    - For every tested `1 <= N, M <= 100`, exactly `N*M` successive calls return distinct top-left positions `(2*r, 2*c)` with `0 <= r < N` and `0 <= c < M`.
    - State is correctly reset by repeated `init` calls in the same process.
  - Negative Tests (expected to FAIL):
    - The independent checker detects odd, out-of-range, duplicate, missing, or post-capacity placements.
    - The checker detects any use of future block data; the harness supplies blocks strictly one call at a time and retains no sequence API visible to the solution.

- AC-3: Safety for the unrestricted block set
  - Positive Tests (expected to PASS):
    - Every self-authored exhaustive campaign within feasible small dimensions, over all 15 allowed non-all-black block colorings, completes without any all-black `2 x 2` square after each placement.
    - Adversarial and randomized campaigns cover all-white blocks, each single-white orientation, mixed numbers of white tiles, long homogeneous runs, alternating orientations, boundary-heavy patterns, and dimensions with `N=1`, `M=1`, odd/even sides, and `N,M=100`.
  - Negative Tests (expected to FAIL):
    - Checker unit tests intentionally feed a known-invalid placement strategy and confirm detection of both overlap and all-black `2 x 2` formation.
    - Checker unit tests confirm that an all-black input block is rejected as outside the statement contract.

- AC-4: Mathematical proof covers the full online claim
  - Positive Tests (expected to PASS):
    - `solutions/03-tiling/README.md` defines the strategy and its state precisely, proves availability of every returned position, proves the online property, and proves safety for every possible dangerous `2 x 2` alignment.
    - The proof explicitly handles internal block squares, squares straddling one macro-cell boundary, squares straddling both a row and column boundary, degenerate one-row/one-column macro-grids, and completion after exactly `N*M` calls.
    - Every non-obvious invariant in the proof maps directly to identifiable implementation state and transitions.
  - Negative Tests (expected to FAIL):
    - Review rejects arguments that assume a favorable arrival order, rely on the fixed-but-hidden future sequence, cover only the single-white case without a valid reduction, or establish only final-board safety rather than safety after each placement.

- AC-5: Independent, reproducible validation
  - Positive Tests (expected to PASS):
    - An executable repository-root `test.sh` builds the solution with strict warnings and sanitizers where supported, then runs checker self-tests, exhaustive small-state validation, deterministic adversarial suites, and seeded randomized validation.
    - The checker is independently implemented rather than reusing the solution's safety logic or placement state, scans the concrete `2N x 2M` cell board after each move, and emits actionable diagnostics on failure.
    - The full test script completes in a practical local runtime and clearly reports success.
  - Negative Tests (expected to FAIL):
    - Deliberately injected invalid strategies are caught by checker self-tests.
    - Build/test commands propagate nonzero status for compilation errors, sanitizer errors, illegal moves, incomplete placement, or unsafe boards.

- AC-6: Quality, isolation, and delivery
  - Positive Tests (expected to PASS):
    - The implementation is bounded for `N,M <= 100`, has documented time and memory complexity, and uses no network, filesystem, environment, clock, or nondeterministic dependencies.
    - Repository history contains the plan, implementation, documentation, checker, test script, and Humanize RLCR evidence, with a clean final worktree.
  - Negative Tests (expected to FAIL):
    - Review rejects copied solution material, access to grading examples/test cases, access to any external `tests` path, or dependence on files outside this isolated repository at build/test time.

## Path Boundaries

### Upper Bound (Maximum Scope)

A full-score C++20 contestant implementation, a rigorous derivation/proof, and a standalone validation system sufficient to challenge legality and safety across exhaustive feasible state spaces and large deterministic/randomized stress campaigns. Humanize review evidence and reproducible commands are included.

### Lower Bound (Minimum Scope)

The exact solution artifact, proof-quality README, executable `test.sh`, independent checker, and successful validation required by every acceptance criterion. A subtask-only strategy, empirical-only argument, or one-shot unreviewed implementation is not acceptable.

### Allowed Choices

- Can use: standard C++20, deterministic in-memory state, the supplied contestant API/header/grader as interface references, public sample data, self-authored tests under this repository, brute force or model exploration for validating small cases, and assertions in test-only code.
- Cannot use: web/network access, Git remotes, official or unofficial editorials/solutions, task-archive or grading tests/examples, future block knowledge, rotation, randomness as part of correctness, changes outside this repository, or any path named `tests` outside self-authored repository content.
- The implementation may reduce a multi-white block to one selected white corner only if the proof establishes that this reduction is conservative and the tests still exercise all 15 legal colorings.
- Keep `plan.md` immutable after RLCR initialization. Do not encode plan terminology such as `AC-`, milestones, or review-loop mechanics in production solution code.

## Dependencies and Sequence

### Milestones

1. Formalize the game and derive the strategy
   - Enumerate the geometrically distinct `2 x 2` danger windows relative to the fixed even-aligned block slots.
   - Derive a deterministic online placement invariant that works for every arrival sequence of the 15 legal block types.
   - Stress the invariant with a small independent search/model before relying on it in code.

2. Implement the contestant API
   - Create `solutions/03-tiling/solution.cpp` with complete state reset in `init` and one legal immediate decision per `receive_block` call.
   - Keep the implementation compact, deterministic, standard-compliant, and independent of harness-only facilities.

3. Build an independent oracle and campaigns
   - Implement a concrete-cell legality/safety checker and checker self-tests.
   - Add exhaustive feasible exploration over legal colorings and dimensions selected to expose boundary/corner interactions.
   - Add crafted adversarial generators and deterministic seeded randomized campaigns, including maximum dimensions.

4. Prove and document
   - Explain the construction from first principles without citing external solution material.
   - Prove position availability, uniqueness, online behavior, all danger-window cases, termination, and complexity.
   - Document exact build/test/delivery usage and the scope of validation.

5. Validate and review to completion
   - Run `test.sh`, strict compiler diagnostics, sanitizers where supported, and independent review.
   - Resolve every correctness or proof concern surfaced by Humanize; do not finalize while a material concern remains.
   - Confirm exact artifact paths, executable permissions, repository cleanliness, and committed Humanize completion evidence.

## Implementation Notes

- Treat the board as an `N x M` grid of fixed macro-slots, but validate safety on the actual `2N x 2M` tile grid.
- A safety proof must account for danger windows whose top-left coordinate has parity `(0,0)`, `(0,1)`, `(1,0)`, or `(1,1)`; the internal `(0,0)` case alone is insufficient.
- Because all-black blocks are forbidden, selecting one witnessed white tile can simplify reasoning, but extra white tiles must never invalidate assumptions about classification or state transitions.
- Exhausting all length-`N*M` input sequences becomes exponential quickly. Use complete enumeration only where feasible; augment it with state deduplication/model exploration, targeted adversaries, and long randomized runs. State clearly what is proven versus empirically tested.
- Keep the checker structurally independent: reconstruct tile colors from returned coordinates, scan all physical `2 x 2` windows after every move, and separately track macro-slot occupancy.
- Do not inspect or import any grading tests. The public sample is a smoke test, not evidence of full correctness.
