# Classroom Game — Full-Score Contestant Solution Plan

## Goal Description

Implement and validate a deterministic, production-quality contestant strategy for the IOI 2026 Day 2 task **Classroom Game** using only `problem/statement-en.pdf` (SHA-256 `19c007bc47da7f1e6f57c8d54b7a3bf63f0e264c15bd8bcd9287a73aad9a1aef`). The strategy must be correct for every legal game, must remain correct when every API call is executed in a different process, and must guarantee that every paper returned by `process_step` contains at most **two** integers. The last condition is a hard acceptance requirement because `C <= 2` earns the full `1.00` scoring multiplier in every subtask.

The final repository must contain the exact contestant implementation at `solutions/01-classroom/solution.cpp`, a rigorous self-contained explanation/proof, self-authored local API support and validation, and an executable root `test.sh`. No grading data, official attachment, solution, editorial, or other task material may be used.

## Official Contract and Evidence Boundary

- The sole official artifact is the tracked English statement PDF. Do not inspect sibling repositories, task archives, caches, testdata, graders, attachments, reports, the web, or the network.
- No official contestant attachment is available. Reconstruct only the declarations needed to compile locally, in a clearly identified self-authored mock header under `tests/support/`; do not present it as official.
- Legal bounds are `2 <= N <= 63` and `1 <= M <= 63`. Each student occurs in at most one raising set, every raising set is sorted, and every step leaves at least one student not raising.
- A game starts with `N` empty papers. After the teacher returns `B` in step `R`, the hidden fixed permutation is applied as `next[P[i]] = B[i]` for every `i`.
- The teacher API is exactly:

  ```cpp
  std::vector<std::vector<int>> process_step(
      int N, int M, int R,
      std::vector<int> T,
      std::vector<std::vector<int>> A);
  ```

- The headmaster API is exactly:

  ```cpp
  std::vector<int> determine_steps(
      int N, int M,
      std::vector<std::vector<int>> A);
  ```

- `process_step` is called for `R = 0, 1, ..., M-1`. It must return exactly `N` papers; for every `i` in `T`, `B[i]` must equal `A[i]` byte-for-byte; every returned integer must be in `[0, 63]`; and this plan additionally requires every returned paper length to be at most `2`.
- `determine_steps` is called once after the final permutation and must return exactly `N` values. Entry `i` must be the unique step when student `i` raised, or `-1` if that never happened.
- Calls from one game may execute in different program instances, and different games may share an instance. The implementation must therefore be a pure function of each call's arguments: no mutable globals/statics, files, environment, process identity, clock, RNG state, thread-local state, retained pointers, or any other cross-call channel.

## Acceptance Criteria

- **AC-1: Exact, legal contestant API and packaging**
  - Positive Tests (expected to PASS):
    - Compile `solutions/01-classroom/solution.cpp` as C++17 against the self-authored `tests/support/classroom.h` with the exact two by-value signatures above.
    - Link it both into an in-process simulator and a single-call subprocess wrapper without a contestant `main` function or symbol conflicts.
    - For every simulated call, verify `B.size() == N`, `D.size() == N`, all paper symbols lie in `[0,63]`, and every paper length is at most `2`.
  - Negative Tests (expected to FAIL):
    - Harness self-checks must reject deliberately malformed responses having the wrong outer length, a paper of length `3`, a symbol outside `[0,63]`, or a result vector of the wrong length.

- **AC-2: Frozen papers are never modified**
  - Positive Tests (expected to PASS):
    - On every generated game and step, retain a copy of `A` and assert exact vector equality `B[i] == A[i]` for every `i` in `T`, including empty, one-element, and two-element frozen papers.
    - Cover `T` empty, singleton, mixed-size, and size `N-1`.
  - Negative Tests (expected to FAIL):
    - A harness negative control that changes, clears, appends to, or reorders one frozen paper must be detected before permutation is applied.

- **AC-3: Universal game correctness under an unknown fixed permutation**
  - Positive Tests (expected to PASS):
    - Independently simulate the game from a chosen ground-truth schedule `Q` and permutation `P`, construct each sorted `T` directly from `Q`, apply exactly `next[P[i]] = B[i]`, and require the final `D` to equal `Q` entry-for-entry.
    - Exhaustively enumerate all legal `Q` and all permutations for `2 <= N <= 4`, `1 <= M <= 4`, and for `N = 5`, `1 <= M <= 3`.
    - Test identity, a full cycle, reverse order, rotations, transpositions, and multiple disjoint-cycle shapes explicitly, without exposing `P` to either contestant procedure.
  - Negative Tests (expected to FAIL):
    - The independent oracle must reject injected wrong answers for never-raised students, off-by-one step answers, identity-only assumptions, and schedules decoded for paper identities instead of student identities.

- **AC-4: Full-score length bound is a proved invariant**
  - Positive Tests (expected to PASS):
    - The construction and proof establish `|B[i]| <= 2` for every legal input, not merely for tested cases; the simulator records a global maximum and asserts it never exceeds `2`.
    - Include adversarial cases where `N=63`, `M=63`, a step has `N-1` raisers, many steps have no raisers, and all `N` raises are spread across different steps.
  - Negative Tests (expected to FAIL):
    - A two-symbol encoding overflow, accidental third metadata field, or fallback representation longer than two must be rejected even when the decoded answer is correct.

- **AC-5: Statelessness across instances and games**
  - Positive Tests (expected to PASS):
    - Run representative complete games with every `process_step` call and the final `determine_steps` call in a newly launched process, serializing only the explicit arguments and returned value through a self-authored wrapper.
    - In one process, interleave calls belonging to several legal games and compare every result with isolated execution; repeat games in different orders and after unrelated games.
    - Source review confirms that all algorithm state is derived from the supplied papers and scalar/vector arguments, with immutable compile-time constants only.
  - Negative Tests (expected to FAIL):
    - A stateful test double whose answer depends on a prior call must pass neither the fresh-process suite nor the interleaving/reordering suite.

- **AC-6: Rigorous construction and correctness proof**
  - Positive Tests (expected to PASS):
    - The explanation defines the exact meaning of each possible empty/one-symbol/two-symbol paper and the teacher update and headmaster decode rules without relying on the hidden permutation.
    - Prove representation legality, update feasibility for every legal `T` (especially `|T|=N-1`), preservation through the fixed unknown permutation, an inductive invariant after every round, uniqueness/completeness of final decoding, and the `-1` case.
    - Explicitly prove that student identity, paper identity, and current holder are not conflated and that calls require no shared state.
    - State justified worst-case time and auxiliary-space bounds within the official `N,M <= 63` domain.
  - Negative Tests (expected to FAIL):
    - Review must block completion for a construction justified only empirically, an invariant that assumes `P` is known/identity, a decoder with ambiguous representations, or an unproved exceptional/fallback branch.

- **AC-7: Independent, adversarial, exhaustive, and stress validation**
  - Positive Tests (expected to PASS):
    - Keep the oracle/simulator structurally independent of production encoding logic: its expected answer is the input `Q`, and its state transition is implemented directly from the statement.
    - Use deterministic seeded random tests across the full range, including thousands of schedules/permutations and dedicated large cases at `(63,1)`, `(63,63)`, `(2,63)`, and varied intermediate dimensions.
    - Include no-raise games; all students raising at distinct steps; exactly one raiser per populated step; `N-1` simultaneous raisers early/middle/last; consecutive-step raisers arranged along and against permutation cycles; schedules with long empty prefixes/suffixes; and five-game batches.
    - Run strict-warning optimized builds plus an address/undefined-behavior sanitizer build on a representative bounded suite. Make failures reproducible by printing the seed and a compact legal case description.
  - Negative Tests (expected to FAIL):
    - Built-in validator self-tests must demonstrate detection of a wrong permutation direction, a skipped final exchange, an illegal paper write, and a corrupted final answer.

- **AC-8: One-command reproducibility and repository hygiene**
  - Positive Tests (expected to PASS):
    - Root `./test.sh` is executable, needs no network or nonstandard task assets, builds in a temporary directory, runs all mandatory suites, and exits nonzero on any compile, contract, correctness, sanitizer, or hygiene failure.
    - A clean checkout on branch `main` can run `./test.sh`; afterward `git status --short` is empty.
    - Final tracked artifacts include the statement, immutable `plan.md`, contestant source, explanation, self-authored support/harness files, `test.sh`, and appropriate ignore rules only.
  - Negative Tests (expected to FAIL):
    - `test.sh` must reject or avoid persistent binaries, logs, core files, generated state, grading data, or tracked `.humanize` content.

## Path Boundaries

### Upper Bound (Maximum Scope)

A single deterministic full-score (`C <= 2`) C++17 solution, a formal proof/explanation, and a local self-authored validation package sufficient to establish the contract for all legal inputs through exhaustive small cases, adversarial edge cases, deterministic stress, sanitizer checks, process-isolation checks, and repository-hygiene checks.

### Lower Bound (Minimum Scope)

The exact production source, self-authored mock declaration, rigorous proof, executable root test runner, independent simulator/oracle, full-score length assertion, cross-process statelessness validation, and clean reproducible Git state. A partial-score strategy, unproved heuristic, examples-only validation, or process-local solution does not meet the goal.

### Allowed Choices

- May use standard C++17 and POSIX shell facilities already present locally for compilation and testing.
- May use deterministic combinatorial, algebraic, graph, or coding constructions, provided every representation and exceptional case is proved and the paper bound is always two.
- May create self-authored API stubs, wrappers, simulators, enumerators, property tests, fuzz/stress generators, proof notes, and fixtures derived solely from the statement.
- May use empty, one-integer, and two-integer papers and any integer symbols in `[0,63]`.
- Must not use network access, web search, Git remotes, outside repositories/files, official or unofficial attachments/graders/tests/solutions/editorials, hidden data, or undocumented grader behavior.
- Must not use mutable cross-call state, undefined behavior, process persistence, nondeterminism, or a paper longer than two as a fallback.
- Must not alter `problem/statement-en.pdf` or this tracked `plan.md` after the Humanize run begins.
- Production code must not contain planning labels such as `AC-`, `Milestone`, or Humanize runtime terminology.

## Dependencies and Sequence

### Milestones

1. **Contract reconstruction and invariant design**
   - Reconstruct the two declarations in a local mock header and document the exact transition direction, frozen-write rule, legal ranges, final output mapping, and stateless execution model.
   - Derive a deterministic two-symbol construction. Before coding, specify its paper grammar, update rule, decoder, and invariant for arbitrary fixed unknown `P`.
   - Check the hardest transitions (`T` empty and `|T|=N-1`), arbitrary permutation cycles, `M=1`, `N=2`, and the final exchange on paper.

2. **Production implementation and proof**
   - Implement only the two required procedures in `solutions/01-classroom/solution.cpp` against the mock declaration.
   - Write the self-contained explanation with lemmas for legality, update feasibility, permutation invariance, inductive preservation, final decode, statelessness, and complexity.
   - Keep the implementation deterministic, warning-clean, and free of mutable global/static state and I/O.

3. **Independent validation infrastructure**
   - Implement a statement-level simulator whose ground truth is `Q` and whose permutation transition is visibly independent of the contestant construction.
   - Add response validation and negative controls before running exhaustive enumeration.
   - Add exhaustive small-domain enumeration, named adversarial cases, deterministic full-range stress, repeated/interleaved games, and the fresh-process single-call wrapper.

4. **Reproducible test and hygiene gate**
   - Implement executable root `test.sh` with temporary builds, strict compilation, optimized tests, bounded sanitizer tests, process-isolation tests, cleanup traps, and meaningful diagnostics.
   - Run the full suite from repository root, verify the statement hash and immutable plan, inspect tracked files, and ensure no build/runtime/grading artifacts remain.

5. **Humanize review and finalize**
   - Address every implementation and independent review finding through the native RLCR rounds, preserving the immutable plan and evidence boundary.
   - Finalize only after all acceptance criteria are proved/tested, `./test.sh` passes from root, Git is clean on `main`, the statement hash matches, and Humanize produces its genuine `complete-state.md`.

## Implementation Notes

- Treat the teacher-visible array as papers currently held by named students, not as persistent paper ownership. The only movement rule in the validator must be `next[P[i]] = B[i]`.
- The hidden permutation is fixed for a game but never an API argument. Any knowledge the construction uses in a later call must be reconstructible solely from that call's papers and other arguments.
- A locally convenient encoding is not acceptable unless the explanation proves that all symbol values remain in `[0,63]`, all arrays remain length at most two, every frozen paper is returned exactly, and the decoder is total and unambiguous on every reachable state.
- Keep validation code conceptually separate from solution code. Do not copy a production decoder into the oracle or derive expected results from returned papers.
- Prefer explicit assertions and compact failure witnesses over silently skipping expensive or difficult cases. Mandatory test counts must remain fixed and deterministic; optional extra stress may accept a seed/count override.
- All runtime state belongs in `.humanize/` and must remain ignored/untracked. Do not manually edit Humanize state or completion files.
