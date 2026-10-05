# Monuments Full-Score Solution Plan

## Goal Description

Produce a contest-ready C++20 implementation of IOI 2026 Day 1 task **Monuments**. The implementation must expose exactly

```cpp
long long get_cost(std::vector<int> X, std::vector<int> P);
```

and return the minimum total movement cost, or `-1` precisely when the immovable monuments make a symmetric final configuration impossible. It must be proved and engineered for every stated input, including `N <= 500000`, repeated coordinates, coordinate zero, both coordinate signs, and all values representable by the statement's `int` API.

The deliverables are `solutions/02-monuments/solution.cpp`, a rigorous `README.md`, an executable top-level `test.sh`, and independently authored brute-force/randomized differential checks. Only the supplied statement, starter attachment, and public examples may be used; external solutions and grading data are forbidden.

## Acceptance Criteria

- **AC-1: Exact functional result and grader interface**
  - Positive Tests (expected to PASS):
    - Compile `solution.cpp` with an independently authored harness that includes the supplied header and invokes the exact `get_cost` signature.
    - Reproduce all three permitted public examples.
    - Cover `M = 0`, `M = N`, all coordinates zero, all coordinates on one side, balanced and unbalanced fixed multiplicities, repeated coordinates, odd/even `N`, and movable monuments that optimally stay put, move to zero, pair with one another, or satisfy an ancient monument's deficit.
  - Negative Tests (expected to FAIL for an incorrect implementation):
    - Fixed nonzero multiplicity deficits requiring more counterparts than the number of movable monuments must return `-1` rather than a finite cost.
    - Mutants that greedily match each fixed deficit independently, always send unused movable monuments to zero, assume distinct coordinates, or use 32-bit cost arithmetic must be distinguished by authored exhaustive/random cases.

- **AC-2: Provably full-score algorithm**
  - Positive Tests (expected to PASS):
    - `README.md` derives a globally optimal algorithm from the symmetry constraints and one-dimensional absolute-distance structure, with lemmas covering feasibility, every allowed role of a movable monument, the optimization recurrence/data structure, and the final complexity.
    - Worst-case time must be `O(N log N)` or better and worst-case auxiliary memory `O(N)` or better, with no dependence on coordinate magnitude.
    - A deterministic stress case with `N = 500000` completes under a practical contest limit and does not recurse linearly on the call stack.
  - Negative Tests (expected to FAIL for an incorrect implementation):
    - A quadratic or pseudo-polynomial transition, coordinate-indexed array, exponential matching, or unproved heuristic does not satisfy this criterion.
    - Arithmetic that can overflow before conversion to `long long` does not satisfy this criterion.

- **AC-3: Independent correctness oracle and differential validation**
  - Positive Tests (expected to PASS):
    - Add a small-instance oracle authored from the statement, not copied from the optimized algorithm. It may cancel already balanced ancient counts, enumerate which labeled movable monuments satisfy the remaining reflected ancient destinations, and independently enumerate pairing-versus-zero choices for all leftovers.
    - Run deterministic exhaustive families where feasible and thousands of reproducible random cases (including duplicates and coordinates around zero), comparing the optimized result with the oracle.
    - `./test.sh` rebuilds from source, runs public examples, focused regressions, differential checks, and a maximum-size smoke/performance test without any network or external test corpus.
  - Negative Tests (expected to FAIL for an incorrect implementation):
    - The oracle must not call or transliterate the production recurrence/data structure.
    - Random-only testing without fixed seeds, focused edge cases, or a failure report containing the reproducing input does not satisfy this criterion.

- **AC-4: Submission quality and reproducibility**
  - Positive Tests (expected to PASS):
    - `solution.cpp` is self-contained apart from the supplied header, uses standard C++20, has no `main`, performs no I/O, and compiles cleanly with strict warnings and sanitizers in the authored harness.
    - `README.md` explains the API, mathematical reduction, correctness proof, complexity, file layout, and exact local test command.
    - Scripts use repository-relative paths, leave generated binaries in a disposable build location, and are executable.
  - Negative Tests (expected to FAIL for an incorrect implementation):
    - Debug output, hard-coded sample answers, dependency on unstated libraries, network access, or reliance on files outside this repository is unacceptable.

## Path Boundaries

### Upper Bound (Maximum Scope)

- A full-score `O(N log N)`-or-better C++20 solution and proof.
- An exact independent small-instance oracle, deterministic case generator, randomized differential testing, sanitizer build, maximum-constraint smoke test, and submission-compatible compilation check.
- Documentation sufficient for another contestant to audit every optimization step without outside references.

### Lower Bound (Minimum Scope)

- All four acceptance criteria pass from a clean checkout using `./test.sh`.
- The exact required source exists at `solutions/02-monuments/solution.cpp` and is safe for all stated constraints.

### Allowed Choices

- May use C++20 standard-library containers/algorithms and Python 3 for the independent test driver/oracle.
- May use sorting, dynamic programming, Monge/exchange arguments, min-cost matching reductions, prefix/suffix envelopes, Fenwick/segment trees, or equivalent structures if fully proved.
- Must first establish and use (or rigorously replace) these statement-derived facts:
  - Ancient monuments already balanced at `+a` and `-a` cancel pairwise; every remaining ancient excess at one side forces one movable destination at the reflected coordinate.
  - If the number of forced reflected destinations exceeds the movable count, the answer is impossible.
  - After forced deficits are satisfied, remaining movable monuments may go individually to zero or in pairs to opposite coordinates; for two originals `x <= y`, their optimal unconstrained symmetric-pair cost is `|x + y|`.
  - The difficult global choice is which movable monuments satisfy forced destinations and which participate in movable pairs; it must be optimized jointly rather than greedily.
- Cannot use web access, Git remotes, official or unofficial editorials/solutions, task archives, grading examples, hidden/public grading tests, sibling-worker files, or any unpermitted input source.
- Cannot weaken constraints, edit the immutable plan after tracking begins, or replace the Humanize RLCR loop with a one-shot implementation.

## Dependencies and Sequence

### Milestones

1. **Mathematical reduction and scalable recurrence**
   - Formalize the fixed-count cancellation, forced reflected destinations, and movable-only symmetric completion.
   - Derive a global optimization exploiting sorted coordinates and absolute-cost/Monge structure.
   - Prove feasibility, recurrence invariants, transition completeness, and `O(N log N)`-or-better complexity before trusting implementation-specific shortcuts.

2. **Reference oracle and tests first**
   - Implement a statement-level bitmask/enumerative oracle for small movable counts.
   - Add public-example parsing and focused hand-authored cases.
   - Set deterministic seeds and make mismatches print a standalone reproducer.

3. **Production implementation**
   - Implement only the proved recurrence/data structure behind the exact grader API.
   - Use `long long` for coordinates once arithmetic begins, costs, sentinels, and intermediate sums.
   - Keep memory contiguous and stack usage bounded for `N = 500000`.

4. **Validation and proof audit**
   - Run strict-warning, optimized, and address/undefined-sanitizer builds.
   - Run exhaustive/differential cases and maximum-size deterministic stress patterns.
   - Check each proof lemma against code invariants and add a regression for every RLCR-discovered defect.

5. **Submission packaging and review closure**
   - Finish `README.md`, executable `test.sh`, and clean source layout.
   - Ensure no generated binary, external data, or grading material is committed.
   - Let the Humanize implementation and code-review phases run until `complete-state.md` is produced, then commit the reviewed artifacts.

## Implementation Notes

- `X` is nondecreasing, but removing ancient indices leaves a nondecreasing movable sequence; exploit this directly.
- Count multiplicities, not just distinct ancient coordinates.
- Coordinate negation and absolute value must occur after widening to `long long` (notably for the full `int` range).
- If using an infinity sentinel, leave enough headroom that additions cannot overflow.
- The production code must not contain planning vocabulary such as acceptance-criterion or milestone labels.
- Tests must remain independently authored under this repository (for example `selftest/`) and must never inspect external paths.
