# IOI 2026 Day 2 — Partition: Corrected Full-Score Plan

## Goal Description

Produce a submission-quality C++17 implementation of the exact procedures

```cpp
std::vector<int> add_numbers(std::vector<int> A, int K, int M);
std::vector<int> find_partition(std::vector<int> B, int K);
```

for every legal `3 <= N <= 100000`, `2 <= K <= N`,
`1 <= A[i] <= M <= 10^9`.  The first procedure returns at most `K-1` values
in `[1,M]`.  After those values are appended and sorted, the second procedure,
in a separate execution receiving only sorted `B` and `K`, labels every element
into exactly `K` nonempty groups of equal sum.

Implement and prove the deterministic perturbed-contiguous-block construction:
sort `A`; encode `w[i] = A[i] * Q + (i+1)` for
`Q = N(N+1)/2 + N + 1`; binary-search the least capacity `ans` for which the
positive sequence `w` is greedily split into at most `K` contiguous segments;
let `Z = floor(ans/Q)`; append each segment's positive deficit to sum `Z`, then
append `Z` for missing groups.  From `B,K` alone, compute `Z=sum(B)/K` and fill
each group by repeatedly taking the greatest unused value not exceeding its
remaining capacity, implemented with binary search and predecessor DSU.

The immutable statement and this implementation plan are the only permitted
task evidence. Implement the construction independently and prove the result
locally. Never inspect or import official or alternative solutions, archive
tests, subtasks, incorrect solutions, graders, grading examples, hidden data,
contestant attachments, sibling repositories, or other solution sources.
Nested implementation/review processes have web and network disabled and may
read only this repository.

## Acceptance Criteria

- AC-1: Exact APIs and the two-execution boundary are implemented.
  - Positive Tests (expected to PASS):
    - A C++17 grader compiles and links both exact signatures from
      `solutions/03-partition/solution.cpp`, with no contestant `main`.
    - `add_numbers` and `find_partition` run in distinct processes; only sorted
      `B` and `K` cross into the second process.
    - The returned label vector has `B.size()` entries, every label is in
      `[0,K)`, every label occurs, every position is used once, and all sums are
      equal.
  - Negative Tests (expected to FAIL):
    - Compile fixtures reject wrong signatures, an extra required entry point,
      or non-C++17 dependencies.
    - A state-sharing mutant fails after memory, working directory, environment,
      and temporary protocol state are isolated between executions.

- AC-2: The first procedure implements the proved canonical construction and
  returns legal additions on the full domain.
  - Positive Tests (expected to PASS):
    - Sorting, `Q`, perturbed weights, greedy feasibility, minimal-capacity
      binary search, `Z`, segment deficits, and missing-group additions agree
      with an independent specification on exhaustive small inputs.
    - For every tested legal input, `0 <= |C| <= K-1` and
      `1 <= C[i] <= M`; `sum(A)+sum(C)=K*Z`.
    - Tests include zero deficits, fewer than `K` greedy segments, `M=1`,
      `K=2`, `K=N`, duplicate-heavy arrays, and `M=10^9`.
  - Negative Tests (expected to FAIL):
    - Mutants for a nonminimal capacity, wrong `Q`, wrong residue index,
      omitted final deficit, omitted missing group, zero deficit emission,
      `K` additions, and 32-bit perturbed arithmetic are detected.

- AC-3: The second procedure reconstructs a valid partition from sorted `B,K`
  alone.
  - Positive Tests (expected to PASS):
    - It derives the target only as `sum(B)/K` and repeatedly removes the
      greatest unused value at most the current remainder using `upper_bound`
      plus predecessor DSU.
    - Each of the `K` group fills terminates at remainder zero, including with
      ties, indistinguishable original/added copies, and values equal to `Z`.
    - Labels correspond to positions in sorted `B`; every position is removed
      exactly once and all labels occur.
  - Negative Tests (expected to FAIL):
    - Checker fixtures reject a dead-end remainder, stale DSU predecessor,
      duplicate position, unused item, bad label, empty group, or unequal sum.
    - Mutants that receive or recover `A`, `M`, `C`, original indices, first-run
      bins, files, retained globals, or shared randomness fail isolation audit.

- AC-4: A rigorous proof covers the complete constructor-decoder theorem.
  - Positive Tests (expected to PASS):
    - `docs/solution.md` proves greedy segment feasibility for a fixed capacity
      and correctness of the least-capacity binary search on positive weights.
    - It proves why the residue perturbation and the gap in `Q` force every
      segment deficit and every missing-group `Z` into `[1,M]`, and why no more
      than `K-1` additions are emitted, including all terminal cases.
    - It proves total sum `K*Z` and the central induction/exchange lemma that
      descending greatest-fit reconstruction cannot get stuck on any multiset
      produced by the constructor.
    - It proves termination, exact use of all elements, nonempty groups,
      duplicate/tie safety, and statelessness after sorting.
    - It proves `O(N log(sum w) + (N+K) log(N+K))` time (or a tighter valid
      bound), `O(N+K)` memory, `__int128` safety for perturbed weights/totals,
      and 64-bit safety for ordinary sums and targets.
  - Negative Tests (expected to FAIL):
    - Review rejects an argument based only on total divisibility, an assumed
      remembered partition, distinguishable equal copies, empirical greedy
      success, or a deficit/missing-group bound without the minimality lemma.
    - Any mismatch among proof, production tie-breaking, and test specification
      blocks acceptance.

- AC-5: Independent exact and differential validation exercises the theorem,
  not merely examples.
  - Positive Tests (expected to PASS):
    - A self-authored oracle, sharing no production helpers, independently
      computes the construction and uses exact backtracking/DP to validate an
      equal-sum certificate on tractable cases.
    - Exhaustively enumerate sorted histograms over a documented envelope at
      least as strong as all `N<=8`, `M<=6`, all legal `K`, plus focused larger
      boundary states for each proof lemma.
    - Compare production additions and production-linked two-process decoding
      to the independent specification/checker, and retain every historical
      scheduler/packing counterexample as a regression.
    - Deterministic randomized and adversarial campaigns record seeds and cover
      equal perturbed-capacity ties, final-segment boundaries, missing groups,
      maximal deficits, duplicate predecessor chains, sparse alphabets, and
      neighboring histograms.
  - Negative Tests (expected to FAIL):
    - Seeded mutants for off-by-one count, residue, binary-search endpoint,
      segment reset, target, predecessor deletion, duplicate ties, overflow,
      and cross-run state are each killed by a named test.
    - The oracle may not define correctness by calling the same greedy decoder
      or any helper from production.

- AC-6: Maximum-scale, robustness, and arithmetic tests are reproducible.
  - Positive Tests (expected to PASS):
    - Strict warnings and ASan/UBSan runs cover exhaustive and randomized suites.
    - Release stress covers `N=K=100000`, `N=100000,K=2`, `M=1`,
      `M=10^9`, all equal values, alternating extremes, long duplicate runs,
      and seeded random/skewed distributions within documented time/memory
      limits.
    - Tests explicitly reach perturbed products and totals beyond signed 64-bit
      while checking the public `int` return-value range.
  - Negative Tests (expected to FAIL):
    - Compiler failure, sanitizer finding, timeout, crash, malformed protocol,
      oracle mismatch, invalid additions, or bad certificate exits nonzero.

- AC-7: Provenance, packaging, and repository hygiene are auditable.
  - Positive Tests (expected to PASS):
    - Root `./test.sh` uses an ignored temporary build directory, needs no
      network, and passes from a clean checkout.
    - Preserve statement SHA-256
      `91db6aa3531da46801816ecbd2ecd1f96fcd09a36a1ed7442513582543751c8c`.
    - Documentation records the single authorized theorem-source commit/path/
      digest and explicitly attests that no forbidden archive or grading data
      entered the repository, tests, oracle, or implementation.
    - Deliver only production source, proof, statement-derived stubs/checker,
      self-authored tests/oracle, root test script, and concise reproduction
      docs; generated files, credentials, `.humanize/`, and build products stay
      ignored and untracked.
    - Final root `./test.sh` passes, Git status is clean, and native Humanize
      completion exists at the fresh run's `complete-state.md`.
  - Negative Tests (expected to FAIL):
    - Statement corruption, forbidden-source provenance, tracked runtime state,
      leaked credentials, absolute external dependencies, network use, or build
      artifacts fail the audit.

## Path Boundaries

### Upper Bound (Maximum Scope)

A full-score standard-library C++17 solution; complete theorem proof; exact
two-process grader; structurally independent construction specification,
certificate checker, and exact oracle; exhaustive, differential, mutation,
adversarial, sanitizer, and maximum-scale tests; and minimal reproducibility and
provenance documentation.

### Lower Bound (Minimum Scope)

No result is acceptable without both exact procedures, proved `K-1` legal
additions, proved stateless decoding for every constructor output, production-
linked independent validation, passing root `test.sh`, clean packaging, and a
genuine native Humanize `complete-state.md`.  Examples or empirical evidence
alone are insufficient.

### Allowed Choices

- Use deterministic sorting, greedy positive-sequence segmentation, binary
  search, `__int128`, `int64_t`, `upper_bound`, and predecessor DSU.
- Independently reorganize and name the implementation; do not copy the
  authorized source verbatim.
- Optimize the self-authored oracle separately, provided it stays independent
  from production and its exhaustive envelope is documented.
- Derive local API stubs and protocol serialization only from the statement.
- Do not alter this plan, the original `plan.md`, `AGENTS.md`, or statement after
  the fresh baseline commit.
- Do not read/import any archive path except the single authorized model file;
  never access tests, subtasks, incorrect solutions, graders, grading examples,
  hidden data, contestant attachments, sibling work, or other external code.
- Nested workers/reviewers must not use web/network or read outside this repo.
- Do not weaken the theorem to heuristic or randomized correctness, and do not
  use persistent communication between the two procedures.

## Dependencies and Sequence

### Milestones

1. Freeze contract, provenance, and proof obligations.
   - Reconfirm exact signatures, sorting semantics, two-execution isolation,
     limits, statement hash, and single-source authorization.
   - Write the constructor and decoder as mathematical pseudocode, then prove
     the perturbation/minimal-capacity lemmas before relying on implementation.

2. Implement independent validation first.
   - Build a certificate checker, exact small partition oracle, and independent
     constructor specification without production helpers.
   - Encode historical counterexamples and exhaustive small histograms; require
     the explicit theorem to survive before production acceptance.

3. Implement and link production.
   - Add the two exact procedures using checked integer domains and deterministic
     tie-breaking matching the proof.
   - Exercise the compiled production code through separate first/second-run
     executables and compare with the independent checker/specification.

4. Broaden robustness and complete the proof.
   - Add mutation, randomized, metamorphic, adversarial, sanitizer, and maximum-
     scale campaigns; investigate every mismatch before proceeding.
   - Finish `docs/solution.md` with all edge cases, central decoder induction,
     duplicate-position mapping, and complexity/arithmetic bounds.

5. Package and audit.
   - Make root `test.sh` hermetic and executable, document reproduction and
     provenance, verify statement integrity and tracked-file scope, then run the
     complete suite from repository root.
   - Finish only after native Humanize review accepts every criterion, writes
     `complete-state.md`, root tests pass, and Git status is clean.

## Implementation Notes

- Perturbed values and their sum may exceed signed 64-bit: convert operands to
  `__int128` before multiplication/addition and binary-search in that type.
- Ordinary `A/B` sums and `Z` fit signed 64-bit; validate every conversion back
  to API `int` for appended values.
- Use exact positive-sequence greedy semantics: begin a new segment precisely
  when adding the next perturbed item would exceed the tested capacity.
- In decoding, DSU index `0` is a sentinel and deleting an item links it to its
  nearest live predecessor.  Specify `upper_bound(rem)` and duplicate behavior
  exactly so proof, source, and oracle agree.
- Positivity plus `K<=N` supports nonemptiness, but the proof and checker must
  still verify every group label is used.
- `test.sh` must not read `.humanize` or paths outside the repository and must
  clean temporary processes/files on every exit.
- Production comments should describe invariants, not planning or acceptance-
  criterion labels.
