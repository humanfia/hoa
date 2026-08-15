# Magic City Full-Score Construction Plan

## Goal Description

Implement the exact contestant procedure

```cpp
std::pair<std::vector<int>, std::vector<std::pair<int, int>>>
construct(int K);
```

for every statement input `1 <= K <= 50`. The returned attraction types and
undirected walkways must satisfy every stated validity condition, including
every interesting ordered type triple and the degree bound, while meeting the
published full-score attraction target for each of the 50 output-only
subtasks. Provide a deterministic output-file exporter, a statement-semantic
checker independent of the construction, a rigorous proof, and a root test
entrypoint. All work and validation must remain blind: the released English
statement is the only task material, and no official attachments, graders,
tests, editorials, prior solutions, web resources, or sibling repositories may
be read.

The immutable attraction-count target is the full-score threshold `P` printed
in the statement:

| `K` | 1 | 2 | 3 | 4 | 5 | 6 through 50 |
|---:|---:|---:|---:|---:|---:|---:|
| target `N` | 2 | 12 | 24 | 40 | 50 | `12*K` |

There is no scoring benefit to going below `P`. The construction below reaches
these thresholds exactly, so its intended score is the maximum published score
in every subtask. Only generic, self-authored validation may substantiate that
claim.

## Acceptance Criteria

- AC-1: The production source exposes precisely the stated API and constructs
  a syntactically valid park for every `K` from 1 through 50.
  - Positive Tests (expected to PASS):
    - A local runner links against `solutions/02-magiccity/solution.cpp`, calls
      `construct(K)` exactly once, and serializes the result for each legal K.
    - Every returned type lies in `[0, 2*K)`, every one of the `2*K` types is
      represented, every edge endpoint lies in `[0, N)`, and every edge has
      distinct endpoints.
    - Every produced `N` is at most 2000; in fact it equals the target table.
  - Negative Tests (expected to FAIL):
    - The API/build harness rejects a missing or incorrectly typed `construct`
      symbol under strict C++17 compilation.
    - The semantic checker rejects out-of-range types or endpoints, a missing
      type, a loop edge, malformed counts, truncation, and unexpected trailing
      tokens.

- AC-2: Condition 1 holds for every interesting ordered triple, not only for
  sampled triples or cyclic-distance representatives.
  - Positive Tests (expected to PASS):
    - For every legal K, an independent checker exhaustively enumerates all
      `2*K*(2*K-1)^2` ordered triples `(t1,t2,t3)` with `t1 != t2` and
      `t2 != t3` and finds one middle attraction of type `t2` adjacent to both
      required endpoint types.
    - Cases with `t1 == t3` pass while permitting the same adjacent attraction
      to witness both endpoints, exactly as the statement allows.
    - Tests separately audit every cyclic-difference incidence and every pair
      of neighbor differences in the construction tables.
  - Negative Tests (expected to FAIL):
    - A self-authored park with one deliberately uncovered triple is rejected,
      even if all types occur and all degrees are legal.
    - Removing selected construction edges is detected whenever it destroys a
      required witness.

- AC-3: Condition 2 counts walkway incidences exactly, including parallel
  walkways, and no attraction exceeds degree K.
  - Positive Tests (expected to PASS):
    - Generic validation counts each edge occurrence at both endpoints and
      confirms every production attraction has degree exactly K.
    - A structural audit independently confirms that each block contains
      exactly K directed neighbor differences and that the edge pairing uses
      every corresponding stub once.
  - Negative Tests (expected to FAIL):
    - Adding one extra edge incident to an already degree-K attraction is
      rejected.
    - Parallel copies of an edge count separately and can trigger rejection;
      they are not silently deduplicated for the degree check.

- AC-4: The construction reaches the maximum-score target for all 50 subtasks.
  - Positive Tests (expected to PASS):
    - Exhaustive tests assert `N == 2, 12, 24, 40, 50` for K = 1, 2, 3, 4, 5
      respectively and `N == 12*K` for each K from 6 through 50.
    - Tests assert `N <= 2000` and the expected handshake count
      `M == N*K/2` for every K.
  - Negative Tests (expected to FAIL):
    - A valid but oversized fixture fails the score-target assertion.
    - Any regression that adds an attraction, even while staying below 2000,
      fails the all-subtask target audit.

- AC-5: Edge generation is deterministic, complete, and free of accidental
  loops or missing/reused stubs.
  - Positive Tests (expected to PASS):
    - Repeated calls for each legal K return byte-for-byte identical vectors.
    - For each attraction/block/difference incidence, a structural test finds
      exactly one incident edge to the prescribed neighbor type.
    - The edge vector has no duplicate unordered attraction pair (although the
      statement would permit parallel edges).
  - Negative Tests (expected to FAIL):
    - A deleted, duplicated, reversed-table, or incorrectly paired edge is
      caught by structural and/or semantic validation.

- AC-6: Output-only files can be exported reproducibly and checked without any
  official attachment.
  - Positive Tests (expected to PASS):
    - A deterministic exporter emits exactly the statement format: `N M`, one
      line of N types, and exactly M endpoint-pair lines.
    - A documented all-K export command creates one unambiguous file per K,
      and every exported file passes the independent checker.
    - Re-exporting produces identical bytes and stable hashes.
  - Negative Tests (expected to FAIL):
    - Files with a wrong K, inconsistent N/M, missing values, extra values, or
      non-integer tokens are rejected with a nonzero exit status.

- AC-7: The mathematical explanation proves the construction for the complete
  input range and maps it exactly to the API and output formats.
  - Positive Tests (expected to PASS):
    - The proof establishes table size, pairwise intersection, inverse-count
      balance, edge/stub pairing, degree, triple witnesses, bounds, score
      targets, determinism, and all exceptional K = 1 through 5.
    - The explanation distinguishes cyclic directed neighbor differences from
      undirected edges and explicitly handles the self-inverse difference K.
  - Negative Tests (expected to FAIL):
    - Review rejects an argument that assumes the incidence set for difference
      d equals that for `2*K-d`; only their cardinalities are required to agree.
    - Review rejects sampled or probabilistic evidence in place of the
      pairwise-intersection proof.

- AC-8: The repository is strict, reproducible, isolated, and submission-clean.
  - Positive Tests (expected to PASS):
    - `./test.sh` builds all C++ with C++17, optimization, `-Wall -Wextra
      -Werror -pedantic`, runs the complete K=1..50 suite, runs independent
      negative fixtures, and leaves no products in the repository.
    - A sanitizer-enabled build/run covers representative and boundary K
      values if the host compiler supports AddressSanitizer and
      UndefinedBehaviorSanitizer.
    - The recorded SHA-256 of `problem/statement-en.pdf` remains
      `8d1b2a122d382656b6e07777fb30c93ea69ae29c12042561cbc787abe026d10c`.
    - Git ignores `.humanize/` and generated/build files; final tracked content
      contains no hidden data, official grader, downloaded attachment, runtime
      state, binary, cache, or generated output park.
  - Negative Tests (expected to FAIL):
    - Statement hash drift, compiler warnings, a dirty post-test tree, or a
      tracked Humanize/runtime artifact prevents completion.

## Path Boundaries

### Upper Bound (Maximum Scope)

- `solutions/02-magiccity/solution.cpp`: production C++17 implementation of
  only the required `construct(int K)` API and its private helpers.
- `tools/export.cpp` and a small deterministic all-K export script: locally
  derived replacement for the absent sample-grader attachment.
- `tools/check.py`: independent strict parser and exhaustive checker expressed
  directly in statement semantics, without calling or importing production
  construction logic.
- `tests/`: self-authored API, structural, determinism, exporter, score, and
  negative-fixture tests.
- `docs/solution.md` (or README-equivalent): exact construction, proof,
  complexity, API/output mapping, and blind-validation limitations.
- Root `test.sh`, `.gitignore`, and a statement checksum record.
- Native untracked `.humanize/rlcr/<run>/complete-state.md` evidence produced by
  the required Humanize Stop-hook workflow.

### Lower Bound (Minimum Scope)

- A warning-free exact-API solution valid for all K = 1..50.
- Exact full-score N target in all 50 cases.
- A proof complete enough to justify every triple and degree.
- A genuinely independent exhaustive semantic checker and deterministic
  exporter.
- A root `./test.sh` that validates all legal K plus meaningful corruptions.
- Successful native Humanize finalize and a clean Git worktree.

### Allowed Choices

- Can use standard C++17 containers and deterministic integer arithmetic.
- Can model type labels as residues modulo `q = 2*K` and attraction indices as
  `block*q + type`.
- Can use Python 3 standard-library code for the independent text checker and
  test orchestration.
- Can create temporary build/export directories outside tracked paths with
  cleanup traps.
- Cannot access the network, web, sibling workers, parent task repositories,
  prior attempts, caches, reports, official attachments, graders, testdata, or
  hidden tests.
- Cannot depend on random search, nondeterministic iteration, third-party
  libraries, nonstandard C++ extensions, or precomputed data not fully stated
  and proved in this repository.
- Cannot modify `plan.md` after its initial tracked commit or manually edit,
  bypass, cancel, or forge Humanize state.
- Cannot enable agent teams, spawn problem-solving subagents, push a remote, or
  package `.humanize` state with the submission.

## Construction Specification

Let `q = 2*K`. For each K choose B blocks. For every nonzero directed
difference `d` in `{1, ..., q-1}`, define a nonempty incidence set `A[d]` of
block indices. The required invariant is:

1. `A[d1]` intersects `A[d2]` for every pair of nonzero differences.
2. `|A[d]| == |A[q-d]|` for every d.
3. Each block occurs in exactly K of the `A[d]` sets.

For K = 1 through 5 use these explicit block contents, where a row lists all d
whose set `A[d]` contains that block:

| K | B | directed-difference contents of blocks 0 through B-1 |
|---:|---:|---|
| 1 | 1 | `{1}` |
| 2 | 3 | `{1,3}`; `{1,2}`; `{2,3}` |
| 3 | 4 | `{1,3,5}`; `{1,2,4}`; `{2,4,5}`; `{2,3,4}` |
| 4 | 5 | `{1,2,6,7}`; `{1,3,4,5}`; `{3,4,5,7}`; `{2,3,4,5}`; `{3,4,5,6}` |
| 5 | 5 | `{1,4,5,6,9}`; `{1,2,3,7,8}`; `{2,3,7,8,9}`; `{2,4,5,6,8}`; `{3,4,5,6,7}` |

For every K >= 6 use B = 6 and assign d cyclically to one of four triples:

- `d mod 4 == 1`: `A[d] = {0,1,2}`.
- `d mod 4 == 2`: `A[d] = {0,3,4}`.
- `d mod 4 == 3`: `A[d] = {1,3,5}`.
- `d mod 4 == 0`: `A[d] = {2,4,5}`.

These four triples intersect pairwise, and all have cardinality three. In each
complete group of four d values, every block occurs twice. Since `q-1=2*K-1`,
if K is even the final prefix is complete groups plus the first three triples,
and if K is odd it is complete groups plus the first triple. Direct counting
shows no block occurs more than K times; the total count and the displayed
prefixes show that every block occurs exactly K times in the selected range.

Create attraction `v(b,t) = b*q+t` of type t for every block b and type t. To
turn neighbor-type requirements into undirected edges, process canonical
differences `d=1,...,K-1`. Sort `A[d]` and `A[q-d]`; their equal size permits
positionwise pairing. For every type t and position r add

```text
{ v(A[d][r], t), v(A[q-d][r], (t+d) mod q) }.
```

For the self-inverse difference K, for every `b in A[K]`, pair antipodal types
once by adding `{v(b,t), v(b,t+K)}` for `0 <= t < K`.

Every block/difference incidence becomes exactly one edge stub at every type.
Thus each attraction has degree K. For an interesting triple with middle type
t2, let `d1=(t1-t2) mod q` and `d2=(t3-t2) mod q`. Both are nonzero, so choose a
block in `A[d1] intersect A[d2]`. Attraction `v(block,t2)` has a neighbor of
each required type and witnesses the triple. This is the core argument that
the implementation, proof, and structural tests must preserve.

The number of attractions is `N=q*B`. The chosen B values give exactly the
target table. Since every vertex has degree K, the handshake lemma gives
`M=N*K/2`. At K=50, `N=600`, comfortably below 2000.

## Dependencies and Sequence

### Milestones

1. Milestone 1: Freeze specification and blind provenance.
   - Record statement SHA-256 and repository isolation rules.
   - Commit the statement, AGENTS.md, and this immutable plan on `main` before
     setting up Humanize with tracked-plan enforcement.

2. Milestone 2: Implement production construction.
   - Encode and internally assert the five small tables and the four cyclic
     masks for K >= 6.
   - Build deterministic incidence lists, attraction types, canonical paired
     edges, and the self-inverse edges.
   - Keep production code exact-API, warning-free, bounded, and free of I/O.

3. Milestone 3: Build independent validation and exporter.
   - Implement a strict output parser/checker from statement predicates only.
   - Implement the API runner/exporter and reproducible all-K file generation.
   - Add construction-specific stub/table audits separate from the generic
     checker, so two different formulations cover likely implementation bugs.

4. Milestone 4: Exercise all 50 subtasks and adversarial failures.
   - Exhaustively validate types, endpoints, every edge incidence, degree,
     every ordered triple, target N, M, determinism, and stable export bytes.
   - Run corruption fixtures and representative sanitizer builds.
   - Make root `./test.sh` the single authoritative local check and verify it
     leaves the tracked tree unchanged.

5. Milestone 5: Prove, document, package, and finalize.
   - Write a line-by-line construction proof and API/output usage guide.
   - Audit statement integrity, strict compilation, all-K validation, file
     permissions, ignores, and Git hygiene.
   - Complete every Humanize implementation/review/finalize gate genuinely,
     retain untracked completion evidence, rerun `./test.sh`, and finish with a
     clean Git status.

## Implementation Notes

- Use no plan vocabulary such as `AC-`, `Milestone`, or `Phase` in production
  source code.
- Use sorted integer vectors for incidence lists; never rely on hash iteration.
- Keep all modular values nonnegative by construction (`t+d < 2*q` before one
  reduction suffices).
- The API has no stated behavior outside K = 1..50; tests must not turn an
  arbitrary extension into a task requirement. Defensive assertions may be
  local/private and must not alter valid behavior.
- A checker adjacency mask represents neighbor *types* for triple coverage,
  but its degree array must count raw edge occurrences. These are intentionally
  different notions.
- The independent checker must not assume cyclic symmetry, exact degree, the
  planned edge order, absence of parallel edges, or target N when deciding
  basic statement validity. Score-target and structural audits are separate.
- Generated output files are reproducible artifacts, not source deliverables;
  generate them only into a caller-selected or temporary directory.
- Humanize nested reviews must run with web/network disabled and must be
  instructed to read only this repository. No review result can be treated as
  access to official grading data.
