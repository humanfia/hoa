# Ball Machine Full-Score Solution Plan

## Goal Description

Develop, prove, implement, and independently validate a deterministic C++20
contestant solution for the Ball Machine task. The solution must reconstruct every
valid hidden rooted tree with `2 <= N <= 1000` and `1 <= M <= 200`, up to the
internal-node relabeling permitted by the statement, while always using
`C = K + B <= 44`, at most 500,000 calls to `insert`, and legal ball values. The
machine must be empty when `find_structure` returns. Deliver the exact grader API
at `solutions/01-ballmachine/solution.cpp`, rigorous documentation, and wholly
self-authored simulator/property tests.

## Acceptance Criteria

- AC-1: The submission artifact implements the exact contestant API and compiles
  as C++20 with the unmodified contestant header and sample grader.
  - Positive Tests (expected to PASS):
    - Compile `solutions/01-ballmachine/solution.cpp` with copied
      `ballmachine.h` and `grader.cpp` under strict warnings and optimization.
    - Run the public contestant sample and verify the returned tree with an
      isomorphism-aware validator rather than requiring one particular valid
      internal labeling.
  - Negative Tests (expected to FAIL):
    - A deliberately malformed result with the wrong length, an out-of-range
      parent, a cycle, a mislabeled leaf, or a non-equivalent topology is rejected
      by the local validator.

- AC-2: `find_structure(M)` returns an array of length exactly `N - 1` describing
  a tree isomorphic to the hidden tree under a bijection that fixes every leaf
  `0..M-1` and the root `N-1`.
  - Positive Tests (expected to PASS):
    - Exhaustive or broad enumerative checks on all feasible very small trees,
      including internal unary nodes and non-binary branching.
    - Random independently generated valid trees across varied `N` and `M`, plus
      adversarial stars, long unary chains, brooms, combs, balanced trees,
      high-degree nodes, unequal leaf depths, and repeated isomorphic subtrees.
    - Maximum-scale constructions with `M=200` and `N=1000`.
  - Negative Tests (expected to FAIL):
    - Mutating one genuine edge or one leaf attachment in a returned tree causes
      the validator to reject it even if internal labels are permuted.

- AC-3: Resource usage is valid on every legal tree, not merely on sampled cases.
  In particular, every inserted value is in `[0,1000]`, `B` is the maximum value
  actually used, `K` counts every `collect`, `K+B <= 44`, and total `insert` calls
  never exceed 500,000. No asymptotic or input-dependent corner case may violate
  these limits.
  - Positive Tests (expected to PASS):
    - The simulator instruments calls and checks the bounds after every operation
      on both adversarial and maximum-scale families.
    - A written worst-case derivation bounds `K`, `B`, successful insertions,
      failed insertions, memory, and runtime for `N=1000, M=200`.
  - Negative Tests (expected to FAIL):
    - Test harness probes detect intentional variants that make a 45th unit of
      `K+B`, an illegal value, or excessive insertion calls.

- AC-4: The reconstruction method has a rigorous, implementation-matched proof.
  It must explain the information obtained from each insertion/collection phase,
  why the decoded structure is unique up to allowed labels, why all nodes
  including unary internal nodes are recovered, why tie ordering cannot corrupt
  the result, why calls terminate without knowing `N`, and why the final machine
  is empty.
  - Positive Tests (expected to PASS):
    - Every nontrivial invariant in the proof is represented by a targeted
      property test or exhaustive small-instance comparison against a direct
      hidden-tree oracle.
    - Any dependence on the grader's stated determinism is isolated and tested
      with distinct deterministic tie policies.
  - Negative Tests (expected to FAIL):
    - An experimental decoder that relies on lucky random hashes, an unstated
      stable-sort rule, or a particular arbitrary order among equal values is not
      accepted as the final method.

- AC-5: The repository contains an independent, statement-derived test system.
  `test.sh` is executable and builds/runs a local simulator, structural validator,
  deterministic regression cases, exhaustive small cases where practical,
  seeded randomized properties, and stress/resource checks. It must not consume
  task-archive or grading tests.
  - Positive Tests (expected to PASS):
    - Re-running `./test.sh` from a clean checkout is deterministic and succeeds.
    - The simulator implements successful and failed insertions, movement to the
      highest reachable free ancestor, recursive value-sorted collection,
      clearing after collection, all counters, and legal arbitrary tie behavior.
  - Negative Tests (expected to FAIL):
    - Simulator self-checks distinguish the empty machine, occupied-leaf failure,
      incorrect collection order, failure to clear, and invalid resource usage.

- AC-6: `README.md` is a self-contained handoff. It states the algorithm,
  pseudocode-level phase structure, correctness proof, exact resource analysis,
  complexity, API/build instructions, and test coverage. Final source is clean,
  portable C++20, contains no debug output or `main`, and does not mention
  Humanize plan terminology in implementation comments.
  - Positive Tests (expected to PASS):
    - A reviewer can match every proof invariant and bound to the code and tests.
  - Negative Tests (expected to FAIL):
    - Placeholder arguments, empirical-only bounds, undocumented assumptions, or
      generated artifacts required for normal testing remain in the final tree.

## Path Boundaries

### Upper Bound (Maximum Scope)

One production solution file, a rigorous root-level README, an executable
root-level `test.sh`, and compact self-authored support code/data under
`selftests/`. The copied statement and contestant package under `source/` may be
used as read-only references. Small diagnostic programs may be created during
research but must either become justified tests or be removed before completion.

### Lower Bound (Minimum Scope)

A provably full-score (`C <= 44`) algorithm for all stated constraints, exact API
implementation, reproducible independent validation, and complete resource and
correctness documentation. Partial-subtask strategies are insufficient.

### Allowed Choices

- Can use deterministic combinatorial encodings, batched leaf priorities,
  insertion return values, repeated full-machine fillings, arbitrary internal
  relabeling, and C++20 standard-library facilities.
- Can use the public sample shipped in `source/attachment/examples/` as a smoke
  test, but all other cases must be generated independently from the statement.
- Can use the statement's guarantee that repeated identical operation sequences
  receive deterministic collection arrays; any reliance must be explicit.
- Cannot use probabilistic correctness, collision-prone fingerprints without
  deterministic disambiguation, undefined sort stability, assumptions that the
  tree is binary or has no unary nodes, or bounds that hold only typically.
- Cannot use network access, Git remotes, external solutions or editorials,
  task-archive data, grading examples, hidden tests, or another worker's files.
- Cannot inspect any outside path named `tests`; self-authored cases belong only
  under this repository's `selftests/` directory.
- Must not modify `plan.md` after Humanize initialization.

## Dependencies and Sequence

### Milestones

1. Milestone 1: Formalize the observation model and a high-resource oracle.
   - Phase A (`analyze`): Prove the full-fill primitive: repeatedly inserting from
     leaves in a fixed order until each selected leaf rejects fills the union of
     their root paths; when all leaves are processed it places exactly one ball at
     every node and terminates without knowing `N`.
   - Phase B (`analyze`): Associate each filled node with the earliest processed
     descendant leaf and derive exactly what insertion success counts and the
     collected owner-value preorder reveal.
   - Phase C (`coding`): Build a tiny-tree research oracle and verify the derived
     invariants exhaustively. As a conceptual reference, investigate the
     high-resource construction assigning distinct reverse leaf priorities; its
     owner preorder should admit a unique stack/recursive parse. This reference is
     for proof and differential testing, not an acceptable final resource bound.

2. Milestone 2: Derive and prove a deterministic compressed encoding with
   `K+B <= 44`.
   - Phase A (`analyze`): Convert the distinct-priority oracle into bounded-value
     batches/digits/threshold probes. A promising direction is to give one active
     leaf block distinct priorities while mapping leaves on either side to low and
     high sentinels, possibly using complementary directional phases. Treat this
     only as a feasibility hint: derive the exact transcript and decoder before
     committing to it.
   - Phase B (`analyze`): Prove that the combined transcripts identify every
     parent relation (including repeated unary nodes) and are invariant under all
     allowed equal-value child orders. Use insertion booleans/counts as free
     side-information where useful.
   - Phase C (`analyze`): Select concrete constants valid for `M=200`; state closed
     formulas for `K`, `B`, and insertion calls and prove their maxima satisfy
     `K+B <= 44` and 500,000. Reject a candidate immediately if exhaustive small
     instances produce two non-isomorphic trees with the same usable transcript.

3. Milestone 3: Implement the production decoder.
   - Phase A (`coding`): Create
     `solutions/01-ballmachine/solution.cpp` with only the required API and robust
     local data structures. Ensure every collection follows a completely filled
     or otherwise explicitly modeled state and leaves the machine empty.
   - Phase B (`coding`): Add defensive internal invariants that do not print or
     alter grader-visible behavior, avoid recursion-depth hazards where relevant,
     and construct a valid parent array whose root label is exactly `N-1` and
     whose leaf labels remain fixed.
   - Phase C (`coding`): Differential-test production transcripts and decoded
     trees against the independently written oracle before optimizing.

4. Milestone 4: Build adversarial verification and documentation.
   - Phase A (`coding`): Implement the simulator and an independent rooted-tree
     isomorphism validator under `selftests/`; deliberately vary deterministic
     tie policies for equal ball values.
   - Phase B (`coding`): Add exhaustive small enumeration, named adversarial
     families, seeded random generation, maximum-scale stress, resource
     instrumentation, invalid-result validator checks, and the public sample.
   - Phase C (`coding`): Write executable `test.sh` and `README.md`, then run debug,
     sanitizer where supported, warning-clean, optimized, and stress checks.

5. Milestone 5: Review and finalize.
   - Phase A (`analyze`): Audit code line-by-line against the mathematical proof
     and all acceptance criteria, focusing on `M=1`, long unary chains, equal
     values/ties, label construction, off-by-one batch sizes, and worst-case call
     formulas.
   - Phase B (`coding`): Remove research-only clutter, confirm repository
     reproducibility, leave no uncommitted implementation changes, and provide
     the Humanize-required round/final summaries through its native Stop hook.

## Implementation Notes

- Keep the production solution independent of the copied sample grader and do not
  include a `main` function.
- Prefer a small number of explicit phases with replayable insertion schedules.
  Record the return from every insertion whenever the proof uses success counts.
- A successful all-leaf fill uses exactly one success per hidden node; bound every
  deliberate failed call separately. Be careful that processing a leaf "until
  false" includes its terminating failed call.
- Collection sorting is by the values on occupied child nodes, not by leaf index,
  insertion time, or a stable tie rule. Equal-valued siblings may appear in any
  deterministic order allowed by the statement.
- Internal labels in the answer are free, but leaves `0..M-1` and root `N-1` are
  fixed. Design the output-label assignment only after the abstract topology and
  total node count are known.
- The implementation source should not contain plan labels such as `AC-`,
  `Milestone`, or `Phase`; comments should explain the algorithm itself.
