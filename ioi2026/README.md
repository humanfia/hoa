# IOI 2026 solutions

Submission-ready C++ solutions for the IOI 2026 tasks released so far.

## Day 1

- `ballmachine.cpp` — Ball Machine
- `monuments.cpp` — Monuments
- `tiling.cpp` — Tiling Game

## Day 2

- `classroom.cpp` — Classroom Game
- `magiccity.cpp` — Magic City
- `partition.cpp` — Partition

Each file implements the corresponding contestant API and is intended to be
submitted separately with that task's grader and header.

The solutions were developed with iterative independent code review. No
grading or hidden tests were accessed; validation used released public
materials and self-authored tests. The Partition construction was also
cross-checked against the released official model implementation, without
accessing its test data.

For Ball Machine, the achieved full-score resource bounds are `K <= 15`,
`B <= 34`, `K + B <= 43`, and at most `18,000` calls to `insert`.

For Classroom Game, every paper has at most two integers (`C <= 2`).

For Magic City, the construction uses exactly `N = 2, 12, 24, 40, 50` for
`K = 1, 2, 3, 4, 5`, and `N = 12K` for `6 <= K <= 50`.

For Partition, `add_numbers` returns at most `K - 1` legal additions and
supports the full stated range `M <= 10^9`; `find_partition` is stateless.
