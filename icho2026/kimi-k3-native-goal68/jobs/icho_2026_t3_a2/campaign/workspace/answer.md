# IChO 2026, Theory Problem 3 (T3), Part 3.2 - Answer

**Requested output.** The internal diameter `d`, in Å, of the COF-2 honeycomb
(question 3.2, 3.0 pt; answer sheet A3-1 line `d = ______ Å`).

## Answer

d = sqrt(3) * a = sqrt(3) * 8.66 Å = 14.9996 Å ≈ **15.0 Å**

(three significant figures; raw value d = √3 × 8.66 Å = 14.9996 Å).

## Derivation

**Step 1 — identify the hexagon side (a).**
From the Q3-1 figure, COF-2 is made from benzene-1,3,5-triboronic acid
(monomer A2), which dehydrates into B₃O₃ boroxine rings. In the honeycomb, the
corners of each pore hexagon are boroxine rings (modelled as regular hexagons
of B–O = 1.38 Å, so their centre-to-B distance — the circumradius — equals
1.38 Å), and each side of the pore hexagon is the straight chain:

```
boroxine centre -> B (1.38 Å) — aryl C–B (1.56 Å) — benzene ring crossed
along its para axis (2 × C–C = 2 × 1.39 Å) — aryl C–B (1.56 Å) —
B -> next boroxine centre (1.38 Å)
```

All segments are collinear: the boroxine ring has 120° interior angles
(trigonal B and O), benzene para crossings are along the side axis (benzene
C–C bonds on the axis are perpendicular to it), and with the linker width
neglected the boroxine rings touch, but do not protrude inside, the pore.

Hence

a = 2(1.38) + 2(1.56) + 2(1.39) = 2.76 + 3.12 + 2.78 = 8.66 Å.

All three stipulated bond lengths are used: B–O (two boroxine circumradii),
C–B (two aryl–boron bonds), C–C/C=C (one benzene para crossing).

**Step 2 — inscribed-circle diameter.**

The problem stipulates d = sqrt(3) * a for the diameter of the circle
inscribed in a regular hexagon of side a:

d = 1.7320508… × 8.66 Å = 14.9996 Å ≈ 15.0 Å.

No intermediate rounding was performed; the bond lengths were taken as the
exact stipulated constants (1.39, 1.56, 1.38 Å) throughout.

## Source grounding

- Question text: `theory_problem.pdf`, page Q3-2 (printed page 26): bond-length
  assumptions and the formula d = √3a, plus "Neglect the width of the linkers."
- COF-2 structure (boroxine honeycomb from monomer A2): page Q3-1 figure —
  boroxine rings at the honeycomb vertices, benzene (A2) linkers on the edges.
- Student answer sheet: page A3-1 shows the single blank `d = ______ Å`,
  confirming one numeric output in Å.
- Reporting: the blind-evaluation default of three significant figures gives
  d = 15.0 Å (the raw 14.9996 Å lies in the 14.95–15.05 half-quantum window
  of the 0.1 Å quantum).
- The modelling assumptions used (regular hexagons for the arene C–C and the
  boroxine B–O angles; boroxine centre-to-B distance = B–O as circumradius of
  a regular hexagon of side B–O; collinear side chain) follow from the
  problem's own stipulation of uniform bond lengths and its instruction to
  neglect linker widths; they are the unique reading under which all three
  supplied bond lengths contribute. The regular-hexagon circumradius = side
  fact is elementary geometry (each sector of a regular hexagon is an
  equilateral triangle), analogous to the problem's own inscribed-circle note.

## Formalization

`IChO2026Problems/problem_icho_2026_t3_a2.lean` proves, over the reals:

- `cof2HexagonSide_eq` — the side length a = 2·bO + 2·cB + 2·cC = 8.66 Å;
- `cof2InternalDiameter_sq` — d² = 2249868/10000 = 224.9868 Å² (exact, from
  d = √3 · a);
- `cof2InternalDiameter_lower` / `cof2InternalDiameter_upper` /
  `cof2InternalDiameter_bounds` — 14.95 < d < 15.05, proved by
  square-root monotonicity applied to the exact square;
- `cof2InternalDiameter_three_sf` — |d − 15.0| < 0.05;
- `cof2InternalDiameter_rounding_uniqueness` — 15.0 is the unique multiple of
  the 0.1 Å quantum within half a quantum of d;
- `cof2InternalDiameter_reported` and `cof2Submission_valid` — the
  answer-blind reporting contract (`ReportsAtQuantum` /
  `ValidNumericSubmission` from `IChO2026Chem.Reporting`): raw value √3 · 8.66,
  reported value 15, quantum 0.1, ties away from zero (vacuous here since
  d > 14.95 strictly).

All proofs depend only on the standard Lean logical axioms
(propext, Classical.choice, Quot.sound); see `verification.md`.
