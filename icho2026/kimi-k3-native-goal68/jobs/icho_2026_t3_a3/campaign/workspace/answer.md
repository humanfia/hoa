# IChO 2026, Theory T3, subquestion 3.3 — reticular-design table

## Completed table

Two blank rows per column; the printed (non-graded) example row is shown for
context. `XXX` = "no additional combination remains" under the problem's
restriction to boronate-ester, imine and C=C condensations using only the
printed monomers.

| Column | Printed example | Row 1 | Row 2 |
|---|---|---|---|
| Tetragonal 1 | — | **A3 + B2** | **XXX** |
| Tetragonal 2 | — | **C3 + D4** | **XXX** |
| Hexagonal 1 | A2 + B3 | **A1 + B2** | **C1 + D2** |
| Hexagonal 2 | E1 + D2 | **A1 + B3** | **XXX** |
| Trigonal | — | **C1 + D1** | **XXX** |
| Kagome | C2 + D4 | **B1 + A2** | **XXX** |
| Tetrahedral | — | **A4 + B2** | **C1 + D3** |

No combination is used twice anywhere in the table, and every entry realises
its column's topology under the chemistry allowed by the question.

## Source grounding (problem-only)

**Allowed linkages.** The question banner restricts formation to COFs with
**boronate esters**, **imines**, and **C=C bonds** through condensation.
Matching the printed functional-group classes: A (boronic acids) pairs only
with B (catechols); C (amines) only with D (aldehydes); E (benzylic nitrile,
Knoevenagel-type C=C partner) only with D.

**Connectivities** counted from the drawn structures (Q3-3): A1 = 3, A2 = 2,
A3 = 4, A4 = 4 (Si, tetrahedral); B1 = 4, B2 = 2, B3 = 3 (three catechol
faces on triphenylene); C1 = 2, C2 = 4, C3 = 4; D1 = 6, D2 = 3, D3 = 4
(sp³ C, tetrahedral), D4 = 2; E1 = 3.

**Geometry.** Only A4 (Si) and D3 (sp³ C) are tetrahedral (3-D) centres; all
other printed monomers are planar. The six 2-D topology figures admit only
planar building blocks; the Tetrahedral figure is a 3-D net requiring a
tetrahedral degree-4 vertex.

**Net signatures** read off the topology figures and printed examples:

* Tetragonal 1 / Tetragonal 2: square nets, role degrees (4, 2).
* Hexagonal 1: honeycomb, (3 vertex, 2 linker) — printed example A2+B3 has
  B3 (3) at the vertices.
* Hexagonal 2: staggered honeycomb, **(3, 3)** — the printed example E1+D2
  pairs two 3-connecting monomers with no 2-linker, so both vertex
  sublattices are occupied by 3-connected centres joined directly; this is
  the only signature consistent with the printed example, and it matches the
  figure (monomer junctions sit at the net vertices on both sublattices).
* Trigonal: triangular net, (6, 2).
* Kagome: (4, 2) — printed example C2+D4 has C2 (4) on the corner-sharing
  degree-4 vertices and D4 (2) bridging them.
* Tetrahedral: 3-D net, tetrahedral 4-vertex + 2-linker.

**Exhaustive admissible pairs** (enumeration over all 15×15 ordered printed
pairs, checked by the kernel in the Lean file):

* square net (4,2): A3+B2, B1+A2, C2+D4, C3+D4
* honeycomb (3,2): A2+B3, A1+B2, C1+D2, E1+D4
* staggered honeycomb (3,3): E1+D2, A1+B3
* triangular (6,2): C1+D1 only
* tetrahedral 3-D: A4+B2, C1+D3

**Cell accounting.** Every admissible pair is either the printed example of
its column or appears in exactly one filled cell, except E1+D4 in Hexagonal
1: the two Hexagonal-1 cells are already occupied by A1+B2 and C1+D2, so
E1+D4 simply has no cell — which is exactly why **no XXX is written in the
Hexagonal 1 column** (an additional valid combination exists). Every other
XXX is justified because all remaining admissible pairs of that column are
already committed elsewhere (e.g. in Kagome, C2+D4 is the printed example
and A3+B2 / C3+D4 are committed in the two Tetragonal columns, leaving only
B1+A2).

## Honesty note on Hexagonal 1 vs Hexagonal 2

The two hexagonal figures are topologically the same skeleton; the
defensible distinguishing feature forced by the printed examples is the role
signature: Hexagonal 1 admits a (3, 2) pair (A2+B3), Hexagonal 2's printed
example is a (3, 3) pair (E1+D2). This is the reading formalised in Lean; it
is grounded in the printed monomer structures and printed examples, not in
any marking scheme.
