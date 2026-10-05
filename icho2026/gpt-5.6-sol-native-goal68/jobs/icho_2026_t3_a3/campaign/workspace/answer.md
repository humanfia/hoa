# IChO 2026 T3-A3

## Table to enter

The two answer rows may be filled as follows. The three combinations already
printed in the question (`A2 + B3`, `E1 + D2`, and `C2 + D4`) are not repeated.

| Tetragonal 1 | Tetragonal 2 | Hexagonal 1 | Hexagonal 2 | Trigonal | Kagome | Tetrahedral |
|---|---|---|---|---|---|---|
| **A2 + B1** | **A3 + B1** | **A1 + B2** | **A1 + B3** | **C1 + D1** | **A3 + B2** | **A4 + B2** |
| **C3 + D4** | **XXX** | **C1 + D2** | **XXX** | **XXX** | **XXX** | **C1 + D3** |

For Hexagonal 1, `E1 + D4` is another valid new example. There are only two
blank answer cells in that column, so it is not necessary to enter all three
new examples; the table above uses `A1 + B2` and `C1 + D2`.

## Derivation and source grounding

The source is the supplied official problem-only material:

- `T3_page-3.png` / PDF page Q3-3 displays every monomer and the seven coloured
  topology schematics.
- `T3_page-4.png` / PDF page Q3-4 states the instruction and shows the three
  supplied examples.
- The blank student answer sheet, PDF page A3-2 (physical PDF page 33), confirms
  that exactly two cells must be completed in every topology column.

The image gives two filters.

First, the functional groups and the restriction to the three stated
condensations leave only these reaction-compatible class pairings:

- `A + B`: boronic acid plus vicinal diol, producing boronate esters;
- `C + D`: amine plus aldehyde, producing imines;
- `E + D`: activated nitrile-containing carbon centres plus aldehydes,
  producing C=C linkages.

Second, counting the reactive ends and reading their displayed geometry gives:

- linear two-ended: `A2`, `B2`, `C1`, `D4`;
- trigonal three-ended: `A1`, `B3`, `D2`, `E1`;
- square-planar four-ended: `B1`, `C3`;
- rhombic/C2-symmetric four-ended (the dual-pore Kagome knot): `A3`, `C2`;
- hexagonal six-ended: `D1`;
- tetrahedral four-ended: `A4`, `D3`.

Matching those roles to the black/red building-block patterns in the seven
schematics, while retaining only reaction-compatible class pairs, gives the
following exhaustive candidate sets:

- Tetragonal 1: `A2 + B1`, `C3 + D4`.
- Tetragonal 2: `A3 + B1`.
- Hexagonal 1: `A1 + B2`, the supplied `A2 + B3`, `C1 + D2`, and `E1 + D4`.
- Hexagonal 2: `A1 + B3` and the supplied `E1 + D2`.
- Trigonal: `C1 + D1`.
- Kagome: `A3 + B2` and the supplied `C2 + D4`.
- Tetrahedral: `A4 + B2`, `C1 + D3`.

This exhaustive list justifies every `XXX`: after accounting for the supplied
and newly entered examples, Tetragonal 2, Hexagonal 2, Trigonal, and Kagome have
no further compatible combinations among the displayed monomers. In
particular, the Kagome column has one new example (`A3 + B2`), so only its
second answer cell is `XXX`.

The Lean formalization keeps the source transcription (`roleA` through
`roleE`, the permitted `Combination` constructors, and `requiredRoles`)
separate from the derived exhaustive theorem `fits_iff_mem_allSolutions`.
The final theorem `topology_table_valid` proves all fourteen cells at once and
requires exhaustive coverage whenever a column contains `XXX`.

No numerical reporting convention is involved in this exact-symbolic
classification, and no earlier subquestion result is used.
