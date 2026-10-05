# IChO 2026 T7-A1 answer

## Boxes to tick

| Gas | M1 | M2 |
|---|:---:|:---:|
| CH4 |  |  |
| H2O |  |  |
| CO | ✓ |  |
| O2 |  |  |
| H2 | ✓ | ✓ |
| N2 | ✓ | ✓ |
| NH3 |  | ✓ |
| CO2 |  |  |

For the comparison, tick **`x > y`**.

Thus, as sets,

- **M1 = {CO, H2, N2}**;
- **M2 = {H2, N2, NH3}**;
- **x > y**.

## Derivation

The first reactor carries out the quantitative 1:1 steam-reforming reaction

`CH4 + H2O → CO + 3 H2`.

If its reaction extent is `min(x,y)`, the residual amounts of methane and water are respectively

`x − min(x,y)` and `y − min(x,y)`.

The outlet drawn after this reactor is labeled `CH4, CO, H2`: methane remains, while water is absent. In particular,
`x − min(x,y) > 0`. If `x ≤ y`, then `min(x,y) = x`, making that residual amount zero, a contradiction. Therefore `x > y`.

The next reactor receives the reformer stream and the `4 N2 + 1 O2` air stream. Its quantitative reaction is

`2 CH4 + O2 → 2 CO + 4 H2`.

Consequently the residual methane and oxygen are consumed, carbon monoxide and hydrogen are present, and nitrogen passes through unchanged. Hence M1 contains exactly `CO`, `H2`, and `N2`. This is independently consistent with the next quantitative step: after adding water, `CO + H2O → CO2 + H2` gives the diagram's labeled stream `N2, CO2, H2`.

The CO2 scrubber removes `CO2`, leaving `N2` and `H2` for ammonia synthesis. Unlike the other reactions, ammonia formation is explicitly not quantitative. The diagram also shows unreacted `N2, H2` returning from the cooler and `NH3` leaving it. Therefore the cooler inlet M2 contains the two unreacted gases together with produced ammonia: exactly `N2`, `H2`, and `NH3`.

## Source grounding

- `TASK.json` identifies the three required outputs as the complete gas sets in M1 and M2 and the classification of the relation between `x` and `y`.
- `T7_page-1.png` (SHA-256 `ee7fe1adff7ac3aae8701bf684981bd2b1e21b28f1c9e4b21dd9c38c3bdb79ad`) supplies Fig. 1, its reactions, stream labels, and the stipulation that every displayed reaction except NH3 formation is quantitative.
- The original `theory_problem.pdf` (SHA-256 `af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60`) was checked directly at PDF page 63 (Q7-1). Its blank student answer sheet at PDF page 67 (A7-1) confirms that the offered gas choices are `CH4, H2O, CO, O2, H2, N2, NH3, CO2` and that the offered relations are `x > y`, `x = y`, and `x < y`; the sheet contains no filled answer.

No official solution, marking scheme, answer repository, or historical answer was used.

