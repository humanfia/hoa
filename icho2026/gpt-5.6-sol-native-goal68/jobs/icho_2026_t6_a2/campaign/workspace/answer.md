# IChO 2026 T6-A2

## Answer

The three requested intermediates are neutral monocyclic carbon rings. Their
formulas and unpaired electrons are:

| Structure | Formula | Unpaired electrons |
|---|---:|---:|
| **B** | C₁₄Cl₃ | 1 |
| **C** | C₁₄Cl | 1 |
| **D** | C₁₄Cl₅ | 1 |

Here is an exact line-structure specification. Number the carbon atoms around
the outer perimeter of the anthracene drawing as follows:

```text
                  1──2──3──4──5
                ╱    │     │    ╲
               0     │     │     6
               │     │     │     │
              13     │     │     7
                ╲    │     │    ╱
                 12─11─10──9──8
```

The perimeter is the cycle 0–1–…–13–0. In A only, the vertical lines are the
anthracene fusion bonds 2–11 and 4–9. Both fusion bonds are absent in B, C,
and D. Let `eᵢ` denote the perimeter bond from carbon `i` to carbon `i+1`
(modulo 14), and let S, D, and T mean single, double, and triple.

| Structure | Chlorinated carbons (single C–Cl bonds) | Radical carbon | `(e₀,…,e₁₃)` |
|---|---|---|---|
| **B** | 0, 3, 13 | 10 | `(S,T,S,D,D,D,D,D,D,D,S,T,S,D)` |
| **C** | 3 | 10 | `(S,T,S,D,D,D,D,D,D,D,S,T,S,T)` |
| **D** | 0, 3, 6, 7, 13 | 10 | `(S,T,S,D,D,D,S,D,D,D,S,T,S,D)` |

This table is the complete drawing: every carbon is one of 0–13, the only
C–C bonds are the fourteen listed perimeter bonds, and each listed chlorine
is attached by a single bond. All atoms have formal charge zero. There are no
stereocentres.

## Derivation

The blank answer sheet gives A. In the numbering above, A has chlorine at
0, 1, 3, 6, 7, 8, 12, and 13, and radical dots at 5 and 10. Its perimeter
bond orders, beginning at `e₀`, alternate S,D,S,D,…,D, and it retains the two
single fusion bonds 2–11 and 4–9.

The chlorine protrusions in the AFM panels can be calibrated against that
fully drawn A. The A→D image loses the chlorines at 1, 8, and 12, leaving the
five protrusions at 0, 3, 6, 7, and 13. This creates radical pairs (1,12) in
the left terminal ring and (5,8) in the right terminal ring. Applying the
retro-Bergman reaction printed in the question:

- the 2–11 fusion bond opens, while 1–2 and 11–12 become triple bonds;
- the 4–9 fusion bond opens, while 4–5 and 8–9 become double bonds.

Those two openings consume four radical electrons. The unpaired electron
already at carbon 10 remains, giving D as tabulated.

On the A→B branch the same three chlorines are lost together with the adjacent
chlorines at 6 and 7. After the two retro-Bergman openings, the radical
electrons at 6 and 7 pair to change 6–7 from single to double. Thus only the
chlorines at 0, 3, and 13 and the radical at 10 remain: structure B.

B→C removes the adjacent chlorine atoms at 13 and 0. Their two carbon radical
electrons pair, changing the 13–0 bond from double to triple. Structure C
therefore has only Cl at 3 and the radical at 10.

As a consistency check, the last pictured loss removes Cl· from carbon 3.
The resulting radicals at 3 and 10 pair through the seven-double-bond arc;
the bond orders shift to an alternating single/triple cyclo[14]carbon. This
reproduces the C→C₁₄ endpoint in the problem figure and verifies the placement
of the last chlorine and radical independently of the simple chlorine counts.

## Source grounding

- [`TASK.json`](TASK.json) identifies PDF page 52 and asks for B–D.
- [`T6_page-1.png`](icho_2026_source/image/T6_page-1.png) supplies the
  perchlorinated anthracene, the AFM sequence, the `−5Cl·`, `−2Cl·`, `−3Cl·`,
  and `−Cl·` counts, and the retro-Bergman transformation.
- [`theory_problem.pdf`](icho_2026_source/raw/theory_problem.pdf), PDF page 57,
  is the original blank student answer sheet. It supplies the explicit A
  structure used to calibrate the carbon numbering and AFM features.

No official solution, marking scheme, answer repository, or external solver
was used. The only general chemical rules used beyond the printed reaction
are homolytic C–Cl cleavage and ordinary neutral-carbon Lewis valence. The
Lean development checks valence four at every carbon, explicit C–Cl
connectivity, atom/radical counts, zero formal charges, and absence of
stereocentres for all three outputs.

