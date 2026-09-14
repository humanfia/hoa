# IChO 2026 — Theory Problem 3, Subquestion 3.6 (`icho_2026_t3_a6`)

**Question (theory_problem.pdf p. 30 = Q3-6; images T3_page-5/-6.png):**
“3.6 **Calculate** the π–π stacking energy between two layers of one repeat
unit of COF-8, for the **AA**, **AB** and **AB'** arrangements. **Assume**
π–π stacking happens only between aromatic units.”

## Answer

| Arrangement | Contact count per repeat-unit bilayer | Energy / kJ mol⁻¹ |
|---|---|---|
| **AA**  | 1 eclipsed t–t + 10 eclipsed b–b | **−85.7** |
| **AB**  | 6 slipped b–b | **−75.6** |
| **AB'** | 6 slipped b–t | **−333.6** |

(All energies per mole of bilayer repeat units, three significant figures —
the precision of every printed table entry.)

## Source material used

Everything below is taken from the problem pages themselves:

* **Energy table** (Q3-6, two geometry columns):

  | Interaction geometry | eclipsed / kJ mol⁻¹ | slipped / kJ mol⁻¹ |
  |---|---|---|
  | benzene–benzene (b–b) | −7.9 | −12.6 |
  | benzene–triazine (b–t) | −49.8 | −55.6 |
  | triazine–triazine (t–t) | −6.7 | −16.7 |

  The first column shows two rings stacked face-to-face with coincident centroids
  (eclipsed); the second column shows the ring centroids offset so that one ring
  faces the *gap between its own arms* in the other ring (slipped).

* **COF-8 structure** (E1 + D2): each honeycomb vertex is a tris(phenylene)
  triazine core (1 triazine ring + 3 phenylene rings) and each edge is
  two phenylene rings joined by a –CH=C(CN)– (E1-derived) linker.
  Per repeat unit per layer: **1 triazine ring and 10 benzene rings**
  (3 vertex phenylenes + 6 edge phenylenes + 1 E1 core benzene) are aromatic;
  the C=C double bonds, the C≡N groups and the nitrile carbons are *not*
  aromatic and — by the problem's explicit assumption — contribute no π–π
  stacking.
* **Stacking-mode figure** (a) AA eclipsed; (b) AA′ slightly shifted
  (datum −67.1 kJ mol⁻¹, pre-filled on answer sheet A3-4); (c) AB with the
  second layer's vertices (triazine cores, shown blue) sitting above the
  hexagon-hole centres of the first layer.

## Counting the π–π contacts

One repeat unit of one COF-8 layer (blue dashed boundary in the printed
structure) contains, on the two-layer bilayer:

* **AA (fully eclipsed).** Every ring of one layer lies exactly above the same
  ring of the other layer: **1 t–t** contact and, per repeat unit of the
  bilayer, **10 b–b** contacts (1 + 1 triazine rings and 10 + 10 benzene rings
  in the two-layer cell; the shared-edge bookkeeping of the honeycomb gives
  exactly 10 aromatic benzene rings per layer per repeat unit).

  E(AA) = (−6.7) + 10·(−7.9) = **−85.7 kJ mol⁻¹**

* **AB (triazines over hole centres).** The centre of a honeycomb hexagon is
  the centroid of the triangle formed by the **midpoints of its three
  alternating edges** (equivalently of the three surrounding triazine rings).
  Hence, when one layer's triazines sit over the other layer's hole centres,
  each of the **6 edge-midpoint aromatic jobs** of one repeat unit faces a
  *benzene* job of the other layer in the slipped geometry, while the
  hole-centred triazines sit over the empty interior of the hexagons and stack
  with nothing.  No ring ever faces a triazine ring.

  E(AB) = 6·(−12.6) = **−75.6 kJ mol⁻¹**

* **AB' (the complementary hole-centred registry).** Shifting the top layer by
  the *other* triangular sublattice vector (or, equivalently, turning it over)
  puts the same hole centres at the centroids of the complementary
  (up-pointing) edge-midpoint triangles — the ones whose vertices border two
  triazines of the opposite layer.  Now every one of the 6 edge jobs faces a
  **triazine** ring of the other layer in the slipped geometry.

  E(AB′) = 6·(−55.6) = **−333.6 kJ mol⁻¹**

  AB′ ≠ AB because the honeycomb edge lattice has no translation mapping its
  up-pointing onto its down-pointing midpoint triangles (proved in Lean as the
  arithmetic statement `centroids_distinct`).

*The given AA′ value −67.1 kJ mol⁻¹ is an independent problem datum; it lies
between the eclipsed AA limit and zero, consistent with a small slip from the
eclipsed AA geometry, and is not needed for the three requested outputs.*

## Assumptions made explicit

1. Only the six table entries and the printed structures/figures are used.
2. “Aromatic units” = the triazine rings and the six-membered all-carbon
   (benzene/phenylene) rings of the repeat unit; vinyl C=C, C≡N and nitrile
   carbon atoms are excluded, as the question instructs.
3. Each slipped contact uses the second table column, each eclipsed contact
   the first; all contacts are counted once per bilayer repeat unit.

No external data, no official solution material, and no hidden premises were
used at any stage.
