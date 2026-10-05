# IChO 2026 T1-A1

## Answer

**X is compound 6, α-terpineol.**  
**Y is compound 3, 1,8-cineole (eucalyptol).**

Thus, on answer sheet A1-1, select **6** for X and **3** for Y.

## Reasoning

Structures 2, 3, 6, and 10 are the four displayed compounds with the same
printed molecular formula, `C10H18O`. Structure 6 is α-terpineol: the drawing
contains a p-menthane framework with a tertiary alcohol and a suitably tethered
carbon-carbon double bond. In acid, protonation of that double bond produces a
tertiary carbocation. Intramolecular attack by the alcohol oxygen, followed by
deprotonation, closes the oxygen bridge without changing the molecular formula.
The resulting cyclic ether is 1,8-cineole, structure 3.

This α-terpineol-to-cineole step is the standard protonation-induced
intramolecular cyclization. Independent primary literature reports both the
acid-catalysed isomerisation of α-terpineol to 1,8-cineole and the corresponding
protonation/cyclization mechanism:

- E. J. L. Lana et al., “Synthesis of 1,8-cineole and 1,4-cineole by isomerization
  of α-terpineol catalyzed by heteropoly acid,” *Journal of Molecular Catalysis
  A: Chemical* 259 (2006), 99–102,
  [doi:10.1016/j.molcata.2006.05.064](https://doi.org/10.1016/j.molcata.2006.05.064).
- B. Piechulla et al., “The α-Terpineol to 1,8-Cineole Cyclization
  Reaction of Tobacco Terpene Synthases,” *Plant Physiology* 172 (2016),
  2120–2131,
  [doi:10.1104/pp.16.01378](https://doi.org/10.1104/pp.16.01378).

The second clue agrees independently with structure 3. Its heavy-atom skeleton
has a mirror plane through the two bridgehead carbons and the ether bridge. The
reflection exchanges the two equivalent carbon paths around the six-membered
ring and exchanges the two methyl groups attached to the tertiary bridge
carbon. Structure 3 therefore has the stated plane of symmetry.

## Source grounding

- `TASK.json` states the requested outputs are the identities of X and Y and
  points to source page 7.
- `icho_2026_source/image/T1_page-2.png` and PDF page 7 (`Q1-2`) show the ten
  numbered structures, the four printed `C10H18O` formulae, and the observations
  that X isomerises into Y in acid and that Y has a plane of symmetry.
- The original `icho_2026_source/raw/theory_problem.pdf` was inspected directly.
  It contains 93 pages. Its blank student answer sheet on PDF page 10 (`A1-1`)
  gives separate check boxes numbered 1–10 for X and Y, grounding the finite
  candidate domain used in the formalization.
- The supplied hashes were checked and match `TASK.json`/
  `isolation_manifest.json`: the PDF hash is
  `af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60`;
  the Q1-2 image hash is
  `06f9276f8440fd17bd18f6778d1cc5950d47ffebaa60395b7078b96fcbf4f0cb`.

The Lean file treats the printed candidate formulae and diagram descriptors as
problem inputs. It treats protonation followed by intramolecular oxygen attack
as the trusted general chemical rule. It then proves candidate uniqueness by
finite elimination. For structure 3 it additionally constructs an explicit
embedded heavy-atom graph, proves formula `C10H18O` by atom/valence counting,
and supplies a nontrivial involutive reflection that preserves elements,
coordinates, and every bond.

No official solution, marking scheme, grading report, historical answer, or
answer repository was used. There is no measurement or rounding issue in this
classification question, and no source gap is needed for the identification.
