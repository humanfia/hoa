# IChO 2026 T8-A3

Tick the **bottom-right (seventh) structure** on answer sheet A8-2.

It is the six-coordinate, octahedral **trans-dichloride** complex: ligand 8
binds through all four pyridyl nitrogen atoms in the equatorial plane, and the
two chloride ligands occupy the two opposite axial sites. In compact notation,
the coordination sphere is trans-`[Fe(κ⁴-N₄-8)Cl₂]`.

## Derivation from the supplied problem

1. The synthesis drawing on Q8-1 (PDF page 72; also `T8_page-1.png`) shows one
   molecule of ligand 8 with four pyridyl N atoms reacting with `FeCl₂`.
   Reading the conjugated quaterpyridine ligand in its standard κ⁴ mode gives
   four N donor sites around Fe.
2. Q8-2 (PDF page 73) independently fixes the chloride count: the first
   catalytic step is printed as addition of `2 H₂O` with loss of `2 Cl⁻` from
   1. Thus 1 contains two replaceable coordinated chlorides, not zero or one.
3. The coordination number is therefore `4 + 2 = 6`, so the applicable
   coordination polyhedron among the supplied choices is octahedral.
4. The four donor atoms of the planar κ⁴ quaterpyridine occupy the four
   equatorial sites. The only two sites left in an octahedron are the mutually
   opposite axial sites, so the chlorides are trans.
5. On the blank student answer sheet A8-2 (PDF page 78), only the bottom-right
   drawing has four equatorial N donors and two trans axial chlorides. The two
   other N₄Cl₂ drawings in the bottom row have cis chlorides; all top-row
   choices contain fewer than two chlorides and have coordination number four
   or five.

## Source grounding and formalization boundary

The actual problem inputs used are `TASK.json`, the official Q8-1 image, Q8-1
and Q8-2 in `theory_problem.pdf`, and the blank A8-1/A8-2 student answer sheets
on PDF pages 77–78. No filled answer sheet, official solution, marking scheme,
or answer repository was used.

The only general chemistry interpretation is the standard one encoded
explicitly in the Lean model: the four pyridyl N atoms form a planar κ⁴ donor
set, and a saturated six-coordinate Fe-N₄Cl₂ sphere is represented by the six
octahedral axis sites. The Lean proof then establishes, by finite site
enumeration, that the complement of the four equatorial sites is exactly the
trans axial pair and that the seventh printed option is the unique matching
choice. There is no source gap needed to determine the requested tick box.

