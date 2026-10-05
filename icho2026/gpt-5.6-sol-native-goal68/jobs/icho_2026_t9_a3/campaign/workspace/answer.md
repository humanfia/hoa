# IChO 2026 T9-A3

The requested values are

\[
\boxed{r_s=35}, \qquad \boxed{s_c=21}.
\]

## Derivation

The starting material in the reaction leading to **X** is β-cyclodextrin, and
the structure in the problem explicitly has seven glucopyranoside repeats.
Within each repeat, sodium periodate cleaves the vicinal-diol bond C2–C3.
Sodium borohydride then reduces the two carbonyl ends to methylene alcohols,
and acetic anhydride acetylates the alcohols.  Neither of the last two steps
forms another carbon-skeleton bond.

After the C2–C3 cleavage, the unbroken cyclic path through one repeat is

\[
\mathrm{C1-O5-C5-C4-O_{glycosidic}},
\]

where the glycosidic oxygen connects C4 of that repeat to C1 of the next one.
Thus each repeat contributes five atoms to the surviving macrocycle, giving

\[
r_s=7\times 5=35.
\]

An intact glucopyranoside unit has stereogenic carbons C1–C5.  In **X**, the
former C2 and C3 atoms are each methylene carbons after cleavage and reduction,
so neither is stereogenic.  C1, C4, and C5 retain four different substituents;
acetylation does not change those carbon configurations or create a new
stereocentre.  Therefore each repeat contributes three stereocentres:

\[
s_c=7\times 3=21.
\]

## Source grounding

- `TASK.json` identifies the two exact integer outputs and points to Q9-2 of
  the official problem PDF.
- `icho_2026_source/image/T9_page-1.png` states that β-CD contains seven
  α-D-glucopyranoside units.
- `icho_2026_source/image/T9_page-2.png` (physical PDF page 85) shows the
  seven-repeat starting structure, the NaIO₄/NaBH₄/Ac₂O sequence leading to
  **X**, and the text of question 9.3.
- The original `icho_2026_source/raw/theory_problem.pdf` was inspected at its
  Q9-2 page and at blank student answer-sheet pages A9-1 and A9-2.  A9-2
  (physical PDF page 90) contains only blank fields for `rs` and `sc`; it adds
  no numerical premise or answer.

The use of periodate cleavage of a vicinal diol and borohydride reduction is
standard reaction chemistry applied to the bonds explicitly drawn in the
problem.  T9-A2 concerns the separate product **K** and is not needed to count
the atoms or stereocentres of **X**.  No source gap or supplementary model
assumption is needed.

## Formalization correspondence

`IChO2026Problems/problem_icho_2026_t9_a3.lean` represents a ring atom by a
pair consisting of one of the seven repeats and one of the five surviving ring
sites.  It separately represents a stereocentre by a repeat and one of the
three retained stereogenic carbon sites.  Lean proves the local inventories,
the two product-cardinality factorizations, and finally `ringSizeX = 35` and
`stereocentreCountX = 21`.
