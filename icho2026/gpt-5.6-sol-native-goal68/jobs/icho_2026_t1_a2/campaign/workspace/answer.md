# IChO 2026 T1-A2

## Answer

- **Z is compound 7, chamazulene**, i.e. **7-ethyl-1,4-dimethylazulene**.
- **A is azulene**, the fused aromatic **5–7 ring** hydrocarbon.
- **B is naphthalene**, the fused aromatic **6–6 ring** hydrocarbon.

The following line structures are unambiguous Kekulé SMILES (all unshown
hydrogens are implicit):

| Substance | Structure | Formula |
|---|---|---|
| Z, chamazulene | `CCC1=CC2=C(C=CC2=C(C=C1)C)C` | C₁₄H₁₆ |
| A, azulene | `C1=CC=C2C=CC=C2C=C1` | C₁₀H₈ |
| B, naphthalene | `C1=CC=C2C=CC=CC2=C1` | C₁₀H₈ |

Thus the structure to draw for Z is an azulene 5–7 fused-ring skeleton with
CH₃ groups at positions 1 and 4 and an ethyl group at position 7.  Removing
those three alkyl substituents and restoring hydrogen gives A.  Rearranging
the 5–7 fusion to two fused six-membered rings gives B.

## Derivation

A two-peak molecular-ion cluster separated by 2 u and having an intensity
ratio close to 3:1 is the signature of one chlorine atom: the peaks contain
³⁵Cl and ³⁷Cl, respectively.  Natural chlorine contains about 75.8% ³⁵Cl and
24.2% ³⁷Cl, which explains the ratio.  The isotope data are independently
tabulated by [NIST](https://physics.nist.gov/cgi-bin/Compositions/stand_alone.pl?ele=Cl)
and [CIAAW](https://www.ciaaw.org/chlorine.htm).

Under ordinary chlorination by replacement of H with Cl, the nominal mass
increase for the ³⁵Cl isotopologue is `35 − 1 = 34`.  Therefore

\[
M(Z)=218-34=184.
\]

Equivalently, for candidate 7,

\[
\begin{aligned}
M(\mathrm{C}_{14}\mathrm{H}_{16})
  &=14(12)+16=184,\\
M(\mathrm{C}_{14}\mathrm{H}_{15}{}^{35}\mathrm{Cl})
  &=14(12)+15+35=218,\\
M(\mathrm{C}_{14}\mathrm{H}_{15}{}^{37}\mathrm{Cl})
  &=14(12)+15+37=220.
\end{aligned}
\]

Checking all ten formulae in the printed table, only compound 7 has nominal
mass 184 and hence gives exactly this monochlorinated 218/220 pair.  The drawn
structure of 7 is the blue azulene derivative chamazulene.  Its formula,
connectivity, and systematic name are independently recorded by
[PubChem (CID 10719)](https://pubchem.ncbi.nlm.nih.gov/compound/Chamazulene)
and [NIST Chemistry WebBook](https://webbook.nist.gov/cgi/cbook.cgi?ID=C529055).

The 5–7 fused core of chamazulene is azulene, so A is azulene.  Azulene is
C₁₀H₈ and its structure is recorded by
[PubChem (CID 9231)](https://pubchem.ncbi.nlm.nih.gov/compound/azulene).  Its
planar C₂ᵥ structure has the molecular plane and a second mirror plane
perpendicular to it, matching the two-plane clue.

Thermal rearrangement of azulene gives the more stable benzenoid isomer
naphthalene; this transformation is also documented in the primary chemical
literature, for example
[Scott and Kirms, *J. Chem. Soc., Perkin Trans. 2* (1975), 1464](https://pubs.rsc.org/en/content/articlelanding/1975/p2/p29750001464).
Naphthalene has the same formula C₁₀H₈ but a 6–6 fused-ring graph; its structure
is recorded by [PubChem (CID 931)](https://pubchem.ncbi.nlm.nih.gov/compound/91-20-3).
Its planar D₂h structure supplies three mutually perpendicular mirror planes:
the molecular plane and the two planes perpendicular to it along and across
the long molecular axis.

## Source grounding and scope

The answer was derived from the problem-only assets before the ordinary
reference checks above:

- `TASK.json` supplies the exact requested outputs and identifies source PDF
  page 8.
- `icho_2026_source/image/T1_page-2.png` supplies the ten candidate structures
  and formulae, including candidate 7 as C₁₄H₁₆.
- `icho_2026_source/image/T1_page-3.png` supplies the colour, derivative,
  symmetry, heating, and 218/220 mass-spectrum clues.
- `icho_2026_source/raw/theory_problem.pdf` was inspected directly.  PDF page
  8 contains the question.  The blank student sheets on PDF pages 10–11 show
  that Z is to be selected from compounds 1–10 and that A and B are to be
  drawn in separate boxes; they contain no answer information.

No official solution, marking scheme, answer repository, or historical
competition answer was used.  The only interpretive premise beyond the printed
data is the standard mass-spectrometric convention that the stated 218/220
cluster is the molecular-ion isotope cluster of the monochlorinated
H-substitution product.  This is exactly the convention signalled by the
printed two-peak 3:1 chlorine pattern.  There is no unresolved source gap.

## What the Lean proof establishes

`IChO2026Problems/problem_icho_2026_t1_a2.lean` does not encode the answer as
mere strings.  It:

- checks all ten printed molecular formulae and proves candidate 7 is the
  unique formula producing the 218/220, 3:1 monochloro pattern;
- represents every C and H atom explicitly, with formal charge, radical count,
  and stereochemical annotation;
- represents every bond and verifies a full-valence Kekulé form for
  chamazulene, azulene, and naphthalene;
- proves that chamazulene contains exactly the ten-carbon azulene aromatic
  core and explicitly checks its ethyl and two methyl attachment bonds;
- proves an exact atom/bond graph rewrite from the azulene 5–7 fusion to the
  naphthalene 6–6 fusion while preserving C₁₀H₈; and
- constructs exact integral planar embeddings and verifies two perpendicular
  reflection planes for azulene and three mutually perpendicular reflection
  planes for naphthalene.

The problem itself supplies the experimental fact that heating A causes the
rearrangement.  The formalization proves the atom-level identity of its stated
product and the corresponding structural rewrite; it does not pretend to
derive reaction kinetics from graph theory.
