# IChO 2026 T9.6

The number of constitutional linkage isomers is

\[
\boxed{3}.
\]

## Derivation

Call the initially formed primary alcohol site unit 1.  The directing rule in
the question places the next debenzylation at unit 4.  Unit 4 is available in
the fully benzylated starting cyclodextrin, so the stated unit-3 fallback is
not used here.  Intermediate **L** therefore has two free primary-OH sites,
at units 1 and 4.

In the next step, one of these two OH groups is converted to the alkenyl ether
that ultimately becomes the dimer tether; the product drawing shows that the
other site remains `CH₂OH`.  There are consequently two regioisomeric
monomeric ends:

- **A:** tether at unit 1 and residual OH at unit 4;
- **B:** tether at unit 4 and residual OH at unit 1.

These are distinct on the oriented seven-membered α-1,4-glycosidic ring: seen
from the tether, the residual OH is displaced in one or the other cyclic
direction.  A rotation of the ring does not interchange the two differently
labelled sites, and reversing the α-1,4 connectivity is not an allowed
relabeling of the molecular constitution.

Olefin metathesis followed by hydrogenation joins two such ends with a
symmetric spacer.  Exchanging the two identical β-CD ends does not make a new
constitutional isomer.  Thus the unordered pairs of end types are

\[
AA,\qquad AB=BA,\qquad BB.
\]

Equivalently, this is the number of size-two multisets drawn from two types,
\(\binom{2+2-1}{2}=\binom{3}{2}=3\).

## Source grounding

- `TASK.json` identifies the requested output as one exact integer: the
  number of β-CD dimer isomers.
- `icho_2026_source/image/T9_page-3.png` and page 86 of
  `icho_2026_source/raw/theory_problem.pdf` supply the unit-1 → unit-4
  directing rule, the unit-3 fallback, the reaction sequence, and the final
  dimer drawing with one free `CH₂OH` and one tether on each β-CD end.
- `icho_2026_source/image/T9_page-2.png` supplies the immediately preceding
  official context.  It introduces no additional premise needed for this
  count.
- The blank student response sheet on page 91 of the PDF (`A9-3`, section
  9.6) contains only an open answer area and therefore adds no hidden data or
  answer cue.

No official solution, marking scheme, answer repository, or historical
experimental answer was used.  The only general identification used is the
definition of a constitutional isomer: reversing a symmetric connection
between two identical molecular ends does not create a second constitution.

