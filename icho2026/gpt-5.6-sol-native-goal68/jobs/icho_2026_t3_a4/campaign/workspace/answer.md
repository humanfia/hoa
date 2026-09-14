# IChO 2026 T3-A4

![Repeat units of COFs 3–6, with the cell boundaries shown as blue dashed lines](cof_repeat_units.svg)

The part of each drawing on the same side of a blue dashed line as the central
tritopic ring belongs to the displayed repeat unit.  As in the supplied COF-1
example, each of the three dashed lines bisects a peripheral ditopic aryl
linker.  It therefore crosses two arene C–C bonds, giving six boundary cuts per
repeat unit.  The wavy bonds show continuation into neighbouring cells.

- **COF-3:** the three aldehydes of benzene-1,3,5-tricarbaldehyde have condensed
  with amino groups of the 1,4-diamino-2,5-dihydroxybenzene linker.  Each arm is
  therefore `central aryl–C(H)=N–hydroxyphenylene`.  The cell contains three
  ordinary imine groups.

- **COF-4:** oxidize and cyclize every imine with its adjacent phenolic OH.  In
  each arm the phenolic O bonds to the imine carbon, while O–H and that carbon's
  C–H are lost.  This gives a benzoxazole linkage.  Thus the product still has
  three C=N bonds, but they are benzoxazole C=N bonds rather than imines.  The
  loss is two H per arm, hence six H per repeat unit, exactly as stated.

- **COF-5:** the three aldehydes of
  2,4,6-trihydroxybenzene-1,3,5-tricarbaldehyde condense with
  p-phenylenediamine.  The drawn form is the aromatic enol–imine form: the
  central ring bears three OH groups and each arm is
  `central aryl–C(H)=N–p-phenylene`.

- **COF-6:** each enol–imine arm of COF-5 undergoes the irreversible
  keto–enamine tautomerization.  Each central OH becomes C=O, its H moves to the
  corresponding imine N, the C=N bond becomes C–NH, and the bond from the node
  to the former imine carbon becomes C=C(H).  The node is consequently a
  cyclohexane-1,3,5-trione unit with three exocyclic
  `C=C(H)–NH–p-phenylene` arms.  There is no C=N bond and hence no imine stretch.

For the exact dashed-cell convention in the figure, the atom inventories are
`C18H12N3O3` for COF-3, `C18H6N3O3` for COF-4, and `C18H12N3O3` for both COF-5
and COF-6.  These formulas are checks on the drawings rather than additional
assumptions: COF-4 differs from COF-3 only by H6, while the COF-5/COF-6
isomerization preserves composition.

## Source grounding and derivation

I used the problem-only assets recorded in `TASK.json`.  The hashes of the two
provided image renders and the PDF agree with the isolation manifest.  The
monomer structures and reaction/IR/elemental-analysis statements were read
from `T3_page-3.png`, `T3_page-4.png`, and original PDF page 28.  I also
inspected original PDF page 34, the blank four-panel student answer sheet for
COFs 3–6.  The dashed-cell choice is copied from the COF-1 example on page 28;
the answer-sheet panel arrangement itself supplies no chemical information.

The only general chemistry used beyond the printed structures is local bond
bookkeeping: aldehyde–primary-amine condensation gives C(H)=N; oxidative
cyclization of an o-hydroxy imine gives a benzoxazole by loss of O–H and C–H;
and an o-hydroxy imine can tautomerize to the corresponding beta-ketoenamine by
proton transfer and pi-bond rearrangement.  Applying those rules independently
to the three symmetry-equivalent arms gives all four structures above.  No
extra stereochemical choice is needed, and all atoms are neutral closed-shell
atoms in the depicted forms.
