# IChO 2026 T3-A1

**Answer:** \(\boxed{\mathrm{C_3H_2BO}}\), with carbon mass percentage
\(\boxed{55.55\%}\).

## Derivation

In the COF-1 drawing, each para-phenylene linker is a doubly substituted
benzene unit, \(\mathrm{C_6H_4}\), and has two ends. Each boroxine ring is an
alternating six-membered ring, \(\mathrm{B_3O_3}\), with three phenyl
attachment sites. For a closed periodic piece containing \(L\) linkers and
\(R\) boroxine rings, counting attachments in the two ways gives

\[
2L=3R.
\]

The smallest positive ratio is therefore \(L:R=3:2\). Its atom inventory is

\[
3(\mathrm{C_6H_4})+2(\mathrm{B_3O_3})
=\mathrm{C_{18}H_{12}B_6O_6}
=6(\mathrm{C_3H_2BO}).
\]

The subscripts \(3,2,1,1\) have greatest common divisor 1, so the empirical
formula is \(\mathrm{C_3H_2BO}\).

Using the atomic weights printed in the supplied periodic table
(C 12.01, H 1.008, B 10.81, O 16.00), the mass of one empirical-formula unit
on a molar scale is

\[
M=3(12.01)+2(1.008)+10.81+16.00=64.856\ \mathrm{g\ mol^{-1}}.
\]

Carbon contributes \(3(12.01)=36.03\ \mathrm{g\ mol^{-1}}\), hence the raw
percentage is

\[
w_{\mathrm C}=100\frac{36.03}{64.856}
=\frac{450375}{8107}\%=55.553842358\ldots\%.
\]

Rounding only this final value to the explicitly requested two decimal places
gives \(55.55\%\).

## Source grounding

- `TASK.json` identifies T3-A1 and requires the empirical formula plus carbon
  mass percentage to two decimal places.
- `icho_2026_source/image/T3_page-1.png` and page 25 (`Q3-1`) of
  `icho_2026_source/raw/theory_problem.pdf` supply the COF-1 structural drawing,
  identify the alternating rings as boroxine rings, and state that dashed lines
  indicate repeat units.
- Page 5 (`G1-5`) of the same PDF supplies the four atomic weights used above.
- The blank student answer sheet on PDF page 32 (`A3-1`) has exactly two fields
  for 3.1: `COF-1: ______` and `C: ______ %`; this confirms the requested output
  shape without supplying either answer.
- The interpretations of an unlabeled line-angle carbon framework and the
  hydrogen count on a doubly substituted benzene ring are ordinary chemical
  notation conventions. No external solution, marking scheme, or prior answer
  was used.
