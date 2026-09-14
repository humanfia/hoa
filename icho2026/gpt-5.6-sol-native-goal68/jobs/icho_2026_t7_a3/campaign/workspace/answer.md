# IChO 2026 T7-A3 answer

## Results

a) The amount of nitrogen after the 58th cycle is

\[
\boxed{5.6662\ \mathrm{mol\ N_2}}.
\]

The unrounded value is

\[
5.6662099726118159072\ldots\ \mathrm{mol\ N_2}.
\]

b) The first cycle at which the overall yield reaches 97.0% is

\[
\boxed{n=189\text{ cycles}}.
\]

## Derivation

A 4 mol fresh portion with the stated stoichiometric ratio
\(N_2:H_2=1:3\) contains

\[
n_{N_2,\mathrm{fresh}}=4\left(\frac{1}{1+3}\right)=1\ \mathrm{mol}.
\]

The per-cycle yield is \(\eta=0.150=3/20\), so the fraction of the
reactants retained for recycle after each cycle is

\[
q=1-\eta=0.850=\frac{17}{20}.
\]

Let \(f_k\) be the moles of \(N_2\) remaining after cycle \(k\), before
the next fresh portion is added. Initially \(f_0=0\). Adding 1 mol of fresh
\(N_2\) and then retaining the fraction \(q\) gives

\[
f_{k+1}=q(f_k+1).
\]

Consequently,

\[
f_k=q+q^2+\cdots+q^k
    =\frac{q(1-q^k)}{1-q}
    =\frac{17}{3}\left(1-\left(\frac{17}{20}\right)^k\right).
\]

At \(k=58\),

\[
f_{58}=\frac{17}{3}\left(1-\left(\frac{17}{20}\right)^{58}\right)
       =5.6662099726118159072\ldots\ \mathrm{mol},
\]

which rounds to 5.6662 mol at the requested four decimal places.

After \(k\) cycles, \(k\) fresh portions have supplied \(k\) mol of
\(N_2\). The amount converted to ammonia is therefore \(k-f_k\) mol, so
the cumulative overall yield is

\[
Y_k=\frac{k-f_k}{k}=1-\frac{f_k}{k}\qquad(k\ge 1).
\]

This also checks the stated starting value:
\(Y_1=1-0.85=0.150=15.0\%\). The quantity \(f_k/k\) is the average of the
decreasing sequence \(q,q^2,\ldots,q^k\), so it decreases with \(k\), and
therefore \(Y_k\) increases. It is thus enough to check the two cycle counts
on either side of the threshold:

\[
Y_{188}=0.9698581560283704\ldots<0.970,
\]

\[
Y_{189}=0.9700176366843047\ldots\ge 0.970.
\]

Hence 189 is the least positive number of cycles that reaches 97.0% overall
yield.

## Source grounding

- `TASK.json` identifies the two requested outputs and the four-decimal
  reporting requirement for part (a).
- `icho_2026_source/image/T7_page-2.png` and page 64 of
  `icho_2026_source/raw/theory_problem.pdf` state the fresh-feed ratio and
  amount, the 0.150 cycle yield, complete ammonia separation, reagent recycle,
  the observation time after cycle 58, and the 97.0% target.
- `icho_2026_source/image/T7_page-1.png` supplies the shared Haber--Bosch
  context and displays the reaction stoichiometry. No answer from T7-A1 or
  T7-A2 is needed here.
- The blank student sheet on page 69 of the PDF provides fields for the two
  T7-A3 results but adds no scientific premise.

The calculation treats the printed feed amount and stipulated yield as exact,
as required by `TASK.json`. It uses only the problem's idealized cycle model:
stoichiometric fresh feed, a constant fraction reacting on each pass, complete
ammonia separation, and complete return of unreacted gases. There are no source
gaps and no supplementary scientific assumptions.
