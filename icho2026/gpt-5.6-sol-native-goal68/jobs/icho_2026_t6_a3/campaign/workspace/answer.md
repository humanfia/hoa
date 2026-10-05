# IChO 2026 T6-A3 (printed question 6.3)

**Answer:** \(\boxed{X=\mathrm{I}}\). The halogenated reagent can use iodine only.

## Calculation

An electron accelerated through a potential difference \(V\) receives energy
\(eV\). For one mole of electrons, the corresponding energy is \(FV\), where
\(F\) is the Faraday constant. Using the value printed in the problem
booklet,

\[
E=\frac{(96\,485\ \mathrm{C\,mol^{-1}})(2.5\ \mathrm{V})}
        {1000\ \mathrm{J\,kJ^{-1}}}
 =241.2125\ \mathrm{kJ\,mol^{-1}}.
\]

Here \(1\ \mathrm{C\,V}=1\ \mathrm{J}\). Comparing this energy directly
with every C-X bond dissociation energy in the question gives

| bond | BDE / \(\mathrm{kJ\,mol^{-1}}\) | comparison with \(241.2125\) | possible? |
|---|---:|---:|:---:|
| C-F  | 467 | \(467>241.2125\) | no |
| C-Cl | 346 | \(346>241.2125\) | no |
| C-Br | 290 | \(290>241.2125\) | no |
| C-I  | 228 | \(228<241.2125\) | yes |

Thus the applied electron energy is sufficient to meet the C-I bond
dissociation energy but not that of any of the other listed C-X bonds.

## Source grounding and formalization scope

- `TASK.json` identifies the requested output as the exact finite set of
  possible halogens and reproduces the four BDE values.
- `icho_2026_source/image/T6_page-2.png` and one-based PDF page 53 (Q6-2) of
  `icho_2026_source/raw/theory_problem.pdf` show the same 2.5 V prompt and BDE
  table. `T6_page-1.png` supplies the immediately preceding reaction context.
- One-based PDF page 3 supplies \(F=96\,485\ \mathrm{C\,mol^{-1}}\). The
  conversion uses the standard electrical-energy law \(E=qV\).
- The blank student answer sheet on one-based PDF page 58 (A6-2) provides a
  single field `X = _____`; it adds no condition or alternative output.

The Lean file separates these printed numerical inputs from the derived
energy and classification. `EnergeticallyAccessible` expresses the energy
screen requested by the prompt: a listed bond is accessible when its BDE is
at most the molar energy delivered to the electrons. The proof checks all four
members of the problem's candidate domain and proves the resulting finite set
is exactly the iodine singleton. There is no underdetermination or additional
source gap for this requested classification.

