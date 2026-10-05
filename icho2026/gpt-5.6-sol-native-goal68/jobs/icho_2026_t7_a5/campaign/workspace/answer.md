# IChO 2026 T7-A5

## Answer

Complex **5** is the dinitrogen-bridged dimolybdenum complex

\[
\boxed{\left[\{\mathrm{Mo}(\mathrm{PNP})(\mathrm{N_2})_2\}_2
(\mu\text{-}\eta^1{:}\eta^1\text{-}\mathrm{N_2})\right]}
\]

or, more compactly,

\[
\boxed{[(\kappa^3\text{-}P,N,P\text{-PNP})\mathrm{Mo}(\mathrm{N_2})_2]_2
(\mu\text{-}\mathrm{N_2})}.
\]

Using the permitted simplified PNP symbol, its connectivity is

```text
             N≡N                         N≡N
              |                           |
     (PNP)──Mo──N≡N──Mo──(PNP)
              |                           |
             N≡N                         N≡N
```

Each PNP is one neutral tridentate ligand bound through P,N,P. Each outer
N≡N is a terminal end-on ligand; the central N≡N is the single
\(\mu\)-\(\eta^1{:}\eta^1\) bridge. In the meridional PNP drawing, the two P
donors are trans, the bridging N₂ donor is trans to pyridine N, and the two
terminal N₂ donors are mutually trans. The product is neutral Mo(0), with no
radical or stereocentre annotation.

The corresponding formation stoichiometry is

\[
2\,\mathrm{MoCl_3(PNP)}+6\,\mathrm{Na}+5\,\mathrm{N_2}
\longrightarrow
[\{\mathrm{Mo(PNP)(N_2)_2}\}_2(\mu\text{-}\mathrm{N_2})]
+6\,\mathrm{NaCl},
\]

with Hg serving as the amalgam medium.

## Derivation

From the printed molar mass,

\[
n(4)=\frac{1.00}{597.824}
=1.672733112\times10^{-3}\ \mathrm{mol}.
\]

Using \(PV=nRT\), with
\(R=0.08314\ \mathrm{L\,bar\,mol^{-1}\,K^{-1}}\), and converting 94.97 cm³ to
0.09497 L,

\[
n(\mathrm{N_2})=
\frac{(1.0)(0.09497)}{(0.08314)(273.15)}
=4.181915113\times10^{-3}\ \mathrm{mol}.
\]

Thus the raw central-value ratio is

\[
\frac{n(\mathrm{N_2})}{n(4)}=2.500049220\ldots,
\]

which gives the primitive whole-molecule ratio \(2\,4:5\,\mathrm{N_2}\).
Conversely, exactly \(5/2\) mol N₂ per mol 4 predicts
\(94.96813025\ldots\ \mathrm{cm^3}\), inside the volume's displayed
half-quantum interval \([94.965,94.975]\ \mathrm{cm^3}\), and hence reports as
94.97 cm³ without intermediate rounding.

The neutral PNP ligand and three chloride ligands make Mo in 4 formally
Mo(III). Three equivalents of Na–Hg remove the chlorides and supply three
electrons per Mo, giving Mo(0). Neutral-atom electron counting at each metal is

\[
6\ (\mathrm{Mo^0})+6\ (\mathrm{PNP})+2c\ (c\ \mathrm{N_2\ contacts})=18,
\]

so \(c=3\). Each of the two Mo centers therefore needs three N₂ contacts. Five
intact N₂ molecules provide six contacts only when one N₂ contacts both
metals and the other four are terminal. Consequently there is exactly one
bridging N₂ and exactly two terminal N₂ ligands at each Mo.

## Source grounding and scope

- `T7_page-2.png` and PDF page 64 show neutral \(\mathrm{MoCl_3(PNP)}\), three
  equivalents of Na–Hg, N₂ at 1.0 bar,
  \(M_W(4)=597.824\ \mathrm{g\,mol^{-1}}\), and the permitted PNP abbreviation. Its expanded
  template is 2,6-bis[(di-tert-butylphosphino)methyl]pyridine.
- `T7_page-3.png` and PDF page 65 give the 1.00 g/94.97 cm³ gas-uptake clue.
- The blank student sheet on PDF page 70 was inspected. It supplies only an
  empty box labeled 5, with no additional charge, stereochemical, or drawing
  template constraint.
- The only general chemistry used beyond the figures is the ideal-gas law,
  oxidation-state/electron bookkeeping, neutral two-electron donation by each
  end-on N₂ contact, and the closed-shell 18-electron rule. The numerical clue
  alone would not distinguish arbitrary high-order empirical ratios; the
  intended primitive molecular stoichiometry and closed-shell single-product
  model are stated explicitly here.

The Lean file represents both Mo atoms, all ten atoms belonging to the five N₂
units, all six P/N/P donor atoms of the two simplified PNP symbols, every
coordinate or N≡N bond, ligand membership, charge, radical state, and the trans
relationships. It separately proves the gas-volume match and the uniqueness of
the 2-terminal/1-bridging topology under the stated electron-count constraints.
