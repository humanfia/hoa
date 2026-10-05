# IChO 2026 T5-A4

## Answer

\[
\boxed{X=\mathrm{IBr}}
\]

Thus, `X` is iodine monobromide (the order `BrI` denotes the same molecular
formula).

## Calculation

The fatty-acid result needed from 5.3 can be derived from the problem-only
material rather than assumed. Three distinct equimolar products from reductive
ozonolysis of an acyclic fatty-acid chain mean that the chain is cut at two
C=C bonds. If the acid has `n` carbon atoms, its formula is consequently
\(\mathrm{C_nH_{2n-4}O_2}\).

Using the fragments printed in 5.1, non-ionised PL1 is obtained by condensing
three glycerols, four of these fatty acids, and two phosphoric acids, with eight
water molecules eliminated:

\[
3\,\mathrm{C_3H_8O_3}
+4\,\mathrm{C_nH_{2n-4}O_2}
+2\,\mathrm{H_3PO_4}
-8\,\mathrm{H_2O}
=\mathrm{C_{4n+9}H_{8n-2}O_{17}P_2}.
\]

For this neutral formula, half the sum of the ordinary valences counts all
sigma and pi bonds:

\[
N_{\sigma+\pi}
=\frac{4(4n+9)+(8n-2)+2(17)+5(2)}{2}
=12n+39.
\]

The stated value \(N_{\sigma+\pi}=255\) therefore gives \(n=18\), so the fatty
acid is \(\mathrm{C_{18}H_{32}O_2}\). Using the atomic masses printed in the
problem PDF,

\[
M(\mathrm{C_{18}H_{32}O_2})
=18(12.01)+32(1.008)+2(16.00)
=280.436\ \mathrm{g\,mol^{-1}}.
\]

As a check, its two C=C bonds consume two moles of iodine per mole of acid:

\[
\frac{100}{280.436}\times2\times[2(126.9)]
=181.0039\ \mathrm{g}\approx181.0\ \mathrm{g},
\]

which reproduces the stated iodine uptake without intermediate rounding.

Because `X` reacts in the same addition pattern as iodine and the product
contains iodine, write the iodine-containing diatomic reagent as
\(\mathrm{IE}\). Two molecules add to the two C=C bonds. With the displayed
iodine mass fraction \(w_\mathrm I=0.3657\),

\[
0.3657
=\frac{2(126.9)}{280.436+2[126.9+A_r(E)]}.
\]

Solving gives

\[
A_r(E)
=\frac12\left(\frac{2(126.9)}{0.3657}-280.436\right)-126.9
=79.8875,
\]

which identifies bromine (the supplied table gives \(A_r(\mathrm{Br})=79.90\)).
The unrounded forward check for IBr is

\[
M\bigl(\mathrm{C_{18}H_{32}O_2(IBr)_2}\bigr)
=280.436+2(126.9+79.90)=694.036,
\]

\[
w_\mathrm I
=\frac{2(126.9)}{694.036}\times100\%
=36.568708\ldots\%=36.57\%.
\]

The printed 36.57% represents the half-last-place interval
\([36.565\%,36.575\%]\); the exact IBr calculation lies inside it.

## Source grounding and interpretation

- `T5_page-1.png` and PDF source page 44 supply the fragment counts and the
  non-ionised PL1 context used to rederive the fatty-acid dependency.
- `T5_page-2.png`/PDF source page 45 is the blank drawing area for 5.2 and adds
  no numerical premise.
- `T5_page-3.png` and PDF source page 46 state the three ozonolysis products,
  255 total bonds, 181.0 g iodine uptake per 100 g acid, 36.57% iodine in the
  adduct, and the request for the formula of `X`.
- PDF source page 5 supplies H 1.008, C 12.01, O 16.00, Br 79.90, and I 126.9.
- The original blank student sheets on PDF source pages 48--51 were inspected;
  the A5-3 sheet (source page 50) contains only blank response fields and no
  answer or additional premise.

The chemical interpretation of “reacts in similar way with iodine” is the
standard 1:1 addition of a diatomic halogen/interhalogen molecule across each
C=C bond. Since the fatty acid itself contains no iodine, the iodine in the
adduct comes from `X`. Within the iodine-containing diatomic halogen family
IF/ICl/IBr/I2, the measured interval uniquely selects IBr; the Lean proof
checks all four candidates exactly. No official solution, marking scheme, or
answer repository was used.
