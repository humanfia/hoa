# IChO 2026 T3-A7

The concentration decrease is

\[
\Delta c=19.90-9.225=10.675\ \mathrm{mg\,dm^{-3}}.
\]

Since \(200.0\ \mathrm{mL}=0.2000\ \mathrm{dm^3}\), the mass of uranyl removed
from the solution is

\[
m_{\mathrm{ads}}=\Delta c\,V
=10.675\times 0.2000
=2.1350\ \mathrm{mg}.
\]

The mass of COF-9 is \(5.000\ \mathrm{mg}=0.005000\ \mathrm{g}\). Therefore

\[
q_e=\frac{m_{\mathrm{ads}}}{m_{\mathrm{COF-9}}}
=\frac{2.1350\ \mathrm{mg}}{0.005000\ \mathrm{g}}
=427\ \mathrm{mg\,g^{-1}}.
\]

To obtain the number of ions per pore, first derive the formula mass represented
by one pore. The pictured honeycomb has three D2 and three E1 vertices around a
pore, and each tritopic vertex is shared by three pores. Thus one pore contains
one D2 and one E1 monomer equivalent. Direct atom counting in the structures
gives

\[
\mathrm{D2=C_{24}H_{15}N_3O_3},\qquad
E1=C_{12}H_9N_3}.
\]

There are six edges around a pore, each shared by two pores, so there are three
water-eliminating condensations per pore. Hence COF-8 has the per-pore formula

\[
\mathrm{C_{24}H_{15}N_3O_3+C_{12}H_9N_3-3H_2O
=C_{36}H_{18}N_6}.
\]

The figure shows that all three nitrile groups in that formula unit react with
hydroxylamine to give amidoxime groups. Each conversion adds \(\mathrm{NH_2OH}\),
so the COF-9 formula per pore is

\[
\mathrm{C_{36}H_{18}N_6+3NH_2OH=C_{36}H_{27}N_9O_3}.
\]

Using the atomic masses printed on the supplied periodic table,

\[
M_{\mathrm{COF-9,pore}}
=36(12.01)+27(1.008)+9(14.01)+3(16.00)
=633.666\ \mathrm{g\,mol^{-1}},
\]

and

\[
M_{\mathrm{UO_2^{2+}}}=238.03+2(16.00)=270.03\ \mathrm{g\,mol^{-1}}.
\]

Therefore the exact nominal mole ratio, which is also the ratio of uranyl ions
to pores because the Avogadro factors cancel, is

\[
\begin{aligned}
N_{\mathrm{UO_2^{2+}}/\mathrm{pore}}
&=\left(427\ \frac{\mathrm{mg\ UO_2^{2+}}}{\mathrm{g\ COF-9}}\right)
  \left(\frac{1\ \mathrm{g}}{1000\ \mathrm{mg}}\right)
  \left(\frac{633.666\ \mathrm{g\ COF-9}}{1\ \mathrm{mol\ pore}}\right)
  \left(\frac{1\ \mathrm{mol\ UO_2^{2+}}}{270.03\ \mathrm{g\ UO_2^{2+}}}\right)\\
&=\frac{45095897}{45005000}
=1.0020197089\ldots\ \mathrm{ions\,pore^{-1}}.
\end{aligned}
\]

Thus, to three significant figures,

\[
\boxed{q_e=427\ \mathrm{mg\,g^{-1}}},\qquad
\boxed{1.00\ \mathrm{UO_2^{2+}\ ions\ per\ pore}}.
\]

## Source grounding

- `TASK.json` transcribes the experimental values and identifies the supplied
  problem pages. The SHA-256 hashes of `T3_page-6.png`, `T3_page-7.png`, and
  `theory_problem.pdf` were checked against `isolation_manifest.json`.
- `T3_page-6.png` supplies the D2 and E1 structures and the COF-8 repeat/pore
  drawing. `T3_page-7.png` supplies the COF-8 to COF-9 hydroxylamine conversion,
  the three amidoxime groups per pore formula unit, and all adsorption data.
- The original PDF was inspected at Q3-7 (PDF page 31), the periodic table at
  G1-5 (PDF page 5), and the blank student answer sheet at A3-5 (PDF page 36).
  The answer sheet asks only for \(q_e\) and the `COF-9 : UO2^2+` ratio and adds
  no further numerical premise or normalization.
- The printed experimental decimals are used as exact nominal inputs for the
  requested contest calculation. No uncertainty interval is claimed. The final
  displays follow the task's three-significant-figure reporting policy.

There is no source gap: the formula and pore normalization are derivable from
the supplied structures and the honeycomb sharing count, while the capacity is
fixed by the supplied equilibrium mass balance.
