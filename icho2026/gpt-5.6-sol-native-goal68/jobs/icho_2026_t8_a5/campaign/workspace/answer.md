# IChO 2026 T8-A5

Take a basis of $1\ \mathrm{g}$ of the loaded material. Because
“3.8% mass fraction” means catalyst mass divided by total loaded-material
mass,

\[
m_{\mathrm{cat}}=0.038\ \mathrm{g},\qquad
m_{\mathrm{C_3N_4}}=(1-0.038)\ \mathrm{g}=0.962\ \mathrm{g}.
\]

Using the Avogadro constant printed in the problem booklet,
$N_A=6.022\times10^{23}\ \mathrm{mol^{-1}}$, the number of catalyst
molecules is

\[
n_{\mathrm{cat}}N_A
=\frac{0.038\ \mathrm{g}}{557.21\ \mathrm{g\ mol^{-1}}}
  (6.022\times10^{23}\ \mathrm{mol^{-1}})
\approx4.1068178963\times10^{19}\ \text{molecules}.
\]

The corresponding C₃N₄ surface area is

\[
A=(0.962\ \mathrm{g})(17.8\ \mathrm{m^2\ g^{-1}})
  =17.1236\ \mathrm{m^2}
  =1.71236\times10^{19}\ \mathrm{nm^2},
\]

where $1\ \mathrm{m^2}=10^{18}\ \mathrm{nm^2}$. Therefore

\[
N_{\mathrm{cat}}
=\frac{(0.038/557.21)(6.022\times10^{23})}
       {(0.962)(17.8)(10^{18})}
=\frac{5720900000}{2385360289}
=2.3983379057586\ldots\ \mathrm{molecules\ nm^{-2}}.
\]

Thus, to the required three significant figures,

\[
\boxed{N_{\mathrm{cat}}=2.40\ \mathrm{molecules\ nm^{-2}}}.
\]

## Source grounding

- `T8_page-2.png` and PDF page 73 state the three task inputs:
  $\omega_{\mathrm{cat}}=3.8\%$, C₃N₄ specific surface area
  $17.8\ \mathrm{m^2\ g^{-1}}$, and
  $M_{\mathrm{cat}}=557.21\ \mathrm{g\ mol^{-1}}$.
- The original booklet’s general-information page (PDF page 3) supplies
  $N_A=6.022\times10^{23}\ \mathrm{mol^{-1}}$ and
  $1\ \mathrm{nm}=10^{-9}\ \mathrm m$.
- The blank student answer sheet on PDF page 81 contains only the field
  $N_{\mathrm{cat}}=\underline{\hspace{1.5cm}}$; it supplies no hidden
  value or extra condition.
- `T8_page-1.png` provides the shared catalyst context but no additional
  numerical premise needed for T8-A5.

The calculation uses the ordinary definition of a component mass fraction,
$\omega_{\mathrm{cat}}=m_{\mathrm{cat}}/m_{\mathrm{loaded}}$, and the
definition of specific surface area. The 1 g basis is arbitrary: both the
number of molecules and the support area scale linearly with total sample
mass, so their ratio is independent of that choice. No uncertainty interval
is asserted; the raw value is the direct calculation from the displayed
problem data, followed only by final reporting to three significant figures.
