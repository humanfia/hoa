# IChO 2026 T1-A6

## Answer

The stone is aluminium mellitate hexadecahydrate,

\[
\boxed{\mathrm{Al_2[C_6(COO)_6]\cdot16H_2O}}
\]

(equivalently, \(\mathrm{Al_2C_{12}O_{12}\cdot16H_2O}\), whose flattened
elemental formula is \(\mathrm{Al_2C_{12}H_{32}O_{28}}\)). Compound H is

\[
\boxed{\mathrm{Al_2O_3}}.
\]

## Derivation of the prerequisites

These identifications can be derived from A4 and A5 rather than assumed.
The atomic weights below are those printed in the supplied periodic table:
H 1.008, C 12.01, O 16.00, F 19.00, Na 22.99, and Al 26.98.

For A4, the industrial clue and both mass percentages identify D as cryolite,
\(\mathrm{Na_3AlF_6}\), and hence Q as Al:

\[
M(\mathrm{Na_3AlF_6})=3(22.99)+26.98+6(19.00)=209.95,
\]

\[
w(\mathrm{Na})=\frac{3(22.99)}{209.95}(100\%)
=32.8506787\%,\qquad
w(\mathrm{Al})=\frac{26.98}{209.95}(100\%)
=12.8506787\%.
\]

Thus C is \(\mathrm{AlF_3}\), because
\(\mathrm{AlF_3+3NaF\rightarrow Na_3AlF_6}\). Its trihydrate gives

\[
\frac{3(18.016)}{83.98+3(18.016)}(100\%)
=39.1572724\%,
\]

which is the displayed 39.16%; therefore the precipitate is
\(\mathrm{AlF_3\cdot3H_2O}\).

For A5, the six-fold-symmetric E is hexamethylbenzene,
\(\mathrm{C_{12}H_{18}}\). Its hydrogen percentage is

\[
\frac{18(1.008)}{12(12.01)+18(1.008)}(100\%)=11.1817778\%,
\]

matching 11.18%. Oxidation of all six methyl groups gives mellitic acid,
\(\mathrm{C_6(COOH)_6}\). Dehydrating its six carboxyl groups three times
gives mellitic trianhydride, \(\mathrm{C_{12}O_9}\), for which

\[
\frac{9(16.00)}{12(12.01)+9(16.00)}(100\%)=49.9791753\%,
\]

matching 49.98%. It is a binary compound with a three-fold axis. The stone's
anion is consequently mellitate, \(\mathrm{C_6(COO)_6^{6-}}\). Charge balance
between this ion and \(\mathrm{Al^{3+}}\) gives the anhydrous salt
\(\mathrm{Al_2[C_6(COO)_6]}=\mathrm{Al_2C_{12}O_{12}}\).

## Thermogravimetric calculation

Let the stone be
\(\mathrm{Al_2C_{12}O_{12}\cdot xH_2O}\), with integral \(x\). The molar
masses are

\[
M(\mathrm{Al_2C_{12}O_{12}})=390.08,\qquad
M(\mathrm{H_2O})=18.016\ \mathrm{g\,mol^{-1}}.
\]

The first plateau is the anhydrous salt, so

\[
\frac{390.08}{390.08+18.016x}\approx\frac{5.75}{10.00}.
\]

Using the nominal displayed numbers gives the unrounded value

\[
x=\frac{390.08(10.00/5.75-1)}{18.016}
=16.0035524.
\]

More rigorously, each displayed mass has half-width 0.005 g. Hence the actual
dry/initial ratio lies in

\[
\frac{5.745}{10.005}=\frac{1149}{2001}
\leq \frac{m_{200}}{m_0}\leq
\frac{5.755}{9.995}=\frac{1151}{1999}.
\]

For \(x=16\), the theoretical ratio is
\(390.08/678.336=0.5750542504\), inside this interval. Every integer
\(x\leq15\) gives a ratio at least 0.5907438818, while every integer
\(x\geq17\) gives one at most 0.5601764625. Thus \(x=16\) is unique; no
arbitrary search bound is needed. A nominal 10.00 g sample is predicted to
leave 5.750542504 g at this stage.

On further heating in open air, the mellitate carbon is oxidised to volatile
\(\mathrm{CO_2}\), leaving the stable aluminium oxide:

\[
2\,\mathrm{Al_2C_{12}O_{12}}+15\,\mathrm{O_2}
\longrightarrow 2\,\mathrm{Al_2O_3}+24\,\mathrm{CO_2}.
\]

The predicted fraction of the original hydrate remaining as alumina is

\[
\frac{M(\mathrm{Al_2O_3})}
 {M(\mathrm{Al_2C_{12}O_{12}\cdot16H_2O})}
=\frac{101.96}{678.336}=0.1503089914.
\]

Thus a nominal 10.00 g sample leaves 1.503089914 g. The displayed final and
initial masses allow the ratio interval

\[
\frac{1.495}{10.005}=\frac{299}{2001}
\leq\frac{m_H}{m_0}\leq
\frac{1.505}{9.995}=\frac{301}{1999},
\]

and 0.1503089914 lies inside it, confirming \(H=\mathrm{Al_2O_3}\).

## Source grounding and scope

I used `TASK.json`, the SHA-matched images
`icho_2026_source/image/T1_page-3.png` and `T1_page-4.png`, and the original
`icho_2026_source/raw/theory_problem.pdf`. In the PDF I checked the printed
periodic table (G1-5), question pages Q1-3 and Q1-4, and the blank student
answer pages A1-3 through A1-5. The A1-5 sheet contains only the two requested
fields, “Stone” and “H”; it adds no unstated numerical condition.

The problem inputs used are the A4/A5 analytical data, the statement that the
stone is stoichiometric, the three displayed TGA masses, and the printed atomic
weights. The chemical laws used are charge neutrality, dehydration of hydrate
water at the first low-temperature plateau, and complete oxidation of the
organic anion in open air to carbon dioxide with alumina as the stable
aluminium-containing solid. These are the standard chemical interpretation of
the experiment; no official solution, marking scheme, or answer repository was
consulted. No source gap is needed for the stated result.

