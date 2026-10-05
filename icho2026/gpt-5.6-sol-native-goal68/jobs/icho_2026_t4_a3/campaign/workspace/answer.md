# IChO 2026 T4-A3

The most common fission channel selected by the graph and the same-group clue is

\[
{}^{235}_{92}\mathrm{U}+{}^{1}_{0}\mathrm n
\longrightarrow
{}^{93}_{37}\mathrm{Rb}+{}^{140}_{55}\mathrm{Cs}
+3\,{}^{1}_{0}\mathrm n.
\]

The two maxima of the supplied fission-product yield graph occur at the integer
mass numbers $A=93$ and $A=140$. The problem text states that three neutrons
are released. Hence mass number is conserved:

\[
235+1=236=93+140+3(1).
\]

The periodic table supplied in the problem PDF puts Rb and Cs in the same
vertical column, group 1, and gives their atomic numbers as 37 and 55. Nuclear
charge is therefore also conserved:

\[
92+0=37+55+3(0).
\]

## Source grounding

- `TASK.json` identifies the sole requested output as the exact symbolic
  fission equation and reproduces the statement of T4-A3.
- `icho_2026_source/image/T4_page-1.png` (PDF page 37, Q4-1) supplies the
  mass-yield graph and states the three-neutron reaction frame.
- `icho_2026_source/image/T4_page-2.png` (PDF page 38, Q4-2) contains T4-A3 and
  its requirement that the two product elements be in the same periodic-table
  group.
- `icho_2026_source/raw/theory_problem.pdf` was inspected directly: page 5 is
  the supplied periodic table (Rb: $Z=37$, Cs: $Z=55$, both group 1), pages
  37–38 contain the question and graph, and page 40 is the blank A4-1 student
  answer sheet with a free-form box for 4.3.

No official solution, marking scheme, answer repository, or historical answer
was used. The graph readings and stated neutron count are represented in Lean
as source data; periodic-table identities are represented separately. The Lean
proof then checks both conservation laws, the two peak masses, the neutron
multiplicity, and the common group.
