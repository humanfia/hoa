# IChO 2026 T4-A4

## Answer

The reaction referred to in 4.4 is the most probable channel from 4.3. The two maxima in the supplied fission-yield graph are at mass numbers (A=93) and (A=140). The same-group clue selects rubidium and caesium (both group 1), and their atomic numbers conserve charge:

\[
{}^{235}_{92}\mathrm U+{}^{1}_{0}\mathrm n
\longrightarrow
{}^{93}_{37}\mathrm{Rb}+{}^{140}_{55}\mathrm{Cs}
+3\,{}^{1}_{0}\mathrm n .
\]

Indeed, (37+55=92) and (93+140+3=236=235+1). Thus the two *bound* fission fragments contain

\[
93+140=233
\]

nucleons. The absorbed neutron is initially free and the three emitted neutrons are finally free. Their binding-energy contributions are all zero under the instruction to neglect the binding energy of free neutrons.

Using the standard positive binding-energy convention, energy released is final total binding energy minus initial total binding energy:

\[
\begin{aligned}
B_{\mathrm{initial}}
  &=235(7.59)+1(0)=1783.65\ \mathrm{MeV},\\
B_{\mathrm{final}}
  &=(93+140)(8.45)+3(0)=1968.85\ \mathrm{MeV},\\
\Delta E
  &=B_{\mathrm{final}}-B_{\mathrm{initial}}\\
  &=1968.85-1783.65\\
  &=185.20\ \mathrm{MeV}.
\end{aligned}
\]

The raw result is therefore (185.20\ \mathrm{MeV}). Under the target's three-significant-figure reporting rule, the requested entry is

\[
\boxed{\Delta E=185\ \mathrm{MeV}}.
\]

## Source grounding

- `TASK.json` identifies the current question as T4-A4, gives (BE(^{235}\mathrm U)=7.59\ \mathrm{MeV/nucleon}), (BE(\mathrm{fis.})=8.45\ \mathrm{MeV/nucleon}), says to neglect free-neutron binding energy, and requires a three-significant-figure final display while retaining the raw result.
- `icho_2026_source/image/T4_page-1.png` (PDF page 37, Q4-1) supplies the three-neutron reaction context and the fission-yield graph. Its two maxima give (A=93) and (A=140).
- `icho_2026_source/image/T4_page-2.png` and original PDF page 38 (Q4-2) contain 4.3 and 4.4 verbatim: the same-periodic-group condition, the two binding energies, and the free-neutron instruction.
- The original PDF's blank student sheets were also checked: page 40 (A4-1) provides the space for the 4.3 reaction, while page 41 (A4-2) asks for a single value `ΔE: ___ MeV` for 4.4. They impose no additional condition or alternative convention.
- The PDF and both supplied T4 images match the SHA-256 values recorded in `TASK.json`: `af51373f...8d3d60`, `f3b21152...f81ddcf`, and `60fade5d...2c94` respectively.

The only scientific law used beyond the printed data is standard nuclear binding-energy accounting, (Q=\sum B_{\mathrm{products}}-\sum B_{\mathrm{reactants}}), with binding energy taken as a positive quantity. Standard periodic-table facts identify Rb as (Z=37) and Cs as (Z=55), both in group 1. No final answer, marking scheme, or answer repository was used. There is no source gap affecting the requested result.

