# IChO 2026 T4-A2

The three nuclear equations are

\[
\text{(a)}\qquad {}^{11}_{5}\mathrm{B}+{}^{4}_{2}\mathrm{He}
\longrightarrow {}^{14}_{7}\mathrm{N}+{}^{1}_{0}\mathrm{n},
\]

\[
\text{(b)}\qquad \gamma+{}^{2}_{1}\mathrm{H}
\longrightarrow {}^{1}_{1}\mathrm{H}+{}^{1}_{0}\mathrm{n},
\]

\[
\text{(c)}\qquad {}^{9}_{4}\mathrm{Be}+{}^{4}_{2}\mathrm{He}
\longrightarrow {}^{12}_{6}\mathrm{C}+{}^{1}_{0}\mathrm{n}.
\]

Here \({}^{4}_{2}\mathrm{He}\) is an alpha particle and
\({}^{2}_{1}\mathrm{H}\) is deuterium (D).

## Derivation

Mass number \(A\) and atomic number \(Z\) must each be conserved. Treating
the gamma ray as \((A,Z)=(0,0)\) and the neutron as \((1,0)\):

- (a) gives \(11+4=A+1\) and \(5+2=Z\), hence
  \((A,Z)=(14,7)\), which is \({}^{14}\mathrm N\).
- (b) gives \(0+2=A+1\) and \(0+1=Z\), hence
  \((A,Z)=(1,1)\), which is \({}^{1}\mathrm H\).
- (c) gives \(9+4=A+1\) and \(4+2=Z\), hence
  \((A,Z)=(12,6)\), which is \({}^{12}\mathrm C\).

Thus each equation is balanced in both nucleon number and nuclear charge.

## Source grounding and formalization scope

`TASK.json` identifies T4-A2 and asks for the three equations. The matching
official question image, `T4_page-1.png` (PDF page 37), states that neutrons
are produced by (a) boron-11 plus alpha particles, (b) gamma rays interacting
with deuterium nuclei, and (c) beryllium-9 plus alpha particles. The original
PDF's blank answer sheet A4-1 (PDF page 40) has three separate response fields
labelled (a), (b), and (c), and adds no further condition.

The problem statement supplies the occurrence of these neutron-producing
channels. The derivation uses the standard nuclear-equation conservation laws
and the standard bookkeeping values for an alpha particle, a gamma ray, and a
neutron. In the Lean model, each requested net channel has one residual
nuclear species and one emitted neutron. The proofs establish both that the
displayed equations are balanced and that, within each such channel, the
residual species is uniquely forced by conservation. They do not purport to
derive reaction rates or energetics, which the question does not request.

No official solution, marking scheme, answer repository, or external answer
source was used.
