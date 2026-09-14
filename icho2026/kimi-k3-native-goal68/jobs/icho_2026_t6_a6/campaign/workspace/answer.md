# IChO 2026 T6.6 (icho_2026_t6_a6): structures of M–R

## Source grounding

The subquestion is the last scheme on page Q6-4 of the official theory paper
(`theory_problem.pdf`, page image `T6_page-4.png`), titled by the task schema
"T6-A6: Draw the structures of M–R."  Everything below is read off that scheme
and the accompanying P6/nanobelt figure; no external solution material was
used.

Scheme as printed (Q6-4):

```
toluene ──(t-BuCl (2 equiv.), AlCl₃)──▶ M
M ──(1) NBS, (BzO)₂; 2) HMTA; 3) HCl, H₂O)──▶ N
N ──(1) dipyrromethane ▸shown◂, CF₃COOH; 2) DDQ; 3) Zn(OAc)₂)──▶ O
O ──(NBS)──▶ Q
Q ──(1) Pd⁰, PPh₃, CuI, (C₆H₁₃)₃Si–C≡CH; 2) n-Bu₄NF)──▶ R
R + template (drawn: hexakis[4-(pyridin-4-yl)phenyl]benzene)
      ──(PdCl₂, PPh₃, CuI)──▶ (nanobelt: six P6 around the template)
```

Hints printed with the scheme: *"M is the thermodynamic product and has four
types of protons"*; the porphyrin building block is drawn as **P6** with two
*trans* meso **Ar** groups and two *trans* β,β′-ethynyl groups; the final
belt shows these P6 units linked by alternating butadiyne (–C≡C–C≡C–) edges
with each Zn additionally coordinated to one pyridine nitrogen of the
six-armed template.

## Answers

**M = 1-methyl-4-tert-butylbenzene (p-tert-butyltoluene).**
Friedel–Crafts alkylation of toluene with t-BuCl/AlCl₃ installs the tert-butyl
group ortho/para to the methyl; the thermodynamic product is the *para* isomer
(steric decompression), and this is exactly the isomer having four proton
environments (CH₃Ar, C(CH₃)₃, and two aromatic types in the AA'BB' pattern), as
the hint demands.  Formula C₁₁H₁₆.

**N = 4-tert-butylbenzaldehyde.**
NBS with benzoyl peroxide initiator selectively brominates the *benzylic*
methyl of M (Wohl–Ziegler) to ArCH₂Br; hexamethylenetetramine (HMTA) after
acidic aqueous work-up performs the Sommelet oxidation ArCH₂Br → ArCHO.  The
aldehyde group carries one aldehydic proton.  Formula C₁₁H₁₄O.

**O = 5,15-bis(4-tert-butylphenyl)porphyrinato zinc(II).**
Two equivalents of the aldehyde N and one equivalent of dipyrromethane
condense under BF₃/TFA catalysis (MacDonald "2+2" porphyrin synthesis);
DDQ oxidises the porphyrinogen to the porphyrin, and Zn(OAc)₂ metallates it.
The two aryl groups end up at the two *trans* meso positions (5 and 15),
the meso carbons 10 and 20 keep their hydrogens, and Zn²⁺ sits in the N₄
cavity coordinated by all four pyrrole nitrogens.  Ar = 4-tert-butylphenyl.

**Q = 2,3,17,18-tetrabromo-O.**
Treatment of the Zn porphyrin O with NBS brominates the four free β-pyrrole
positions — the two rings between the two Ar-bearing meso edges.  These are
the positions used for the later cross-couplings, confirmed by the P6/belt
figure where the butadiyne links leave from exactly those β-carbons.  The two
other pyrrole rings remain unbrominated.

**R = 3,17-diethynyl-2,18-dibromo porphyrinato Zn(II).**
Pd⁰/PPh₃/CuI with trihexylsilyl-acetylene, (C₆H₁₃)₃Si–C≡CH, performs a double
Sonogashira coupling, replacing *two* of the four bromines (the pair lying on
the oligomer axis drawn for P6) with THS-protected ethynyls; step 2
(tetra-n-butylammonium fluoride) then removes the THS (=TIPS-analogue
trihexylsilyl) groups to expose *terminal* alkynes.  The remaining two
β-bromines survive and are the sites consumed in the final template-directed
ring-closing Sonogashira that stitches the butadiyne edges of the belt.
Hence R still contains two Br atoms and two terminal C≡CH groups and no
silicon.

**Template** (context for the final step, also drawn in the scheme):
hexakis[4-(pyridin-4-yl)phenyl]benzene — a central benzene with six
4-(pyridin-4-yl)phenyl arms, one pyridine N per arm (para to the biaryl
bond), providing the six Zn-binding sites shown in the belt structure.

## Formal Lean content

`IChO2026Problems/problem_icho_2026_t6_a6.lean` encodes each of M, N, O, Q, R
and the template as an explicit finite structural model (atoms, labelled bond
orders, metal coordination list) and proves the full structural answer set by
`decide` over those finite models:

- `icho_2026_t6_a6_structures` — conjunction of the element counts, key
  connectivities and proton-count invariants of all six requested outputs.
- Axioms used: only `propext` (Lean's standard logical axiom); no `sorry`,
  no custom axiom.

Compilation: `lake env lean IChO2026Problems/problem_icho_2026_t6_a6.lean`
succeeds (see `verification.md`).
