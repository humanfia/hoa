# IChO 2026 T9-A5 — structure of L

Fill the seven primary-rim boxes clockwise, using the red unit numbering in
the question figure, as follows:

| unit | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| group attached to CD | **CH₂OH** | **CH₂OBn** | **CH₂OBn** | **CH₂OH** | **CH₂OBn** | **CH₂OBn** | **CH₂OBn** |
| lettering on the printed template | **CH₂OH** | **CH₂OBn** | **BnOCH₂** | **HOCH₂** | **BnOCH₂** | **CH₂OBn** | **CH₂OBn** |

The box outside the ring is **(OBn)₁₄**.

Equivalently, on the blank A9-3 template the placement is

```text
                         unit 2: CH₂OBn

             unit 1: CH₂OH          unit 3: BnOCH₂

          unit 7: CH₂OBn       L       unit 4: HOCH₂

             unit 6: CH₂OBn          unit 5: BnOCH₂

                         outside box: (OBn)₁₄
```

Here `Bn = C₆H₅CH₂–`. Thus `CH₂OBn` means
`CD–CH₂–O–CH₂–C₆H₅`, while each secondary `OBn` means
`CD–O–CH₂–C₆H₅`. The molecule is neutral and closed-shell. Its seven
α-D-glucopyranoside residues retain the stereochemistry already fixed by the
β-CD template; neither benzylation nor O-debenzylation changes a backbone
stereocentre.

The atom order is reversed in the three right-hand boxes only to keep `CH₂`
next to the template bond, exactly as on the supplied Q9-3 drawing; it does
not denote a different group.

## Derivation and source grounding

The Q9-3 problem page shows β-CD with seven primary `CH₂OH` groups and the
fourteen secondary hydroxyls abbreviated by `(OH)₁₄`. It then applies 30
equivalents each of NaH and BnCl followed by 2 equivalents of DIBAL-H. There
are 21 hydroxyl groups in total, so the first operation benzylates all seven
primary and all fourteen secondary oxygen atoms.

The paragraph immediately above that scheme supplies the selectivity needed
for the second operation: a protic group at unit 1 directs the **next**
primary reductive debenzylation to unit 4 when that position is available.
Because the fully benzylated β-CD is cyclically symmetric, the site of the
first cleavage may be labelled unit 1. The first DIBAL-H event therefore
gives `CH₂OH` at unit 1, and the directed second event gives `CH₂OH` at unit
4. The other five primary sites remain `CH₂OBn`; the fourteen secondary sites
remain `OBn`.

The blank A9-3 student answer sheet independently fixes the requested layout:
seven individual primary-rim boxes and one outside box carrying the subscript
14. The Q9-2 page fixes the α-D-glucopyranoside backbone represented by that
template. No stereogenic carbon is altered in the displayed steps.

As a consistency check on the fully expanded structure, β-CD has formula
`C₄₂H₇₀O₃₅`. Replacing nineteen hydroxyl hydrogens by nineteen benzyl groups
adds `19(C₇H₆)`, so `L` has formula **C₁₇₅H₁₈₄O₃₅**. This formula check is
not used to choose the box pattern.

Sources inspected (problem-only material):

- `icho_2026_source/image/T9_page-3.png` — reaction scheme, directing rule,
  unit numbering, and the requested question.
- `icho_2026_source/image/T9_page-2.png` — β-CD/α-D-glucopyranoside template
  context.
- `icho_2026_source/raw/theory_problem.pdf`, PDF pages 86 and 91 — the
  original Q9-3 page and blank A9-3 student answer sheet.

No official solution, marking scheme, grading report, answer repository, or
external solver was used.
