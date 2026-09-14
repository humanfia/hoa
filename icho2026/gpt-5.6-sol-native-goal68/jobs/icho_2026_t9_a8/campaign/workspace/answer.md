# IChO 2026 T9.8 — structures O–S

Number the α-CD units exactly as on the answer templates: unit 1 is at the top
and 2–6 proceed clockwise. In every structure below, the α-CD skeleton remains
the cyclic α-(1→4)-linked ring of six α-D-glucopyranoside residues, and the
twelve secondary groups remain **(OBn)₁₂**. Here `Bn = CH₂C₆H₅` and
`Boc = C(=O)OC(CH₃)₃`.

## Entries for the six primary-rim boxes

| product | unit 1 | unit 2 | unit 3 | unit 4 | unit 5 | unit 6 |
|---|---|---|---|---|---|---|
| **O** | CH=CH₂ | CH₂OBn | CH₂OBn | CH₂OBn | CH₂OBn | CH₂OBn |
| **P** | CH=CH₂ | CH₂N₃ | CH₂OBn | CH₂OBn | CH₂OBn | CH₂OBn |
| **Q** | CH=CH₂ | CH₂NH– (bridge) | CH₂OBn | CH₂OBn | CH₂O– (bridge) | CH₂OBn |
| **R** | CH=CH₂ | CH₂N(Boc)– (bridge) | CH₂OBn | CH₂OBn | CH₂O– (bridge) | CH₂N₃ |
| **S** | CH=CH₂ | CH₂N(Bn)– (bridge) | CH₂OBn | CH₂OBn | CH₂O– (bridge) | CH₂N₃ |

For Q–S, join the unit-2 and unit-5 entries outside the boxes as

```text
(unit 2)–CH₂–N(R)–CH₂–C(=CH₂)–CH₂–O–CH₂–(unit 5)
```

with `R = H` in Q, `R = Boc` in R, and `R = Bn` in S. Thus the bridge is an
N/O methallyl bridge; the double bond is the exocyclic `C=CH₂` bond shown
above. A charge-explicit resonance form of each azide is
`–CH₂–N=N⁺=N⁻`; all other atoms are neutral and none of O–S contains a
radical.

## Derivation

1. N has CH₂OH only at unit 1. Oxalyl chloride/DMSO oxidizes that primary
   alcohol to the aldehyde, and methylene Wittig olefination changes it to
   CH=CH₂. This gives **O**.
2. The unit-1 alkene directs the one-equivalent DIBAL-H debenzylation to its
   ortho unit. The problem fixes a 1,2 choice as clockwise, hence unit 2 becomes
   CH₂OH. Mesylation and azide displacement then give unit-2 CH₂N₃, producing
   **P**.
3. With two equivalents of DIBAL-H, the azide at unit 2 is reduced to CH₂NH₂;
   that new protic group directs the other event to the diametrically opposite
   unit 5, whose CH₂OBn becomes CH₂OH. NaH and
   ClCH₂–C(=CH₂)–CH₂Cl connect those two groups. The amine loses one H and the
   alcohol loses its O–H proton, yielding the unit-2-N/unit-5-O bridge in
   **Q**.
4. In Q the protic secondary NH has the stronger directing effect. Its preferred
   opposite site, unit 5, is already the ether end of the bridge, so the stated
   1,3 fallback applies. Two units counterclockwise from unit 2 is unit 6;
   DIBAL-H therefore unveils unit-6 CH₂OH. Boc₂O protects the bridge nitrogen,
   and MsCl/NaN₃ converts unit-6 CH₂OH to CH₂N₃, giving **R**.
5. Trifluoroacetic acid removes Boc, and NaH/BnI benzylates the regenerated
   secondary NH. No primary-rim position changes in this last operation, so
   **S** differs from R only by `N(Boc) → N(Bn)` on the bridge.

No new stereocentre is formed by these primary-rim operations. The six
α-D-glucopyranoside configurations and α-(1→4) linkages shown by the α-CD
template are therefore retained throughout.

## Source grounding

- [TASK.json](TASK.json) identifies the requested outputs as the complete
  structures O–S and supplies the clockwise 1,2, counterclockwise 1,3, and
  protic-over-alkene directing rules.
- [T9_page-4.png](icho_2026_source/image/T9_page-4.png) supplies compound N,
  every reagent in the N→O→P→Q→R→S route, and the printed unit numbering.
- [T9_page-3.png](icho_2026_source/image/T9_page-3.png) supplies the preceding
  problem statement that a protic NH/OH directs the next DIBAL-H event to the
  opposite unit, with the 1,3 position as fallback when that site is not
  available.
- [theory_problem.pdf](icho_2026_source/raw/theory_problem.pdf), PDF pages 87,
  92, and 93, confirms the original question and the blank O–S student
  templates. The blank templates require all six primary boxes plus the common
  `(OBn)₁₂` field for each product.

The remaining chemical interpretations are standard transformations read
directly from the printed reagents: Swern oxidation, Wittig methylenation,
DIBAL-H azide reduction/debenzylation, mesylate-to-azide displacement, Boc
protection/deprotection, and N-benzylation. No official solution, marking
scheme, answer repository, or prior answer was used.
