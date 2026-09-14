# IChO 2026, T9-A5 — Structure of L

## Requested output (TASK.json `requested_outputs.structure_l`)

Draw the structure of **L** on the β-CD template and **fill in all the boxes**:
the complete substituent state of every site of the β-CD template for
compound **L** — the 7 primary (C6-side) boxes plus the secondary-face box
showing all 14 secondary (2-OH, 3-OH) positions.

## Answer (what goes in the boxes)

**L is 6¹,6⁴-di-O-debenzylated heptakis(2,3,6-tri-O-benzyl)-β-cyclodextrin:
units 1 and 4 carry a free primary CH₂OH, units 2, 3, 5, 6, 7 carry CH₂OBn,
and all 14 secondary positions remain OBn.**

Template layout (unit numbering 1–7 exactly as printed in red on the β-CD
starting material of the 9.5 scheme, page Q9-3):

| Template site | Box content for L |
|---|---|
| Unit 1 — C6 position | **CH₂OH** (free primary hydroxy) |
| Unit 2 — C6 position | **CH₂OBn** |
| Unit 3 — C6 position | **CH₂OBn** ("BnOH₂C" on the right-hand side) |
| Unit 4 — C6 position | **CH₂OH** (written "HOH₂C"; free primary hydroxy) |
| Unit 5 — C6 position | **CH₂OBn** ("BnOH₂C") |
| Unit 6 — C6 position | **CH₂OBn** |
| Unit 7 — C6 position | **CH₂OBn** |
| Macrocycle (secondary) face | **(OBn)₁₄** |

## Derivation (problem-internal reasoning)

The β-CD starting material of the 9.5 scheme has all 7 primary boxes labelled
CH₂OH and the secondary-face box labelled (OH)₁₄ — 7 primary + 14 secondary
= 21 free hydroxy groups (consistent with 9.1: 7 × 180.16 − 7 × 18.02 =
1134.98… g mol⁻¹, C₄₂H₇₀O₃₅).

1. **NaH (30 equiv.), BnCl (30 equiv.).** With "equiv." per mole of β-CD,
   30 ≥ 21, so base and benzyl chloride exceed *every* free OH (primary and
   secondary). Williamson etherification exhaustively converts all 21 OH
   groups to OBn ethers: a **perbenzylated β-CD** (C₁₈₉H₁₉₆O₃₅) after step 1.

2. **DIBAL-H (2 equiv.)** reductively debenzylates primary O–Bn groups
   (Cleve/Pearce–Sinaÿ chemistry; DIBAL-H shown in the legend).  The preamble
   on the same page supplies the regiochemistry (Sinay *et al.*, 2000):
   a single protic group at unit 1 directs the **next** reductive
   debenzylation of a **primary** OH to **unit 4** (or to unit 3 only if
   unit 4 is not available).  Reading the two equivalents sequentially:
   * First DIBAL-H equivalent: the perbenzylated ring is fully C₇-symmetric
     (no directing protic group yet), so debenzylation of a primary benzyl
     ether gives a free CH₂OH at a first unit — **conventionally unit 1**,
     the anchor used throughout the preamble and answer sheet so that the
     dimer becomes a definite set of constitutional linkage isomers (9.6).
   * Second DIBAL-H equivalent: the free primary OH now at unit 1 *is* the
     single protic group of the Sinay rule.  Unit 4 (1,4-relationship
     around the heptagon) is available, so the rule sends the next primary
     debenzylation to **unit 4** — provably *not* unit 3 (fallback premise
     absent) and *not* unit 6 (both rule directions confine the choice to
     {3, 4}; see `sinayRule_unit6_not_chosen`).
   * With only 2 equiv. available, no further primary cleavage occurs; the
     remaining five CH₂OBn groups and all 14 secondary OBn groups are
     untouched (trusted general law: DIBAL-H cleaves the primary benzyl
     ethers selectively, secondary benzyl ethers persist).

3. **Consequence:** L = 6¹-OH, 6⁴-OH, otherwise per-O-benzylated β-CD:
   benzyl-group count 5 (primary) + 14 (secondary) = 19; free-OH count 2
   (both primary, at units 1 and 4); molecular formula
   C₄₂H₇₀O₃₅ + 19 × C₇H₆ = **C₁₇₅H₁₈₄O₃₅**.

**Why this must be the answer — the printed dimer.** The dimer drawn below L
on page Q9-3 shows, *per ring*, exactly one free CH₂OH, five CH₂OBn, and one
primary oxygen tied into the –CH₂O(CH₂)₄OCH₂– tether, plus (OBn)₁₄ on the
face.  That tether is installed by t-BuOK / allyl bromide
(CH₂=CH–CH₂–Br, as drawn) → Grubbs I (olefin metathesis joining the two
allyl ethers, CH₂=CH₂ evolved) → H₂/PtO₂ (hydrogenation to the saturated
(CH₂)₄ bridge).  Only a **free primary OH** can be allylated by t-BuOK /
allyl bromide, so the tethered CH₂O– of the dimer must come from a free
primary OH of L; the leftover printed CH₂OH is the second free one.
Because the allylation selects **one** of L's two equivalent-but-labelled
sites (then topological metathesis heads/tails), the Sinay route delivers
the mixture of constitutional linkage isomers (4 and 6) counted in 9.6.

## Source grounding

- β-CD template, 21 OH, secondary box (OH)₁₄: page Q9-1 figure and the 9.5
  scheme starting material (page Q9-3).
- NaH (30 equiv.), BnCl (30 equiv.), DIBAL-H (2 equiv.): 9.5 arrow, Q9-3.
- DIBAL-H, Grubbs I, Bn, allyl bromide drawings; "equiv. = equivalent":
  legends on Q9-2/Q9-3.
- Sinay directing rule, exactly as quoted: preamble of Q9-3 ("…directs the
  *next* reductive debenzylation of a *primary* OH group to unit 4 … or to
  unit 3 if the unit 4 position is not available").
- Dimer connectivity (one free CH₂OH, five CH₂OBn, one tethered CH₂O–,
  (OBn)₁₄ per ring): dimer figure, Q9-3.
- No official answer, marking scheme, or competition-answer repository was
  consulted; ordinary general chemistry (Williamson etherification,
  DIBAL-H reductive debenzylation, allylation-metathesis-hydrogenation) is
  used as trusted general law only.

## Companion formalisation

`IChO2026Problems/problem_icho_2026_t9_a5.lean` encodes the β-CD template
(7 enumerated primary boxes, 7 secondary pairs, the printed face box), an
explicit atom/bond molecule language (glucose residue C₆H₁₀O₅, β-CD
C₄₂H₇₀O₃₅ as 7 residues, substituent fragments as real atoms), the Sinay
rule in both directions, the 9.5 stoichiometry, and proves:

- formula reconstructions (β-CD C₄₂H₇₀O₃₅; core C₄₂H₄₉O₃₅; per-benzylated
  intermediate C₁₈₉H₁₉₆O₃₅);
- 30 ≥ 21 forces exhaustive benzylation; DIBAL-H is sub-stoichiometric
  (2 < 7);
- the Sinay rule with unit 4 available forces the second cleavage to unit 4
  and never to unit 6 or unit 3;
- the forced-L theorem: the unique well-formed template consistent with the
  Sinay rule and the dimer downstream is `lTemplate` — primary boxes
  `[H, Bn, Bn, H, Bn, Bn, Bn]` (units 1 → 7), all secondary pairs
  `(Bn, Bn)`, face box `(Bn, 14)`;
- L's molecule `lMolecule` has formula **C₁₇₅H₁₈₄O₃₅**, exactly 2 free
  primary OH groups (at units 1 and 4), 19 benzyl groups;
- L is a valid precursor of the printed dimer: the dimer's box counts and
  secondary-face labels are reproduced site-wise.
