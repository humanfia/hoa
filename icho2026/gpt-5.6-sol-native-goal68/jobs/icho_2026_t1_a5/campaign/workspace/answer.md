# IChO 2026 T1.5 — structures of E, F, and G

## Answer

- **E is hexamethylbenzene**, `C6(CH3)6` (`C12H18`): an aromatic six-membered carbon ring with one methyl group on every ring carbon.
- **F is mellitic acid** (benzene-1,2,3,4,5,6-hexacarboxylic acid), `C6(COOH)6` (`C12H6O12`): the same aromatic ring with one `–C(=O)OH` group on every ring carbon.
- **G is mellitic trianhydride**, `C12O9`: all six carboxyl carbon atoms remain attached to the aromatic ring, and three anhydride oxygens bridge the neighbouring carbonyl-carbon pairs `(1,2)`, `(3,4)`, and `(5,6)`.

An exact connectivity description of the drawings is obtained by numbering the aromatic ring atoms `r0,…,r5` cyclically:

| Substance | Substituents and bonds |
|---|---|
| E | `ri–CH3` for every `i = 0,…,5` |
| F | `ri–Ci(=Oi)–OHi` for every `i = 0,…,5` |
| G | `ri–Ci(=Oi)` for every `i = 0,…,5`, together with `C0–O–C1`, `C2–O–C3`, and `C4–O–C5` |

Thus G contains three five-membered cyclic-anhydride rings fused around the central aromatic ring. All three substances are neutral closed-shell structures. No stereocentre or configured E/Z bond is present.

## Derivation

The sixfold axis points to six identical substituents around a benzene ring. Acidic permanganate exhaustively oxidizes a benzylic alkyl group having benzylic hydrogen to `–CO2H`. In the corresponding unbounded C6-symmetric peralkylbenzene homologous family, chain length `k` gives

`C = 6 + 6k`, `H = 6(2k + 1)`.

Using the standard atomic masses adopted in the formalization (`C = 12.010`, `H = 1.008`), the `k = 1` member has

`100 × (18 × 1.008)/(12 × 12.010 + 18 × 1.008) = 11.1817778…%`,

which reports as 11.18%. The exact interval proof in Lean shows that no other natural `k` lies in the printed half-last-place interval `[11.175%, 11.185%]`. Hence E is the `k = 1` member, hexamethylbenzene.

Oxidation of each of its six methyl groups gives six carboxylic-acid groups, so

`C6(CH3)6  →  C6(COOH)6`,

identifying F as mellitic acid. This product retains a sixfold rotation axis and is the highly symmetrical acid described in the question.

`P2O5` is a dehydrating agent. Pairwise cyclodehydration of the six adjacent carboxyl groups removes three waters:

`C12H6O12 − 3 H2O = C12O9`.

Its calculated oxygen mass percentage is

`100 × (9 × 15.999)/(12 × 12.010 + 9 × 15.999) = 49.9776128…%`,

which reports as 49.98%. Three equivalent anhydride bridges give the stated threefold rotation axis. This identifies G as mellitic trianhydride.

## Source grounding and scope

The clues above are present on problem page Q1-3 in `T1_page-3.png` and on PDF page 8 of `theory_problem.pdf`; `T1_page-2.png` supplies the immediately preceding T1 context. PDF page 13 (student sheet A1-4) was also inspected: it provides three separate blank drawing boxes labelled E, F, and G, with no hidden structural template or stereochemical field.

The source does not give a closed universe of all conceivable molecular graphs or a molar mass for E or G. As is standard for this structure puzzle, uniqueness therefore uses the reaction-pattern interpretation: a C6-symmetric peralkylbenzene precursor, exhaustive benzylic permanganate oxidation, and complete adjacent-carboxyl dehydration by `P2O5`. The Lean uniqueness proof deliberately uses an **unbounded** homologous family (not an answer-selected finite candidate list), and separately verifies the complete atom/bond graphs, formulas, neutral closed-shell valences, and exact rotational automorphisms.

