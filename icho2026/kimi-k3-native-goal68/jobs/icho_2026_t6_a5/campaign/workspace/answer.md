# IChO 2026, Theory Problem T6 ("Carbon Nanorings"), Question 6.5

**Question (verbatim, page Q6-3 of `theory_problem.pdf` / image `T6_page-3.png`):**
"Draw the **structures** of F–L." (24.0 pt)

All structural information below is taken from the printed scheme on page Q6-3:
the drawn starting material (a p-quinol), the drawn aryllithium reagents over the
arrows, the printed molecular formulas of **H** (C₃₆H₄₇BrO₃Si₂) and **L**
(C₅₄H₈₀O₄Si₄), the printed legend structures (TBSCl, TESCl, imidazole, COD,
2,2′-bipyridine), the statement that "PhI(OAc)₂ acts as a two electron oxidant",
and the drawn product **[5]CPP** (a macrocycle of five para-linked benzenes).

---

## Overview of the route

The scheme is a five-ring cycloparaphenylene construction:

> **p-quinol (drawn)** → **F** (aryl-Li addition) → **G** (TES-protection, 2×) →
> **H** (LiOH, selective aryl silyl-ether cleavage) → **I** (PhI(OAc)₂ oxidative
> dearomatization to a new p-quinol) → **J** (aryl-Li addition) →
> **K** (TES-protection, 2×) → **L** (Ni(0)/bpy Yamamoto macrocyclization) →
> **[5]CPP** (TBAF deprotection, SnCl₂ reductive aromatization).

The five six-membered ring units are (the notation also used in the Lean file):
**R** = the cyclohexadienone/diol core of the starting quinol; **W** = the
4-bromophenyl substituent of the starting material; **A**–**B** = the
TBSO-capped biphenyl arm installed in step F (A ipso to R, B remote);
**P** = the 4-bromophenyl group installed in step J.

---

## Structure of F — **C₃₀H₃₃BrO₃Si** (M = 549)

The drawn starting material is a *para*-quinol:
4-(4-bromophenyl)-4-hydroxycyclohexa-2,5-dien-1-one (C=O at the top, the sp³
C4 bearing OH and the 4-bromophenyl ring W). The reagent "2." drawn over the
arrow is 4-lithio-4′-[(tert-butyldimethylsilyl)oxy]biphenyl (Li para to the
biphenyl junction).

- NaH deprotonates the quinol O–H; the aryllithium then adds to the **ketone
  C=O** of the dienone (nucleophilic 1,2-addition of ArLi to a ketone; NaH
  simply removes the acidic quinol proton).

**F** is therefore a 1,4-dihydroxycyclohexa-2,5-diene:

- ring R: cyclohexa-2,5-diene core; **C1 (former C=O) is sp³** and now bears
  **OH** plus the biphenyl arm through **ring A**; **C4 is sp³** bearing **OH**
  and ring W; the two C=C bonds 2–3 and 5–6 remain.
- ring W: untouched 4-bromophenyl (ipso at the R-link, Br *para*).
- ring A: benzene linking R to ring B (both links *para*).
- ring B: benzene bearing **OTBS** *para* to the A-link.

Molecular formula: C₁₂H₉BrO₂ + C₁₈H₂₃LiOSi + H (workup) − Li = **C₃₀H₃₃BrO₃Si**.
The two new quaternary carbinol centres are constitutionally fixed but the
problem prints no stereochemical template, so none is specified.

## Structure of G — **C₄₂H₆₁BrO₃Si₃** (M = 777)

TESCl (2 equiv.) / imidazole: silylation of the **two tertiary OH groups** of F
as O–SiEt₃ (the reason the arrow labels 2 equivalents).

- ring R unchanged constitutionally (now 1,4-bis(triethylsilyloxy)-cyclohexa-2,5-diene);
- W, A unchanged; B drawn with the aryl silyl ether as **OTES** (TBS and TES are
  both C₆H₁₅Si, so the formula is unaffected either way; what matters — and is
  fixed by the printed formula of H — is which silicon-bearing groups survive
  the LiOH step).

G = F + 2(C₆H₁₄Si): **C₄₂H₆₁BrO₃Si₃**.

## Structure of H — **C₃₆H₄₇BrO₃Si₂** (M = 663) *(formula printed in the problem)*

LiOH: selective cleavage of the **aryl** silyl ether only. The labile
aryl–O–Si bond is hydrolysed, liberating the **free phenol** on ring B, while
the two robust *tertiary alkyl* silyl ethers on ring R survive. The printed
formula fixes exactly this selectivity: removal of *one* C₆H₁₄Si unit from G.

- ring B: now a **phenol** (OH *para* to the A-link);
- ring R: retains its two OTES groups; W unchanged (still 4-bromophenyl).

H = G − C₆H₁₄Si = **C₃₆H₄₇BrO₃Si₂**, matching the printed formula.

## Structure of I — **C₃₆H₄₇BrO₄Si₂** (M = 679)

PhI(OAc)₂ / H₂O: oxidative **dearomatization** of the phenol ring B to a
*para*-quinol. The hypervalent iodine(III) reagent is stated to be a
two-electron oxidant; water traps the para-position (the carbon already bearing
the biphenyl junction), exactly the same transformation that produced the
drawn starting quinol of the route.

- ring B becomes a **cyclohexa-2,5-dien-1-one**: C=O at the para carbon of the
  former phenol (B3); **sp³ quinol junction at B0** bearing the **new OH** (from
  H₂O) and the link to A; B retains double bonds B1–B2 and B4–B5;
- rings R, W, A unchanged (R still 1,4-bis(OTES); W still 4-bromophenyl).

I = H + O (the phenolic O–H is replaced by the quinol O–H, net +O):
**C₃₆H₄₇BrO₄Si₂**.

## Structure of J — **C₄₂H₅₂Br₂O₄Si₂** (M = 836)

1. NaH, 2. 4-lithiobromobenzene (drawn: Li and Br para on one ring): exact
analogy with step F. NaH deprotonates the quinol O–H; the aryllithium adds to
the **dienone C=O of ring B**.

- ring B becomes a 1,4-dihydroxycyclohexa-2,5-diene: **B0** bears OH and ring A;
  **B3** bears OH and the new 4-bromophenyl group **P**;
- rings R, W, A unchanged.

J = I + C₆H₄BrLi + H − Li = **C₄₂H₅₂Br₂O₄Si₂**.

## Structure of K — **C₅₄H₈₀Br₂O₄Si₄** (M = 1064)

TESCl (2 equiv.) / imidazole: silyl-capping of the **two B-ring OH groups**.
K = J + 2(C₆H₁₄Si): the molecule now carries **four OTES groups, two aryl
bromides (on W and P), and two 1,4-bis(silyloxy)-cyclohexa-2,5-diene rings
(R and B)**, with W, A, P aromatic benzenes.

**C₅₄H₈₀Br₂O₄Si₄**.

## Structure of L — **C₅₄H₈₀O₄Si₄** (M = 904) *(formula printed in the problem)*

Ni(COD)₂ (2 equiv.) / 2,2′-bipyridine (2 equiv.): Ni(0)-mediated **Yamamoto
aryl–aryl homocoupling**. The complex inserts into both C−Br bonds; the
geometrically constrained chain closes as a **macrocycle** through one **new
biaryl σ-bond between rings W and P** (between the two brominated positions).
Both bromines are expelled.

- the five ring units R, A, B, P, W are now connected in one closed belt of
  five *para*-linked six-membered rings (five biaryl links in total);
- R and B remain 1,4-bis(OTES)-cyclohexa-2,5-dienes; W, A, P are benzenes.

L = K − 2Br = **C₅₄H₈₀O₄Si₄**, matching the printed formula.

## Final step (drawn in the problem, as a consistency check)

1. *n*-Bu₄NF (4 equiv.) removes all four OTES groups (→ the macrocyclic
tetraol); 2. SnCl₂ (excess) reductively re-aromatizes rings R and B, producing
the drawn **[5]CPP**: a macrocycle of five para-linked benzene rings,
**C₃₀H₂₀**, five aromatic 6π systems. This last transformation is drawn and
boxed in the problem, so it serves as the endpoint consistency check of the
whole sequence.

---

## Source-grounding summary

| Structure | Basis in the problem | Formula (proved in Lean) |
|---|---|---|
| F | aryllithium reagent drawn over arrow + drawn starting quinol | C₃₀H₃₃BrO₃Si |
| G | TESCl (2 equiv.), imidazole | C₄₂H₆₁BrO₃Si₃ |
| H | LiOH; **printed C₃₆H₄₇BrO₃Si₂** | C₃₆H₄₇BrO₃Si₂ ✓ |
| I | PhI(OAc)₂ stated 2e⁻ oxidant, H₂O; analogy to drawn quinol | C₃₆H₄₇BrO₄Si₂ |
| J | 4-Li-bromobenzene drawn over arrow; NaH | C₄₂H₅₂Br₂O₄Si₂ |
| K | TESCl (2 equiv.), imidazole | C₅₄H₈₀Br₂O₄Si₄ |
| L | Ni(COD)₂/bpy; **printed C₅₄H₈₀O₄Si₄** | C₅₄H₈₀O₄Si₄ ✓ |

No stereochemistry is requested or printed for F–L; the encodings record the
relevant centres as explicit sp³ quaternary carbinols.

The corresponding Lean 4 file
`IChO2026Problems/problem_icho_2026_t6_a5.lean` encodes every molecule as an
explicit molecular graph (ring units, sp³ carbons, hydrogen counts,
substituents, Kekulé double bonds, biaryl links), proves every formula above
by `decide`, proves the Hückel aromatic ring counts (3, 3, 3, 2, 3, 3, 3 for
F–L respectively; 5 aromatic 6π systems in [5]CPP, 0 antiaromatic systems
throughout), and proves the eight stoichiometric derivation identities
(F = SM + reagent + H − Li, G = F + 2 TES caps, …, L = K − 2Br, and the
TBAF/SnCl₂ endpoint), so the structures are *derived from* the problem inputs
rather than assumed. Compile: `lake env lean IChO2026Problems/problem_icho_2026_t6_a5.lean`;
the axiom audit (`#print axioms`) reports only `propext` and `Quot.sound` for
every final theorem.
