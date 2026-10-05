# IChO 2026, Theory Problem T5 (Cardiolipins), Subquestion 5.4

**Question (T5_page-3.png, printed page 3 of the exam):**

> "100 g of RCOOH reacts with 181.0 g of iodine. RCOOH also reacts in similar
> way with X and forms an adduct with an iodine mass fraction of 36.57 %.
> **5.4 Determine the molecular formula of X. Support your answer with
> calculations.**"

## Answer

**X = IBr — iodine monobromide.**

## Full solution

**Step 1 — How many C=C bonds does RCOOH have?**

Earlier in the problem it is stated: *"During reductive ozonolysis, RCOOH
forms three different organic products in equimolar amounts."* Reductive
ozonolysis cleaves every C=C double bond of an acyclic chain into two
carbonyl fragments, so a chain with k C=C bonds gives exactly k + 1 organic
products. Three products therefore means **k = 2 C=C bonds**.

**Step 2 — Molar mass of RCOOH from the iodine datum.**

Iodine adds across C=C double bonds in the classical iodine-value reaction,
one I₂ molecule per π-bond. With k = 2:

n(RCOOH) = 100/M mol consume n(I₂) = 2·(100/M) mol of mass

  m(I₂) = (100/M) · 2 · (2 · 126.904) g = 181.0 g

Solving:

  M(RCOOH) = 100 · 2 · 2 · 126.904 / 181.0 = 50761.6/181.0
           = **280.451 g/mol** (exactly 253808/905).

**Step 3 — Molecular formula of RCOOH.**

A monocarboxylic fatty acid with c hydrocarbon carbons and k double bonds is
C\_{c+1}H\_{2c+2−2k}O₂, of molar mass

  M(c, 2) = (c+1)·12.011 + (2c−2)·1.008 + 2·15.999
          = 14.027·c + 42.000  g/mol.

Setting M(c, 2) = 280.451 gives c = 17.0009, i.e. **c = 17**: the lattice
step is 14.027 g/mol, hundreds of times wider than the ±0.05 g measurement
window, so the integer solution is unique. RCOOH = **C₁₈H₃₂O₂**
(M = 280.452 g/mol, linoleic acid; the check 100·2·2·126.904/280.452 =
180.999 g lands inside 181.0 ± 0.05 g). This is exactly the fatty acid found
predominantly in mammalian heart cardiolipins, and its two internal,
non-symmetrically placed double bonds (Δ9, Δ12) are consistent with "three
*different*" ozonolysis products.

**Step 4 — The equation for X.**

"Reacts **in similar way**" means X also adds one molecule per C=C bond, two
X per RCOOH. An iodine-containing reagent that adds across C=C is an
interhalogen X = I–R′ (iodine plus a residual group R′ of mass r). The
adduct C₁₈H₃₂O₂·2X has molar mass M + 2·(Ar(I) + r) and contains exactly two
iodine atoms, so

  w(I) = 2 · 126.904 / (280.451 + 2·(126.904 + r)) = 36.57 %.

Solving for r:

  r = 126.904 · (100/36.57 − 1) − 280.451/2
    = 126.904 · 1.734208 − 140.225
    = **79.887 g/mol** (exactly 6609842429/82739625).

**Step 5 — Which element is R′?**

Bromine's standard atomic mass is **79.904 g/mol — 0.017 g/mol from the
required value**, i.e. inside the measurement window. Every other halogen
fails by hundreds of measurement half-quanta (one half-quantum = 0.005 % on
the printed 36.57 %):

| X (as I–R′) | predicted w(I) | distance from 36.57 % |
|---|---|---|
| IF | 44.35 % | +1556 half-quanta |
| ICl | 41.94 % | +1074 half-quanta |
| **IBr** | **36.568 %** | **−0.35 half-quanta** |
| I₂ (R′ = I) | 32.21 % | −872 half-quanta |
| IAt | 26.60 % | −1994 half-quanta |

(I₂ is additionally excluded on chemical grounds: it is the reagent of the
*preceding* sentence, while X is introduced as a distinct reactant.)

Higher-valence iodine halides IR′ᵥ share the same equation with the adduct
mass M + 2·(Ar(I) + v·r), so the required residual would be 79.887/v:
v = 2 → 39.94, v = 3 → 26.63, v = 5 → 15.98 g/mol — none of these matches
any halogen (Cl 35.45, F 19.00). Hence R′ is monovalent bromine.

**Step 6 — Robustness to the printed precision.**

Even sliding both measured quantities to the far ends of their ±½-last-digit
windows (181.0 ± 0.05 g, 36.57 ± 0.005 %) keeps the required residual
between 79.33 and 80.45 g/mol; bromine (79.904) is the only halogen whose
standard mass lies in that interval.

**Conclusion: the molecular formula of X is IBr.**

## Source grounding

- Printed data used: "100 g of RCOOH reacts with 181.0 g of iodine" and
  "adduct with an iodine mass fraction of 36.57 %" — verbatim from
  T5_page-3.png; "three different organic products in equimolar amounts"
  (reductive ozonolysis) — same page, two sentences earlier.
- Previous-part dependency (T5-A3, formula of RCOOH): derived inline from
  the problem-only material (ozonolysis + iodine datum + fatty-acid lattice)
  rather than assumed; the 5.3 instruction "you can use a–d fragments from
  5.1" is the problem-stated fallback permitting use of the identified acid.
- Trusted general law: halogen addition across C=C consumes exactly one
  reagent molecule per π-bond; standard atomic masses (I 126.904, Br 79.904,
  Cl 35.453, F 18.998, At 209.987, C 12.011, H 1.008, O 15.999) as supplied
  with the exam paper.
- No official solutions, marking schemes, or external answer sources were
  consulted.
