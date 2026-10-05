# IChO 2026, Theory Problem 8.4 — Structures of 9–15 (target `icho_2026_t8_a4`)

## Sources used

Problem-only official materials of the provided bundle:

* `T8_page-1.png` / `theory_problem.pdf` p. 72 — catalyst 1 is made from
  ligand **8** + FeCl₂; the cartoon of **8** shows a *linear tetradentate N₄*
  ligand (four pyridinic nitrogens in a chain, i.e. a quaterpyridine-type
  ligand bearing a benzoic-acid anchor).
* `T8_page-2.png` / `theory_problem.pdf` p. 73 — the C₃N₄-supported catalytic
  cycle with the eight edge labels (used literally):
  1 →(+2H₂O, −2Cl⁻)→ 9; 9 →(+hν, +1e⁻, −H₂O)→ 10; 10 →(−H₂O, +CO₂)→ 11;
  11 →(+hν, +1e⁻, +H⁺)→ 12; 12 →(+H₂O)→ 13; 13 →(+H⁺, −H₂O)→ 14;
  14 →(−CO)→ 15; 15 →(+H₂O)→ back to 9.  Question 8.5 on the same page
  stipulates `M_cat = 557.21 g mol⁻¹`.
* Blank answer sheet, `theory_problem.pdf` pp. 79–80 (A8-3 / A8-4):
  pre-printed **11: OS = +3, CN = 6; 12: CN = 5; 13: OS = +2; 15: VE = 16**.

No official answers, marking schemes, or external solutions were used.  The
electron-counting conventions are the standard ionic (2-electron donor,
oxidation-state) rules of coordination chemistry: group(Fe) = 8,
VE = (8 − OS) + 2·CN, and Z = OS + Σ (formal ligand charges), with ligand
formal charges: 8 = 0, H₂O = 0, Cl⁻ = −1, CO = 0, −C(=O)OH = −1,
η²-CO₂²⁻ = −2.

## Grounding the ligand formula

Reading the drawn ligand 8 as a benzoic-acid-substituted linear
quaterpyridine gives the connectivity formula C₂₇H₁₈N₄O₂ (see note on
ambiguity below).  Catalyst 1 = [Fe(C₂₇H₁₈N₄O₂)Cl₂] then has
M = 27(12.011) + 18(1.008) + 4(14.007) + 2(15.999) + 55.845 + 2(35.45)
  = **557.21 g mol⁻¹**, reproducing the stipulated M_cat of question 8.5 to
the printed precision and confirming that ligand 8 is tetradentate (a
tridentate terpyridine-based ligand gives M ≈ 631.9 or 632.3 g mol⁻¹, which
does not match).

## Derivation step by step

Catalyst **1** = [Fe(8)Cl₂]⁰, Fe(II).

* **9** [Fe(8)(H₂O)₂]²⁺.  1 + 2H₂O − 2Cl⁻: the two chlorides are replaced by
  two neutral water ligands; Fe stays +2.  Z = 2 + 2(0) = +2, CN = 4+2 = 6,
  VE = 6 + 12 = 18.
* **10** [Fe(8)(H₂O)]⁺.  9 + hν + 1e⁻ − H₂O: the photoreduced Fe(I) species
  (the C₃N₄ support injects one electron) after loss of one H₂O.
  OS = +1, Z = +1, CN = 5, VE = 7 + 10 = 17.
* **11** [Fe(8)(η²-CO₂)]⁺.  10 − H₂O + CO₂: CO₂ undergoes oxidative addition
  to Fe(I), binding side-on through C and O (metallacarboxylate,
  Fe(III)–CO₂²⁻).  This is exactly the assignment forced by the printed
  answer-sheet values OS = +3, CN = 6 (4 N of 8 + 2 donors of η²-CO₂).
  Z = +3 − 2 = +1, VE = 5 + 12 = 17.
* **12** [Fe(8)(C(=O)OH)]⁺.  11 + hν + 1e⁻ + H⁺: Fe(III) is reduced back to
  Fe(II) and the distal oxygen of the CO₂ unit is protonated, opening the
  metallacycle to the C-bound hydroxycarbonyl (carboxyl) ligand −C(=O)OH
  (η¹ through C; C=O double bond retained; charge −1).  Printed anchor CN = 5
  (4 N of 8 + 1 C donor).  OS = +2, Z = +2 − 1 = +1, VE = 6 + 10 = 16.
* **13** [Fe(8)(C(=O)OH)(H₂O)]⁺.  12 + H₂O: the printed step 12 → 13 is pure
  addition of H₂O, so the carboxyl ligand is retained and a water occupies the
  free site; the sheet prints OS = +2.  CN = 6, Z = +1, VE = 6 + 12 = 18.
* **14** [Fe(8)(CO)(H₂O)]²⁺.  13 + H⁺ − H₂O: protonation of the carboxylic OH
  cleaves the ligand C–O bond, releasing one water and leaving the iron
  carbonyl CO plus the remaining aqua ligand.  OS = +2, Z = +2,
  CN = 6, VE = 18.
* **15** [Fe(8)(H₂O)]²⁺.  14 − CO: the product CO dissociates, leaving the
  monoaqua Fe(II) complex; the sheet prints VE = 16, which fixes CN = 5
  (VE = 6 + 2·CN = 16).  OS = +2, Z = +2.  15 + H₂O → 9 closes the cycle.

Net stoichiometry of one turnover (sum of the eight edge labels):
CO₂ + 2H⁺ + 2e⁻ → CO + H₂O — precisely the half equation of question 8.1,
confirming the assignment.

## Answers (structure, OS, CN, VE, Z)

| # | structure | OS | CN | VE | Z |
|---|-----------|-----|-----|-----|-----|
| 9  | [Fe(8)(H₂O)₂]²⁺               | +2 | 6 | 18 | +2 |
| 10 | [Fe(8)(H₂O)]⁺                | +1 | 5 | 17 | +1 |
| 11 | [Fe(8)(η²-CO₂)]⁺ (side-on C,O) | +3 | 6 | 17 | +1 |
| 12 | [Fe(8)(C(=O)OH)]⁺ (η¹-C)     | +2 | 5 | 16 | +1 |
| 13 | [Fe(8)(C(=O)OH)(H₂O)]⁺       | +2 | 6 | 18 | +1 |
| 14 | [Fe(8)(CO)(H₂O)]²⁺           | +2 | 6 | 18 | +2 |
| 15 | [Fe(8)(H₂O)]²⁺               | +2 | 5 | 16 | +2 |

All seven structures use the cartoon of ligand 8 (four N donors bound to Fe
throughout).  Ground atoms: 12, 13 share the C-bound carboxyl
Fe–C(=O)OH unit with one C=O, one C–O and one O–H bond; 11 binds CO₂ side-on
(Fe–C and Fe–O) with one C=O and one C–O; 14 binds CO through carbon (C≡O);
9, 10, 15 carry only the neutral aqua ligand(s) besides ligand 8.

## Formalization

File `IChO2026Problems/problem_icho_2026_t8_a4.lean` defines the binding
model explicitly (`Ligand` records donor atoms, formal charge and internal
bond orders; `FeComplex` records OS and the full ligand sphere) and proves,
among others, all 28 requested outputs (`complex_N_{oxidation_state,
coordination_number, valence_electrons, total_charge}` for N = 9…15), the four
answer-sheet anchors (`sheet_anchor_11/12/13/15`), the ligand-8 connectivity
invariant, an atom-balance theorem for each of the eight printed arcs, the
net half-reaction balance CO₂ + 2H⁺ → CO + H₂O, closure of the cycle, and the
M_cat consistency check `mcat_consistent`.  See `verification.md` for the
exact commands and `#print axioms` output.

## Honest caveats (source gaps)

* The exact Ar–N inter-ring connectivity of ligand 8 within the C₂₇H₁₈N₄O₂
  connectivity formula (i.e. which pyridine carries the benzoic-acid arm, and
  the order of pyridines in the N₄ chain) is at the resolution limit of the
  page-1 cartoon at hand; the answer-sheet-relevant quantities (denticity 4,
  neutrality, formula/mass) are grounded by the stipulated value
  M_cat = 557.21 g mol⁻¹, which the formalization uses as the check.
* The 11 assignment (Fe(III)–η²-CO₂²⁻, Z = +1) and the 12/13 carboxyl
  tautomer (Fe–C(=O)OH vs. Fe–η²-CH(O)O) are two resonance/ionic-limit
  descriptions of the same C-bound carboxyl intermediate; they give identical
  OS/CN/VE/Z values for 11–13, so the requested numeric answers are unaffected
  by which depiction is drawn.
* Question 8.3 (geometry of 1, square pyramidal) is a previous part whose
  result is asserted from the printed synthesis 8 + FeCl₂ → 1 with the drawn
  molecular model (square-pyramidal), per the task's stated fallback rule;
  nothing in 8.4 depends on it beyond 1 = [Fe(8)Cl₂].
