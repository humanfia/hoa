# IChO 2026 — T9-A3 (problem 9.3): ring size and stereocentres of macrocycle X

**Answers**

- Ring size of macrocycle X: **rs = 35**
- Number of stereocentres in X: **sc = 21**

## Source grounding

Sources used (problem-only material, no solutions):

- `icho_2026_source/image/T9_page-1.png` (printed page Q9-1; source page 85 of
  `icho_2026_source/raw/theory_problem.pdf`, sha256
  af51373f43201cecf81457afa4cd44a2cf68a776068abf216292482dbc8d3d60):
  * "Cyclodextrins (CD) are a family of cyclic oligosaccharides, consisting of
    glucose subunits joined by α-1,4-glycosidic bonds. The three most common
    cyclodextrins (α-, β-, γ-cyclodextrin) contain 6, 7, and 8
    α-D-glucopyranoside units, respectively."
  * The β-CD structure printed with "n = 7", one OBn test substituent per unit,
    and the CD template circle annotated "(OH)₁₄" (the fourteen secondary
    2-OH/3-OH groups) plus seven CH₂OH boxes (primary 6-OH groups). This fixes
    the connectivity of each unit: C1–O(glycosidic)–C4 links between units;
    within a unit the pyranose ring O5–C1–C2–C3–C4–C5 with CH₂OH on C5.
- `icho_2026_source/image/T9_page-2.png` (printed page Q9-2):
  * Scheme: a bracketed cyclodextrin unit with subscript **7** and a free
    vicinal diol drawn (HO– … –HO on C2/C3, plus the C6 CH₂OH) sits between two
    arrows: `—(1) TsCl (7 equiv.), Py; 2) NaOH, H₂O, 60 °C)→ K` (used in 9.2)
    and `X ←(1) NaIO₄; 2) NaBH₄, H₂O; 3) Ac₂O, Py)—` (used here in 9.3).
  * Question 9.3 text: "**Determine** the ring size, rs, of macrocycle **X**.
    **Give** the number of stereocentres, sc, in **X**." (8.0 pt)

Pages Q9-3 to Q9-5 concern compounds L, N–S and α-cycloaltrin; they were
inspected and contain no additional inputs needed for 9.3.

## Chemistry

**What the reagents do (trusted general laws).**

1. **NaIO₄** performs Malaprade oxidative cleavage of vicinal diols:
   a C–C bond flanked by two OH groups is split, giving two carbonyls. The only
   vicinal diol in a glucopyranoside unit of β-CD is the C2–C3 diol (the 6-OH
   is a primary alcohol, not part of a vicinal diol; the glycosidic oxygens and
   the ring oxygen O5 are ethers, inert to periodate). Hence periodate cleaves
   the **C2–C3 bond of each of the seven units**, producing a 2,3-dialdehyde at
   every unit.
2. **NaBH₄, H₂O** reduces aldehydes to primary alcohols. Former C2 becomes a
   –CH₂OH arm on C1; former C3 becomes a –CH₂OH arm on C4.
3. **Ac₂O, Py** acetylates the free OH groups (the new 2- and 3-arms plus the
   6-CH₂OH). Acetylation changes only the substituent H→Ac and does not alter
   the connectivity, the ring, or any stereocentre, so it is immaterial for rs
   and sc.

**Why X is still one macrocycle, and its ring size.** The β-CD macrocyclic
backbone does not run through the C2–C3 bond. Going around the macrocycle,
within each unit the backbone passes from C4 to C1 via the long side of the
pyranose ring: C4–C5–O5–C1, and between units via the glycosidic link
C1–O–C4. Cleaving C2–C3 therefore opens each six-membered pyranose ring but
leaves the backbone loop intact; former C2 and C3 (now –CH₂OAc arms) become
pendant substituents on C1 and C4 respectively, and the 6-CH₂OAc arm on C5 is
pendant. The unique cycle of X traverses, per unit, exactly five atoms:

C1_i → O(glycosidic, C1_i–O–C4_{i+1}) → C4_{i+1} → C5_{i+1} → O5_{i+1} → C1_{i+1}

so with seven units:

rs(X) = 7 × (C1, O_glyc, C4, C5, O5) = 7 × 5 = **35**.

**Stereocentres.** In native β-CD each unit carries five stereocentres
(C1–C5). In X:

- C2 and C3 are reduced to –CH₂– groups (two identical H substituents) and are
  no longer stereogenic; C6 was never a stereocentre (–CH₂OH/–CH₂OAc);
- C1, C4, C5 each retain four pairwise different substituents:
  - C4: H, O_glyc(toward C1 of the previous unit), C5-side, CH₂OAc arm (former C3);
  - C5: H, O5(toward C1), C4-side, CH₂OAc arm (C6);
  - C1: H, O5-side, O_glyc-side, CH₂OAc arm (former C2). The two oxygen arms are
    constitutionally similar but distinguishable as ligands: X is the chiral,
    C₇-symmetric macrocycle built from seven homochiral D-glucose-derived units
    with no mirror or inversion symmetry, so the two ring-traversal directions
    from C1 are diastereomorphic ligands, distinguished under CIP sequence
    rule 5 — the same reason why the anomeric carbon of a native cyclodextrin
    is stereogenic.

Hence each unit contributes 3 stereocentres and sc(X) = 7 × 3 = **21**.

## Lean deliverable

`IChO2026Problems/problem_icho_2026_t9_a3.lean` encodes the molecular bond
graph of X explicitly (7 units; atoms C1, glycosidic O, C4, C5, ring O, and
the three pendant –CH₂OAc arms per unit), and proves:

- the explicit 35-atom traverse is a genuine cycle of the bond graph
  (`x_ring_is_cycle`),
- every backbone atom lies in that ring and the ring contains only backbone
  atoms (`x_backbone_mem_ring`, `x_ring_elems_backbone`),
- exhaustive bond accounting: every bond of X is either one of the 35 ring
  edges or one of the 21 pendant arm bonds (`x_bond_exact`), so no chord and no
  further cycle exists and the pendant arms cannot shorten the ring,
- the ring-size theorem `icho_2026_t9_a3_ring_size : rsX = 35`,
- per-centre substituent analysis: C1/C4/C5 carry four pairwise distinct
  substituents (`c1_stereogenic`, `c4_stereogenic`, `c5_stereogenic`) while
  the former C2/C3 and C6 arms carry duplicate hydrogens
  (`arm2_not_stereogenic`, `arm3_not_stereogenic`, `arm6_not_stereogenic`),
- the stereocentre theorem `icho_2026_t9_a3_stereocentres : scX = 21`.

All proofs are axiom-clean apart from Lean's standard logical axioms
(`propext`, `Classical.choice`, `Quot.sound`); see `verification.md`.

## Assumptions and gaps

- The bracketed intermediate drawn between the arrows on page Q9-2 is read as
  β-CD (7 units, free 2,3-diols), consistent with page Q9-1 ("n = 7",
  "(OH)₁₄", 7 × CH₂OH). This is grounded in the problem statement, not in
  external answer material.
- Standard general reactivity (Malaprade cleavage of vicinal diols; NaBH₄
  reduction of aldehydes; acetylation with Ac₂O/Py; ketals/ethers inert to
  these reagents) is used as trusted general law, allowed by the candidate
  domain policy.
- No ungrounded conditions were needed; no source gaps remain for this
  subquestion. The K-branch (9.2) is not needed numerically for 9.3 and is not
  assumed beyond what the scheme itself shows.
