# IChO 2026 — Problem T1, Subquestion 1.1: Identify X and Y

## Answer

**X = 6 (linalool)** and **Y = 3 (1,8-cineole, eucalyptol)**.

On the blank answer sheet A1-1 this means marking X: □6 and Y: □3.

## Problem data (source grounding)

From `theory_problem.pdf`, printed page Q1-2 (identical to
`T1_page-2.png`), the only four plants in Avicenna's laboratory can yield
ten numbered compounds, each drawn as a skeletal structure with a printed
molecular formula:

- Zingiber: **1** (C₁₁H₁₄O₃), **2** (C₁₀H₁₈O), **3** (C₁₀H₁₈O)
- Hypericum: **4** (C₆H₁₂O), **5** (C₁₀H₁₂O₂), **6** (C₁₀H₁₈O)
- Chamomilla: **7** (C₁₄H₁₆), **8** (C₁₅H₂₄), **3** (C₁₀H₁₈O)
- Artemisia: **9** (C₁₀H₁₆O), **10** (C₁₀H₁₈O), **3** (C₁₀H₁₈O)

(Compound 3 is drawn identically in all three rows — one compound.)
Chromatography shows the elixir consists of four *different* substances X, Y,
Z, W; **X can isomerise into Y in an acidic medium**, and **Y has a plane of
symmetry**. Subquestion 1.1 asks to identify X and Y; the answer sheet (page
A1-1) asks for one compound number each in 1–10.

Reading of the four C₁₀H₁₈O structures as drawn on Q1-2:

- **2** = borneol: bicyclo[2.2.1]heptan-2-ol skeleton, gem-dimethyl on the
  one-carbon bridge, one methyl on a bridgehead, –OH on a bridge carbon
  adjacent to that bridgehead. Bicyclic secondary alcohol, no C=C.
- **3** = 1,8-cineole (1,3,3-trimethyl-2-oxabicyclo[2.2.2]octane): the ether
  oxygen links a methyl-bearing bridgehead carbon and the gem-dimethyl
  carbon; the two bridgeheads are joined by two equivalent –CH₂–CH₂–
  bridges.
- **6** = linalool: acyclic tertiary allylic alcohol
  CH₂=CH–C(OH)(Me)–CH₂–CH₂–CH=C(Me)₂ as drawn, with two C=C bonds and one
  O–H.
- **10** = umbellulone skeleton as drawn: bicyclo[3.1.0]hexan-2-one carrying
  one methyl α to the carbonyl and one isopropyl group on the opposite
  ring-junction carbon. A ketone: no O–H.

## Solution

**Step 1 — the formula filter.** Isomerisation preserves the molecular
formula, so X and Y must be two *different* compounds carrying the *same*
printed formula. Among the ten printed formulae, only C₁₀H₁₈O occurs more
than once (and all nine other formulae occur exactly once), so
{X, Y} ⊆ {2, 3, 6, 10}. Formally this is `printedFormula` plus the kernel-
checked `formulaC10H18O_carriers` and `shared_formula_class`.

**Step 2 — Y has a plane of symmetry.** Check the four candidates:

- **2 (borneol):** its only labelled symmetry is the swap of the two gem
  methyls on the bridge carbon, which fixes all seven cage atoms
  (`borneol_sym_cases`). A mirror plane of the rigid, non-planar
  bicyclo[2.2.1] cage must move some cage atom (`law_cage` with the premise
  `NonPlanarRigidCage gBorneol [0…6]`, read off the drawing) — so any
  realised mirror would have to fix the entire cage, which is impossible
  (`borneol_no_mirror`). Borneol is in fact chiral (it contains stereogenic
  centres that are not compensated).
- **6 (linalool):** its only labelled symmetry is the swap of the two methyls
  on the =C(Me)₂ end (`linalool_sym_cases`), which fixes the tertiary
  carbinol carbon and all four of its substituents (–OH, –Me, vinyl, chain),
  which are pairwise distinguishable in the labelled graph. A tetrahedral
  atom with four inequivalent substituents cannot lie in a mirror plane with
  all four substituents fixed (`law_tetra`), so linalool has no mirror plane
  (`linalool_no_mirror`) — consistent with the stereogenic carbinol centre
  making linalool chiral.
- **10 (umbellulone):** its only labelled symmetry is the swap of the two
  isopropyl methyls, fixing the whole bicyclic frame
  (`umbellulone_sym_cases`); the cage argument again forbids a mirror plane
  (`umbellulone_no_mirror`). The molecule carries two different ring
  substituents (Me α to C=O, iPr on the other junction); no mirror plane can
  exchange them.
- **3 (1,8-cineole):** the drawing admits the mirror plane through the ether
  oxygen, both bridgehead carbons and the three methyl carbons, exchanging
  the two –CH₂–CH₂– bridges and the two gem-methyls. Mechanised as the
  involution (4 5)(7 9)(8 10), verified bond-by-bond by the kernel
  (`cineoleMirror_valid`, `cineoleMirror_moves`, `cineoleMirror_fixed`).

Hence **Y = 3**, the only candidate with a plane of symmetry.

**Step 3 — X isomerises to 3 in acid.** Y = cineole is a cyclic ether, and
acid-catalysed isomerisation to a cyclic ether requires in the starting
material an alcoholic O–H (the future ether oxygen) and a C=C double bond
(the cyclisation target) — `law_ether_cyclisation`. Among the remaining
candidates {2, 6, 10}: borneol (2) has an O–H but **no C=C**
(`borneol_noCC`), umbellulone (10) is a ketone with **no O–H**
(`umbellulone_noOH`), and only linalool (6) has both (`linalool_hasOH`,
`linalool_hasCC`). Since X ≠ Y, **X = 6**.

**Consistency check (the drawn reaction is exactly 6 → 3).** The explicit
atom correspondence `linToCin` from the drawn linalool skeleton to the drawn
cineole skeleton maps every existing bond of 6 onto a bond of 3
(`cyclisation_preserved`), preserves elements (`cyclisation_elements`), is
injective (`linToCin_inj`), and creates only the two new σ-bonds of the
cyclisation: the ether bond from the O–H oxygen to the isopropylidene
alkene carbon (`cyclisation_newbond1`) and the ring-closing C–C bond between
the two other alkene carbons (`cyclisation_newbond2`). Correspondence in
everyday terms: –OH oxygen ↦ ether O; carbinol C ↦ methyl-bearing
bridgehead; its methyl ↦ the bridgehead methyl; vinyl –CH=CH₂ ↦ one
–CH₂–CH₂– bridge; chain –CH₂–CH₂– ↦ the other bridge; alkene –CH= ↦ the
second bridgehead; the –C(Me)₂ alkene carbon ↦ the gem-dimethyl carbon with
its two methyls. (This is the classical linalool → 1,8-cineole cyclisation
via the α-terpineol-type intermediate.)

## Documentation of a source discrepancy

Compound 10's drawn skeleton (methyl + isopropyl on a bicyclo[3.1.0]hexan-2-
one) corresponds to hydrogen count 16, i.e. C₁₀H₁₆O, while the printed label
under it reads C₁₀H₁₈O; this is recorded by the theorem
`umbellulone_Hcount_drawn : Hcount gUmbellulone 11 = 16`. The discrepancy
does not affect the answer: compound 10 is eliminated structurally (as a
ketone it lacks the O–H required for the acid-catalysed ether cyclisation,
and its labelled symmetries cannot realise a mirror plane of the non-planar
cage), regardless of which formula is taken as authoritative. The formula
filter in Step 1 uses the printed label, as printed; if instead the drawn
structure (C₁₀H₁₆O) were taken, compound 10 would carry a unique formula and
drop out of the {X, Y} pool even earlier, strengthening the same conclusion.
