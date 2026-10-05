# IChO 2026 · Problem T8 · Sub‑question 8.3 (`icho_2026_t8_a3`)

## Requested output

`geometry_1` — *tick the correct geometry for the structure of **1***
(classification, exact symbolic).

## Answer

**Correct box = option (vii)** — the octahedral structure of **[Fe(8)Cl₂]**
with the **four nitrogen donors of ligand 8 in the equatorial plane** and the
**two chloride ligands trans (axial), Cl–Fe–Cl**.  This is the *trans*‑
dichlorido, six‑coordinate Fe(II) octahedron (bottom‑right tick box on answer
sheet A8‑2).

## Reasoning (source‑grounded)

1. **Ligand 8 is a linear tetradentate N4 polypyridyl.**
   `[ProblemInput]` On problem page Q8‑1, ligand **8** is drawn as a
   benzoic‑acid–functionalised phenyl–pyridine joined to a terpyridine‑type
   arm, i.e. an *unbranched chain* of four pyridine N‑donors.  The cartoon
   box symbol for **8** explicitly shows the four N atoms connected by three
   consecutive chelate arcs in a single linear row.

2. **Complex 1 is a dichlorido iron complex.**
   `[ProblemInput]` The synthesis on Q8‑1 reads “ligand **8** + FeCl₂ → **1**”.
   Therefore **1** contains one Fe together with the **two** chloride ligands
   supplied by FeCl₂.  This is independently corroborated by the mechanism on
   Q8‑2, where complex **1** is activated to **9** by the step
   “+ 2 H₂O, − 2 Cl⁻”: exactly two chlorides are present to be displaced.

3. **Complex 1 is six‑coordinate.**
   `[ProblemInput]` Together with ligand 8’s four N donors and the two
   chlorides, the coordination number of Fe in **1** is `4 + 2 = 6`, matching
   the six‑coordinate entries (CN = 6 for **11**) on the 8.4 answer sheet.

4. **A linear tetradentate N4 ligand binds equatorially.**
   `[TrustedLaw]` A linear chain of four pyridine donors connected through
   three five‑membered chelate rings (a quaterpyridine‑type backbone) cannot
   span two mutually perpendicular planes of a single octahedron.  Its bite
   geometry forces the four N donors into the four *equatorial* sites of an
   octahedron, so the only positions left for the two chlorides are the two
   *axial* sites.  (An axial/equatorial mixture or an all‑equatorial cis pair
   would require the inflexible aromatic N4 backbone to bend out of its plane,
   which it cannot do.)

5. **Therefore the two chlorides are trans.**
   `[Derived]` With the four N atoms fixed in the equatorial plane, the two
   Cl⁻ ligands must occupy the two axial sites, i.e. they are *trans*
   (Cl–Fe–Cl angle 180°).

6. **Excluding the other six options:**
   * (i), (ii) show FeN₄ **without any chloride** — inconsistent with the
     FeCl₂ derived dichlorido composition.
   * (iii), (iv) show FeN₄ with **only one** Cl — again inconsistent (⧟ 2 Cl).
   * (v) has two N donors **axial** and the two Cl *cis* in the equatorial
     plane — a linear N4 ligand cannot place donors axially (violates the
     span law).
   * (vi) has one Cl axial and one Cl equatorial — a *cis* Cl pair.  With the
     N4 ligand in the equatorial plane there is no equatorial site left for a
     chloride, so this is impossible.
   * (vii) has four equatorial N and two trans axial Cl — the only structure
     consistent with all the above. ✓

## Source‑grounding explanation

* **Problem inputs used** (all from the official English problem/answer
  sheets in this workspace, no solutions consulted):
  * Q8‑1 line drawing and cartoon of ligand **8** (tetradentate, linear,
    four pyridine N donors) and the synthesis “**8** + FeCl₂ → **1**”.
  * Q8‑2 catalytic mechanism: activation of **1** to **9** by
    “+ 2 H₂O, − 2 Cl⁻” (⇒ two chlorides in **1**).
  * Answer‑sheet A8‑2, item 8.3: the seven printed geometry tick boxes.
  * Answer‑sheet A8‑3/A8‑4 entries for 8.4 recording CN = 6 (**11**) and
    CN = 5 (**13**), confirming six‑coordinate Fe at the resting level.
* **Trusted general law used** (standard coordination chemistry, not an
  official answer): a *linear* tetradentate polypyridyl binds an octahedral
  metal through the equatorial plane, because three connected five‑membered
  chelate rings can tile the four equatorial positions but cannot wrap over
  an axial edge.

No official solution, marking scheme, or pre‑existing answer was consulted.
The classification is derived solely from the printed problem material plus
that single standard coordination‑geometry principle.

## Deliverables

* Natural‑language answer: this file.
* Machine‑checked proof: [`IChO2026Problems/problem_icho_2026_t8_a3.lean`](IChO2026Problems/problem_icho_2026_t8_a3.lean)
  proves `geometry_1 = PrintedOption.vii` and that this is the *unique*
  correct option (theorems `correct_geometry_1_is_trans_dichloro`,
  `geometry_1_is_correct`, `no_other_option_is_correct`).
* Verification record: see [`verification.md`](verification.md).
