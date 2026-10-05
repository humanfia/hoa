# IChO 2026 – Theory Problem 9, subquestion 9.9 (icho_2026_t9_a9)

**Question (from `theory_problem.pdf`, page Q9-5):**
"Determine the number of all possible arrangements of the functional groups on a
hexadifferentiated α-CD (**assume** only the CH₂OH groups have been modified)." — 4.0 pt

## Answer

**120**

## Reasoning

Step 1 – The scaffold. α-Cyclodextrin is a cyclic oligosaccharide of **six**
α-D-glucopyranoside units joined by α-1,4-links (shared context of T9, page Q9-1:
"the three most common cyclodextrins (α-, β-, γ-cyclodextrin) contain 6, 7, and 8
α-D-glucopyranoside units, respectively"). Each glucose unit carries exactly one
primary CH₂OH group on C6; 9.9 tells us that only the CH₂OH groups have been
modified, so the functionalization sites are the six primary positions, which
form a **six-membered cyclic array** on the primary rim of the torus.

Step 2 – The functional groups. A *hexadifferentiated* α-CD (the compound S of
question 9.8, built by Sollogoub *et al.*'s sequence N → O → P → Q → R → S)
carries **six different** functional groups, one on each primary position.
If all six sites were independently addressable, the groups could be placed in
6·5·4·3·2·1 = **6! = 720** ways.

Step 3 – Symmetry reduction. Two placements describe the *same molecule* iff
they differ by a rotation of the macrocycle about its symmetry axis; the cyclic
array of six equivalent sites has exactly 6 rotations (including the identity).
No reflection symmetry identifies arrangements: α-CD contains only D-glucose
units, so the macrocycle is **chiral**, and reversing the sense of the ring
produces the enantiomer — a *different* molecule, counted separately. The
correct symmetry group is therefore the cyclic group C₆ of order 6, not the
dihedral group D₆.

Step 4 – Every orbit has size exactly 6. If a nontrivial rotation k ≠ 0 mapped
an arrangement to itself, the assignment of groups to sites would have to be
constant on every cycle of the shift permutation of the six sites induced by k.
Every nontrivial rotation of a hexagon decomposes the 6 sites into cycles of
length 6 / gcd(6, k) ≥ 2, so some two different sites would carry the same
functional group — impossible, because all six functional groups are *distinct*.
Hence every arrangement is fixed by no nontrivial rotation, and every rotation
orbit contains exactly 6 of the 720 addressed placements.

Step 5 – Count.
  number of arrangements = 720 / 6 = 5! = **120**.

## Source grounding

* Question text and 4.0 pt weighting: `theory_problem.pdf`, page Q9-5 (image
  `T9_page-5.png`, box 9.9). TASK.json `source_page` 88 corresponds to this page.
* Six glucose units in α-CD: T9 preamble (page Q9-1): "the three most common
  cyclodextrins (α-, β-, γ-cyclodextrin) contain 6, 7, and 8 α-D-glucopyranoside
  units, respectively."
* Only the primary (CH₂OH) positions are modified, i.e. six sites total:
  question 9.9's parenthetical "(**assume** only the CH₂OH groups have been
  modified)".
* Six *different* functional groups (hexadifferentiation) and the chemoselective
  context: question 9.8 (image `T9_page-4.png`), Sollogoub *et al.* sequence
  N → O → P → Q → R → S.
* Counting: the underlying symmetry group of the 6-site rim is C₆ (rotations
  only, since α-CD is chiral); the orbit-stabilizer argument is formalized in
  `IChO2026Problems/problem_icho_2026_t9_a9.lean`.

## Formalization summary

The Lean 4 file `IChO2026Problems/problem_icho_2026_t9_a9.lean` proves:
`patterns_count` — there are 6! = 720 addressed assignments
(`ZMod 6 ≃ Fin 6` bijections, cardinality via `Fintype.card_perm`);
`rotation_action_isFree` — no nontrivial rotation fixes any assignment
(injectivity of a fixed bijection forces the rotation to be trivial);
`orbit_card_eq_six` — every rotation orbit contains exactly 6 assignments
(orbit–stabilizer, `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`);
`arrangement_count` — the number of arrangements (orbits of the rotation
action on addressed patterns) is exactly 120, via the disjoint-orbit
decomposition `MulAction.selfEquivSigmaOrbits` and Finset summation.
The requested integer output is `arrangement_count : Fintype.card Arrangement = 120`.
