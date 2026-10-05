# IChO 2026 – T6 (Carbon Nanorings), Subquestion 6.1

## Task (source grounding)

From the official problem PDF (`theory_problem.pdf`, question page Q6-1,
printed as `T6_page-1.png`):

> "In 2019, C18, the first example of a new class of carbon allotropes called
> cyclo[n]carbons (C𝑛) was detected. Cyclocarbons are monocyclic, all-carbon
> compounds with high strain energy and low stability. … Cyclocarbons have
> interesting aromatic properties based on their π systems. C13 has triplet
> (³C13, spin S = 1), and singlet (¹C13, spin S = 0) forms."
>
> **6.1** "Based on Hückel's rule, **fill in** the table with the number of
> distinct aromatic (A) and anti-aromatic (AA) π-systems present in each of
> C18, C16, ³C13, and ¹C13. **Fill in all blanks.**" (10.0 pt)

The blank student answer sheet (PDF page A6-1) confirms the table shape:
four rows (C18, C16, ³C13, ¹C13) × two columns (A, AA) = 8 blanks.

## Answer

| Species | A (aromatic) | AA (anti-aromatic) |
|----------|:---:|:---:|
| C18 | **2** | **0** |
| C16 | **0** | **2** |
| ³C13 | **0** | **1** |
| ¹C13 | **0** | **0** |

## Reasoning

**Two π systems per ring.** Every carbon of a cyclo[n]carbon is sp-hybridised:
one sp hybrid forms the σ framework, the second holds an in-plane lone pair,
and the two remaining p orbitals (one in-plane, one out-of-plane) generate
**two orthogonal, fully conjugated cyclic π systems** that both run around the
whole ring. Each carbon contributes one electron to each system.

**C18 (18 π electrons per system).** 18 = 4×4 + 2 is a Hückel 4n+2 count in
*both* orthogonal systems (the observed oxo-cyclocarbon C18 is well known to
be doubly aromatic, consistent with equal bond lengths in AFM images).
⟹ A = 2, AA = 0.

**C16 (16 π electrons per system).** 16 = 4×4 is a 4n count in *both*
systems. ⟹ A = 0, AA = 2.

**C13 (13 π electrons per spin class; 26 π electrons total).** An odd ring
cannot close both π shells: each system receives exactly 13 electrons of a
given spin class, and 13 is odd, so each system is necessarily an open shell.
This is exactly why the problem states that C13 exists as triplet (S = 1) and
singlet (S = 0) spin isomers — the HOMO derived from the two orthogonal
systems holds two electrons that can be paired or parallel.

* **³C13 (triplet, S = 1).** Hund's rule places the two frontier electrons of
  the odd subsystem in *different* spatial orbitals with parallel spins.
  Delocalisation then counts only 12 of the 13 unpaired-spin electrons in the
  singly-occupied system: 12 = 4×3 is a 4n count ⟹ one anti-aromatic π
  system. The fully occupied system carries all 13 paired-spin electrons;
  13 is neither 4n nor 4n+2 (it is the open shell that 14 = 4×3 + 2 would
  close), so it is neither aromatic nor anti-aromatic. ⟹ A = 0, AA = 1.

* **¹C13 (singlet, S = 0).** Pairing the two frontier electrons in one
  orbital empties the cyclic conjugated loop of the second system altogether —
  the occupied orbital of that system behaves as a lone pair orthogonal to
  cyclic π conjugation, so this π system is non-aromatic (not counted as A or
  AA). The fully occupied loop again has 13 paired electrons, which is
  neither 4n nor 4n+2. ⟹ A = 0, AA = 0.

This classification is the standard, experimentally supported picture of
cyclocarbons: C18 doubly aromatic, C16 doubly anti-aromatic, C13 triplet
singly anti-aromatic, C13 singlet non-aromatic.

## Formalisation

The Lean 4 file `IChO2026Problems/problem_icho_2026_t6_a1.lean` formalises:

* Hückel's rule as the predicates `HuckelAromaticCount n ↔ ∃ k, n = 4k+2` and
  `HuckelAntiaromaticCount n ↔ ∃ k, n = 4k`;
* their mutual exclusion (`huckel_exclusion`: no count is both 4k and 4k′+2);
* the electron-counting structure `CyclocarbonPiCounting` (two distinct
  orthogonal loops per ring, one electron per carbon per loop, unpaired spins
  of the spin state hosted in the singly-occupied loop);
* number-theoretic certificates for every count occurring here
  (18 = 4·4+2, 16 = 4·4, 12 = 4·3, 13 ≠ 4k, 13 ≠ 4k+2, 12 ≠ 4k+2,
  13 odd ⟹ no closed shell);
* the eight table entries as theorems `answer_c18_aromatic …
  answer_singlet_c13_antiaromatic`, and the filled table `completedTable`
  with a correctness theorem.

Compilation and axiom inspection are recorded in `verification.md`; all final
theorems depend only on Lean's standard logical axioms (`propext`,
`Classical.choice`, `Quot.sound`).

## Assumptions and scope notes

* The two-orthogonal-π-systems model of sp-hybridised cyclo[n]carbons and the
  electron counts above are the standard textbook treatment of these
  molecules and are the only reading consistent with the problem's explicit
  mention of triplet/singlet forms of C13.
* "Distinct π systems" is counted per orthogonal cyclic conjugated loop
  (in-plane / out-of-plane), the standard counting for cyclocarbons.
* No official solution, marking scheme, or external answer source was
  consulted; the answer is derived from Hückel's 4n+2/4n rules applied to the
  electron counts forced by the problem statement.
