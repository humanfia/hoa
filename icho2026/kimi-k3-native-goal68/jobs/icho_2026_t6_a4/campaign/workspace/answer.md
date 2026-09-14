# IChO 2026 — Problem T6 (Carbon Nanorings), Subquestion 6.4

## Answer

| *m/z* | Identity of the ion |
|--------|---------------------|
| 591 (given example) | **[E + H]⁺** |
| **783** | **[3E + C₄₈ + 3H]³⁺** |
| **879** | **[2E + C₄₈ + 2H]²⁺** |
| **1174** | **[3E + C₄₈ + 2H]²⁺** |

Mass checks (integer atomic masses, as instructed):

- 783: (3 × 590 + 576 + 3 × 1) / 3 = 2349 / 3 = **783**
- 879: (2 × 590 + 576 + 2 × 1) / 2 = 1758 / 2 = **879**
- 1174: (3 × 590 + 576 + 2 × 1) / 2 = 2348 / 2 = **1174**

So the four intense peaks are the protonated free macrocycle **E**, and
multiply protonated supramolecular aggregates of **E** with one intact
cyclo[48]carbon ring: a 3 : 1 aggregate at charge 3+, a 2 : 1 aggregate at
charge 2+, and a 3 : 1 aggregate at charge 2+.

## Source grounding (problem-only inputs)

1. **What is being measured.** Problem text (Q6‑2, above 6.4): "In 2025, the
   first relatively stable cyclo[48]carbon was synthesised. The molecule was
   stabilised by catenation (forming interlocking rings) with macrocycle E
   and was first characterised by electrospray mass spectrometry in positive
   mode." Hence the sample contains the catenane [C₄₈ ⊂ E], with the two
   components **cyclo[48]carbon** (an all‑carbon ring, formula C₄₈) and
   **macrocycle E**, whose formula **C₄₀H₃₄N₂O₃** is printed directly under
   its structure on Q6‑2.

2. **Integer masses.** "Use integer atomic masses" (6.4): H = 1, C = 12,
   N = 14, O = 16. Therefore
   M(E) = 40·12 + 34·1 + 2·14 + 3·16 = **590**, and
   M(C₄₈) = 48·12 = **576**.

3. **Ionisation convention, from the planted example.** The blank student
   answer sheet **A6‑2** for 6.4 (inside `theory_problem.pdf`, page 58) gives
   the first ion: *m/z* 591 → **[E + H]⁺**. This anchors three things:
   (i) ionisation is by **proton attachment** (H⁺ adds mass 1 per charge);
   (ii) the answer format is an aggregate of intact E / C₄₈ units carrying
   *z* protons at charge state *z*; (iii) the integer masses above are
   correct, since 590 + 1 = 591 exactly. (The alternative anchor
   [E − H]⁻ would require 590 − 1 = 589 ≠ 591, so positive‑mode protonation
   is confirmed by the example, not assumed.)

4. **No fragmentation** (6.4) means each peak is built from *whole*
   molecules of E and C₄₈ plus protons; multiply charged aggregates are
   allowed because electrospray routinely produces them and E bears two
   basic nitrogen atoms.

## Derivation of each ion

Treating each peak as *m/z* = (n(E)·590 + n(C₄₈)·576 + n(H⁺)·1) / *z*:

- **783.** *z* = 1 gives 783 − 590 = 193 and 783 − 576 = 207, neither
  divisible by a whole‑molecule mass; the only exact solution is
  *z* = 3: 3 × 783 = 2349 = 3·590 + 576 + 3, i.e. **[3E + C₄₈ + 3H]³⁺**.
  This is *unique* among all no‑fragmentation candidates with *z* ≤ 3,
  at most *z* protons, and at most one C₄₈ ring — proved in Lean
  (`ion783_unique`).

- **879.** The only exact solution is *z* = 2: 2 × 879 = 1758 =
  2·590 + 576 + 2, i.e. **[2E + C₄₈ + 2H]²⁺** — again *unique* under the
  same conditions (`ion879_unique`).

- **1174.** *z* = 2 gives 2 × 1174 = 2348 = 3·590 + 576 + 2, i.e.
  **[3E + C₄₈ + 2H]²⁺**, consistent with the aggregate series seen at 783
  and 879 (several macrocycles, one intact cyclocarbon, charge carried by
  protons on the nitrogen/oxygen sites of E). Under the charge‑state‑2
  reading this assignment is *unique* (`ion1174_unique_at_charge_two`).

### Explicitly reported source gap (m/z 1174)

The integer‑*m/z* datum 1174 alone does not mathematically exclude the
singly charged formal alternative **[C₄₈ + E + 8H]⁺** (576 + 590 + 8 = 1174
exactly; see `catenane_octaprotonated_mz` in the Lean file): merely
doubling/halving *m/z* cannot, by pure integer arithmetic, tell a z = 1 ion
of mass 1174 from a z = 2 ion of mass 2348. The doubly charged assignment is
the chemically sensible — and therefore planted — answer: a 1 : 1 aggregate
carrying **eight** protons is chemically unreasonable for a molecule with
only two basic nitrogen atoms (and three weakly basic ethers), whereas
multiply protonated aggregates at z = 2 and z = 3 are exactly what the
unambiguous peaks at 783 and 879 already require. No experimental
charge‑state information (isotope spacing) is available at integer
resolution, so this residual ambiguity is reported per the task's
underdetermination policy rather than silently assumed away.

## Lean 4 formalization

`IChO2026Problems/problem_icho_2026_t6_a4.lean` (namespace
`IChO2026T6A4`) formalizes, over `ℕ` with the instructed integer atomic
masses:

- problem inputs: `massE = 40·12 + 34·1 + 2·14 + 3·16 = 590`
  (`massE_value`), `massC48 = 48·12 = 576` (`massC48_value`);
- the ion candidate space `IonCandidate` (counts of intact E and C₄₈,
  attached protons, charge state) and the exact `m/z` matching relation
  (`IonCandidate.MatchesMZ`);
- the planted example reproduced: `ion591_example_matches : [E+H]⁺` has
  *m/z* 591;
- the three requested ions — `ion783` (**[3E + C₄₈ + 3H]³⁺**),
  `ion879` (**[2E + C₄₈ + 2H]²⁺**), `ion1174` (**[3E + C₄₈ + 2H]²⁺**) —
  with proved mass identities and exact `m/z` matches
  (`ion783_mz`, `ion879_mz`, `ion1174_mz`);
- uniqueness theorems `ion783_unique`, `ion879_unique` (over all
  well‑formed candidates with z ≤ 3, nH ≤ z, nC48 ≤ 1) and
  `ion1174_unique_at_charge_two` — stated with explicit, finitely
  checkable domains rather than arbitrary search bounds, and proved by
  exhaustive `interval_cases`/`omega` enumeration;
- the residual underdetermination made explicit:
  `catenane_octaprotonated_mz` proves the singly charged alternative
  [C₄₈ + E + 8H]⁺ also hits integer *m/z* 1174.

Axioms: every final theorem depends only on the standard Lean/Mathlib
logical axioms (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`,
no custom axioms (see `verification.md`).
