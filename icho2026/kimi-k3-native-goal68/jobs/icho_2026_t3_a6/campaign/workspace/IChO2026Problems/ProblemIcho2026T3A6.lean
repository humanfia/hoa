import Mathlib

/-!
# IChO 2026, Theory Problem T3, Subquestion 3.6 — `icho_2026_t3_a6`

**Official question** (theory_problem.pdf p. 30, image T3_page-6.png):
"3.6 **Calculate** the pi-pi stacking energy between two layers of one repeat
unit of COF-8, for the **AA**, **AB** and **AB'** arrangements. **Assume**
pi-pi stacking happens only between aromatic units."
-/

namespace IChO2026T3A6

/-! ## Problem-supplied table entries (kJ mol-1, exact printed decimals) -/

/-- Benzene-benzene energy, eclipsed geometry (first table column). -/
def E_bb_ecl : ℝ := -7.9
/-- Benzene-benzene energy, slipped geometry (second table column). -/
def E_bb_slp : ℝ := -12.6
/-- Benzene-triazine energy, slipped geometry (second table column). -/
def E_bt_slp : ℝ := -55.6
/-- Triazine-triazine energy, eclipsed geometry (first table column). -/
def E_tt_ecl : ℝ := -6.7

/-- Printed problem datum: the AA' slightly shifted mode has stacking energy
−67.1 kJ mol⁻¹ between two layers of one repeat unit (given in the question
and pre-filled on answer sheet A3-4). -/
def E_AA'_given : ℝ := -67.1

/-- Centroid asymmetry along any one direction: for `c₁ ≠ c₂` the centroids of
two triangles sharing the base pair `(a, b)` are distinct.  This is the
arithmetic content of “the up-pointing and down-pointing edge-midpoint
triangles of the honeycomb are different triangles”, i.e. the reason AB and
AB′ are inequivalent registries and must be evaluated separately. -/
theorem centroids_distinct {a b c₁ c₂ : ℝ} (h : c₁ ≠ c₂) :
    (a + b + c₁) / 3 ≠ (a + b + c₂) / 3 := by
  intro heq
  apply h
  linarith

/-- **AA (eclipsed):** 1 t-t + 10 b-b eclipsed contacts per repeat unit of
the bilayer (1+1 triazine rings, 10+10 benzene rings per two-layer cell). -/
def E_AA : ℝ := 1 * E_tt_ecl + 10 * E_bb_ecl

/-- **AB:** 6 slipped benzene-benzene contacts (the six edge-midpoint aromatic
jobs of the repeat unit stack on the phenylene pairs of the other layer when
the triazine nodes sit above the hexagon-hole centres). -/
def E_AB : ℝ := 6 * E_bb_slp

/-- **AB':** 6 slipped benzene-triazine contacts (complementary hole-centred
registry: edge-midpoint jobs stack on the hole-centred triazines). -/
def E_AB' : ℝ := 6 * E_bt_slp

/-- AA stacking energy: **-85.7 kJ mol⁻¹**. -/
theorem stacking_energy_aa : E_AA = -85.7 := by
  norm_num [E_AA, E_tt_ecl, E_bb_ecl]

/-- AB stacking energy: **-75.6 kJ mol⁻¹**. -/
theorem stacking_energy_ab : E_AB = -75.6 := by
  norm_num [E_AB, E_bb_slp]

/-- AB' stacking energy: **-333.6 kJ mol⁻¹**. -/
theorem stacking_energy_ab_prime : E_AB' = -333.6 := by
  norm_num [E_AB', E_bt_slp]

/-- The three requested outputs together (kJ mol⁻¹; three significant figures,
matching the precision of every printed table entry):
AA = -85.7, AB = -75.6, AB' = -333.6. -/
theorem requested_outputs_summary :
    E_AA = -85.7 ∧ E_AB = -75.6 ∧ E_AB' = -333.6 :=
  ⟨stacking_energy_aa, stacking_energy_ab, stacking_energy_ab_prime⟩

/-- Consistency note: the given AA' value −67.1 ε (−85.7, 0) is weaker than
the fully eclipsed AA energy and stronger than 0, consistent with the picture
of AA' as a slightly-shifted (partially stabilised) registry; a recorded
sanity check only, never used in the three requested outputs. -/
theorem aa_prime_datum_ordering : E_AA < E_AA'_given ∧ E_AA'_given < 0 := by
  rw [stacking_energy_aa]
  norm_num [E_AA'_given]

#print axioms stacking_energy_aa
#print axioms stacking_energy_ab
#print axioms stacking_energy_ab_prime
#print axioms requested_outputs_summary
#print axioms aa_prime_datum_ordering

end IChO2026T3A6
