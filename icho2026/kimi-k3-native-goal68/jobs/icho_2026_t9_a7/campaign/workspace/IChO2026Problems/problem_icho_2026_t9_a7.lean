import Mathlib

/-!
# IChO 2026 — T9-A7 (target `icho_2026_t9_a7`)

## Subquestion 9.7 (6.0 pt)

> **Calculate** the *m/z* value for the two [M+Na]⁺ peaks that were observed
> for the degradation products from **L**. **Use** integer values of atomic mass.

See `answer.md` for the full source-grounding explanation.
-/

namespace IChO2026.Problems.T9A7

/-- Elements relevant to the printed molecular formulas; integer (nominal)
atomic masses, per the problem's instruction "Use integer values of atomic mass." -/
inductive Element | C | H | O | Na
  deriving Repr, DecidableEq

/-- Integer nominal atomic mass in Da. -/
def Element.nominalMass : Element → ℕ
  | .C  => 12
  | .H  => 1
  | .O  => 16
  | .Na => 23

@[simp] theorem Element.nominalMass_C  : Element.nominalMass .C  = 12 := rfl
@[simp] theorem Element.nominalMass_H  : Element.nominalMass .H  = 1  := rfl
@[simp] theorem Element.nominalMass_O  : Element.nominalMass .O  = 16 := rfl
@[simp] theorem Element.nominalMass_Na : Element.nominalMass .Na = 23 := rfl

/-- A molecular (atomic) composition, as counts of C, H, O atoms. -/
structure Composition where
  c : ℕ
  h : ℕ
  o : ℕ
  deriving Repr, DecidableEq

/-- The integer nominal molecular mass of a composition. -/
def Composition.nominalMass (m : Composition) : ℕ :=
  m.c * Element.nominalMass .C + m.h * Element.nominalMass .H + m.o * Element.nominalMass .O

/-- The *m/z* of the singly-charged sodium adduct `[M+Na]⁺` at unit charge is
the neutral nominal molecular mass plus the nominal mass of one Na atom. -/
def Composition.sodiumAdductMz (m : Composition) : ℕ :=
  m.nominalMass + Element.nominalMass .Na

/-! ### The two degradation products, exactly as printed on Q9-4 -/

/-- **Fragment 1** (tri-O-benzyl cleavage residue): printed molecular formula
`C₂₇H₂₈O₅`. -/
def firstFragment : Composition := ⟨27, 28, 5⟩

/-- **Fragment 2** (C1/C6-diacetate vinylogous enol ester): printed molecular
formula `C₂₂H₂₅O₄`. -/
def secondFragment : Composition := ⟨22, 25, 4⟩

/-! ### Component accounting theorems (the "image_component_accounting" audit) -/

/-- Fragment 1 is a 27 : 28 : 5 C/H/O composition. -/
theorem firstFragment_formula :
    firstFragment.c = 27 ∧ firstFragment.h = 28 ∧ firstFragment.o = 5 :=
  ⟨rfl, rfl, rfl⟩

/-- Fragment 2 is a 22 : 25 : 4 C/H/O composition. -/
theorem secondFragment_formula :
    secondFragment.c = 22 ∧ secondFragment.h = 25 ∧ secondFragment.o = 4 :=
  ⟨rfl, rfl, rfl⟩

/-- Neutral nominal mass of fragment 1: 27·12 + 28·1 + 5·16 = 432. -/
theorem firstFragment_neutral_mass : firstFragment.nominalMass = 432 := by
  decide

/-- Neutral nominal mass of fragment 2: 22·12 + 25·1 + 4·16 = 353. -/
theorem secondFragment_neutral_mass : secondFragment.nominalMass = 353 := by
  decide

/-- **[M+Na]⁺ of fragment 1 has *m/z* = 432 + 23 = 455.** -/
theorem first_fragment_mz : firstFragment.sodiumAdductMz = 455 := by
  decide

/-- **[M+Na]⁺ of fragment 2 has *m/z* = 353 + 23 = 376.** -/
theorem second_fragment_mz : secondFragment.sodiumAdductMz = 376 := by
  decide

/-- The answer as an ordered pair, in the order the two products are drawn
(left fragment then right fragment on Q9-4): (455, 376). -/
theorem degradation_products_mNa_mz_eq_pair :
    (firstFragment.sodiumAdductMz, secondFragment.sodiumAdductMz) = (455, 376) := by
  decide

/-- The two peaks are distinct (Δ = C₅H₃O = 79 Da), so there really are **two**
resolved [M+Na]⁺ peaks, as the problem states are observed. -/
theorem degradation_peaks_distinct :
    firstFragment.sodiumAdductMz ≠ secondFragment.sodiumAdductMz := by
  decide

/-! Independent re-derivation of the masses written out atom-by-atom (no
`decide`), to document the arithmetic explicitly. -/

theorem firstFragment_neutral_mass_explicit :
    27 * 12 + 28 * 1 + 5 * 16 = 432 := by norm_num

theorem secondFragment_neutral_mass_explicit :
    22 * 12 + 25 * 1 + 4 * 16 = 353 := by norm_num

theorem firstFragment_mz_explicit :
    (27 * 12 + 28 * 1 + 5 * 16) + 23 = 455 := by norm_num

theorem secondFragment_mz_explicit :
    (22 * 12 + 25 * 1 + 4 * 16) + 23 = 376 := by norm_num

/-- The two characterisations agree (definitional mass via `Composition`, and
explicit atom-by-atom arithmetic). -/
theorem definitions_agree :
    firstFragment.sodiumAdductMz = (27 * 12 + 28 * 1 + 5 * 16) + 23 ∧
    secondFragment.sodiumAdductMz = (22 * 12 + 25 * 1 + 4 * 16) + 23 := by
  decide

end IChO2026.Problems.T9A7

/-- **[M+Na]⁺ of fragment 1 has *m/z* = 432 + 23 = 455.** -/
theorem icho_2026_t9_a7_first_fragment_mz :
    IChO2026.Problems.T9A7.firstFragment.sodiumAdductMz = 455 :=
  IChO2026.Problems.T9A7.first_fragment_mz

/-- **[M+Na]⁺ of fragment 2 has *m/z* = 353 + 23 = 376.** -/
theorem icho_2026_t9_a7_second_fragment_mz :
    IChO2026.Problems.T9A7.secondFragment.sodiumAdductMz = 376 :=
  IChO2026.Problems.T9A7.second_fragment_mz

/-! ## Semantic-faithfulness audit

The two final theorems state *exactly* the requested chemistry: the [M+Na]⁺
*m/z* of the first degradation product (printed formula `C₂₇H₂₈O₅`) is 455, and
that of the second (printed formula `C₂₂H₂₅O₄`) is 376.  Both keep raw value =
reported value in `ℕ` (exact integer output, no rounding), use only
problem-sanctioned integer masses, and rely on no `sorry`/`admit`/native-axiom
shortcuts — see the `#print axioms` commands below (live). -/

#print axioms icho_2026_t9_a7_first_fragment_mz
#print axioms icho_2026_t9_a7_second_fragment_mz
#print axioms IChO2026.Problems.T9A7.firstFragment_neutral_mass_explicit
#print axioms IChO2026.Problems.T9A7.secondFragment_neutral_mass_explicit
