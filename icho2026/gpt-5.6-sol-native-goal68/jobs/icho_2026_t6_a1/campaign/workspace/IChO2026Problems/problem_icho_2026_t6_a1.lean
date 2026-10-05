import Mathlib

/-!
# IChO 2026 T6-A1: Hückel classification of cyclocarbon π systems

The problem asks for the number of aromatic and anti-aromatic π systems in
`C₁₈`, `C₁₆`, triplet `C₁₃`, and singlet `C₁₃`.

## Separation of inputs from deductions

The names of the four species, including the multiplicities of the two `C₁₃`
states, come from the problem statement.  The statement does not print an
orbital diagram, so `piElectronCount` explicitly records the standard
cyclocarbon electron-accounting model used to apply Hückel's rule:

* an sp cyclocarbon has orthogonal in-plane and out-of-plane π manifolds;
* `C₁₈` and `C₁₆` put one electron per carbon in each manifold;
* triplet `C₁₃` has the two carbene electrons unpaired, one in each manifold,
  so the counts are 13 and 13;
* singlet `C₁₃` pairs them in the in-plane manifold, leaving the corresponding
  out-of-plane orbital empty, so the counts are 14 and 12.

Everything after `piElectronCount` is a proved arithmetic deduction from that
model and Hückel's `4k+2` / `4k` criterion.  No unchecked axioms are introduced.
-/

namespace IChO2026Problems.IChO2026T6A1

/-- The four columns printed on answer sheet A6-1. -/
inductive Species where
  | c18
  | c16
  | tripletC13
  | singletC13
  deriving DecidableEq, Fintype, Repr

/-- The two mutually orthogonal π manifolds of an sp cyclocarbon. -/
inductive PiSystem where
  | inPlane
  | outOfPlane
  deriving DecidableEq, Fintype, Repr

/--
Electron accounting needed to apply Hückel's rule.

This is the chemistry model input.  In particular, the two odd-electron
manifolds of triplet C₁₃ are deliberately *not* rounded into a Hückel class.
-/
def piElectronCount : Species → PiSystem → ℕ
  | .c18, _ => 18
  | .c16, _ => 16
  | .tripletC13, _ => 13
  | .singletC13, .inPlane => 14
  | .singletC13, .outOfPlane => 12

/-- Hückel aromaticity for a positive cyclic conjugated system: remainder 2 modulo 4. -/
def HuckelAromatic (electrons : ℕ) : Prop :=
  electrons % 4 = 2

/-- Hückel anti-aromaticity: a positive multiple of four π electrons. -/
def HuckelAntiaromatic (electrons : ℕ) : Prop :=
  0 < electrons ∧ electrons % 4 = 0

instance (electrons : ℕ) : Decidable (HuckelAromatic electrons) := by
  unfold HuckelAromatic
  infer_instance

instance (electrons : ℕ) : Decidable (HuckelAntiaromatic electrons) := by
  unfold HuckelAntiaromatic
  infer_instance

/-- The remainder definition is exactly the usual `4k+2` Hückel rule. -/
theorem huckelAromatic_iff_four_k_plus_two (electrons : ℕ) :
    HuckelAromatic electrons ↔
      ∃ k : ℕ, electrons = 4 * k + 2 := by
  constructor
  · intro h
    change electrons % 4 = 2 at h
    refine ⟨electrons / 4, ?_⟩
    have hdiv := Nat.mod_add_div electrons 4
    omega
  · rintro ⟨k, rfl⟩
    simp [HuckelAromatic]

/-- The anti-aromatic predicate is exactly the positive `4k` Hückel rule. -/
theorem huckelAntiaromatic_iff_four_k (electrons : ℕ) :
    HuckelAntiaromatic electrons ↔
      ∃ k : ℕ, 0 < k ∧ electrons = 4 * k := by
  constructor
  · rintro ⟨hpos, hmod⟩
    change 0 < electrons at hpos
    change electrons % 4 = 0 at hmod
    refine ⟨electrons / 4, ?_, ?_⟩
    · have hdiv := Nat.mod_add_div electrons 4
      omega
    · have hdiv := Nat.mod_add_div electrons 4
      omega
  · rintro ⟨k, hk, rfl⟩
    simp [HuckelAntiaromatic, hk]

/-- Number of the two π manifolds that satisfy the aromatic criterion. -/
def aromaticCount (species : Species) : ℕ :=
  ((Finset.univ : Finset PiSystem).filter fun system =>
    HuckelAromatic (piElectronCount species system)).card

/-- Number of the two π manifolds that satisfy the anti-aromatic criterion. -/
def antiaromaticCount (species : Species) : ℕ :=
  ((Finset.univ : Finset PiSystem).filter fun system =>
    HuckelAntiaromatic (piElectronCount species system)).card

/-! The electron counts really have the required `4k+2`, `4k`, or neither forms. -/

theorem eighteen_is_four_k_plus_two : 18 = 4 * 4 + 2 := by norm_num

theorem sixteen_is_four_k : 16 = 4 * 4 := by norm_num

theorem fourteen_is_four_k_plus_two : 14 = 4 * 3 + 2 := by norm_num

theorem twelve_is_four_k : 12 = 4 * 3 := by norm_num

theorem thirteen_is_neither_huckel_class :
    ¬ HuckelAromatic 13 ∧ ¬ HuckelAntiaromatic 13 := by
  norm_num [HuckelAromatic, HuckelAntiaromatic]

/-! Each theorem below proves one requested table entry. -/

theorem c18_aromatic : aromaticCount .c18 = 2 := by
  decide

theorem c18_antiaromatic : antiaromaticCount .c18 = 0 := by
  decide

theorem c16_aromatic : aromaticCount .c16 = 0 := by
  decide

theorem c16_antiaromatic : antiaromaticCount .c16 = 2 := by
  decide

theorem triplet_c13_aromatic : aromaticCount .tripletC13 = 0 := by
  decide

theorem triplet_c13_antiaromatic : antiaromaticCount .tripletC13 = 0 := by
  decide

theorem singlet_c13_aromatic : aromaticCount .singletC13 = 1 := by
  decide

theorem singlet_c13_antiaromatic : antiaromaticCount .singletC13 = 1 := by
  decide

/-- The eight blanks in answer-sheet order, packaged as one checked result. -/
theorem completed_table :
    (aromaticCount .c18, aromaticCount .c16,
     aromaticCount .tripletC13, aromaticCount .singletC13,
     antiaromaticCount .c18, antiaromaticCount .c16,
     antiaromaticCount .tripletC13, antiaromaticCount .singletC13) =
    (2, 0, 0, 1, 0, 2, 0, 1) := by
  rw [c18_aromatic, c18_antiaromatic, c16_aromatic, c16_antiaromatic,
    triplet_c13_aromatic, triplet_c13_antiaromatic,
    singlet_c13_aromatic, singlet_c13_antiaromatic]

#print axioms c18_aromatic
#print axioms c18_antiaromatic
#print axioms c16_aromatic
#print axioms c16_antiaromatic
#print axioms triplet_c13_aromatic
#print axioms triplet_c13_antiaromatic
#print axioms singlet_c13_aromatic
#print axioms singlet_c13_antiaromatic
#print axioms completed_table

end IChO2026Problems.IChO2026T6A1
