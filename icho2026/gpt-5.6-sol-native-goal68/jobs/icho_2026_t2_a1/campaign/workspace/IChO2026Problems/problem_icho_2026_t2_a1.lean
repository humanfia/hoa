import Mathlib

/-!
# IChO 2026, theory problem 2, part A1

The problem states that malonic acid, `CH₂(COOH)₂`, is oxidised to `CO₂`,
that `BrO₃⁻` is reduced to `Br⁻`, and that Ce(IV) is a catalyst.  This file
models exactly those species.  The molecular formulae and ionic charges in
`SourceData.formula` are parsed from the formulae printed in the problem;
the coefficients of the answer are not included there.

`Balanced` is the general conservation-of-atoms-and-charge condition.  The
main theorem checks the proposed equation against it.  The classification
theorem additionally derives the coefficient ratio from conservation, rather
than merely checking five preselected numbers.
-/

namespace IChO2026Problems.icho_2026_t2_a1

/-- Elements that occur in the species named in T2-A1. -/
inductive Element
  | carbon
  | hydrogen
  | oxygen
  | bromine
  | cerium
  deriving DecidableEq, Fintype, Repr

/-- Species occurring in the requested net ionic equation, together with the
Ce(IV) catalyst named by the statement. -/
inductive Species
  | malonicAcid
  | bromate
  | carbonDioxide
  | bromide
  | water
  | ceriumIV
  deriving DecidableEq, Fintype, Repr

/-- Atom counts and net electric charge of one formula unit. -/
structure Formula where
  atoms : Element → ℕ
  charge : ℤ

namespace SourceData

/-- Formula data read from the printed species names:

* `CH₂(COOH)₂ = C₃H₄O₄`;
* `BrO₃⁻`, `CO₂`, `Br⁻`, `H₂O`, and `Ce⁴⁺` have their displayed
  compositions and charges.

This is problem input (formula parsing), separate from the derived reaction
coefficients below.
-/
def formula : Species → Formula
  | .malonicAcid =>
      { atoms := fun
          | .carbon => 3
          | .hydrogen => 4
          | .oxygen => 4
          | .bromine => 0
          | .cerium => 0
        charge := 0 }
  | .bromate =>
      { atoms := fun
          | .carbon => 0
          | .hydrogen => 0
          | .oxygen => 3
          | .bromine => 1
          | .cerium => 0
        charge := -1 }
  | .carbonDioxide =>
      { atoms := fun
          | .carbon => 1
          | .hydrogen => 0
          | .oxygen => 2
          | .bromine => 0
          | .cerium => 0
        charge := 0 }
  | .bromide =>
      { atoms := fun
          | .carbon => 0
          | .hydrogen => 0
          | .oxygen => 0
          | .bromine => 1
          | .cerium => 0
        charge := -1 }
  | .water =>
      { atoms := fun
          | .carbon => 0
          | .hydrogen => 2
          | .oxygen => 1
          | .bromine => 0
          | .cerium => 0
        charge := 0 }
  | .ceriumIV =>
      { atoms := fun
          | .carbon => 0
          | .hydrogen => 0
          | .oxygen => 0
          | .bromine => 0
          | .cerium => 1
        charge := 4 }

end SourceData

/-- A reaction has whole-number stoichiometric coefficients on each side and
a separately recorded set of catalysts. -/
structure Reaction where
  reactantCoeff : Species → ℕ
  productCoeff : Species → ℕ
  catalysts : Finset Species

/-- Explicit exhaustive list of the finite species type. -/
def speciesList : List Species :=
  [.malonicAcid, .bromate, .carbonDioxide, .bromide, .water, .ceriumIV]

/-- Total atoms of an element on one side of a reaction. -/
def atomTotal (coeff : Species → ℕ) (e : Element) : ℕ :=
  (speciesList.map fun s => coeff s * (SourceData.formula s).atoms e).sum

/-- Total electric charge on one side of a reaction. -/
def chargeTotal (coeff : Species → ℕ) : ℤ :=
  (speciesList.map fun s => (coeff s : ℤ) * (SourceData.formula s).charge).sum

/-- The standard chemical balance law: every atom count and the total charge
are the same on the two sides. -/
def Balanced (r : Reaction) : Prop :=
  (∀ e : Element, atomTotal r.reactantCoeff e = atomTotal r.productCoeff e) ∧
    chargeTotal r.reactantCoeff = chargeTotal r.productCoeff

/-- The reaction shape fixed by the problem's stated endpoints.  The variables
are, in order, the coefficients of malonic acid, bromate, carbon dioxide,
bromide, and water.  Ce(IV) is recorded over the arrow as a catalyst and has no
net stoichiometric coefficient. -/
def overallShape (a b c d w : ℕ) : Reaction where
  reactantCoeff
    | .malonicAcid => a
    | .bromate => b
    | _ => 0
  productCoeff
    | .carbonDioxide => c
    | .bromide => d
    | .water => w
    | _ => 0
  catalysts := {.ceriumIV}

/-- Expanding `Balanced` for the problem's reaction shape gives exactly the
four independent atom-balance equations.  Charge balance is automatic once
bromine balance gives `b = d`, since bromate and bromide both have charge -1.
-/
theorem overallShape_balanced_iff (a b c d w : ℕ) :
    Balanced (overallShape a b c d w) ↔
      3 * a = c ∧
      4 * a = 2 * w ∧
      4 * a + 3 * b = 2 * c + w ∧
      b = d := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Balanced, atomTotal, speciesList, overallShape, SourceData.formula,
        Nat.mul_comm] using
        h.1 .carbon
    · simpa [Balanced, atomTotal, speciesList, overallShape, SourceData.formula,
        Nat.mul_comm] using
        h.1 .hydrogen
    · simpa [Balanced, atomTotal, speciesList, overallShape, SourceData.formula,
        Nat.mul_comm] using
        h.1 .oxygen
    · simpa [Balanced, atomTotal, speciesList, overallShape, SourceData.formula] using
        h.1 .bromine
  · rintro ⟨hC, hH, hO, hBr⟩
    constructor
    · intro e
      cases e <;>
        simp [atomTotal, speciesList, overallShape, SourceData.formula] <;>
        omega
    · simp [chargeTotal, speciesList, overallShape, SourceData.formula, hBr]

/-- Conservation alone forces every whole-number balanced equation with the
stated reactants and products to be an integer multiple of `(3,4,9,4,6)`.
-/
theorem balanced_overall_shape_classification
    {a b c d w : ℕ} (h : Balanced (overallShape a b c d w)) :
    ∃ k : ℕ,
      a = 3 * k ∧ b = 4 * k ∧ c = 9 * k ∧ d = 4 * k ∧ w = 6 * k := by
  rcases (overallShape_balanced_iff a b c d w).1 h with ⟨hC, hH, hO, hBr⟩
  have hRatio : 3 * b = 4 * a := by omega
  have hThreeDvdA : 3 ∣ a :=
    Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 4) ⟨b, hRatio.symm⟩
  rcases hThreeDvdA with ⟨k, rfl⟩
  exact ⟨k, rfl, by omega, by omega, by omega, by omega⟩

/-- In particular, any nonzero balanced equation of this shape has coefficients
at least `(3,4,9,4,6)` componentwise. -/
theorem least_positive_balanced_coefficients
    {a b c d w : ℕ} (h : Balanced (overallShape a b c d w)) (ha : 0 < a) :
    3 ≤ a ∧ 4 ≤ b ∧ 9 ≤ c ∧ 4 ≤ d ∧ 6 ≤ w := by
  rcases balanced_overall_shape_classification h with ⟨k, rfl, rfl, rfl, rfl, rfl⟩
  omega

/-- The derived overall BZ reaction:

`3 CH₂(COOH)₂ + 4 BrO₃⁻ ⟶ 9 CO₂ + 4 Br⁻ + 6 H₂O`,

with Ce(IV) recorded as catalyst.
-/
def bzReaction : Reaction := overallShape 3 4 9 4 6

/-- Requested output: the displayed BZ equation conserves every modelled atom
and total charge, and Ce(IV) is a catalyst with zero net coefficient. -/
theorem balanced_bz_equation :
    Balanced bzReaction ∧
    bzReaction.reactantCoeff .malonicAcid = 3 ∧
    bzReaction.reactantCoeff .bromate = 4 ∧
    bzReaction.productCoeff .carbonDioxide = 9 ∧
    bzReaction.productCoeff .bromide = 4 ∧
    bzReaction.productCoeff .water = 6 ∧
    .ceriumIV ∈ bzReaction.catalysts ∧
    bzReaction.reactantCoeff .ceriumIV = bzReaction.productCoeff .ceriumIV := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · apply (overallShape_balanced_iff 3 4 9 4 6).2
    norm_num
  · simp [bzReaction, overallShape]

/-- Among nonzero equations with the named support, the answer is the unique
componentwise-minimal balanced coefficient vector. -/
theorem bz_coefficients_are_the_minimum :
    Balanced bzReaction ∧
      ∀ {a b c d w : ℕ},
        Balanced (overallShape a b c d w) → 0 < a →
          bzReaction.reactantCoeff .malonicAcid ≤ a ∧
          bzReaction.reactantCoeff .bromate ≤ b ∧
          bzReaction.productCoeff .carbonDioxide ≤ c ∧
          bzReaction.productCoeff .bromide ≤ d ∧
          bzReaction.productCoeff .water ≤ w := by
  constructor
  · exact balanced_bz_equation.1
  · intro a b c d w h ha
    simpa [bzReaction, overallShape] using least_positive_balanced_coefficients h ha

end IChO2026Problems.icho_2026_t2_a1

#print axioms IChO2026Problems.icho_2026_t2_a1.balanced_bz_equation
#print axioms IChO2026Problems.icho_2026_t2_a1.balanced_overall_shape_classification
#print axioms IChO2026Problems.icho_2026_t2_a1.bz_coefficients_are_the_minimum
