import Mathlib

/-!
# IChO 2026, Problem T2, Subquestion 2.1 (target `icho_2026_t2_a1`)

**Problem statement (verbatim from the official English problem sheet, page Q2-1):**

> **Write** the overall balanced reaction equation of the Belousov–Zhabotinsky
> reaction (BZ reaction). Note: in this reaction, MA is oxidised to CO₂, BrO₃⁻
> is reduced to Br⁻, and Ce(IV) is a catalyst. (2.0 pt)

Shared context (page Q2-1): the chemicals mixed are KBrO₃, CH₂(COOH)₂
(malonic acid, abbreviated MA), Ce(SO₄)₂, and H₂SO₄.

## Problem-derived inputs (chemical semantics)

* MA is malonic acid, CH₂(COOH)₂ = **C₃H₄O₄** (stated in the shared context).
* MA is completely **oxidised to CO₂** (stated in the note).
* **BrO₃⁻ is reduced to Br⁻** (stated in the note).
* **Ce(IV) is a catalyst** (stated in the note), hence cerium is regenerated
  and does not appear in the *overall* equation.
* The medium is strongly acidic (H₂SO₄ is a reactant environment), so the
  half-reactions are balanced with H⁺/H₂O.

## Derivation of the stoichiometry (oxidation-number method)

Oxidation half-reaction (C in C₃H₄O₄ has oxidation number +4/3, in CO₂ it is
+4, so the three carbons release 8 electrons in total):

  C₃H₄O₄ + 2 H₂O → 3 CO₂ + 8 H⁺ + 8 e⁻

Reduction half-reaction (Br goes from +5 in BrO₃⁻ to −1 in Br⁻, taking up
6 electrons):

  BrO₃⁻ + 6 H⁺ + 6 e⁻ → Br⁻ + 3 H₂O

With lcm(8, 6) = 24, taking 3 copies of the oxidation and 4 copies of the
reduction and cancelling 24 H⁺ and 6 H₂O gives the overall equation

  **3 CH₂(COOH)₂ + 4 BrO₃⁻ → 9 CO₂ + 4 Br⁻ + 6 H₂O**

which this file encodes as a balanced `Reaction` over the elements
`C, H, O, Br` and proves balanced in atoms *and* charge, with no custom
axioms.  (Protons appear in the half-reactions but cancel in the overall
equation.)
-/

namespace IChO2026

/-- The elements occurring in the BZ overall equation. -/
inductive BZElement
  | C | H | O | Br
  deriving DecidableEq, Repr

open BZElement

/-- A chemical species as an element-count vector together with its net
charge (in units of the elementary charge). -/
structure BZSpecies where
  count : BZElement → ℤ
  charge : ℤ

/-- Malonic acid MA = CH₂(COOH)₂ = C₃H₄O₄, a neutral molecule. -/
def MA : BZSpecies where
  count := fun | C => 3 | H => 4 | O => 4 | Br => 0
  charge := 0

/-- Bromate ion, BrO₃⁻. -/
def BrO3 : BZSpecies where
  count := fun | C => 0 | H => 0 | O => 3 | Br => 1
  charge := -1

/-- Carbon dioxide, CO₂, neutral. -/
def CO2 : BZSpecies where
  count := fun | C => 1 | H => 0 | O => 2 | Br => 0
  charge := 0

/-- Bromide ion, Br⁻. -/
def BrIon : BZSpecies where
  count := fun | C => 0 | H => 0 | O => 0 | Br => 1
  charge := -1

/-- Water, H₂O, neutral. -/
def H2O : BZSpecies where
  count := fun | C => 0 | H => 2 | O => 1 | Br => 0
  charge := 0

/-- A reaction: stoichiometric coefficients (natural numbers) on the
left-hand side and the right-hand side. -/
structure Reaction where
  lhs : List (ℕ × BZSpecies)
  rhs : List (ℕ × BZSpecies)

/-- Total count of element `e` on one side of a reaction. -/
def elementTotal (e : BZElement) (side : List (ℕ × BZSpecies)) : ℤ :=
  side.foldl (fun acc (n, s) => acc + n * s.count e) 0

/-- Total charge on one side of a reaction. -/
def chargeTotal (side : List (ℕ × BZSpecies)) : ℤ :=
  side.foldl (fun acc (n, s) => acc + n * s.charge) 0

/-- A reaction is balanced iff every element is conserved and charge is
conserved.  Coefficients are also required to be nonzero, so every listed
reactant and product genuinely appears in the equation. -/
def Reaction.IsBalanced (r : Reaction) : Prop :=
  (∀ e : BZElement, elementTotal e r.lhs = elementTotal e r.rhs) ∧
    chargeTotal r.lhs = chargeTotal r.rhs ∧
    (∀ p ∈ r.lhs, p.1 ≠ 0) ∧ (∀ p ∈ r.rhs, p.1 ≠ 0)

/-- The overall BZ reaction as stated in the problem, with the stoichiometric
coefficients derived by the half-reaction method:

    3 CH₂(COOH)₂ + 4 BrO₃⁻ → 9 CO₂ + 4 Br⁻ + 6 H₂O  -/
def overallBZ : Reaction where
  lhs := [(3, MA), (4, BrO3)]
  rhs := [(9, CO2), (4, BrIon), (6, H2O)]

/-- The overall BZ equation is balanced: every element C, H, O, Br is
conserved, and so is the electric charge. -/
theorem overallBZ_isBalanced : overallBZ.IsBalanced := by
  refine ⟨fun e => ?_, ?_, ?_, ?_⟩
  · cases e <;> rfl
  · rfl
  · intro p hp
    fin_cases hp <;> decide
  · intro p hp
    fin_cases hp <;> decide

/-- Atom balance, spelled out element by element as concrete integer
identities (carbon: 3·3 = 9·1, hydrogen: 3·4 = 6·2, oxygen:
3·4 + 4·3 = 9·2 + 6·1, bromine: 4·1 = 4·1). -/
theorem overallBZ_atom_balance :
    3 * 3 = 9 * 1
    ∧ 3 * 4 = 6 * 2
    ∧ 3 * 4 + 4 * 3 = 9 * 2 + 6 * 1
    ∧ 4 * 1 = 4 * 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Charge balance of the overall equation: 4·(−1) = 4·(−1). -/
theorem overallBZ_charge_balance : 4 * (-1 : ℤ) = 4 * (-1 : ℤ) := rfl

/-- The oxidation half-reaction for malonic acid,

    C₃H₄O₄ + 2 H₂O → 3 CO₂ + 8 H⁺ + 8 e⁻,

is balanced in atoms (C: 3 = 3, H: 4 + 4 = 8, O: 4 + 2 = 6) and in charge
(0 = 8·(+1) + 8·(−1)). -/
theorem oxidation_half_reaction_balance :
    (3 : ℤ) = 3
    ∧ 4 + 2 * 2 = 8
    ∧ 4 + 2 * 1 = 3 * 2
    ∧ (0 : ℤ) = 8 * 1 + 8 * (-1) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The reduction half-reaction for bromate,

    BrO₃⁻ + 6 H⁺ + 6 e⁻ → Br⁻ + 3 H₂O,

is balanced in atoms (Br: 1 = 1, H: 6 = 6, O: 3 = 3) and in charge
(−1 + 6·(+1) + 6·(−1) = −1). -/
theorem reduction_half_reaction_balance :
    (1 : ℤ) = 1
    ∧ 6 = 3 * 2
    ∧ (3 : ℤ) = 3 * 1
    ∧ (-1 : ℤ) + 6 * 1 + 6 * (-1) = -1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Electron ledger.**  The least common multiple of the 8 electrons
released per malonic acid and the 6 electrons consumed per bromate is 24,
giving the multiplicities 24/8 = 3 (for MA) and 24/6 = 4 (for BrO₃⁻) used
in the overall equation. -/
theorem electron_lcm :
    Nat.lcm 8 6 = 24 ∧ 8 * 3 = 24 ∧ 6 * 4 = 24 :=
  ⟨rfl, rfl, rfl⟩

/-- Cerium is a catalyst: it is unchanged by the overall reaction, so its
coefficient is zero on both sides.  Encoded here as the tautology 0 = 0 for
the Ce balance row — Ce appears in neither `overallBZ.lhs` nor
`overallBZ.rhs`, as the problem stipulates that Ce(IV) is a catalyst. -/
theorem cerium_is_catalyst_balance :
    (0 : ℤ) = 0 := rfl

end IChO2026

#print axioms IChO2026.overallBZ_isBalanced
#print axioms IChO2026.overallBZ_atom_balance
#print axioms IChO2026.overallBZ_charge_balance
#print axioms IChO2026.oxidation_half_reaction_balance
#print axioms IChO2026.reduction_half_reaction_balance
#print axioms IChO2026.electron_lcm
