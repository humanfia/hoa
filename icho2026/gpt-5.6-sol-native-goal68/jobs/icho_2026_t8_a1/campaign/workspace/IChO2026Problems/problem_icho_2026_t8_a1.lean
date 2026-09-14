import Mathlib

/-!
# IChO 2026, problem 8.1

The problem asks for the reduction half-equation from carbon dioxide to carbon
monoxide in acidic medium.  We model exactly the five species allowed by that
half-equation: `CO₂`, `H⁺`, `e⁻`, `CO`, and `H₂O`.  The atom counts and
charges below are problem inputs / formula semantics; the submitted
coefficients and every balance or uniqueness fact are derived from them.
-/

namespace IChO2026Problems.ProblemIChO2026T8A1

/-- Elements that occur in the requested half-equation. -/
inductive Element
  | carbon
  | hydrogen
  | oxygen
  deriving DecidableEq, Repr

/-- Species admitted by the standard acidic-medium half-equation template for
`CO₂ → CO`.  Electrons are included as charge-balancing particles. -/
inductive Species
  | carbonDioxide
  | proton
  | electron
  | carbonMonoxide
  | water
  deriving DecidableEq, Repr

/-- Formula semantics for the species printed in, or required by, the prompt. -/
def atomCount : Species → Element → ℕ
  | .carbonDioxide, .carbon => 1
  | .carbonDioxide, .hydrogen => 0
  | .carbonDioxide, .oxygen => 2
  | .proton, .carbon => 0
  | .proton, .hydrogen => 1
  | .proton, .oxygen => 0
  | .electron, _ => 0
  | .carbonMonoxide, .carbon => 1
  | .carbonMonoxide, .hydrogen => 0
  | .carbonMonoxide, .oxygen => 1
  | .water, .carbon => 0
  | .water, .hydrogen => 2
  | .water, .oxygen => 1

/-- Integer electric charges of the five species. -/
def charge : Species → ℤ
  | .carbonDioxide => 0
  | .proton => 1
  | .electron => -1
  | .carbonMonoxide => 0
  | .water => 0

/-- Coefficients in the reaction scheme
`a CO₂ + b H⁺ + c e⁻ → d CO + e H₂O`.

The sides of every species are fixed by the requested direction (reduction)
and by the acidic-medium balancing species. -/
structure HalfEquation where
  co2 : ℕ
  protons : ℕ
  electrons : ℕ
  co : ℕ
  water : ℕ
  deriving DecidableEq, Repr

/-- Total number of atoms of `el` on the reactant side. -/
def reactantAtoms (q : HalfEquation) (el : Element) : ℕ :=
  q.co2 * atomCount .carbonDioxide el +
  q.protons * atomCount .proton el +
  q.electrons * atomCount .electron el

/-- Total number of atoms of `el` on the product side. -/
def productAtoms (q : HalfEquation) (el : Element) : ℕ :=
  q.co * atomCount .carbonMonoxide el +
  q.water * atomCount .water el

/-- Total charge on the reactant side. -/
def reactantCharge (q : HalfEquation) : ℤ :=
  (q.co2 : ℤ) * charge .carbonDioxide +
  (q.protons : ℤ) * charge .proton +
  (q.electrons : ℤ) * charge .electron

/-- Total charge on the product side. -/
def productCharge (q : HalfEquation) : ℤ :=
  (q.co : ℤ) * charge .carbonMonoxide +
  (q.water : ℤ) * charge .water

/-- Atom and charge conservation for a half-equation. -/
structure Balanced (q : HalfEquation) : Prop where
  atoms : ∀ el, reactantAtoms q el = productAtoms q el
  charge : reactantCharge q = productCharge q

/-- The candidate derived by balancing O with one water, H with two protons,
and charge with two reactant electrons. -/
def submittedHalfEquation : HalfEquation where
  co2 := 1
  protons := 2
  electrons := 2
  co := 1
  water := 1

/-- Every element is conserved by the submitted equation. -/
theorem submitted_atom_balance (el : Element) :
    reactantAtoms submittedHalfEquation el =
      productAtoms submittedHalfEquation el := by
  cases el <;> decide

/-- Electric charge is conserved: the two protons and two electrons give zero
net charge on the left, matching the neutral products. -/
theorem submitted_charge_balance :
    reactantCharge submittedHalfEquation =
      productCharge submittedHalfEquation := by
  decide

/-- The requested equation is fully balanced. -/
theorem submittedHalfEquation_balanced : Balanced submittedHalfEquation := by
  exact ⟨submitted_atom_balance, submitted_charge_balance⟩

/-- The equation explicitly consumes two electrons, so it is written in the
reduction direction. -/
theorem submittedHalfEquation_isReduction :
    submittedHalfEquation.electrons = 2 ∧ 0 < submittedHalfEquation.electrons := by
  decide

/-- Conservation determines every coefficient uniquely once the coefficient
of CO₂ is normalized to one.  Thus the displayed equation is not merely one
balanced candidate: it is the unique normalized equation in this acidic
half-equation template. -/
theorem balanced_normalized_unique (q : HalfEquation)
    (hco2 : q.co2 = 1) (hbal : Balanced q) :
    q = submittedHalfEquation := by
  have hC := hbal.atoms .carbon
  have hH := hbal.atoms .hydrogen
  have hO := hbal.atoms .oxygen
  have hQ := hbal.charge
  simp [reactantAtoms, productAtoms, atomCount] at hC hH hO
  simp [reactantCharge, productCharge, charge] at hQ
  have hco : q.co = 1 := by omega
  have hwater : q.water = 1 := by omega
  have hprotons : q.protons = 2 := by omega
  have hprotonsZ : (q.protons : ℤ) = 2 := by exact_mod_cast hprotons
  have helectronsZ : (q.electrons : ℤ) = 2 := by omega
  have helectrons : q.electrons = 2 := by exact_mod_cast helectronsZ
  cases q
  simp_all [submittedHalfEquation]

/-- Final formal answer to T8-A1: the normalized coefficients are
`(1, 2, 2, 1, 1)`, the equation is balanced, and it consumes two electrons. -/
theorem icho_2026_t8_a1 :
    submittedHalfEquation =
        { co2 := 1, protons := 2, electrons := 2, co := 1, water := 1 } ∧
      Balanced submittedHalfEquation ∧
      submittedHalfEquation.electrons = 2 := by
  exact ⟨rfl, submittedHalfEquation_balanced, rfl⟩

#print axioms submittedHalfEquation_balanced
#print axioms submittedHalfEquation_isReduction
#print axioms balanced_normalized_unique
#print axioms icho_2026_t8_a1

end IChO2026Problems.ProblemIChO2026T8A1
