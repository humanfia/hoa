import Physlib.Units.Dimension

/-!
# Chemical dimensions

This module extends Physlib's physical dimensions by one rational exponent for
amount of substance.  Its source references are
`IUPAC-GOLDBOOK-5.0.0:A00295 definition 1`,
`IUPAC-GOLDBOOK-5.0.0:E02283 displayed extent identity`, and
`IUPAC-GOLDBOOK-5.0.0:R05156 displayed rate identities`, together with the
sanitized build-corpus items `icho_2026_t2_a2:T2-A2`,
`icho_2026_t3_a7:T3-A7`, `icho_2026_t4_a6:T4-A6`, and
`icho_2026_t7_a3:T7-A3`.
-/

namespace Chemlib.Units

/-- A physical dimension together with its amount-of-substance exponent. -/
structure ChemicalDimension : Type where
  physical : _root_.Dimension
  amount : ℚ

namespace ChemicalDimension

/-- Chemical dimensions form a commutative group componentwise. -/
instance instCommGroup : CommGroup ChemicalDimension where
  one := ⟨1, 0⟩
  mul x y := ⟨x.physical * y.physical, x.amount + y.amount⟩
  inv x := ⟨x.physical⁻¹, -x.amount⟩
  mul_assoc := by
    intro x y z
    rcases x with ⟨xp, xa⟩
    rcases y with ⟨yp, ya⟩
    rcases z with ⟨zp, za⟩
    change ⟨(xp * yp) * zp, (xa + ya) + za⟩ =
      (⟨xp * (yp * zp), xa + (ya + za)⟩ : ChemicalDimension)
    rw [mul_assoc, add_assoc]
  one_mul := by
    intro x
    rcases x with ⟨xp, xa⟩
    change ⟨1 * xp, 0 + xa⟩ = (⟨xp, xa⟩ : ChemicalDimension)
    rw [one_mul, zero_add]
  mul_one := by
    intro x
    rcases x with ⟨xp, xa⟩
    change ⟨xp * 1, xa + 0⟩ = (⟨xp, xa⟩ : ChemicalDimension)
    rw [mul_one, add_zero]
  inv_mul_cancel := by
    intro x
    rcases x with ⟨xp, xa⟩
    change ⟨xp⁻¹ * xp, -xa + xa⟩ = (⟨1, 0⟩ : ChemicalDimension)
    rw [inv_mul_cancel, neg_add_cancel]
  mul_comm := by
    intro x y
    rcases x with ⟨xp, xa⟩
    rcases y with ⟨yp, ya⟩
    change ⟨xp * yp, xa + ya⟩ = (⟨yp * xp, ya + xa⟩ : ChemicalDimension)
    rw [mul_comm, add_comm]

/-- Forget the amount exponent, retaining the Physlib dimension. -/
def physicalDimension : ChemicalDimension →* _root_.Dimension where
  toFun := physical
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Read the amount exponent as a multiplicative form of an additive rational. -/
def amountExponent : ChemicalDimension →* Multiplicative ℚ where
  toFun d := Multiplicative.ofAdd d.amount
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Embed a Physlib dimension with zero amount-of-substance exponent. -/
def ofPhyslib : _root_.Dimension →* ChemicalDimension where
  toFun d := ⟨d, 0⟩
  map_one' := rfl
  map_mul' x y := by
    change ⟨x * y, 0⟩ = (⟨x * y, 0 + 0⟩ : ChemicalDimension)
    rw [add_zero]

/-- The base dimension of amount of substance. -/
def amountOfSubstance : ChemicalDimension := ⟨1, 1⟩

/-- Volume, lifted from Physlib. -/
def volume : ChemicalDimension := ofPhyslib (_root_.Dimension.L𝓭 ^ 3)

/-- Time, lifted from Physlib. -/
def time : ChemicalDimension := ofPhyslib _root_.Dimension.T𝓭

/-- Amount concentration: amount of substance per volume. -/
def amountConcentration : ChemicalDimension := amountOfSubstance / volume

/-- Rate of extent: amount of substance per time. -/
def extentRate : ChemicalDimension := amountOfSubstance / time

/-- Reaction rate: rate of extent per volume. -/
def reactionRate : ChemicalDimension := extentRate / volume

theorem amountOfSubstance_physical : amountOfSubstance.physical = 1 := rfl

theorem amountOfSubstance_amount : amountOfSubstance.amount = 1 := rfl

theorem ofPhyslib_physical : (d : _root_.Dimension) → (ofPhyslib d).physical = d :=
  by simp [ofPhyslib]

theorem ofPhyslib_amount : (d : _root_.Dimension) → (ofPhyslib d).amount = 0 :=
  by simp [ofPhyslib]

theorem volume_eq_ofPhyslib : volume = ofPhyslib (_root_.Dimension.L𝓭 ^ 3) := rfl

theorem time_eq_ofPhyslib : time = ofPhyslib _root_.Dimension.T𝓭 := rfl

theorem amountConcentration_eq : amountConcentration = amountOfSubstance / volume := rfl

theorem extentRate_eq : extentRate = amountOfSubstance / time := rfl

theorem reactionRate_eq : reactionRate = extentRate / volume := rfl

end ChemicalDimension

end Chemlib.Units
