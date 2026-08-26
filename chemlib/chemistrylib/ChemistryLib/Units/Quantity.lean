import ChemistryLib.Units.ChemicalDimension

/-!
# Dimension-indexed chemical quantities

This module represents the numerical value of a chemical quantity while its
`ChemicalDimension` is tracked by the type.  Multiplication and division of
values follow multiplication and division of their dimensions, and subtype
aliases record nonnegative or strictly positive domains.

The chemical interpretation is grounded in
`IUPAC-GOLDBOOK-5.0.0:A00295 definition 1` and
`IUPAC-GOLDBOOK-5.0.0:R05156 definition 1`, together with the sanitized
build-corpus items `icho_2026_t2_a2:T2-A2`, `icho_2026_t3_a7:T3-A7`,
`icho_2026_t4_a7:T4-A7`, and `icho_2026_t7_a3:T7-A3`.
-/

namespace ChemistryLib.Units

/-- A real numerical value carrying a chemical dimension at the type level. -/
structure Quantity (d : ChemicalDimension) : Type where
  value : ℝ

namespace Quantity

/-- Equip a real number with a specified chemical dimension. -/
def ofReal (d : ChemicalDimension) (x : ℝ) : Quantity d :=
  ⟨x⟩

/-- Scale a quantity without changing its dimension. -/
def scale {d : ChemicalDimension} (a : ℝ) (q : Quantity d) : Quantity d :=
  ⟨a * q.value⟩

theorem scale_value {d : ChemicalDimension} (a : ℝ) (q : Quantity d) :
    (scale a q).value = a * q.value :=
  rfl

/-- Multiply quantities and multiply their dimensions. -/
def mul {d e : ChemicalDimension} (x : Quantity d) (y : Quantity e) :
    Quantity (d * e) :=
  ⟨x.value * y.value⟩

theorem mul_value {d e : ChemicalDimension} (x : Quantity d) (y : Quantity e) :
    (mul x y).value = x.value * y.value :=
  rfl

/-- Divide quantities and divide their dimensions. -/
noncomputable def div {d e : ChemicalDimension} (x : Quantity d) (y : Quantity e) :
    Quantity (d / e) :=
  ⟨x.value / y.value⟩

theorem div_value {d e : ChemicalDimension} (x : Quantity d) (y : Quantity e) :
    (div x y).value = x.value / y.value :=
  rfl

end Quantity

/-- A dimension-indexed quantity whose value is nonnegative. -/
abbrev NonnegativeQuantity (d : ChemicalDimension) : Type :=
  {q : Quantity d // 0 ≤ q.value}

namespace NonnegativeQuantity

/-- Construct a nonnegative quantity from a nonnegative real value. -/
def ofReal {d : ChemicalDimension} (x : ℝ) (hx : 0 ≤ x) :
    NonnegativeQuantity d :=
  ⟨Quantity.ofReal d x, hx⟩

end NonnegativeQuantity

/-- A dimension-indexed quantity whose value is strictly positive. -/
abbrev PositiveQuantity (d : ChemicalDimension) : Type :=
  {q : Quantity d // 0 < q.value}

namespace PositiveQuantity

/-- Construct a positive quantity from a strictly positive real value. -/
def ofReal {d : ChemicalDimension} (x : ℝ) (hx : 0 < x) :
    PositiveQuantity d :=
  ⟨Quantity.ofReal d x, hx⟩

end PositiveQuantity

end ChemistryLib.Units
