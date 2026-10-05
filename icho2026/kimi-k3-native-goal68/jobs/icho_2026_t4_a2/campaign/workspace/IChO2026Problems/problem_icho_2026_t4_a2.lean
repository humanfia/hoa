import Mathlib

/-!
# IChO 2026, Problem T4 (The nuclear past of Uzbekistan), Part 4.2 (task `icho_2026_t4_a2`)

## Problem statement (official English, source page 37 of `theory_problem.pdf`)

"Neutrons that induce the chain reaction are produced by several ways:
a) Reaction of ¹¹B with α-particles inside the reactor core
b) Interaction of γ rays with ²D nuclei present in the reactor coolant water
c) Reaction of ⁹Be with α-particles produced in an externally installed neutron source.

**Write** the nuclear reaction equations for (a), (b), and (c). (3.0 pt)"

## Answers

* **(a)** ¹¹₅B + ⁴₂He → ¹⁴₇N + ¹₀n
* **(b)** ²₁D + γ → ¹₁H + ¹₀n  (photodisintegration of deuterium)
* **(c)** ⁹₄Be + ⁴₂He → ¹²₆C + ¹₀n  (the classic (α, n) neutron source)

In every case the reaction is dictated by the context: the given projectile
and target must react so that **a neutron ¹₀n is produced** (the prose
explicitly says these channels *produce* the chain-reaction neutrons);
balancing mass number `A` and atomic number `Z` then **forces** the residual
product nucleus: (a) residual `(14, 7)` = ¹⁴N; (b) residual `(1, 1)` = ¹H;
(c) residual `(12, 6)` = ¹²C. Hence the strictly balanced equations are
*uniquely determined* by the problem text plus conservation of mass number
and atomic number — no external answer key is needed.

## What is formalized

Nuclear-reaction balance is purely about the two conserved labels, so each
particle is modeled as a vector in `Fin 2 → ℤ` (index 0 = mass number `A`,
index 1 = atomic number `Z`). `Balanced` states that the sums over reactants
and products agree in both labels. The three displayed equations are proven
balanced (`reaction_a_balanced`, `reaction_b_balanced`,
`reaction_c_balanced`), and three uniqueness theorems
(`reaction_a_residual_forced`, `reaction_b_residual_forced`,
`reaction_c_residual_forced`) show that, given the dictated single-neutron
output, the residual product's `(A, Z)` is necessarily `(14, 7)`, `(1, 1)`
and `(12, 6)` respectively, i.e. ¹⁴N, ¹H and ¹²C. Only standard Lean/mathlib
logical axioms are used (`propext`, `Classical.choice`, `Quot.sound`); no
custom axioms, no `sorry`.
-/

namespace IChO2026T4

/-- A particle in a nuclear equation, given by its mass number `A` and atomic
number `Z`. Photons (γ rays) have `A = Z = 0`. Both are kept as `ℤ` so that
addition and subtraction in balance equations stay in a group. -/
structure Nuclide where
  A : ℤ
  Z : ℤ
  deriving Repr, DecidableEq

/-- Two nuclides with the same mass number and atomic number are equal. -/
@[ext] theorem Nuclide.ext {x y : Nuclide} (hA : x.A = y.A) (hZ : x.Z = y.Z) :
    x = y := by
  cases x; cases y; simp_all

/-- Neutron `¹₀n`. -/
def n_ : Nuclide := ⟨1, 0⟩

/-- α-particle, i.e. `⁴₂He`. -/
def α_ : Nuclide := ⟨4, 2⟩

/-- γ photon (no mass number and no charge). -/
def γ_ : Nuclide := ⟨0, 0⟩

/-- `¹¹₅B` (boron-11 target in reaction (a)). -/
def B11 : Nuclide := ⟨11, 5⟩

/-- `¹⁴₇N` (nitrogen-14, residual product of reaction (a)). -/
def N14 : Nuclide := ⟨14, 7⟩

/-- `²₁D` (deuteron target in reaction (b)). -/
def D2 : Nuclide := ⟨2, 1⟩

/-- `¹₁H` (proton, residual product of reaction (b)). -/
def H1 : Nuclide := ⟨1, 1⟩

/-- `⁹₄Be` (beryllium-9 target in reaction (c)). -/
def Be9 : Nuclide := ⟨9, 4⟩

/-- `¹²₆C` (carbon-12, residual product of reaction (c)). -/
def C12 : Nuclide := ⟨12, 6⟩

/-- The `(A, Z)` label vector of a particle. -/
def label (p : Nuclide) : Fin 2 → ℤ := ![p.A, p.Z]

/-- Conservation of mass number and atomic number across a reaction. -/
def Balanced (reactants products : List Nuclide) : Prop :=
  (reactants.map label).sum = (products.map label).sum

/-- A nuclear reaction: named channel with its reactants and products. -/
structure Reaction where
  name : String
  reactants : List Nuclide
  products : List Nuclide

/-- **Reaction (a)**: `¹¹B + α → ¹⁴N + ¹₀n`. -/
def reactionA : Reaction where
  name := "¹¹₅B + ⁴₂He → ¹⁴₇N + ¹₀n"
  reactants := [B11, α_]
  products := [N14, n_]

/-- **Reaction (b)**: `²D + γ → ¹H + ¹₀n`. -/
def reactionB : Reaction where
  name := "²₁D + γ → ¹₁H + ¹₀n"
  reactants := [D2, γ_]
  products := [H1, n_]

/-- **Reaction (c)**: `⁹Be + α → ¹²C + ¹₀n`. -/
def reactionC : Reaction where
  name := "⁹₄Be + ⁴₂He → ¹²₆C + ¹₀n"
  reactants := [Be9, α_]
  products := [C12, n_]

/-- Reaction (a) conserves mass number (11 + 4 = 14 + 1) and atomic number
(5 + 2 = 7 + 0). -/
theorem reaction_a_balanced :
    Balanced reactionA.reactants reactionA.products := by
  ext i; fin_cases i <;> decide

/-- Reaction (b) conserves mass number (2 + 0 = 1 + 1) and atomic number
(1 + 0 = 1 + 0). -/
theorem reaction_b_balanced :
    Balanced reactionB.reactants reactionB.products := by
  ext i; fin_cases i <;> decide

/-- Reaction (c) conserves mass number (9 + 4 = 12 + 1) and atomic number
(4 + 2 = 6 + 0). -/
theorem reaction_c_balanced :
    Balanced reactionC.reactants reactionC.products := by
  ext i; fin_cases i <;> decide

/-- **Uniqueness for (a)**: if `¹¹B + α → X + ¹₀n` is balanced, then `X` is
forced to be `¹⁴N` — the only possible second product when, as dictated, a
single neutron is emitted. -/
theorem reaction_a_residual_forced {X : Nuclide}
    (h : Balanced [B11, α_] [X, n_]) : X = N14 := by
  obtain ⟨a, z⟩ := X
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [label, B11, α_, n_] at h0 h1
  have ha : a = 14 := by omega
  have hz : z = 7 := by omega
  subst ha; subst hz
  rfl

/-- **Uniqueness for (b)**: if `²D + γ → X + ¹₀n` is balanced, then `X` is
forced to be `¹H` (a proton) — the photodisintegration of the deuteron. -/
theorem reaction_b_residual_forced {X : Nuclide}
    (h : Balanced [D2, γ_] [X, n_]) : X = H1 := by
  obtain ⟨a, z⟩ := X
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [label, D2, γ_, n_] at h0 h1
  have ha : a = 1 := by omega
  have hz : z = 1 := by omega
  subst ha; subst hz
  rfl

/-- **Uniqueness for (c)**: if `⁹Be + α → X + ¹₀n` is balanced, then `X` is
forced to be `¹²C` — the classic (α, n) neutron-source reaction. -/
theorem reaction_c_residual_forced {X : Nuclide}
    (h : Balanced [Be9, α_] [X, n_]) : X = C12 := by
  obtain ⟨a, z⟩ := X
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [label, Be9, α_, n_] at h0 h1
  have ha : a = 12 := by omega
  have hz : z = 6 := by omega
  subst ha; subst hz
  rfl

end IChO2026T4
