import Mathlib
set_option backward.isDefEq.respectTransparency false

namespace TriangleGame

/-- A triangle, viewed as the multiset of its three interior angles (in degrees):
positive reals summing to `180`. -/
def IsTriangle (s : Multiset ℝ) : Prop :=
  s.card = 3 ∧ (∀ x ∈ s, 0 < x) ∧ s.sum = 180

/-- A triangle `s` has an interior angle equal to `θ`. -/
def HasAngle (θ : ℝ) (s : Multiset ℝ) : Prop := θ ∈ s

/-- One admissible cut of the triangle `s`, producing children `L` and `R`.

We pick an apex angle `α` and the two base angles `β, γ` (so `s = {α, β, γ}`), and a
cut parameter `x` in the open interval `(γ, 180 - β)`. The resulting two triangles
have angle multisets `L = {β, x, 180 - β - x}` and `R = {γ, 180 - x, x - γ}`.
Ranging over all `α, β, γ` with `s = {α, β, γ}` captures all three apex choices and
both assignments of the two base angles. -/
def IsCut (s L R : Multiset ℝ) : Prop :=
  ∃ α β γ x : ℝ,
    s = {α, β, γ} ∧ γ < x ∧ x < 180 - β ∧
      L = {β, x, 180 - β - x} ∧ R = {γ, 180 - x, x - γ}

/-- The set of triangles from which Mulan can force, in finitely many steps, a
triangle with an interior angle equal to `θ`, no matter how Shan-Yu discards.

This is the least predicate closed under:
* (`win`) if the current triangle already has an angle equal to `θ`, Mulan has won;
* (`move`) if Mulan can make a cut producing children `L` and `R` from *both* of
  which she wins (so whichever one Shan-Yu keeps, she still wins), then she wins
  from the current triangle.

Membership means Mulan wins in finitely many steps. -/
inductive MulanWins (θ : ℝ) : Multiset ℝ → Prop
  | win {s : Multiset ℝ} (h : HasAngle θ s) : MulanWins θ s
  | move {s L R : Multiset ℝ} (hcut : IsCut s L R)
      (hL : MulanWins θ L) (hR : MulanWins θ R) : MulanWins θ s

/-- Mulan can guarantee victory for the value `θ`: from every valid starting
triangle she wins in finitely many steps regardless of Shan-Yu's play. -/
def MulanCanGuarantee (θ : ℝ) : Prop :=
  ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s

/-- **Main theorem.** For `0 < θ < 180`, Mulan can guarantee her victory in finitely
many steps, no matter how Shan-Yu plays, if and only if `θ = 180 / n` for some
integer `n ≥ 2`. -/
theorem main_theorem (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  sorry

end TriangleGame
