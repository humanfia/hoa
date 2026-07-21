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
  have triple_rotate (a b c : ℝ) :
      ({a, b, c} : Multiset ℝ) = {b, c, a} := by
    calc
      {a, b, c} = {b, a, c} := Multiset.cons_swap a b {c}
      _ = {b, c, a} := congrArg (fun t : Multiset ℝ => b ::ₘ t)
        (Multiset.cons_swap a c 0)

  have triple_reverse (a b c : ℝ) :
      ({a, b, c} : Multiset ℝ) = {c, b, a} := by
    calc
      {a, b, c} = {b, c, a} := triple_rotate a b c
      _ = {c, b, a} := Multiset.cons_swap b c {a}

  have cut_preserves_triangles {s L R : Multiset ℝ}
      (hs : IsTriangle s) (hcut : IsCut s L R) : IsTriangle L ∧ IsTriangle R := by
    rcases hcut with ⟨α, β, γ, x, rfl, hγx, hxβ, rfl, rfl⟩
    rcases hs with ⟨-, hpos, hsum⟩
    have hα : 0 < α := hpos α (by simp)
    have hβ : 0 < β := hpos β (by simp)
    have hγ : 0 < γ := hpos γ (by simp)
    constructor
    · refine ⟨by simp, ?_, ?_⟩
      intro y hy
      have hy' : y = β ∨ y = x ∨ y = 180 - β - x := by simpa using hy
      rcases hy' with hy | hy | hy
      · rw [hy]
        exact hβ
      · rw [hy]
        linarith
      · rw [hy]
        linarith
      · simp only [Multiset.insert_eq_cons, Multiset.sum_cons,
          Multiset.sum_singleton]
        ring
    · refine ⟨by simp, ?_, ?_⟩
      intro y hy
      have hy' : y = γ ∨ y = 180 - x ∨ y = x - γ := by simpa using hy
      rcases hy' with hy | hy | hy
      · rw [hy]
        exact hγ
      · rw [hy]
        linarith
      · rw [hy]
        linarith
      · simp only [Multiset.insert_eq_cons, Multiset.sum_cons,
          Multiset.sum_singleton]
        ring

  have wins_integer_invariant {θ : ℝ} {s : Multiset ℝ}
      (hw : MulanWins θ s) (hs : IsTriangle s) :
      (∃ k : ℤ, (k : ℝ) * θ ∈ s) ∨ ∃ k : ℤ, 180 = (k : ℝ) * θ := by
    revert hs
    induction hw with
    | win h =>
        intro hs
        left
        refine ⟨1, ?_⟩
        simpa [HasAngle] using h
    | @move s L R hcut hL hR ihL ihR =>
        intro hs
        have hchildren := cut_preserves_triangles hs hcut
        rcases ihL hchildren.1 with hLint | htotal
        · rcases ihR hchildren.2 with hRint | htotal
          · rcases hcut with ⟨α, β, γ, x, hsrep, hγx, hxβ, hLrep, hRrep⟩
            rw [hLrep] at hLint
            rw [hRrep] at hRint
            rcases hLint with ⟨m, hm⟩
            rcases hRint with ⟨k, hk⟩
            have hm' : (m : ℝ) * θ = β ∨ (m : ℝ) * θ = x ∨
                (m : ℝ) * θ = 180 - β - x := by
              simpa using hm
            have hk' : (k : ℝ) * θ = γ ∨ (k : ℝ) * θ = 180 - x ∨
                (k : ℝ) * θ = x - γ := by
              simpa using hk
            rcases hm' with hmβ | hmx | hmrest
            · left
              refine ⟨m, ?_⟩
              rw [hsrep]
              simp [hmβ]
            · rcases hk' with hkγ | hkrest | hkdiff
              · left
                refine ⟨k, ?_⟩
                rw [hsrep]
                simp [hkγ]
              · right
                refine ⟨m + k, ?_⟩
                push_cast
                linarith
              · left
                refine ⟨m - k, ?_⟩
                rw [hsrep]
                have heq : ((m : ℝ) - (k : ℝ)) * θ = γ := by linarith
                simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                  Multiset.mem_singleton]
                push_cast
                exact Or.inr (Or.inr heq)
            · rcases hk' with hkγ | hkrest | hkdiff
              · left
                refine ⟨k, ?_⟩
                rw [hsrep]
                simp [hkγ]
              · left
                refine ⟨k - m, ?_⟩
                rw [hsrep]
                have heq : ((k : ℝ) - (m : ℝ)) * θ = β := by linarith
                simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                  Multiset.mem_singleton]
                push_cast
                exact Or.inr (Or.inl heq)
              · left
                refine ⟨m + k, ?_⟩
                rw [hsrep]
                rcases hs with ⟨-, -, hsum⟩
                rw [hsrep] at hsum
                have habc : α + β + γ = 180 := by
                  simpa [add_assoc] using hsum
                have heq : ((m : ℝ) + (k : ℝ)) * θ = α := by linarith
                simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                  Multiset.mem_singleton]
                push_cast
                exact Or.inl heq
          · exact Or.inr htotal
        · exact Or.inr htotal

  have wins_of_nat_multiple_angle (θ : ℝ) (hθ : 0 < θ) :
      ∀ m : ℕ, 1 ≤ m → ∀ β γ : ℝ,
        0 < β → 0 < γ → (m : ℝ) * θ + β + γ = 180 →
        MulanWins θ {(m : ℝ) * θ, β, γ} := by
    intro m
    induction m with
    | zero =>
        intro hm
        omega
    | succ m ih =>
        intro hm β γ hβ hγ hsum
        by_cases hm0 : m = 0
        · subst m
          apply MulanWins.win
          simp [HasAngle]
        · have hmpos : 1 ≤ m := by omega
          have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
          have hmθ : 0 < (m : ℝ) * θ := mul_pos hmreal hθ
          have hsucc : ((Nat.succ m : ℕ) : ℝ) * θ = (m : ℝ) * θ + θ := by
            push_cast
            ring
          have hx : γ + θ < 180 - β := by
            rw [hsucc] at hsum
            linarith
          have hsum' : (m : ℝ) * θ + β + (γ + θ) = 180 := by
            rw [hsucc] at hsum
            linarith
          apply MulanWins.move
            (L := {(m : ℝ) * θ, β, γ + θ})
            (R := {θ, γ, 180 - (γ + θ)})
          · refine ⟨((Nat.succ m : ℕ) : ℝ) * θ, β, γ, γ + θ,
                rfl, by linarith, hx, ?_, ?_⟩
            · have hlast : 180 - β - (γ + θ) = (m : ℝ) * θ := by
                linarith
              rw [hlast]
              exact triple_rotate ((m : ℝ) * θ) β (γ + θ)
            · have hlast : γ + θ - γ = θ := by ring
              rw [hlast]
              exact triple_rotate θ γ (180 - (γ + θ))
          · exact ih hmpos β (γ + θ) hβ (by linarith) hsum'
          · apply MulanWins.win
            simp [HasAngle]

  have wins_small_cut (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (hn : 2 ≤ n)
      (htotal : (n : ℝ) * θ = 180) (α β γ : ℝ)
      (hγsmall : 0 < γ ∧ γ < θ) (hβsmall : β < 180 - θ) :
      MulanWins θ {α, β, γ} := by
    have hn1 : 1 ≤ n := by omega
    have hnsub : 1 ≤ n - 1 := by omega
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1]
      norm_num
    have hmultiple : ((n - 1 : ℕ) : ℝ) * θ = 180 - θ := by
      rw [hcast]
      calc
        ((n : ℝ) - 1) * θ = (n : ℝ) * θ - θ := by ring
        _ = 180 - θ := by rw [htotal]
    apply MulanWins.move
      (L := {β, θ, 180 - β - θ})
      (R := {((n - 1 : ℕ) : ℝ) * θ, γ, θ - γ})
    · refine ⟨α, β, γ, θ, rfl, hγsmall.2, by linarith, rfl, ?_⟩
      rw [hmultiple]
      exact Multiset.cons_swap (180 - θ) γ {θ - γ}
    · apply MulanWins.win
      simp [HasAngle]
    · apply wins_of_nat_multiple_angle θ hθ (n - 1) hnsub γ (θ - γ)
      · exact hγsmall.1
      · linarith
      · rw [hmultiple]
        ring

  have wins_with_small_angle (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (hn : 2 ≤ n)
      (htotal : (n : ℝ) * θ = 180) (α β γ : ℝ)
      (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
      (hsum : α + β + γ = 180) (hαsmall : α < θ) :
      MulanWins θ {α, β, γ} := by
    have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have htwo : 2 * θ ≤ 180 := by
      calc
        2 * θ ≤ (n : ℝ) * θ := mul_le_mul_of_nonneg_right hnreal (le_of_lt hθ)
        _ = 180 := htotal
    by_cases hβsmall : β < 180 - θ
    · have hw := wins_small_cut θ hθ n hn htotal γ β α ⟨hα, hαsmall⟩ hβsmall
      rw [triple_reverse α β γ]
      exact hw
    · have hγsmall : γ < 180 - θ := by
        have hβlarge : 180 - θ ≤ β := le_of_not_gt hβsmall
        by_contra h
        have hγlarge : 180 - θ ≤ γ := le_of_not_gt h
        linarith
      have hw := wins_small_cut θ hθ n hn htotal β γ α ⟨hα, hαsmall⟩ hγsmall
      rw [triple_rotate α β γ]
      exact hw

  have wins_bounded_first_angle (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (hn : 2 ≤ n)
      (htotal : (n : ℝ) * θ = 180) :
      ∀ k : ℕ, ∀ α β γ : ℝ,
        0 < α → 0 < β → 0 < γ → α + β + γ = 180 →
        α < (k : ℝ) * θ → MulanWins θ {α, β, γ} := by
    intro k
    induction k with
    | zero =>
        intro α β γ hα hβ hγ hsum hbound
        norm_num at hbound
        linarith
    | succ k ih =>
        intro α β γ hα hβ hγ hsum hbound
        by_cases hle : α ≤ θ
        · rcases hle.eq_or_lt with rfl | hsmall
          · apply MulanWins.win
            simp [HasAngle]
          · exact wins_with_small_angle θ hθ n hn htotal α β γ
              hα hβ hγ hsum hsmall
        · have hgt : θ < α := lt_of_not_ge hle
          have hα' : 0 < α - θ := by linarith
          have hγ' : 0 < γ + θ := by linarith
          have hsum' : (α - θ) + β + (γ + θ) = 180 := by linarith
          have hsucc : ((Nat.succ k : ℕ) : ℝ) * θ = (k : ℝ) * θ + θ := by
            push_cast
            ring
          have hbound' : α - θ < (k : ℝ) * θ := by
            rw [hsucc] at hbound
            linarith
          have hleft := ih (α - θ) β (γ + θ) hα' hβ hγ' hsum' hbound'
          have hx : γ + θ < 180 - β := by linarith
          apply MulanWins.move
            (L := {α - θ, β, γ + θ})
            (R := {θ, γ, 180 - (γ + θ)})
          · refine ⟨α, β, γ, γ + θ, rfl, by linarith, hx, ?_, ?_⟩
            · have hlast : 180 - β - (γ + θ) = α - θ := by linarith
              rw [hlast]
              exact triple_rotate (α - θ) β (γ + θ)
            · have hlast : γ + θ - γ = θ := by ring
              rw [hlast]
              exact triple_rotate θ γ (180 - (γ + θ))
          · exact hleft
          · apply MulanWins.win
            simp [HasAngle]

  constructor
  · intro hwin
    let s₀ : Multiset ℝ := {θ / 2, θ / 2, 180 - θ}
    have hs₀ : IsTriangle s₀ := by
      refine ⟨by simp [s₀], ?_, by simp [s₀]; ring⟩
      intro y hy
      have hy' : y = θ / 2 ∨ y = 180 - θ := by simpa [s₀] using hy
      rcases hy' with hy | hy <;> rw [hy] <;> linarith
    have hinv := wins_integer_invariant (hwin s₀ hs₀) hs₀
    have htotal : ∃ k : ℤ, 180 = (k : ℝ) * θ := by
      rcases hinv with hlocal | htotal
      · rcases hlocal with ⟨k, hk⟩
        have hk' : (k : ℝ) * θ = θ / 2 ∨ (k : ℝ) * θ = 180 - θ := by
          simpa [s₀] using hk
        rcases hk' with hk | hk
        · exfalso
          have hkcases : k ≤ 0 ∨ 1 ≤ k := by omega
          rcases hkcases with hkneg | hkpos
          · have hkneg' : (k : ℝ) ≤ 0 := by exact_mod_cast hkneg
            have hprod : (k : ℝ) * θ ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg hkneg' (le_of_lt hθ0)
            linarith
          · have hkpos' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
            have hprod : θ ≤ (k : ℝ) * θ := by
              simpa using mul_le_mul_of_nonneg_right hkpos' (le_of_lt hθ0)
            linarith
        · refine ⟨k + 1, ?_⟩
          push_cast
          linarith
      · exact htotal
    rcases htotal with ⟨k, hk⟩
    have hkpos : 0 < k := by
      by_contra h
      have hkneg : k ≤ 0 := le_of_not_gt h
      have hkneg' : (k : ℝ) ≤ 0 := by exact_mod_cast hkneg
      have hprod : (k : ℝ) * θ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hkneg' (le_of_lt hθ0)
      linarith
    let n : ℕ := k.toNat
    have hkcastInt : (n : ℤ) = k := by
      dsimp [n]
      exact Int.toNat_of_nonneg (le_of_lt hkpos)
    have hnpos : 0 < n := by
      exact_mod_cast (show (0 : ℤ) < (n : ℤ) by rw [hkcastInt]; exact hkpos)
    have hkcast : (n : ℝ) = (k : ℝ) := by
      exact_mod_cast hkcastInt
    have hnone : n ≠ 1 := by
      intro hn
      have hkone : k = 1 := by
        simpa [hn] using hkcastInt.symm
      have hkoneReal : (k : ℝ) = 1 := by exact_mod_cast hkone
      rw [hkoneReal] at hk
      norm_num at hk
      linarith
    have hn : 2 ≤ n := by omega
    refine ⟨n, hn, ?_⟩
    apply (eq_div_iff (by positivity : (n : ℝ) ≠ 0)).2
    rw [hkcast]
    nlinarith
  · rintro ⟨n, hn, rfl⟩
    intro s hs
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hθ : 0 < (180 / (n : ℝ)) := div_pos (by norm_num) (by positivity)
    have htotal : (n : ℝ) * (180 / (n : ℝ)) = 180 := by field_simp
    rcases hs.1 with hcard
    rcases Multiset.card_eq_three.mp hcard with ⟨α, β, γ, rfl⟩
    rcases hs with ⟨-, hpos, hsum⟩
    have hα : 0 < α := hpos α (by simp)
    have hβ : 0 < β := hpos β (by simp)
    have hγ : 0 < γ := hpos γ (by simp)
    have habc : α + β + γ = 180 := by simpa [add_assoc] using hsum
    obtain ⟨k, hk⟩ := exists_nat_gt (α / (180 / (n : ℝ)))
    have hbound : α < (k : ℝ) * (180 / (n : ℝ)) :=
      (div_lt_iff₀ hθ).mp hk
    exact wins_bounded_first_angle (180 / (n : ℝ)) hθ n hn htotal
      k α β γ hα hβ hγ habc hbound

end TriangleGame
