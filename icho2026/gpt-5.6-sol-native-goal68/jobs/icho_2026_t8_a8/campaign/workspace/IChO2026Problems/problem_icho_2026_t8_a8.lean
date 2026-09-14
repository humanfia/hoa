import Mathlib

/-!
# IChO 2026, theory problem 8.8

The problem asks which experimental condition produced each of the four bars
`a`--`d`.  The source graph has no products at `a`; among the nonzero bars,
the hydrogen fraction is ordered `d < c < b`.  The preceding Gibbs-energy
diagram makes hydrogen evolution the more energy-demanding branch.  Together
with the photon-energy ordering red < green < blue, this means that a valid
identification must preserve the two strict orders.

The formalization below deliberately separates the observations/ranking model
from the derived answer.  In particular, `ValidCorrespondence` does not state
the three illuminated assignments; the theorem `correspondence_unique` proves
that they are forced by bijectivity, the dark control, and order preservation.
-/

namespace IChO2026Problems.T8A8

/-- The four irradiation conditions printed in the question and answer sheet. -/
inductive Condition where
  | N  -- no irradiation
  | R  -- red LED
  | G  -- green LED
  | B  -- blue LED
  deriving DecidableEq, Fintype, Repr

/-- The four columns in the product-composition diagram. -/
inductive Bar where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype, Repr

/-- Ordinal photon-energy scale.  `N` has no incident photon, and the standard
visible-light ordering is red < green < blue because `E = h c / λ`. -/
def photonEnergyRank : Condition → ℕ
  | .N => 0
  | .R => 1
  | .G => 2
  | .B => 3

theorem photonEnergyRank_injective : Function.Injective photonEnergyRank := by
  intro x y h
  cases x <;> cases y <;> simp_all [photonEnergyRank]

theorem photonEnergyRank_pos_iff (c : Condition) :
    0 < photonEnergyRank c ↔ c ≠ .N := by
  cases c <;> decide

theorem photonEnergyRank_le_three (c : Condition) :
    photonEnergyRank c ≤ 3 := by
  cases c <;> decide

/-- Ordinal hydrogen-share scale read from the supplied stacked-bar diagram.
Only the order is used: `a` is zero, while `d < c < b` among nonzero bars. -/
def hydrogenShareRank : Bar → ℕ
  | .a => 0
  | .d => 1
  | .c => 2
  | .b => 3

/-- A proposed one-to-one labelling is physically consistent with the two
source diagrams when the zero-output bar is the dark control and, among the
illuminated bars, a larger H₂ share corresponds to a higher-energy photon.

The last clause is the qualitative inference from the displayed Gibbs-energy
profiles: proton reduction has the higher energetic demand than CO formation.
-/
def ValidCorrespondence (f : Bar → Condition) : Prop :=
  Function.Bijective f ∧
  f .a = .N ∧
  ∀ x y, x ≠ .a → y ≠ .a →
    (hydrogenShareRank x < hydrogenShareRank y ↔
      photonEnergyRank (f x) < photonEnergyRank (f y))

/-- The classification to be entered on the blank answer sheet. -/
def answer : Bar → Condition
  | .a => .N
  | .b => .B
  | .c => .G
  | .d => .R

/-- The proposed answer satisfies all source-derived consistency conditions. -/
theorem answer_valid : ValidCorrespondence answer := by
  refine ⟨?_, rfl, ?_⟩
  · constructor
    · intro x y
      fin_cases x <;> fin_cases y <;> simp [answer]
    · intro y
      fin_cases y
      · exact ⟨.a, rfl⟩
      · exact ⟨.d, rfl⟩
      · exact ⟨.c, rfl⟩
      · exact ⟨.b, rfl⟩
  · intro x y hx hy
    fin_cases x <;> fin_cases y <;>
      simp_all [answer, hydrogenShareRank, photonEnergyRank]

/-- Any correspondence satisfying the diagram and energy-order constraints is
the proposed answer.  Thus the classification is unique, not merely possible. -/
theorem correspondence_unique {f : Bar → Condition}
    (h : ValidCorrespondence f) : f = answer := by
  rcases h with ⟨hbij, ha, horder⟩
  have hdN : f .d ≠ .N := by
    intro hd
    have : Bar.d = Bar.a := hbij.1 (hd.trans ha.symm)
    cases this
  have hcN : f .c ≠ .N := by
    intro hc
    have : Bar.c = Bar.a := hbij.1 (hc.trans ha.symm)
    cases this
  have hbN : f .b ≠ .N := by
    intro hb
    have : Bar.b = Bar.a := hbij.1 (hb.trans ha.symm)
    cases this
  have hdc : photonEnergyRank (f .d) < photonEnergyRank (f .c) := by
    exact (horder .d .c (by decide) (by decide)).mp (by decide)
  have hcb : photonEnergyRank (f .c) < photonEnergyRank (f .b) := by
    exact (horder .c .b (by decide) (by decide)).mp (by decide)
  have hdPos : 0 < photonEnergyRank (f .d) :=
    (photonEnergyRank_pos_iff (f .d)).mpr hdN
  have hbLe : photonEnergyRank (f .b) ≤ 3 := photonEnergyRank_le_three (f .b)
  have hdRank : photonEnergyRank (f .d) = 1 := by omega
  have hcRank : photonEnergyRank (f .c) = 2 := by omega
  have hbRank : photonEnergyRank (f .b) = 3 := by omega
  have hd : f .d = .R := photonEnergyRank_injective (by
    simpa [photonEnergyRank] using hdRank)
  have hc : f .c = .G := photonEnergyRank_injective (by
    simpa [photonEnergyRank] using hcRank)
  have hb : f .b = .B := photonEnergyRank_injective (by
    simpa [photonEnergyRank] using hbRank)
  funext x
  cases x <;> simp [answer, ha, hb, hc, hd]

/-- Requested output `condition_a`: bar `a` is the no-irradiation condition. -/
theorem condition_a {f : Bar → Condition} (h : ValidCorrespondence f) :
    f .a = .N := by
  rw [correspondence_unique h]
  rfl

/-- Requested output `condition_b`: bar `b` is blue-light irradiation. -/
theorem condition_b {f : Bar → Condition} (h : ValidCorrespondence f) :
    f .b = .B := by
  rw [correspondence_unique h]
  rfl

/-- Requested output `condition_c`: bar `c` is green-light irradiation. -/
theorem condition_c {f : Bar → Condition} (h : ValidCorrespondence f) :
    f .c = .G := by
  rw [correspondence_unique h]
  rfl

/-- Requested output `condition_d`: bar `d` is red-light irradiation. -/
theorem condition_d {f : Bar → Condition} (h : ValidCorrespondence f) :
    f .d = .R := by
  rw [correspondence_unique h]
  rfl

#print axioms answer_valid
#print axioms correspondence_unique
#print axioms condition_a
#print axioms condition_b
#print axioms condition_c
#print axioms condition_d

end IChO2026Problems.T8A8
