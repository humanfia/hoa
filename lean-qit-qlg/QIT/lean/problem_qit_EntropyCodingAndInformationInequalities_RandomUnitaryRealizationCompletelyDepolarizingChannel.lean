import QITBench.Base.OneShot
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Random-unitary realization of the completely depolarizing channel

The finite type `a` labels an orthonormal basis of the Hilbert space, so
`Fintype.card a` is its dimension and `CMatrix a` is its operator algebra.
-/

open scoped BigOperators

namespace QITBench

noncomputable section

universe u

namespace Channel

/-- A quantum channel is unital when it maps the identity operator to itself. -/
def IsUnital {a : Type u} [Fintype a] [DecidableEq a]
    (Φ : Channel a a) : Prop :=
  Φ.map (1 : CMatrix a) = (1 : CMatrix a)

end Channel

/-! ## Weyl operators on an arbitrary finite basis -/

/-- Identify an arbitrary nonempty finite basis with the cyclic group of the
same order. -/
private noncomputable def basisZModEquiv
    (a : Type u) [Fintype a] [Nonempty a] :
    a ≃ ZMod (Fintype.card a) := by
  letI : NeZero (Fintype.card a) := ⟨Fintype.card_ne_zero⟩
  exact (Fintype.equivFin a).trans
    (ZMod.finEquiv (Fintype.card a)).toEquiv

/-- The Weyl operator indexed by a cyclic translation `g` and an additive
character `χ`. -/
private noncomputable def weylMatrix
    (a : Type u) [Fintype a] [DecidableEq a] [Nonempty a]
    (g : ZMod (Fintype.card a))
    (χ : AddChar (ZMod (Fintype.card a)) ℂ) : CMatrix a :=
  fun i j =>
    if basisZModEquiv a j = basisZModEquiv a i + g then
      χ (basisZModEquiv a i)
    else 0

private lemma weylMatrix_mem_unitary
    (a : Type u) [Fintype a] [DecidableEq a] [Nonempty a]
    (g : ZMod (Fintype.card a))
    (χ : AddChar (ZMod (Fintype.card a)) ℂ) :
    weylMatrix a g χ ∈ Matrix.unitaryGroup a ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  let k :=
    (basisZModEquiv a).symm (basisZModEquiv a i + g)
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · by_cases hij : i = j
    · subst j
      simp [weylMatrix, k, Complex.mul_conj', AddChar.norm_apply]
    · have hshift :
          basisZModEquiv a i + g ≠ basisZModEquiv a j + g := by
        intro h
        apply hij
        apply (basisZModEquiv a).injective
        exact add_right_cancel h
      simp [weylMatrix, k, hij, hshift]
  · intro b _ hbk
    have hb :
        basisZModEquiv a b ≠ basisZModEquiv a i + g := by
      intro hb
      apply hbk
      apply (basisZModEquiv a).injective
      simpa [k] using hb
    rw [weylMatrix, if_neg hb]
    simp
  · simp

private noncomputable def weylUnitary
    (a : Type u) [Fintype a] [DecidableEq a] [Nonempty a]
    (g : ZMod (Fintype.card a))
    (χ : AddChar (ZMod (Fintype.card a)) ℂ) :
    Matrix.unitaryGroup a ℂ :=
  ⟨weylMatrix a g χ, weylMatrix_mem_unitary a g χ⟩

/-- Reindex the translation-character pairs by exactly `d²` labels. -/
private noncomputable def weylIndexEquiv
    (a : Type u) [Fintype a] [Nonempty a] :
    Fin ((Fintype.card a) ^ 2) ≃
      ZMod (Fintype.card a) ×
        AddChar (ZMod (Fintype.card a)) ℂ := by
  letI : NeZero (Fintype.card a) := ⟨Fintype.card_ne_zero⟩
  exact
    (Fintype.equivFinOfCardEq
      (α := ZMod (Fintype.card a) ×
        AddChar (ZMod (Fintype.card a)) ℂ)
      (by simp [pow_two])).symm

private lemma weyl_conjugate_apply
    (a : Type u) [Fintype a] [DecidableEq a] [Nonempty a]
    (g : ZMod (Fintype.card a))
    (χ : AddChar (ZMod (Fintype.card a)) ℂ)
    (A : CMatrix a) (i j : a) :
    (weylMatrix a g χ * A *
      Matrix.conjTranspose (weylMatrix a g χ)) i j =
      χ (basisZModEquiv a i) *
        A ((basisZModEquiv a).symm (basisZModEquiv a i + g))
          ((basisZModEquiv a).symm (basisZModEquiv a j + g)) *
        (starRingEnd ℂ) (χ (basisZModEquiv a j)) := by
  let ei := basisZModEquiv a i
  let ej := basisZModEquiv a j
  let ii := (basisZModEquiv a).symm (ei + g)
  let jj := (basisZModEquiv a).symm (ej + g)
  have hWA (x : a) :
      (weylMatrix a g χ * A) i x = χ ei * A ii x := by
    rw [Matrix.mul_apply, Finset.sum_eq_single ii]
    · simp [weylMatrix, ei, ii]
    · intro b _ hbi
      have hb : basisZModEquiv a b ≠ ei + g := by
        intro hb
        apply hbi
        apply (basisZModEquiv a).injective
        simpa [ii] using hb
      rw [weylMatrix, if_neg (by simpa [ei] using hb)]
      simp
    · simp
  rw [Matrix.mul_apply]
  simp_rw [hWA]
  rw [Finset.sum_eq_single jj]
  · simp [weylMatrix, ei, ej, ii, jj, mul_assoc]
  · intro b _ hbj
    have hb : basisZModEquiv a b ≠ ej + g := by
      intro hb
      apply hbj
      apply (basisZModEquiv a).injective
      simpa [jj] using hb
    rw [Matrix.conjTranspose_apply, weylMatrix,
      if_neg (by simpa [ej] using hb)]
    simp
  · simp

private lemma sum_weyl_conjugate_over_char
    (a : Type u) [Fintype a] [DecidableEq a] [Nonempty a]
    (g : ZMod (Fintype.card a)) (A : CMatrix a) (i j : a) :
    (∑ χ : AddChar (ZMod (Fintype.card a)) ℂ,
      (weylMatrix a g χ * A *
        Matrix.conjTranspose (weylMatrix a g χ))) i j =
      if i = j then
        (Fintype.card a : ℂ) *
          A ((basisZModEquiv a).symm (basisZModEquiv a i + g))
            ((basisZModEquiv a).symm (basisZModEquiv a j + g))
      else 0 := by
  letI : NeZero (Fintype.card a) := ⟨Fintype.card_ne_zero⟩
  simp_rw [Matrix.sum_apply, weyl_conjugate_apply]
  let x := basisZModEquiv a i
  let y := basisZModEquiv a j
  let c :=
    A ((basisZModEquiv a).symm (x + g))
      ((basisZModEquiv a).symm (y + g))
  have hterm (χ : AddChar (ZMod (Fintype.card a)) ℂ) :
      χ x * c * (starRingEnd ℂ) (χ y) = c * χ (x - y) := by
    rw [← AddChar.map_neg_eq_conj]
    calc
      χ x * c * χ (-y) = c * (χ x * χ (-y)) := by ring
      _ = c * χ (x - y) := by
        rw [← χ.map_add_eq_mul, sub_eq_add_neg]
  simp_rw [show basisZModEquiv a i = x from rfl,
    show basisZModEquiv a j = y from rfl,
    show
      A ((basisZModEquiv a).symm (x + g))
        ((basisZModEquiv a).symm (y + g)) = c from rfl,
    hterm, ← Finset.mul_sum, AddChar.sum_apply_eq_ite]
  simp [x, y, sub_eq_zero, mul_comm]

private lemma sum_shifted_diagonal
    (a : Type u) [Fintype a] [Nonempty a]
    (A : CMatrix a) (i : a) :
    ∑ g : ZMod (Fintype.card a),
      A ((basisZModEquiv a).symm (basisZModEquiv a i + g))
        ((basisZModEquiv a).symm (basisZModEquiv a i + g)) =
      A.trace := by
  letI : NeZero (Fintype.card a) := ⟨Fintype.card_ne_zero⟩
  exact
    ((Equiv.addLeft (basisZModEquiv a i)).trans
      (basisZModEquiv a).symm).sum_comp (fun k => A k k)

private lemma sum_weyl_conjugates
    (a : Type u) [Fintype a] [DecidableEq a] [Nonempty a]
    (A : CMatrix a) :
    (∑ g : ZMod (Fintype.card a),
      ∑ χ : AddChar (ZMod (Fintype.card a)) ℂ,
        weylMatrix a g χ * A *
          Matrix.conjTranspose (weylMatrix a g χ)) =
      (Fintype.card a : ℂ) •
        (A.trace • (1 : CMatrix a)) := by
  letI : NeZero (Fintype.card a) := ⟨Fintype.card_ne_zero⟩
  ext i j
  rw [Matrix.sum_apply]
  calc
    (∑ g,
      (∑ χ, weylMatrix a g χ * A *
        Matrix.conjTranspose (weylMatrix a g χ)) i j) =
        ∑ g, if i = j then
          (Fintype.card a : ℂ) *
            A ((basisZModEquiv a).symm (basisZModEquiv a i + g))
              ((basisZModEquiv a).symm (basisZModEquiv a j + g))
          else 0 :=
      Finset.sum_congr rfl fun g _ =>
        sum_weyl_conjugate_over_char a g A i j
    _ = ((Fintype.card a : ℂ) •
        (A.trace • (1 : CMatrix a))) i j := by
      by_cases hij : i = j
      · subst j
        simp only [if_pos, ← Finset.mul_sum, sum_shifted_diagonal]
        simp [mul_comm]
      · simp [hij]

/-- On every nonzero finite-dimensional system, the completely depolarizing
channel is a uniformly weighted random-unitary channel with `d²` unitary
operators, where `d` is the dimension of the system. -/
theorem exists_randomUnitary_realization_completelyDepolarizingChannel
    (a : Type u) [Fintype a] [DecidableEq a] [Nonempty a] :
    ∃ (U : Fin ((Fintype.card a) ^ 2) → Matrix.unitaryGroup a ℂ)
      (p : Fin ((Fintype.card a) ^ 2) → ℝ),
      OneShot.IsProbabilityDistribution p ∧
      (∀ i, p i = (1 : ℝ) / (Fintype.card a : ℝ) ^ 2) ∧
      ∀ A : CMatrix a,
        (∑ i, ((p i : ℝ) : ℂ) •
          ((U i : CMatrix a) * A * Matrix.conjTranspose (U i : CMatrix a))) =
        A.trace •
          (((1 : ℂ) / (Fintype.card a : ℂ)) • (1 : CMatrix a)) := by
  letI : NeZero (Fintype.card a) := ⟨Fintype.card_ne_zero⟩
  let idx := weylIndexEquiv a
  let U : Fin ((Fintype.card a) ^ 2) → Matrix.unitaryGroup a ℂ :=
    fun k => weylUnitary a (idx k).1 (idx k).2
  let p : Fin ((Fintype.card a) ^ 2) → ℝ :=
    fun _ => (1 : ℝ) / (Fintype.card a : ℝ) ^ 2
  refine ⟨U, p, ?_, ?_, ?_⟩
  · constructor
    · intro k
      dsimp [p]
      positivity
    · dsimp [p]
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_pow]
      field_simp
  · intro k
    rfl
  · intro A
    let c : ℂ :=
      (((1 : ℝ) / (Fintype.card a : ℝ) ^ 2 : ℝ) : ℂ)
    calc
      (∑ k, ((p k : ℝ) : ℂ) •
          ((U k : CMatrix a) * A *
            Matrix.conjTranspose (U k : CMatrix a))) =
          c • (∑ k, ((U k : CMatrix a) * A *
            Matrix.conjTranspose (U k : CMatrix a))) := by
        simp only [p, c, Finset.smul_sum]
      _ = c •
          (∑ z : ZMod (Fintype.card a) ×
              AddChar (ZMod (Fintype.card a)) ℂ,
            weylMatrix a z.1 z.2 * A *
              Matrix.conjTranspose (weylMatrix a z.1 z.2)) := by
        congr 1
        simpa [U, weylUnitary] using
          idx.sum_comp (fun z =>
            weylMatrix a z.1 z.2 * A *
              Matrix.conjTranspose (weylMatrix a z.1 z.2))
      _ = c •
          (∑ g : ZMod (Fintype.card a),
            ∑ χ : AddChar (ZMod (Fintype.card a)) ℂ,
              weylMatrix a g χ * A *
                Matrix.conjTranspose (weylMatrix a g χ)) := by
        rw [Fintype.sum_prod_type]
      _ = c • ((Fintype.card a : ℂ) •
          (A.trace • (1 : CMatrix a))) := by
        rw [sum_weyl_conjugates]
      _ = A.trace •
          (((1 : ℂ) / (Fintype.card a : ℂ)) •
            (1 : CMatrix a)) := by
        simp only [smul_smul]
        congr 1
        dsimp [c]
        push_cast
        field_simp

end

end QITBench
