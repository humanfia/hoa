import QAlgBench.Base
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order

/-!
# Fidelity bound for hidden-subgroup coset states

This file formalizes the hidden-subgroup coset states, their density operators,
the support projector, and the root-fidelity convention appearing in the
source problem.
-/

open scoped BigOperators Pointwise ComplexOrder MatrixOrder

namespace QAlgFormalized
namespace FidelityBoundHiddenSubgroupCosetStates

open QAlgBench

noncomputable section

/-- The finite register whose computational basis is indexed by the elements
of a finite type. -/
def finiteRegister (ι : Type) [Fintype ι] [DecidableEq ι] : Register where
  Index := ι
  fintype := inferInstance
  decEq := inferInstance

/-- The rank-one operator `|ψ⟩⟨φ|`. -/
def ketbra {R : Register} (ψ φ : StateVector R) : HilbertOperator R :=
  fun i j => ψ i * starRingEnd ℂ (φ j)

/-- Positive semidefiniteness for a complex finite-dimensional Hilbert
operator, expressed by self-adjointness and nonnegative quadratic forms. -/
def IsPositiveSemidefinite {R : Register} (A : HilbertOperator R) : Prop :=
  A.conjTranspose = A ∧
    ∀ ψ : StateVector R,
      0 ≤ (inner ℂ ψ (HilbertOperator.applyVec A ψ)).re

private theorem isPositiveSemidefinite_iff_posSemidef {R : Register}
    (A : HilbertOperator R) :
    IsPositiveSemidefinite A ↔ A.PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  rw [IsPositiveSemidefinite, LinearMap.IsPositive,
    Matrix.isSymmetric_toEuclideanLin_iff]
  simp only [HilbertOperator.applyVec]
  constructor
  · rintro ⟨hA, hq⟩
    exact ⟨hA, fun ψ => by
      rw [Matrix.toLpLin_apply]
      rw [inner_re_symm]
      exact hq ψ⟩
  · rintro ⟨hA, hq⟩
    exact ⟨hA, fun ψ => by
      rw [← Matrix.toLpLin_apply]
      change
        0 ≤ RCLike.re (inner ℂ ψ ((Matrix.toEuclideanLin A) ψ))
      rw [inner_re_symm]
      exact hq ψ⟩

/-- A finite-dimensional density operator: a positive-semidefinite matrix of
trace one. -/
structure DensityOperator (R : Register) where
  op : HilbertOperator R
  posSemidef : IsPositiveSemidefinite op
  trace_eq_one : Matrix.trace op = 1

/-- `B` is the positive-semidefinite square root of `A`. -/
def IsPositiveSquareRoot {R : Register}
    (A B : HilbertOperator R) : Prop :=
  IsPositiveSemidefinite B ∧ B * B = A

/-- Every positive-semidefinite finite-dimensional complex operator has a
positive-semidefinite square root. -/
theorem exists_positiveSquareRoot {R : Register} (A : HilbertOperator R)
    (hA : IsPositiveSemidefinite A) :
    ∃ B : HilbertOperator R, IsPositiveSquareRoot A B := by
  have hA' : A.PosSemidef :=
    (isPositiveSemidefinite_iff_posSemidef A).mp hA
  refine ⟨CFC.sqrt A, ?_, ?_⟩
  · exact (isPositiveSemidefinite_iff_posSemidef _).mpr
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))
  · rw [← pow_two, CFC.sq_sqrt A hA'.nonneg]

/-- The positive-semidefinite square root of a positive-semidefinite
finite-dimensional complex operator. -/
def positiveSqrt {R : Register} (A : HilbertOperator R)
    (hA : IsPositiveSemidefinite A) : HilbertOperator R :=
  Classical.choose (exists_positiveSquareRoot A hA)

theorem positiveSqrt_posSemidefinite {R : Register}
    (A : HilbertOperator R) (hA : IsPositiveSemidefinite A) :
    IsPositiveSemidefinite (positiveSqrt A hA) :=
  (Classical.choose_spec (exists_positiveSquareRoot A hA)).1

theorem positiveSqrt_mul_self {R : Register}
    (A : HilbertOperator R) (hA : IsPositiveSemidefinite A) :
    positiveSqrt A hA * positiveSqrt A hA = A :=
  (Classical.choose_spec (exists_positiveSquareRoot A hA)).2

/-- A positive-semidefinite sandwich `A B A` is positive semidefinite. -/
theorem posSemidefinite_sandwich {R : Register}
    (A B : HilbertOperator R)
    (hA : IsPositiveSemidefinite A)
    (hB : IsPositiveSemidefinite B) :
    IsPositiveSemidefinite (A * B * A) := by
  apply (isPositiveSemidefinite_iff_posSemidef _).mpr
  simpa only [hA.1] using
    ((isPositiveSemidefinite_iff_posSemidef B).mp hB).conjTranspose_mul_mul_same A

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- The normalized left-coset state
`|gK⟩ = |K|⁻¹ᐟ² ∑_{k ∈ K} |gk⟩`. -/
def cosetKet (K : Subgroup G) (g : G) : StateVector (finiteRegister G) :=
  letI : Fintype K := Fintype.ofFinite K
  ((Real.sqrt (Nat.card K) : ℂ)⁻¹) •
    ∑ k : K,
      (PureState.ket (R := finiteRegister G) (g * (k : G)) :
        StateVector (finiteRegister G))

private theorem inner_ket {R : Register} (x y : R.Index) :
    inner ℂ (PureState.ket (R := R) x : StateVector R)
      (PureState.ket (R := R) y : StateVector R) =
        if x = y then 1 else 0 := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, PureState.ket_apply, eq_comm]

private theorem inner_cosetKet_self (K : Subgroup G) (g : G) :
    inner ℂ (cosetKet K g) (cosetKet K g) = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  rw [cosetKet, inner_smul_left, inner_smul_right]
  simp_rw [inner_sum, sum_inner, inner_ket]
  simp only [finiteRegister, mul_left_cancel_iff]
  simp
  have hcard : 0 < Fintype.card K :=
    Fintype.card_pos_iff.mpr ⟨⟨1, K.one_mem⟩⟩
  have hs : (Real.sqrt (Fintype.card K) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by exact_mod_cast hcard)
  field_simp
  norm_cast
  symm
  apply Real.sq_sqrt
  exact_mod_cast hcard.le

private def leftCosetFiberEquiv (K : Subgroup G) (g : G) :
    {g' : G // g⁻¹ * g' ∈ K} ≃ K where
  toFun g' := ⟨g⁻¹ * (g' : G), g'.property⟩
  invFun k := ⟨g * (k : G), by simp⟩
  left_inv g' := by
    ext
    simp
  right_inv k := by
    ext
    simp

private theorem cosetKet_eq_of_inv_mul_mem (K : Subgroup G) {g g' : G}
    (h : g⁻¹ * g' ∈ K) :
    cosetKet K g' = cosetKet K g := by
  letI : Fintype K := Fintype.ofFinite K
  let q : K := ⟨g⁻¹ * g', h⟩
  have hg' : g' = g * (q : G) := by simp [q]
  rw [hg', cosetKet, cosetKet]
  congr 1
  simpa only [Equiv.coe_mulLeft, Subgroup.coe_mul, mul_assoc] using
    (Equiv.sum_comp (Equiv.mulLeft q)
      (fun k : K =>
        (PureState.ket (R := finiteRegister G) (g * (k : G)) :
          StateVector (finiteRegister G))))

private theorem inner_cosetKet_eq_one_of_inv_mul_mem
    (K : Subgroup G) {g g' : G} (h : g⁻¹ * g' ∈ K) :
    inner ℂ (cosetKet K g) (cosetKet K g') = 1 := by
  rw [cosetKet_eq_of_inv_mul_mem K h, inner_cosetKet_self]

private theorem inner_cosetKet_eq_zero_of_inv_mul_not_mem
    (K : Subgroup G) {g g' : G} (h : g⁻¹ * g' ∉ K) :
    inner ℂ (cosetKet K g) (cosetKet K g') = 0 := by
  letI : Fintype K := Fintype.ofFinite K
  rw [cosetKet, cosetKet, inner_smul_left, inner_smul_right]
  simp_rw [inner_sum, sum_inner, inner_ket]
  simp only [finiteRegister]
  have hne : ∀ k l : K, g * (k : G) ≠ g' * (l : G) := by
    intro k l heq
    apply h
    have ht :=
      congrArg (fun x : G => g⁻¹ * x * (l : G)⁻¹) heq
    have he : g⁻¹ * g' = (k : G) * (l : G)⁻¹ := by
      group at ht ⊢
      exact ht.symm
    rw [he]
    exact K.mul_mem k.property (K.inv_mem l.property)
  simp [hne]

/-- The operator underlying the hidden-subgroup coset-state mixture
`ρ_K = |G|⁻¹ ∑_{g ∈ G} |gK⟩⟨gK|`. -/
def cosetDensityOp (K : Subgroup G) : HilbertOperator (finiteRegister G) :=
  ((Fintype.card G : ℂ)⁻¹) •
    ∑ g : G, ketbra (cosetKet K g) (cosetKet K g)

private theorem ketbra_mul {R : Register}
    (ψ φ χ η : StateVector R) :
    ketbra ψ φ * ketbra χ η =
      (inner ℂ φ χ) • ketbra ψ η := by
  ext i j
  rw [Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.smul_apply]
  simp only [ketbra, smul_eq_mul, dotProduct, starRingEnd_apply,
    Pi.star_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem sum_inner_smul_ketbra (K : Subgroup G) (g : G) :
    (∑ g' : G,
      (inner ℂ (cosetKet K g) (cosetKet K g')) •
        ketbra (cosetKet K g) (cosetKet K g')) =
      (Nat.card K : ℂ) •
        ketbra (cosetKet K g) (cosetKet K g) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hcard :
      (Finset.univ.filter fun g' : G => g⁻¹ * g' ∈ K).card =
        Nat.card K := by
    rw [← Fintype.card_subtype, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (leftCosetFiberEquiv K g)
  calc
    (∑ g' : G,
        (inner ℂ (cosetKet K g) (cosetKet K g')) •
          ketbra (cosetKet K g) (cosetKet K g')) =
        ∑ g' : G,
          if g⁻¹ * g' ∈ K then
            ketbra (cosetKet K g) (cosetKet K g)
          else 0 := by
      apply Finset.sum_congr rfl
      intro g' hg'
      by_cases hmem : g⁻¹ * g' ∈ K
      · rw [if_pos hmem,
          inner_cosetKet_eq_one_of_inv_mul_mem K hmem,
          cosetKet_eq_of_inv_mul_mem K hmem]
        simp
      · rw [if_neg hmem,
          inner_cosetKet_eq_zero_of_inv_mul_not_mem K hmem]
        simp
    _ = ∑ g' ∈ Finset.univ.filter (fun g' : G => g⁻¹ * g' ∈ K),
          ketbra (cosetKet K g) (cosetKet K g) := by
      rw [Finset.sum_filter]
    _ = (Nat.card K : ℂ) •
          ketbra (cosetKet K g) (cosetKet K g) := by
      rw [Finset.sum_const, hcard]
      ext i j
      simp [Matrix.smul_apply, nsmul_eq_mul]

private theorem sum_ketbra_mul_self (K : Subgroup G) :
    (∑ g : G, ketbra (cosetKet K g) (cosetKet K g)) *
        (∑ g : G, ketbra (cosetKet K g) (cosetKet K g)) =
      (Nat.card K : ℂ) •
        ∑ g : G, ketbra (cosetKet K g) (cosetKet K g) := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, ketbra_mul, sum_inner_smul_ketbra]
  rw [Finset.smul_sum]

private theorem trace_ketbra_self {R : Register} (ψ : StateVector R) :
    Matrix.trace (ketbra ψ ψ) = inner ℂ ψ ψ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.trace, Matrix.diag, ketbra, dotProduct, starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

private theorem trace_ketbra {R : Register} (ψ φ : StateVector R) :
    Matrix.trace (ketbra ψ φ) = inner ℂ φ ψ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.trace, Matrix.diag, ketbra, dotProduct, starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

private theorem trace_ketbra_mul {R : Register}
    (ψ φ : StateVector R) :
    Matrix.trace (ketbra ψ ψ * ketbra φ φ) =
      inner ℂ ψ φ * inner ℂ φ ψ := by
  rw [ketbra_mul, Matrix.trace_smul, trace_ketbra, smul_eq_mul]

/-- The hidden-subgroup coset-state mixture as a density operator. -/
def cosetDensity (K : Subgroup G) : DensityOperator (finiteRegister G) where
  op := cosetDensityOp K
  posSemidef := by
    apply (isPositiveSemidefinite_iff_posSemidef _).mpr
    unfold cosetDensityOp
    apply Matrix.PosSemidef.smul
    · apply Matrix.posSemidef_sum
      intro g hg
      change
        (Matrix.vecMulVec (cosetKet K g).ofLp
          (star (cosetKet K g).ofLp)).PosSemidef
      exact Matrix.posSemidef_vecMulVec_self_star (cosetKet K g).ofLp
    · positivity
  trace_eq_one := by
    rw [cosetDensityOp, Matrix.trace_smul, Matrix.trace_sum]
    simp_rw [trace_ketbra_self, inner_cosetKet_self]
    simp

private theorem cosetDensityOp_mul_self (K : Subgroup G) :
    cosetDensityOp K * cosetDensityOp K =
      ((Nat.card K : ℂ) / (Fintype.card G : ℂ)) •
        cosetDensityOp K := by
  unfold cosetDensityOp
  rw [smul_mul_assoc, mul_smul_comm, sum_ketbra_mul_self]
  simp only [div_eq_mul_inv]
  module

/-- An orthogonal projector whose fixed subspace is exactly the range (and
hence, for a positive-semidefinite operator, the support) of `ρ`. -/
structure SupportProjector {R : Register} (ρ : DensityOperator R) where
  op : HilbertOperator R
  selfAdjoint : op.conjTranspose = op
  idempotent : op * op = op
  fixes_iff_mem_range :
    ∀ ψ : StateVector R,
      HilbertOperator.applyVec op ψ = ψ ↔
        ∃ φ : StateVector R, HilbertOperator.applyVec ρ.op φ = ψ

/-- For a coset-state density operator, scaling by `|G| / |K|` gives its
orthogonal support projector. -/
def cosetSupportProjector (K : Subgroup G) :
    SupportProjector (cosetDensity K) where
  op :=
    ((Fintype.card G : ℂ) / (Nat.card K : ℂ)) •
      (cosetDensity K).op
  selfAdjoint := by
    rw [Matrix.conjTranspose_smul, (cosetDensity K).posSemidef.1]
    simp
  idempotent := by
    have hG : (Fintype.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
    have hK : (Nat.card K : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card K).ne'
    change
      (((Fintype.card G : ℂ) / (Nat.card K : ℂ)) •
          cosetDensityOp K) *
        (((Fintype.card G : ℂ) / (Nat.card K : ℂ)) •
          cosetDensityOp K) =
        ((Fintype.card G : ℂ) / (Nat.card K : ℂ)) •
          cosetDensityOp K
    rw [smul_mul_assoc, mul_smul_comm, cosetDensityOp_mul_self]
    rw [← mul_smul, ← mul_smul]
    congr 1
    field_simp
  fixes_iff_mem_range := by
    intro ψ
    have hG : (Fintype.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
    have hK : (Nat.card K : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card K).ne'
    have hPmulρ :
        (((Fintype.card G : ℂ) / (Nat.card K : ℂ)) •
            cosetDensityOp K) * cosetDensityOp K =
          cosetDensityOp K := by
      rw [smul_mul_assoc, cosetDensityOp_mul_self, ← mul_smul]
      have hscalar :
          ((Fintype.card G : ℂ) / (Nat.card K : ℂ)) *
              ((Nat.card K : ℂ) / (Fintype.card G : ℂ)) =
            1 := by
        field_simp
      rw [hscalar, one_smul]
    constructor
    · intro hfix
      refine
        ⟨((Fintype.card G : ℂ) / (Nat.card K : ℂ)) • ψ, ?_⟩
      rw [HilbertOperator.applyVec_smul]
      rw [← HilbertOperator.smul_applyVec]
      exact hfix
    · rintro ⟨φ, rfl⟩
      change
        HilbertOperator.applyVec
            (((Fintype.card G : ℂ) / (Nat.card K : ℂ)) •
              cosetDensityOp K)
            (HilbertOperator.applyVec (cosetDensityOp K) φ) =
          HilbertOperator.applyVec (cosetDensityOp K) φ
      rw [← HilbertOperator.mul_applyVec, hPmulρ]

private def leftSetFiberEquiv (S : Set G) (g : G) :
    {g' : G // g⁻¹ * g' ∈ S} ≃ S where
  toFun g' := ⟨g⁻¹ * (g' : G), g'.property⟩
  invFun s := ⟨g * (s : G), by simpa⟩
  left_inv g' := by
    ext
    simp
  right_inv s := by
    ext
    simp

private theorem inter_leftCoset_nonempty_iff_inv_mul_mem_product
    (H H' : Subgroup G) (g g' : G) :
    ((g • (H : Set G)) ∩ (g' • (H' : Set G))).Nonempty ↔
      g⁻¹ * g' ∈ (H : Set G) * (H' : Set G) := by
  constructor
  · rintro ⟨x, hxH, hxH'⟩
    have ha : g⁻¹ * x ∈ H := (mem_leftCoset_iff g).mp hxH
    have hb0 : g'⁻¹ * x ∈ H' := (mem_leftCoset_iff g').mp hxH'
    have hb : x⁻¹ * g' ∈ H' := by
      convert H'.inv_mem hb0 using 1 <;> group
    exact Set.mem_mul.mpr
      ⟨g⁻¹ * x, ha, x⁻¹ * g', hb, by group⟩
  · rw [Set.mem_mul]
    rintro ⟨a, ha, b, hb, hab⟩
    refine
      ⟨g * a, mem_leftCoset g ha, (mem_leftCoset_iff g').mpr ?_⟩
    have heq : g' = g * a * b := by
      calc
        g' = g * (g⁻¹ * g') := by group
        _ = g * (a * b) := by rw [hab]
        _ = g * a * b := by rw [mul_assoc]
    have heq' : g'⁻¹ * (g * a) = b⁻¹ := by
      rw [heq]
      group
    rw [heq']
    exact H'.inv_mem hb

private theorem ncard_inter_leftCoset_eq_card_inf_of_nonempty
    (H H' : Subgroup G) (g g' : G)
    (h : ((g • (H : Set G)) ∩ (g' • (H' : Set G))).Nonempty) :
    Set.ncard ((g • (H : Set G)) ∩ (g' • (H' : Set G))) =
      Nat.card ↥(H ⊓ H') := by
  obtain ⟨x, hxH, hxH'⟩ := h
  have heqH : g • (H : Set G) = x • (H : Set G) :=
    (leftCoset_eq_iff H).mpr ((mem_leftCoset_iff g).mp hxH)
  have heqH' : g' • (H' : Set G) = x • (H' : Set G) :=
    (leftCoset_eq_iff H').mpr ((mem_leftCoset_iff g').mp hxH')
  rw [heqH, heqH', ← Set.smul_set_inter]
  change
    Set.ncard (x • (↑(H ⊓ H') : Set G)) =
      Nat.card ↥(H ⊓ H')
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (Subgroup.leftCosetEquivSubgroup x)

private theorem card_filter_inv_mul_mem_set
    (S : Set G) [DecidablePred (· ∈ S)] (g : G) :
    (Finset.univ.filter fun g' : G => g⁻¹ * g' ∈ S).card =
      Set.ncard S := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card]
  exact Fintype.card_congr (leftSetFiberEquiv S g)

private theorem trace_support_mul_density_eq_sum
    (H H' : Subgroup G) :
    Matrix.trace
        ((cosetSupportProjector H).op * (cosetDensity H').op) =
      (((Fintype.card G : ℂ) / (Nat.card H : ℂ)) *
          (Fintype.card G : ℂ)⁻¹ * (Fintype.card G : ℂ)⁻¹) *
        ∑ g : G, ∑ g' : G,
          inner ℂ (cosetKet H g) (cosetKet H' g') *
            inner ℂ (cosetKet H' g') (cosetKet H g) := by
  change
    Matrix.trace
        ((((Fintype.card G : ℂ) / (Nat.card H : ℂ)) •
            cosetDensityOp H) * cosetDensityOp H') =
      _
  unfold cosetDensityOp
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
  simp only [smul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp_rw [Finset.mul_sum, Matrix.trace_sum, trace_ketbra_mul]
  apply Finset.sum_congr rfl
  intro g hg
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g' hg'
  ring

/-- Root fidelity in the convention
`F(ρ, σ) = tr(sqrt(sqrt(ρ) σ sqrt(ρ)))`.

The real part records the real scalar represented by the trace; positivity of
the operator under the outer square root makes this trace real and
nonnegative. -/
def fidelity {R : Register} (ρ σ : DensityOperator R) : ℝ :=
  let rootρ := positiveSqrt ρ.op ρ.posSemidef
  let middle := rootρ * σ.op * rootρ
  let hrootρ := positiveSqrt_posSemidefinite ρ.op ρ.posSemidef
  let hmiddle :=
    posSemidefinite_sandwich rootρ σ.op hrootρ σ.posSemidef
  (Matrix.trace (positiveSqrt middle hmiddle)).re

private theorem trace_re_nonneg_of_posSemidefinite {R : Register}
    (A : HilbertOperator R) (hA : IsPositiveSemidefinite A) :
    0 ≤ (Matrix.trace A).re := by
  have ht :=
    ((isPositiveSemidefinite_iff_posSemidef A).mp hA).trace_nonneg
  exact (Complex.nonneg_iff.mp ht).1

private theorem fidelity_nonneg {R : Register} (ρ σ : DensityOperator R) :
    0 ≤ fidelity ρ σ := by
  unfold fidelity
  dsimp only
  apply trace_re_nonneg_of_posSemidefinite
  exact positiveSqrt_posSemidefinite _ _

/-- The fidelity between hidden-subgroup coset-state mixtures is bounded by
the square root of the relative intersection size. -/
theorem fidelity_cosetDensity_le_sqrt_card_inf_div
    (H H' : Subgroup G)
    (hFidelityUpper :
      fidelity (cosetDensity H) (cosetDensity H') ^ 2 ≤
        (Matrix.trace
          ((cosetSupportProjector H).op * (cosetDensity H').op)).re)
    (hCosetInner :
      ∀ g g' : G,
        inner ℂ (cosetKet H g) (cosetKet H' g') =
          Complex.ofReal
            ((Set.ncard
                ((g • (H : Set G)) ∩ (g' • (H' : Set G))) : ℝ) /
              Real.sqrt ((Nat.card H : ℝ) * (Nat.card H' : ℝ))))
    (hProductCard :
      (Set.ncard ((H : Set G) * (H' : Set G)) : ℝ) =
        ((Nat.card H : ℝ) * (Nat.card H' : ℝ)) /
          (Nat.card ↥(H ⊓ H') : ℝ)) :
    fidelity (cosetDensity H) (cosetDensity H') ≤
      Real.sqrt
        ((Nat.card ↥(H ⊓ H') : ℝ) / (Nat.card H : ℝ)) := by
  classical
  have hCosetInnerReverse :
      ∀ g g' : G,
        inner ℂ (cosetKet H' g') (cosetKet H g) =
          Complex.ofReal
            ((Set.ncard
                ((g • (H : Set G)) ∩ (g' • (H' : Set G))) : ℝ) /
              Real.sqrt ((Nat.card H : ℝ) * (Nat.card H' : ℝ))) := by
    intro g g'
    calc
      inner ℂ (cosetKet H' g') (cosetKet H g) =
          starRingEnd ℂ
            (inner ℂ (cosetKet H g) (cosetKet H' g')) :=
        (inner_conj_symm (cosetKet H' g') (cosetKet H g)).symm
      _ = _ := by rw [hCosetInner]; simp
  let q : ℂ :=
    Complex.ofReal
      (((Nat.card ↥(H ⊓ H') : ℝ) /
          Real.sqrt ((Nat.card H : ℝ) * (Nat.card H' : ℝ))) ^ 2)
  have hterm :
      ∀ g g' : G,
        inner ℂ (cosetKet H g) (cosetKet H' g') *
            inner ℂ (cosetKet H' g') (cosetKet H g) =
          if ((g • (H : Set G)) ∩
              (g' • (H' : Set G))).Nonempty then q else 0 := by
    intro g g'
    rw [hCosetInner g g', hCosetInnerReverse g g']
    by_cases hne :
        ((g • (H : Set G)) ∩ (g' • (H' : Set G))).Nonempty
    · rw [if_pos hne,
        ncard_inter_leftCoset_eq_card_inf_of_nonempty H H' g g' hne]
      simp only [q, ← Complex.ofReal_mul, Complex.ofReal_inj]
      ring
    · rw [if_neg hne]
      have hempty :
          (g • (H : Set G)) ∩ (g' • (H' : Set G)) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      simp
  have hsum :
      (∑ g : G, ∑ g' : G,
          inner ℂ (cosetKet H g) (cosetKet H' g') *
            inner ℂ (cosetKet H' g') (cosetKet H g)) =
        (Fintype.card G) •
          ((Set.ncard ((H : Set G) * (H' : Set G))) • q) := by
    calc
      (∑ g : G, ∑ g' : G,
          inner ℂ (cosetKet H g) (cosetKet H' g') *
            inner ℂ (cosetKet H' g') (cosetKet H g)) =
          ∑ g : G, ∑ g' : G,
            if ((g • (H : Set G)) ∩
                (g' • (H' : Set G))).Nonempty then q else 0 := by
        simp_rw [hterm]
      _ = ∑ _g : G,
            (Set.ncard ((H : Set G) * (H' : Set G))) • q := by
        apply Finset.sum_congr rfl
        intro g hg
        simp_rw [inter_leftCoset_nonempty_iff_inv_mul_mem_product H H']
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, card_filter_inv_mul_mem_set]
      _ = (Fintype.card G) •
            ((Set.ncard ((H : Set G) * (H' : Set G))) • q) := by
        rw [Finset.sum_const, Finset.card_univ]
  rw [trace_support_mul_density_eq_sum, hsum] at hFidelityUpper
  have hG : Fintype.card G ≠ 0 :=
    Fintype.card_ne_zero
  have hH : Nat.card H ≠ 0 :=
    (Nat.card_pos : 0 < Nat.card H).ne'
  have hH' : Nat.card H' ≠ 0 :=
    (Nat.card_pos : 0 < Nat.card H').ne'
  have hI : Nat.card ↥(H ⊓ H') ≠ 0 :=
    (Nat.card_pos : 0 < Nat.card ↥(H ⊓ H')).ne'
  have hGr : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast hG
  have hHr : (Nat.card H : ℝ) ≠ 0 := by
    exact_mod_cast hH
  have hH'r : (Nat.card H' : ℝ) ≠ 0 := by
    exact_mod_cast hH'
  have hIr : (Nat.card ↥(H ⊓ H') : ℝ) ≠ 0 := by
    exact_mod_cast hI
  have hsqrt :
      Real.sqrt ((Nat.card H : ℝ) * (Nat.card H' : ℝ)) ^ 2 =
        (Nat.card H : ℝ) * (Nat.card H' : ℝ) :=
    Real.sq_sqrt
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hreal :
      (((Fintype.card G : ℝ) / (Nat.card H : ℝ)) *
            (Fintype.card G : ℝ)⁻¹ * (Fintype.card G : ℝ)⁻¹) *
          ((Fintype.card G : ℝ) *
            ((Set.ncard ((H : Set G) * (H' : Set G)) : ℝ) *
              (((Nat.card ↥(H ⊓ H') : ℝ) /
                Real.sqrt
                  ((Nat.card H : ℝ) * (Nat.card H' : ℝ))) ^ 2))) =
        (Nat.card ↥(H ⊓ H') : ℝ) / (Nat.card H : ℝ) := by
    rw [hProductCard, div_pow, hsqrt]
    field_simp
  have hcomplex :
      (((Fintype.card G : ℂ) / (Nat.card H : ℂ)) *
            (Fintype.card G : ℂ)⁻¹ * (Fintype.card G : ℂ)⁻¹) *
          ((Fintype.card G) •
            ((Set.ncard ((H : Set G) * (H' : Set G))) • q)) =
        Complex.ofReal
          ((Nat.card ↥(H ⊓ H') : ℝ) / (Nat.card H : ℝ)) := by
    simpa only [q, nsmul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast] using congrArg Complex.ofReal hreal
  rw [hcomplex] at hFidelityUpper
  simp only [Complex.ofReal_re] at hFidelityUpper
  apply
    (Real.le_sqrt
      (fidelity_nonneg (cosetDensity H) (cosetDensity H'))
      (by positivity)).2
  exact hFidelityUpper

end

end FidelityBoundHiddenSubgroupCosetStates
end QAlgFormalized
