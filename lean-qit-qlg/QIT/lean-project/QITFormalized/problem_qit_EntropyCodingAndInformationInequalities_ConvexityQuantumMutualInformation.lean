import QITFoundations.QITFormalized_problem_qit_EntropyCodingAndInformationInequalities_ConvexityQuantumMutualInformation_Foundation
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Curvature of quantum mutual information

This file models finite-dimensional density operators with `QITBench.State`.
The tensor product `𝓗_A ⊗ 𝓗_B` is represented by the product basis `A × B`.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace QITBench.ConvexityQuantumMutualInformation

universe u v w x

noncomputable section

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The von Neumann entropy `S(ρ) = -∑ᵢ λᵢ log λᵢ` of a density state.

Mathlib defines `Real.log 0 = 0`, so the summand has the standard continuous
value `0` at a zero eigenvalue. The logarithm base is immaterial for the
convexity classification.
-/
def vonNeumannEntropy (rho : State X) : ℝ :=
  -∑ i : X,
    let lambda := rho.pos.isHermitian.eigenvalues i
    lambda * Real.log lambda

/-- A trace-exponential bound yields the entropy upper bound used by the
Gibbs-variational route to strong subadditivity. -/
private theorem vonNeumannEntropy_le_neg_re_trace_mul_of_exp_trace_le_one
    [Nonempty X] (rho : State X) {H : CMatrix X} (hH : H.IsHermitian)
    (htrace : (NormedSpace.exp H).trace.re ≤ 1) :
    vonNeumannEntropy rho ≤
      -Complex.re ((rho.matrix * H).trace) := by
  have h :=
    State.re_trace_mul_le_spectral_sum_of_exp_trace_le_one
      rho hH htrace
  unfold vonNeumannEntropy
  linarith

/-- The spectral trace pairing with `log ρ` is the negative von Neumann
entropy in this file's sign convention. -/
private theorem vonNeumannEntropy_eq_neg_re_trace_mul_spectralLogMatrix
    (rho : State X) :
    vonNeumannEntropy rho =
      -Complex.re ((rho.matrix * rho.spectralLogMatrix).trace) := by
  rw [State.re_trace_mul_spectralLogMatrix_self]
  rfl

/-- A finite ensemble of density states with nonnegative, normalized weights. -/
structure FiniteStateEnsemble (ι : Type w) [Fintype ι]
    (X : Type u) [Fintype X] [DecidableEq X] where
  weight : ι → ℝ
  state : ι → State X
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum_one : ∑ i, weight i = 1

/-- `rho` is the density state obtained by averaging the ensemble `E`. -/
def FiniteStateEnsemble.IsAverage {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι X) (rho : State X) : Prop :=
  rho.matrix = ∑ i, (E.weight i : ℂ) • (E.state i).matrix

variable {A : Type u} {B : Type v}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

private def ssaLiftABMatrix
    {C : Type w} [DecidableEq C]
    (M : CMatrix (A × B)) : CMatrix ((A × B) × C) :=
  Matrix.kronecker M (1 : CMatrix C)

private def ssaLiftBCMatrix
    {C : Type w}
    (M : CMatrix (B × C)) : CMatrix ((A × B) × C) :=
  fun x y => (1 : CMatrix A) x.1.1 y.1.1 *
    M (x.1.2, x.2) (y.1.2, y.2)

private def ssaLiftBMatrix
    {C : Type w} [DecidableEq C]
    (M : CMatrix B) : CMatrix ((A × B) × C) :=
  fun x y => (1 : CMatrix A) x.1.1 y.1.1 *
    M x.1.2 y.1.2 * (1 : CMatrix C) x.2 y.2

private theorem ssaLiftABMatrix_isHermitian
    {C : Type w} [DecidableEq C]
    {M : CMatrix (A × B)} (hM : M.IsHermitian) :
    (ssaLiftABMatrix (C := C) M).IsHermitian := by
  unfold ssaLiftABMatrix Matrix.IsHermitian
  ext x y
  have hentry : star (M y.1 x.1) = M x.1 y.1 := by
    rw [← Matrix.conjTranspose_apply, hM]
  change
    star (M y.1 x.1 * (1 : CMatrix C) y.2 x.2) =
      M x.1 y.1 * (1 : CMatrix C) x.2 y.2
  rw [star_mul, hentry]
  simp [Matrix.one_apply, eq_comm]

private theorem ssaLiftBCMatrix_isHermitian
    {C : Type w}
    {M : CMatrix (B × C)} (hM : M.IsHermitian) :
    (ssaLiftBCMatrix (A := A) M).IsHermitian := by
  unfold ssaLiftBCMatrix Matrix.IsHermitian
  ext x y
  have hentry :
      star (M (y.1.2, y.2) (x.1.2, x.2)) =
        M (x.1.2, x.2) (y.1.2, y.2) := by
    rw [← Matrix.conjTranspose_apply, hM]
  change
    star ((1 : CMatrix A) y.1.1 x.1.1 *
      M (y.1.2, y.2) (x.1.2, x.2)) = _
  rw [star_mul, hentry]
  simp [Matrix.one_apply, eq_comm]

private theorem ssaLiftBMatrix_isHermitian
    {C : Type w} [DecidableEq C]
    {M : CMatrix B} (hM : M.IsHermitian) :
    (ssaLiftBMatrix (A := A) (C := C) M).IsHermitian := by
  unfold ssaLiftBMatrix Matrix.IsHermitian
  ext x y
  have hentry : star (M y.1.2 x.1.2) = M x.1.2 y.1.2 := by
    rw [← Matrix.conjTranspose_apply, hM]
  change
    star ((1 : CMatrix A) y.1.1 x.1.1 * M y.1.2 x.1.2 *
      (1 : CMatrix C) y.2 x.2) = _
  rw [star_mul, star_mul, hentry]
  by_cases ha : x.1.1 = y.1.1
  · by_cases hc : x.2 = y.2
    · simp [Matrix.one_apply, ha, hc]
    · simp [Matrix.one_apply, ha, hc, Ne.symm hc]
  · simp [Matrix.one_apply, ha, Ne.symm ha]

section

open scoped Matrix.Norms.L2Operator

local instance matrixCStarAlgebraForLiftExp
    {Y : Type*} [Fintype Y] [DecidableEq Y] :
    CStarAlgebra (CMatrix Y) where
  norm_mul_self_le := Matrix.instCStarRing.norm_mul_self_le

local instance matrixNormedAlgebraRatForLiftExp
    {Y : Type*} [Fintype Y] [DecidableEq Y] :
    NormedAlgebra ℚ (CMatrix Y) :=
  NormedAlgebra.restrictScalars ℚ ℂ (CMatrix Y)

private theorem normedSpace_exp_matrix_reindex
    {Y Z : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (e : Y ≃ Z) (M : CMatrix Y) :
    NormedSpace.exp (Matrix.reindex e e M) =
      Matrix.reindex e e (NormedSpace.exp M) := by
  symm
  exact
    NormedSpace.map_exp (Matrix.reindexAlgEquiv ℚ ℂ e)
      (by
        simpa [Matrix.reindex_apply] using
          (continuous_id.matrix_submatrix e.symm e.symm)) M

private theorem normedSpace_exp_kronecker_one
    {Y Z : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (M : CMatrix Y) :
    NormedSpace.exp (Matrix.kronecker M (1 : CMatrix Z)) =
      Matrix.kronecker (NormedSpace.exp M) (1 : CMatrix Z) := by
  simp only [Matrix.kronecker]
  rw [Matrix.kronecker_one, Matrix.exp_blockDiagonal,
    Matrix.kronecker_one]
  apply congrArg Matrix.blockDiagonal
  funext z
  exact Pi.coe_exp (fun _ : Z => M) z

private theorem normedSpace_exp_one_kronecker
    {Y Z : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (M : CMatrix Y) :
    NormedSpace.exp (Matrix.kronecker (1 : CMatrix Z) M) =
      Matrix.kronecker (1 : CMatrix Z) (NormedSpace.exp M) := by
  simp only [Matrix.kronecker]
  rw [Matrix.one_kronecker, Matrix.one_kronecker,
    normedSpace_exp_matrix_reindex, Matrix.exp_blockDiagonal]
  apply congrArg
    (Matrix.reindex (Equiv.prodComm Y Z) (Equiv.prodComm Y Z))
  apply congrArg Matrix.blockDiagonal
  funext z
  exact Pi.coe_exp (fun _ : Z => M) z

private theorem normedSpace_exp_ssaLiftABMatrix_spectralLogMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State (A × B)) (hrho : rho.matrix.PosDef) :
    NormedSpace.exp
        (ssaLiftABMatrix (C := C) rho.spectralLogMatrix) =
      ssaLiftABMatrix (C := C) rho.matrix := by
  unfold ssaLiftABMatrix
  simp only [Matrix.kronecker]
  rw [Matrix.kronecker_one, Matrix.exp_blockDiagonal,
    Matrix.kronecker_one]
  apply congrArg Matrix.blockDiagonal
  funext c
  calc
    (NormedSpace.exp
        (fun _ : C => rho.spectralLogMatrix)) c =
        NormedSpace.exp rho.spectralLogMatrix :=
      Pi.coe_exp _ c
    _ = NormedSpace.exp (CFC.log rho.matrix) := by
      congr 1
      unfold State.spectralLogMatrix
      exact (rho.pos.isHermitian.cfc_eq Real.log).symm
    _ = rho.matrix :=
      CFC.exp_log rho.matrix hrho.isStrictlyPositive

private theorem normedSpace_exp_one_kronecker_spectralLogMatrix
    {Y Z : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (rho : State Y) (hrho : rho.matrix.PosDef) :
    NormedSpace.exp
        (Matrix.kronecker (1 : CMatrix Z) rho.spectralLogMatrix) =
      Matrix.kronecker (1 : CMatrix Z) rho.matrix := by
  simp only [Matrix.kronecker]
  rw [Matrix.one_kronecker, Matrix.one_kronecker,
    normedSpace_exp_matrix_reindex, Matrix.exp_blockDiagonal]
  apply congrArg
    (Matrix.reindex (Equiv.prodComm Y Z) (Equiv.prodComm Y Z))
  apply congrArg Matrix.blockDiagonal
  funext z
  calc
    (NormedSpace.exp
        (fun _ : Z => rho.spectralLogMatrix)) z =
        NormedSpace.exp rho.spectralLogMatrix :=
      Pi.coe_exp _ z
    _ = NormedSpace.exp (CFC.log rho.matrix) := by
      congr 1
      unfold State.spectralLogMatrix
      exact (rho.pos.isHermitian.cfc_eq Real.log).symm
    _ = rho.matrix :=
      CFC.exp_log rho.matrix hrho.isStrictlyPositive

private theorem ssaLiftBCMatrix_eq_reindex_one_kronecker
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (B × C)) :
    ssaLiftBCMatrix (A := A) M =
      Matrix.reindex (Equiv.prodAssoc A B C).symm
        (Equiv.prodAssoc A B C).symm
        (Matrix.kronecker (1 : CMatrix A) M) := by
  ext x y
  simp [ssaLiftBCMatrix, Matrix.reindex_apply]

private theorem normedSpace_exp_ssaLiftBCMatrix_spectralLogMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State (B × C)) (hrho : rho.matrix.PosDef) :
    NormedSpace.exp
        (ssaLiftBCMatrix (A := A) rho.spectralLogMatrix) =
      ssaLiftBCMatrix (A := A) rho.matrix := by
  rw [ssaLiftBCMatrix_eq_reindex_one_kronecker,
    normedSpace_exp_matrix_reindex,
    normedSpace_exp_one_kronecker_spectralLogMatrix rho hrho,
    ← ssaLiftBCMatrix_eq_reindex_one_kronecker]

private theorem ssaLiftBMatrix_eq_kronecker_one_kronecker
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix B) :
    ssaLiftBMatrix (A := A) (C := C) M =
      Matrix.kronecker
        (Matrix.kronecker (1 : CMatrix A) M) (1 : CMatrix C) := by
  ext x y
  simp [ssaLiftBMatrix, mul_assoc]

private theorem normedSpace_exp_ssaLiftBMatrix_spectralLogMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State B) (hrho : rho.matrix.PosDef) :
    NormedSpace.exp
        (ssaLiftBMatrix (A := A) (C := C) rho.spectralLogMatrix) =
      ssaLiftBMatrix (A := A) (C := C) rho.matrix := by
  rw [ssaLiftBMatrix_eq_kronecker_one_kronecker,
    normedSpace_exp_kronecker_one,
    normedSpace_exp_one_kronecker]
  have hlog :
      NormedSpace.exp rho.spectralLogMatrix = rho.matrix := by
    calc
      NormedSpace.exp rho.spectralLogMatrix =
          NormedSpace.exp (CFC.log rho.matrix) := by
        congr 1
        unfold State.spectralLogMatrix
        exact (rho.pos.isHermitian.cfc_eq Real.log).symm
      _ = rho.matrix :=
        CFC.exp_log rho.matrix hrho.isStrictlyPositive
  rw [hlog, ← ssaLiftBMatrix_eq_kronecker_one_kronecker]

end

private theorem re_trace_mul_ssaLiftABMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) (T : CMatrix (A × B)) :
    Complex.re ((rho.matrix * ssaLiftABMatrix (C := C) T).trace) =
      Complex.re ((rho.marginalAB.matrix * T).trace) := by
  apply congrArg Complex.re
  exact
    (partialTraceB_mul_trace_eq_trace_mul_kronecker_right
      rho.matrix T).symm

private theorem re_trace_mul_ssaLiftBCMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) (T : CMatrix (B × C)) :
    Complex.re ((rho.matrix * ssaLiftBCMatrix (A := A) T).trace) =
      Complex.re ((rho.marginalBC.matrix * T).trace) := by
  congr 1
  simp [Matrix.trace, Matrix.mul_apply, ssaLiftBCMatrix,
    State.marginalBC, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.sum_mul]
  let f : A → B → C → B → C → ℂ := fun a b c b' c' =>
    rho.matrix ((a, b), c) ((a, b'), c') * T (b', c') (b, c)
  change
    (∑ a, ∑ b, ∑ c, ∑ b', ∑ c', f a b c b' c') =
      ∑ b, ∑ c, ∑ b', ∑ c', ∑ a, f a b c b' c'
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ b', ∑ c', f a b c b' c' := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a, ∑ b', ∑ c', f a b c b' c' := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ b', ∑ a, ∑ c', f a b c b' c' := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b' _
      rw [Finset.sum_comm]

private theorem re_trace_mul_ssaLiftBMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) (T : CMatrix B) :
    Complex.re ((rho.matrix * ssaLiftBMatrix (A := A) (C := C) T).trace) =
      Complex.re ((rho.marginalBOfABC.matrix * T).trace) := by
  congr 1
  simp [Matrix.trace, Matrix.mul_apply, ssaLiftBMatrix,
    State.marginalBOfABC, State.marginalAB, State.marginalB,
    partialTraceA, partialTraceB, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  let f : A → B → C → B → ℂ := fun a b c b' =>
    rho.matrix ((a, b), c) ((a, b'), c) * T b' b
  change
    (∑ a, ∑ b, ∑ c, ∑ b', f a b c b') =
      ∑ b, ∑ b', ∑ a, ∑ c, f a b c b'
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ b', f a b c b' := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a, ∑ b', f a b c b' := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ b', ∑ a, f a b c b' := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ b', ∑ c, ∑ a, f a b c b' := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro b' _
      rw [Finset.sum_comm]

private theorem trace_ssaLiftAB_mul_ssaLiftBC_mul_ssaLiftB
    {C : Type w} [Fintype C] [DecidableEq C]
    (MAB : CMatrix (A × B)) (MBC : CMatrix (B × C))
    (MB : CMatrix B) :
    (ssaLiftABMatrix (C := C) MAB *
        ssaLiftBCMatrix (A := A) MBC *
          ssaLiftBMatrix (A := A) (C := C) MB).trace =
      (partialTraceA MAB * partialTraceB MBC * MB).trace := by
  simp [Matrix.trace, Matrix.mul_apply, ssaLiftABMatrix,
    ssaLiftBCMatrix, ssaLiftBMatrix, partialTraceA, partialTraceB,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  let f : A → B → C → B → B → ℂ := fun a b c b'' b' =>
    MAB (a, b) (a, b') * MBC (b', c) (b'', c) * MB b'' b
  change
    (∑ a, ∑ b, ∑ c, ∑ b'', ∑ b', f a b c b'' b') =
      ∑ b, ∑ b'', ∑ b', ∑ c, ∑ a, f a b c b'' b'
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ b'', ∑ b', f a b c b'' b' := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ a, ∑ b'', ∑ c, ∑ b', f a b c b'' b' := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ b'', ∑ a, ∑ c, ∑ b', f a b c b'' b' := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ b'', ∑ a, ∑ b', ∑ c, f a b c b'' b' := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro b'' _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ b'', ∑ b', ∑ a, ∑ c, f a b c b'' b' := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro b'' _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro b'' _
      apply Finset.sum_congr rfl
      intro b' _
      rw [Finset.sum_comm]

private theorem trace_ssaLiftAB_mul_ssaLiftB_mul_ssaLiftBC_mul_ssaLiftB
    {C : Type w} [Fintype C] [DecidableEq C]
    (MAB : CMatrix (A × B)) (MBC : CMatrix (B × C))
    (MB₁ MB₂ : CMatrix B) :
    (ssaLiftABMatrix (C := C) MAB *
        ssaLiftBMatrix (A := A) (C := C) MB₁ *
        ssaLiftBCMatrix (A := A) MBC *
        ssaLiftBMatrix (A := A) (C := C) MB₂).trace =
      (partialTraceA MAB * MB₁ * partialTraceB MBC * MB₂).trace := by
  simp [Matrix.trace, Matrix.mul_apply, ssaLiftABMatrix,
    ssaLiftBCMatrix, ssaLiftBMatrix, partialTraceA, partialTraceB,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  let f : A → B → C → B → B → B → ℂ := fun a b c d e g =>
    MAB (a, b) (a, g) * MB₁ g e * MBC (e, c) (d, c) * MB₂ d b
  change
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g) =
      ∑ b, ∑ d, ∑ e, ∑ c, ∑ g, ∑ a, f a b c d e g
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ a, ∑ d, ∑ c, ∑ e, ∑ g, f a b c d e g := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ d, ∑ a, ∑ c, ∑ e, ∑ g, f a b c d e g := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ d, ∑ a, ∑ e, ∑ c, ∑ g, f a b c d e g := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ d, ∑ e, ∑ a, ∑ c, ∑ g, f a b c d e g := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ d, ∑ e, ∑ c, ∑ a, ∑ g, f a b c d e g := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

private theorem inv_ssaLiftBMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix B) :
    (ssaLiftBMatrix (A := A) (C := C) M)⁻¹ =
      ssaLiftBMatrix (A := A) (C := C) M⁻¹ := by
  rw [ssaLiftBMatrix_eq_kronecker_one_kronecker]
  unfold Matrix.kronecker
  rw [Matrix.inv_kronecker, Matrix.inv_kronecker]
  rw [ssaLiftBMatrix_eq_kronecker_one_kronecker]
  unfold Matrix.kronecker
  simp

private theorem trace_ssaMarginalLifts_mul_inv_eq_one
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C))
    (hBPos : rho.marginalBOfABC.matrix.PosDef) :
    (ssaLiftABMatrix (C := C) rho.marginalAB.matrix *
        ssaLiftBCMatrix (A := A) rho.marginalBC.matrix *
          (ssaLiftBMatrix (A := A) (C := C)
            rho.marginalBOfABC.matrix)⁻¹).trace = 1 := by
  rw [inv_ssaLiftBMatrix,
    trace_ssaLiftAB_mul_ssaLiftBC_mul_ssaLiftB]
  have hAB :
      partialTraceA rho.marginalAB.matrix =
        rho.marginalBOfABC.matrix := rfl
  have hBC :
      partialTraceB rho.marginalBC.matrix =
        rho.marginalBOfABC.matrix := by
    ext b b'
    simp only [partialTraceB, State.marginalBC,
      State.marginalBOfABC, State.marginalAB,
      State.marginalB_matrix, State.marginalA_matrix, partialTraceA]
    rw [Finset.sum_comm]
  rw [hAB, hBC,
    Matrix.mul_nonsing_inv_cancel_right
      rho.marginalBOfABC.matrix rho.marginalBOfABC.matrix
      ((Matrix.isUnit_iff_isUnit_det
        rho.marginalBOfABC.matrix).mp hBPos.isUnit),
    rho.marginalBOfABC.trace_eq_one]

private def strongSubadditivityLiebResolventIntegrand
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) (t : ℝ) :
    CMatrix ((A × B) × C) :=
  let R :=
    (rho.marginalBOfABC.matrix + t • (1 : CMatrix B))⁻¹
  ssaLiftABMatrix (C := C) rho.marginalAB.matrix *
    ssaLiftBMatrix (A := A) (C := C) R *
    ssaLiftBCMatrix (A := A) rho.marginalBC.matrix *
    ssaLiftBMatrix (A := A) (C := C) R

private theorem re_trace_strongSubadditivityLiebResolventIntegrand
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) (t : ℝ) :
    Complex.re (strongSubadditivityLiebResolventIntegrand rho t).trace =
      Complex.re
        ((rho.marginalBOfABC.matrix *
          (rho.marginalBOfABC.matrix + t • (1 : CMatrix B))⁻¹ *
          rho.marginalBOfABC.matrix *
          (rho.marginalBOfABC.matrix + t • (1 : CMatrix B))⁻¹).trace) := by
  unfold strongSubadditivityLiebResolventIntegrand
  rw [trace_ssaLiftAB_mul_ssaLiftB_mul_ssaLiftBC_mul_ssaLiftB]
  have hAB :
      partialTraceA rho.marginalAB.matrix =
        rho.marginalBOfABC.matrix := rfl
  have hBC :
      partialTraceB rho.marginalBC.matrix =
        rho.marginalBOfABC.matrix := by
    ext b b'
    simp only [partialTraceB, State.marginalBC,
      State.marginalBOfABC, State.marginalAB,
      State.marginalB_matrix, State.marginalA_matrix, partialTraceA]
    rw [Finset.sum_comm]
  rw [hAB, hBC]

private theorem integral_re_trace_strongSubadditivityLiebResolventIntegrand
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C))
    (hBPos : rho.marginalBOfABC.matrix.PosDef) :
    ∫ t : ℝ in Set.Ioi 0,
      Complex.re
        (strongSubadditivityLiebResolventIntegrand rho t).trace = 1 := by
  simp_rw [re_trace_strongSubadditivityLiebResolventIntegrand]
  calc
    _ = ∫ t : ℝ in Set.Ioi 0,
        Complex.re
          ((rho.marginalBOfABC.matrix *
            rho.marginalBOfABC.matrix *
            (rho.marginalBOfABC.matrix + t • (1 : CMatrix B))⁻¹ *
            (rho.marginalBOfABC.matrix + t • (1 : CMatrix B))⁻¹).trace) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      apply congrArg Complex.re
      apply congrArg Matrix.trace
      let R :=
        (rho.marginalBOfABC.matrix + t • (1 : CMatrix B))⁻¹
      have hcomm : Commute rho.marginalBOfABC.matrix R :=
        Matrix.PosDef.commute_inv_add_smul_one hBPos t ht.le
      change
        rho.marginalBOfABC.matrix * R *
            rho.marginalBOfABC.matrix * R =
          rho.marginalBOfABC.matrix *
            rho.marginalBOfABC.matrix * R * R
      calc
        _ = rho.marginalBOfABC.matrix *
            (R * rho.marginalBOfABC.matrix) * R := by
          noncomm_ring
        _ = rho.marginalBOfABC.matrix *
            (rho.marginalBOfABC.matrix * R) * R := by
          rw [hcomm.eq]
        _ = _ := by noncomm_ring
    _ = 1 :=
      State.integral_re_trace_self_mul_resolvent_sq
        rho.marginalBOfABC hBPos

private def strongSubadditivityHamiltonian
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) : CMatrix ((A × B) × C) :=
  ssaLiftABMatrix (C := C) rho.marginalAB.spectralLogMatrix +
    ssaLiftBCMatrix (A := A) rho.marginalBC.spectralLogMatrix -
      ssaLiftBMatrix (A := A) (C := C)
        rho.marginalBOfABC.spectralLogMatrix

private theorem strongSubadditivity_traceExp_bound_of_liebThreeMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C))
    (hBPos : rho.marginalBOfABC.matrix.PosDef)
    (hLieb :
      (NormedSpace.exp (strongSubadditivityHamiltonian rho)).trace.re ≤
        ∫ t : ℝ in Set.Ioi 0,
          Complex.re
            (strongSubadditivityLiebResolventIntegrand rho t).trace) :
    (NormedSpace.exp (strongSubadditivityHamiltonian rho)).trace.re ≤ 1 := by
  rw [integral_re_trace_strongSubadditivityLiebResolventIntegrand
    rho hBPos] at hLieb
  exact hLieb

private theorem normedSpace_exp_add_sub_of_commute
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (M N P : CMatrix Y)
    (hMN : Commute M N) (hMNP : Commute (M + N) P) :
    NormedSpace.exp (M + N - P) =
      NormedSpace.exp M * NormedSpace.exp N *
        (NormedSpace.exp P)⁻¹ := by
  rw [sub_eq_add_neg,
    Matrix.exp_add_of_commute (M + N) (-P)
      hMNP.neg_right,
    Matrix.exp_add_of_commute M N hMN,
    Matrix.exp_neg]

private theorem strongSubadditivityHamiltonian_isHermitian
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) :
    (strongSubadditivityHamiltonian rho).IsHermitian := by
  exact
    (ssaLiftABMatrix_isHermitian
      (State.spectralLogMatrix_isHermitian rho.marginalAB)).add
      (ssaLiftBCMatrix_isHermitian
        (State.spectralLogMatrix_isHermitian rho.marginalBC)) |>.sub
      (ssaLiftBMatrix_isHermitian
        (State.spectralLogMatrix_isHermitian rho.marginalBOfABC))

private theorem normedSpace_exp_strongSubadditivityHamiltonian_of_commute
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C))
    (hABPos : rho.marginalAB.matrix.PosDef)
    (hBCPos : rho.marginalBC.matrix.PosDef)
    (hBPos : rho.marginalBOfABC.matrix.PosDef)
    (hABBC :
      Commute
        (ssaLiftABMatrix (C := C)
          rho.marginalAB.spectralLogMatrix)
        (ssaLiftBCMatrix (A := A)
          rho.marginalBC.spectralLogMatrix))
    (hSumB :
      Commute
        (ssaLiftABMatrix (C := C)
            rho.marginalAB.spectralLogMatrix +
          ssaLiftBCMatrix (A := A)
            rho.marginalBC.spectralLogMatrix)
        (ssaLiftBMatrix (A := A) (C := C)
          rho.marginalBOfABC.spectralLogMatrix)) :
    NormedSpace.exp (strongSubadditivityHamiltonian rho) =
      ssaLiftABMatrix (C := C) rho.marginalAB.matrix *
        ssaLiftBCMatrix (A := A) rho.marginalBC.matrix *
          (ssaLiftBMatrix (A := A) (C := C)
            rho.marginalBOfABC.matrix)⁻¹ := by
  unfold strongSubadditivityHamiltonian
  rw [normedSpace_exp_add_sub_of_commute _ _ _
      hABBC hSumB,
    normedSpace_exp_ssaLiftABMatrix_spectralLogMatrix
      rho.marginalAB hABPos,
    normedSpace_exp_ssaLiftBCMatrix_spectralLogMatrix
      rho.marginalBC hBCPos,
    normedSpace_exp_ssaLiftBMatrix_spectralLogMatrix
      rho.marginalBOfABC hBPos]

private theorem strongSubadditivity_traceExp_bound_of_commute
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C))
    (hABPos : rho.marginalAB.matrix.PosDef)
    (hBCPos : rho.marginalBC.matrix.PosDef)
    (hBPos : rho.marginalBOfABC.matrix.PosDef)
    (hABBC :
      Commute
        (ssaLiftABMatrix (C := C)
          rho.marginalAB.spectralLogMatrix)
        (ssaLiftBCMatrix (A := A)
          rho.marginalBC.spectralLogMatrix))
    (hSumB :
      Commute
        (ssaLiftABMatrix (C := C)
            rho.marginalAB.spectralLogMatrix +
          ssaLiftBCMatrix (A := A)
            rho.marginalBC.spectralLogMatrix)
        (ssaLiftBMatrix (A := A) (C := C)
          rho.marginalBOfABC.spectralLogMatrix)) :
    (NormedSpace.exp (strongSubadditivityHamiltonian rho)).trace.re ≤ 1 := by
  rw [normedSpace_exp_strongSubadditivityHamiltonian_of_commute rho
      hABPos hBCPos hBPos hABBC hSumB,
    trace_ssaMarginalLifts_mul_inv_eq_one rho hBPos]
  norm_num

private theorem re_trace_mul_strongSubadditivityHamiltonian
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) :
    Complex.re
        ((rho.matrix * strongSubadditivityHamiltonian rho).trace) =
      -vonNeumannEntropy rho.marginalAB -
        vonNeumannEntropy rho.marginalBC +
          vonNeumannEntropy rho.marginalBOfABC := by
  unfold strongSubadditivityHamiltonian
  rw [mul_sub, mul_add, Matrix.trace_sub, Matrix.trace_add,
    Complex.sub_re, Complex.add_re,
    re_trace_mul_ssaLiftABMatrix,
    re_trace_mul_ssaLiftBCMatrix,
    re_trace_mul_ssaLiftBMatrix]
  rw [← neg_eq_iff_eq_neg.mpr
      (vonNeumannEntropy_eq_neg_re_trace_mul_spectralLogMatrix
        rho.marginalAB),
    ← neg_eq_iff_eq_neg.mpr
      (vonNeumannEntropy_eq_neg_re_trace_mul_spectralLogMatrix
        rho.marginalBC),
    ← neg_eq_iff_eq_neg.mpr
      (vonNeumannEntropy_eq_neg_re_trace_mul_spectralLogMatrix
        rho.marginalBOfABC)]
  ring

private theorem vonNeumannEntropyStrongSubadditivity_of_traceExp_bound
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C))
    (htrace :
      (NormedSpace.exp (strongSubadditivityHamiltonian rho)).trace.re ≤ 1) :
    vonNeumannEntropy rho +
        vonNeumannEntropy rho.marginalBOfABC ≤
      vonNeumannEntropy rho.marginalAB +
        vonNeumannEntropy rho.marginalBC := by
  letI : Nonempty ((A × B) × C) := rho.nonempty
  have hentropy :=
    vonNeumannEntropy_le_neg_re_trace_mul_of_exp_trace_le_one rho
      (strongSubadditivityHamiltonian_isHermitian rho) htrace
  rw [re_trace_mul_strongSubadditivityHamiltonian] at hentropy
  linarith

private theorem marginalB_matrix_eq_average
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho) :
    rho.marginalB.matrix =
      ∑ i, (E.weight i : ℂ) • (E.state i).marginalB.matrix :=
  State.marginalB_matrix_eq_sum_smul_of_matrix_eq_sum_smul
    E.weight E.state rho hrho

/-- The conditional entropy
`S(A | B)_ρ = S(ρ_AB) - S(Tr_A ρ_AB)`. -/
def quantumConditionalEntropy (rho : State (A × B)) : ℝ :=
  vonNeumannEntropy rho - vonNeumannEntropy rho.marginalB

/-- The quantum mutual information
`I(A : B)_ρ = S(ρ_A) + S(ρ_B) - S(ρ_AB)`. -/
def quantumMutualInformation (rho : State (A × B)) : ℝ :=
  vonNeumannEntropy rho.marginalA + vonNeumannEntropy rho.marginalB -
    vonNeumannEntropy rho

/-- The finite-dimensional strong-subadditivity principle for the concrete
spectral entropy used in this file:
`S(ABC) + S(B) ≤ S(AB) + S(BC)`.

The natural-language problem asks that conditional-entropy concavity be used as
a governing entropy fact.  `QITBench.Base` supplies the required tripartite
marginals but no proof of strong subadditivity, so this proposition exposes the
missing analytic foundation explicitly instead of assuming the desired
ensemble inequality itself. -/
def VonNeumannEntropyStrongSubadditivity : Prop :=
  ∀ {C : Type w} [Fintype C] [DecidableEq C],
    ∀ rhoABC : State ((A × B) × C),
      vonNeumannEntropy rhoABC +
          vonNeumannEntropy rhoABC.marginalBOfABC ≤
        vonNeumannEntropy rhoABC.marginalAB +
          vonNeumannEntropy rhoABC.marginalBC

/-- Convexity of a real-valued function on density states, expressed using
binary convex combinations of their underlying density matrices. -/
def ConvexOnDensityStates (f : State X → ℝ) : Prop :=
  ∀ (rho sigma mix : State X) (t : ℝ),
    0 ≤ t →
    t ≤ 1 →
    mix.matrix =
      (t : ℂ) • rho.matrix + ((1 - t : ℝ) : ℂ) • sigma.matrix →
    f mix ≤ t * f rho + (1 - t) * f sigma

/-- Concavity of a real-valued function on density states, expressed using
binary convex combinations of their underlying density matrices. -/
def ConcaveOnDensityStates (f : State X → ℝ) : Prop :=
  ∀ (rho sigma mix : State X) (t : ℝ),
    0 ≤ t →
    t ≤ 1 →
    mix.matrix =
      (t : ℂ) • rho.matrix + ((1 - t : ℝ) : ℂ) • sigma.matrix →
    t * f rho + (1 - t) * f sigma ≤ f mix

/-- The two source formulas for quantum mutual information agree:
`I(A : B)_ρ = S(A)_ρ - S(A | B)_ρ`. -/
theorem quantumMutualInformation_eq_entropy_sub_conditionalEntropy
    (rho : State (A × B)) :
    quantumMutualInformation rho =
      vonNeumannEntropy rho.marginalA - quantumConditionalEntropy rho := by
  unfold quantumMutualInformation quantumConditionalEntropy
  ring

/-! ## Project-local Mathlib supplement — Spectral entropy concavity -/

private noncomputable def entropyUnitaryConjugate
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (rho : State α) : State α where
  matrix := (U : CMatrix α) * rho.matrix *
    Matrix.conjTranspose (U : CMatrix α)
  pos := rho.pos.mul_mul_conjTranspose_same (U : CMatrix α)
  trace_eq_one := by
    calc
      ((U : CMatrix α) * rho.matrix *
          Matrix.conjTranspose (U : CMatrix α)).trace =
          (Matrix.conjTranspose (U : CMatrix α) *
            (U : CMatrix α) * rho.matrix).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = rho.matrix.trace := by
        rw [show Matrix.conjTranspose (U : CMatrix α) *
            (U : CMatrix α) = 1 by
          simpa [Matrix.star_eq_conjTranspose] using
            Matrix.UnitaryGroup.star_mul_self U]
        simp
      _ = 1 := rho.trace_eq_one

private theorem state_eigenvalues_entropyUnitaryConjugate
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (rho : State α) :
    (entropyUnitaryConjugate U rho).pos.isHermitian.eigenvalues =
      rho.pos.isHermitian.eigenvalues := by
  apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2
  calc
    ((entropyUnitaryConjugate U rho).matrix).charpoly =
        (Matrix.conjTranspose (U : CMatrix α) *
          ((U : CMatrix α) * rho.matrix)).charpoly := by
      exact Matrix.charpoly_mul_comm _ _
    _ = rho.matrix.charpoly := by
      rw [← Matrix.mul_assoc]
      rw [show Matrix.conjTranspose (U : CMatrix α) *
          (U : CMatrix α) = 1 by
        simpa [Matrix.star_eq_conjTranspose] using
          Matrix.UnitaryGroup.star_mul_self U]
      simp

private theorem vonNeumannEntropy_entropyUnitaryConjugate
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (rho : State α) :
    vonNeumannEntropy (entropyUnitaryConjugate U rho) =
      vonNeumannEntropy rho := by
  unfold vonNeumannEntropy
  rw [state_eigenvalues_entropyUnitaryConjugate]

private theorem vonNeumannEntropy_eq_sum_negMulLog
    {α : Type*} [Fintype α] [DecidableEq α] (rho : State α) :
    vonNeumannEntropy rho =
      ∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i) := by
  unfold vonNeumannEntropy Real.negMulLog
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]

/-- The finite Hermitian functional calculus sends an affine real function to
the corresponding affine matrix expression. -/
theorem hermitian_cfc_affine
    {α : Type*} [Fintype α] [DecidableEq α]
    {M : CMatrix α} (hM : M.IsHermitian) (a b : ℝ) :
    hM.cfc (fun x => a * x + b) = a • M + b • 1 := by
  let U := hM.eigenvectorUnitary
  let lambda := hM.eigenvalues
  have hspectral :
      M = (U : CMatrix α) *
          Matrix.diagonal (Complex.ofReal ∘ lambda) *
            star (U : CMatrix α) := by
    simpa [U, lambda] using hM.spectral_theorem
  change
    (U : CMatrix α) *
        Matrix.diagonal
          (Complex.ofReal ∘ (fun x => a * x + b) ∘ lambda) *
          star (U : CMatrix α) =
      a • M + b • 1
  rw [hspectral]
  have hdiag :
      Matrix.diagonal
          (Complex.ofReal ∘ (fun x => a * x + b) ∘ lambda) =
        a • Matrix.diagonal (Complex.ofReal ∘ lambda) + b • 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Function.comp_apply, Complex.real_smul]
    · simp [hij]
  rw [hdiag, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [show (U : CMatrix α) * 1 * star (U : CMatrix α) = 1 by
    rw [Matrix.mul_one]
    simpa [U] using Unitary.coe_mul_star_self U]

/-- A state obtained by finite Hermitian functional calculus has entropy given
by applying the scalar entropy function to the original spectrum. -/
theorem vonNeumannEntropy_of_matrix_eq_cfc
    {α : Type*} [Fintype α] [DecidableEq α]
    (rho sigma : State α) (f : ℝ → ℝ)
    (hmat : sigma.matrix = cfc f rho.matrix) :
    vonNeumannEntropy sigma =
      ∑ i, Real.negMulLog (f (rho.pos.isHermitian.eigenvalues i)) := by
  have hroots :
      sigma.matrix.charpoly.roots =
        Multiset.map
          (fun i =>
            ((f (rho.pos.isHermitian.eigenvalues i) : ℝ) : ℂ))
          Finset.univ.val := by
    rw [hmat, rho.pos.isHermitian.charpoly_cfc_eq,
      Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C]
      simp
    · exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        Polynomial.X_sub_C_ne_zero _
  have heigen := sigma.pos.isHermitian.roots_charpoly_eq_eigenvalues
  rw [hroots] at heigen
  have hmapped := congrArg
    (fun s : Multiset ℂ =>
      (s.map (fun z => Real.negMulLog z.re)).sum) heigen
  rw [vonNeumannEntropy_eq_sum_negMulLog]
  simpa [Multiset.map_map, Function.comp_def] using hmapped.symm

private theorem entropy_unitary_row_normSq_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (j : α) :
    ∑ i, Complex.normSq ((U : CMatrix α) j i) = 1 := by
  have hunit : (U : CMatrix α) * star (U : CMatrix α) = 1 :=
    Unitary.coe_mul_star_self U
  have h := congrArg (fun M : CMatrix α => M j j) hunit
  dsimp only at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← Complex.ofReal_inj]
  simpa [Complex.normSq_eq_conj_mul_self, mul_comm] using h

private theorem entropy_unitary_col_normSq_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (i : α) :
    ∑ j, Complex.normSq ((U : CMatrix α) j i) = 1 := by
  have hunit : star (U : CMatrix α) * (U : CMatrix α) = 1 :=
    Unitary.coe_star_mul_self U
  have h := congrArg (fun M : CMatrix α => M i i) hunit
  dsimp only at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← Complex.ofReal_inj]
  simpa [Complex.normSq_eq_conj_mul_self] using h

private theorem state_diag_re_eq_eigenvalue_average
    {α : Type*} [Fintype α] [DecidableEq α]
    (rho : State α) (j : α) :
    Complex.re (rho.matrix j j) =
      ∑ i, Complex.normSq
          ((rho.pos.isHermitian.eigenvectorUnitary : CMatrix α) j i) *
        rho.pos.isHermitian.eigenvalues i := by
  let U := rho.pos.isHermitian.eigenvectorUnitary
  let lambda := rho.pos.isHermitian.eigenvalues
  have hspectral := rho.pos.isHermitian.spectral_theorem
  have h := congrArg (fun M : CMatrix α => Complex.re (M j j)) hspectral
  dsimp only at h
  change Complex.re (rho.matrix j j) =
    Complex.re (((U : CMatrix α) *
      Matrix.diagonal (Complex.ofReal ∘ lambda) *
        star (U : CMatrix α)) j j) at h
  rw [h]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_comm, mul_left_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_apply]
  dsimp [U, lambda]
  ring

private theorem state_diag_re_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    (rho : State α) (i : α) :
    0 ≤ Complex.re (rho.matrix i i) :=
  (Complex.nonneg_iff.mp rho.pos.diag_nonneg).1

private theorem vonNeumannEntropy_le_sum_negMulLog_diagonal
    {α : Type*} [Fintype α] [DecidableEq α]
    (rho : State α) :
    vonNeumannEntropy rho ≤
      ∑ j, Real.negMulLog (Complex.re (rho.matrix j j)) := by
  let U := rho.pos.isHermitian.eigenvectorUnitary
  let lambda := rho.pos.isHermitian.eigenvalues
  have hrow (j : α) :
      (∑ i, Complex.normSq ((U : CMatrix α) j i) *
          Real.negMulLog (lambda i)) ≤
        Real.negMulLog (Complex.re (rho.matrix j j)) := by
    have hj := Real.strictConcaveOn_negMulLog.concaveOn.le_map_sum
      (t := Finset.univ)
      (w := fun i : α => Complex.normSq ((U : CMatrix α) j i))
      (p := lambda)
      (fun _ _ => Complex.normSq_nonneg _)
      (by simpa using entropy_unitary_row_normSq_sum U j)
      (fun i _ => rho.pos.eigenvalues_nonneg i)
    calc
      (∑ i, Complex.normSq ((U : CMatrix α) j i) *
          Real.negMulLog (lambda i)) ≤
          Real.negMulLog
            (∑ i, Complex.normSq ((U : CMatrix α) j i) * lambda i) := by
        simpa [smul_eq_mul] using hj
      _ = Real.negMulLog (Complex.re (rho.matrix j j)) := by
        rw [state_diag_re_eq_eigenvalue_average]
  rw [vonNeumannEntropy_eq_sum_negMulLog]
  calc
    (∑ i, Real.negMulLog (rho.pos.isHermitian.eigenvalues i)) =
        ∑ j, ∑ i, Complex.normSq ((U : CMatrix α) j i) *
          Real.negMulLog (lambda i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, entropy_unitary_col_normSq_sum]
      simp [lambda]
    _ ≤ ∑ j, Real.negMulLog (Complex.re (rho.matrix j j)) :=
      Finset.sum_le_sum fun j _ => hrow j

/-- Von Neumann entropy is concave for every finite ensemble average; this
project-local theorem supplies the ordinary entropy layer below quantum SSA. -/
theorem vonNeumannEntropy_concave
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι X) (rho : State X)
    (hrho : E.IsAverage rho) :
    ∑ i, E.weight i * vonNeumannEntropy (E.state i) ≤
      vonNeumannEntropy rho := by
  classical
  let U : Matrix.unitaryGroup X ℂ :=
    star rho.pos.isHermitian.eigenvectorUnitary
  let rho' : State X := entropyUnitaryConjugate U rho
  let sigma' : ι → State X :=
    fun i => entropyUnitaryConjugate U (E.state i)
  have hrhoDiagonal :
      rho'.matrix =
        Matrix.diagonal
          (Complex.ofReal ∘ rho.pos.isHermitian.eigenvalues) := by
    change (star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix X)) *
        rho.matrix *
          Matrix.conjTranspose
            (star (rho.pos.isHermitian.eigenvectorUnitary : CMatrix X)) =
      Matrix.diagonal
        (Complex.ofReal ∘ rho.pos.isHermitian.eigenvalues)
    simpa [Matrix.star_eq_conjTranspose] using
      rho.pos.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hrhoAverage :
      rho'.matrix = ∑ i, (E.weight i : ℂ) • (sigma' i).matrix := by
    change (U : CMatrix X) * rho.matrix *
          Matrix.conjTranspose (U : CMatrix X) =
      ∑ i, (E.weight i : ℂ) •
        ((U : CMatrix X) * (E.state i).matrix *
          Matrix.conjTranspose (U : CMatrix X))
    rw [hrho, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hcomponent (i : ι) :
      vonNeumannEntropy (E.state i) ≤
        ∑ j, Real.negMulLog (Complex.re ((sigma' i).matrix j j)) := by
    rw [← vonNeumannEntropy_entropyUnitaryConjugate U (E.state i)]
    exact vonNeumannEntropy_le_sum_negMulLog_diagonal (sigma' i)
  have hweighted :
      (∑ i, E.weight i * vonNeumannEntropy (E.state i)) ≤
        ∑ i, E.weight i *
          ∑ j, Real.negMulLog (Complex.re ((sigma' i).matrix j j)) :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hcomponent i) (E.weight_nonneg i)
  have hdiagAverage (j : X) :
      (∑ i, E.weight i * Complex.re ((sigma' i).matrix j j)) =
        Complex.re (rho'.matrix j j) := by
    have h := congrArg
      (fun M : CMatrix X => Complex.re (M j j)) hrhoAverage
    simpa [Matrix.sum_apply, Matrix.smul_apply] using h.symm
  have hcoordinate (j : X) :
      (∑ i, E.weight i *
          Real.negMulLog (Complex.re ((sigma' i).matrix j j))) ≤
        Real.negMulLog (Complex.re (rho'.matrix j j)) := by
    have hj := Real.strictConcaveOn_negMulLog.concaveOn.le_map_sum
      (t := Finset.univ)
      (w := E.weight)
      (p := fun i => Complex.re ((sigma' i).matrix j j))
      (fun i _ => E.weight_nonneg i)
      (by simpa using E.weight_sum_one)
      (fun i _ => state_diag_re_nonneg (sigma' i) j)
    simpa [smul_eq_mul, hdiagAverage] using hj
  calc
    (∑ i, E.weight i * vonNeumannEntropy (E.state i)) ≤
        ∑ i, E.weight i *
          ∑ j, Real.negMulLog (Complex.re ((sigma' i).matrix j j)) :=
      hweighted
    _ = ∑ j, ∑ i, E.weight i *
          Real.negMulLog (Complex.re ((sigma' i).matrix j j)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ j, Real.negMulLog (Complex.re (rho'.matrix j j)) :=
      Finset.sum_le_sum fun j _ => hcoordinate j
    _ = ∑ j, Real.negMulLog
          (rho.pos.isHermitian.eigenvalues j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hrhoDiagonal]
      simp
    _ = vonNeumannEntropy rho :=
      (vonNeumannEntropy_eq_sum_negMulLog rho).symm

/-- Applying the `B` marginal to every member of a finite state ensemble
preserves its probability weights. -/
def FiniteStateEnsemble.marginalB
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) :
    FiniteStateEnsemble ι B where
  weight := E.weight
  state i := (E.state i).marginalB
  weight_nonneg := E.weight_nonneg
  weight_sum_one := E.weight_sum_one

/-- The `B` marginal of an ensemble average is the average of the component
`B` marginals. -/
theorem FiniteStateEnsemble.marginalB_isAverage
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho) :
    E.marginalB.IsAverage rho.marginalB :=
  marginalB_matrix_eq_average E rho hrho

/-- Every positive-weight component of an ensemble vanishes on the kernel of
its average state, the matrix form of support inclusion. -/
theorem FiniteStateEnsemble.component_mulVec_eq_zero_of_average
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι X) (rho : State X)
    (hrho : E.IsAverage rho) (i : ι) (hi : 0 < E.weight i)
    (v : X → ℂ) (hv : rho.matrix.mulVec v = 0) :
    (E.state i).matrix.mulVec v = 0 := by
  have hsum :
      (∑ j, E.weight j *
        Complex.re (star v ⬝ᵥ (E.state j).matrix.mulVec v)) = 0 := by
    have h := congrArg
      (fun M : CMatrix X => Complex.re (star v ⬝ᵥ M.mulVec v)) hrho
    change
      Complex.re (star v ⬝ᵥ rho.matrix.mulVec v) =
        Complex.re
          (star v ⬝ᵥ
            (∑ j, (E.weight j : ℂ) • (E.state j).matrix).mulVec v) at h
    rw [hv] at h
    simpa [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
      Complex.mul_re] using h.symm
  have hterm_nonneg (j : ι) :
      0 ≤ E.weight j *
        Complex.re (star v ⬝ᵥ (E.state j).matrix.mulVec v) := by
    exact mul_nonneg (E.weight_nonneg j)
      (Complex.nonneg_iff.mp
        ((E.state j).pos.dotProduct_mulVec_nonneg v)).1
  have hterm_zero :
      E.weight i *
        Complex.re (star v ⬝ᵥ (E.state i).matrix.mulVec v) = 0 := by
    exact
      ((Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => hterm_nonneg j)).mp hsum) i (Finset.mem_univ i)
  have hreal :
      Complex.re (star v ⬝ᵥ (E.state i).matrix.mulVec v) = 0 :=
    (mul_eq_zero.mp hterm_zero).resolve_left hi.ne'
  have hquadratic_nonneg :=
    (E.state i).pos.dotProduct_mulVec_nonneg v
  have himag :
      Complex.im (star v ⬝ᵥ (E.state i).matrix.mulVec v) = 0 :=
    (Complex.nonneg_iff.mp hquadratic_nonneg).2.symm
  have hquadratic :
      star v ⬝ᵥ (E.state i).matrix.mulVec v = 0 := by
    apply Complex.ext
    · simpa using hreal
    · simpa using himag
  exact ((E.state i).pos.dotProduct_mulVec_zero_iff v).mp hquadratic

/-- Positive-weight component marginals are supported on the average
`B`-marginal, including when that average is singular. -/
theorem FiniteStateEnsemble.component_marginalB_mulVec_eq_zero_of_average
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho) (i : ι) (hi : 0 < E.weight i)
    (v : B → ℂ) (hv : rho.marginalB.matrix.mulVec v = 0) :
    (E.state i).marginalB.matrix.mulVec v = 0 := by
  exact E.marginalB.component_mulVec_eq_zero_of_average rho.marginalB
    (E.marginalB_isAverage rho hrho) i hi v hv

/-- Entropy concavity applied after the `B` marginal map. -/
theorem vonNeumannEntropy_marginalB_concave
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho) :
    ∑ i, E.weight i * vonNeumannEntropy (E.state i).marginalB ≤
      vonNeumannEntropy rho.marginalB := by
  exact vonNeumannEntropy_concave E.marginalB rho.marginalB
    (E.marginalB_isAverage rho hrho)

/-- The Jensen gap in von Neumann entropy for a specified ensemble average. -/
def FiniteStateEnsemble.entropyConcavityGap
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι X) (rho : State X) : ℝ :=
  vonNeumannEntropy rho -
    ∑ i, E.weight i * vonNeumannEntropy (E.state i)

/-- The entropy concavity gap of every finite state ensemble is nonnegative. -/
theorem FiniteStateEnsemble.entropyConcavityGap_nonneg
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι X) (rho : State X)
    (hrho : E.IsAverage rho) :
    0 ≤ E.entropyConcavityGap rho := by
  exact sub_nonneg.mpr (vonNeumannEntropy_concave E rho hrho)

/-- The entropy concavity gap is the ensemble average of the finite spectral
relative entropies to the average state. -/
theorem FiniteStateEnsemble.entropyConcavityGap_eq_sum_spectralRelativeEntropy
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι X) (rho : State X)
    (hrho : E.IsAverage rho) :
    E.entropyConcavityGap rho =
      ∑ i, E.weight i * (E.state i).spectralRelativeEntropy rho := by
  have htrace :
      (∑ i, E.weight i *
          Complex.re (((E.state i).matrix * rho.spectralLogMatrix).trace)) =
        Complex.re ((rho.matrix * rho.spectralLogMatrix).trace) := by
    have h := congrArg
      (fun M : CMatrix X =>
        Complex.re ((M * rho.spectralLogMatrix).trace)) hrho
    simpa [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
      Matrix.trace_smul, Complex.mul_re] using h.symm
  have hself := rho.spectralRelativeEntropy_self
  rw [State.spectralRelativeEntropy_eq_spectral_sum_sub_trace] at hself
  unfold FiniteStateEnsemble.entropyConcavityGap vonNeumannEntropy
  simp_rw [State.spectralRelativeEntropy_eq_spectral_sum_sub_trace,
    mul_sub, mul_neg]
  rw [Finset.sum_neg_distrib]
  rw [Finset.sum_sub_distrib, htrace]
  linarith

/-- Conditional-entropy concavity is exactly contraction of the ordinary
entropy concavity gap under the `B` marginal. -/
theorem quantumConditionalEntropy_concave_iff_marginalB_entropyConcavityGap_le
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B)) :
    (∑ i, E.weight i * quantumConditionalEntropy (E.state i) ≤
        quantumConditionalEntropy rho) ↔
      E.marginalB.entropyConcavityGap rho.marginalB ≤
        E.entropyConcavityGap rho := by
  simp only [FiniteStateEnsemble.entropyConcavityGap,
    FiniteStateEnsemble.marginalB]
  unfold quantumConditionalEntropy
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  constructor <;> intro h <;> linarith

/-- Data processing for every positive-weight component's finite spectral
relative entropy implies contraction of an ensemble's entropy concavity gap
under the `B` marginal. -/
theorem FiniteStateEnsemble.marginalB_entropyConcavityGap_le_of_spectralRelativeEntropy_le
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho)
    (hdpi : ∀ i, 0 < E.weight i →
      (E.state i).marginalB.spectralRelativeEntropy rho.marginalB ≤
        (E.state i).spectralRelativeEntropy rho) :
    E.marginalB.entropyConcavityGap rho.marginalB ≤
      E.entropyConcavityGap rho := by
  rw [E.marginalB.entropyConcavityGap_eq_sum_spectralRelativeEntropy
      rho.marginalB (E.marginalB_isAverage rho hrho),
    E.entropyConcavityGap_eq_sum_spectralRelativeEntropy rho hrho]
  change
    (∑ i, E.weight i *
      (E.state i).marginalB.spectralRelativeEntropy rho.marginalB) ≤
        ∑ i, E.weight i * (E.state i).spectralRelativeEntropy rho
  exact Finset.sum_le_sum fun i _ => by
    rcases (E.weight_nonneg i).eq_or_lt with hi | hi
    · simp [← hi]
    · exact mul_le_mul_of_nonneg_left (hdpi i hi) hi.le

/-- Conditional entropy is concave for an ensemble whenever finite spectral
relative entropy contracts under the `B` marginal for its positive-weight
components. -/
theorem quantumConditionalEntropy_concave_of_spectralRelativeEntropy_le
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho)
    (hdpi : ∀ i, 0 < E.weight i →
      (E.state i).marginalB.spectralRelativeEntropy rho.marginalB ≤
        (E.state i).spectralRelativeEntropy rho) :
    ∑ i, E.weight i * quantumConditionalEntropy (E.state i) ≤
      quantumConditionalEntropy rho := by
  rw [quantumConditionalEntropy_concave_iff_marginalB_entropyConcavityGap_le]
  exact E.marginalB_entropyConcavityGap_le_of_spectralRelativeEntropy_le
    rho hrho hdpi

/-- Partial trace over the left factor commutes with real scalar
multiplication. -/
theorem partialTraceA_real_smul (r : ℝ) (M : CMatrix (A × B)) :
    partialTraceA (r • M) = r • partialTraceA M := by
  ext b b'
  simp only [partialTraceA, Matrix.smul_apply, Complex.real_smul]
  exact (Finset.mul_sum _ _ _).symm

/-- Partial trace over the right factor commutes with real scalar
multiplication. -/
theorem partialTraceB_real_smul (r : ℝ) (M : CMatrix (A × B)) :
    partialTraceB (r • M) = r • partialTraceB M := by
  ext a a'
  simp only [partialTraceB, Matrix.smul_apply, Complex.real_smul]
  exact (Finset.mul_sum _ _ _).symm

/-- Strict positive definiteness survives tracing out a nonempty left tensor
factor.  This is the matrix bridge needed by positive-definite SSA proofs. -/
theorem partialTraceA_posDef [Nonempty A]
    {M : CMatrix (A × B)} (hM : M.PosDef) :
    (partialTraceA M).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · exact partialTraceA_isHermitian hM.isHermitian
  · intro v hv
    let lift : A → (A × B → ℂ) :=
      fun a x => if x.1 = a then v x.2 else 0
    have hlift_ne (a : A) : lift a ≠ 0 := by
      intro h
      apply hv
      funext b
      have hab := congrFun h (a, b)
      simpa [lift] using hab
    have hpos (a : A) :
        0 < star (lift a) ⬝ᵥ M.mulVec (lift a) :=
      hM.dotProduct_mulVec_pos (hlift_ne a)
    have hidentity :
        star v ⬝ᵥ (partialTraceA M).mulVec v =
          ∑ a, star (lift a) ⬝ᵥ M.mulVec (lift a) := by
      simp [dotProduct, Matrix.mulVec, partialTraceA, lift,
        Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, apply_ite]
      rw [Finset.sum_comm_cycle]
    rw [hidentity]
    exact Finset.sum_pos (fun a _ => hpos a) Finset.univ_nonempty

/-- Strict positive definiteness survives tracing out a nonempty right tensor
factor.  This is the symmetric matrix bridge needed by entropy SSA proofs. -/
theorem partialTraceB_posDef [Nonempty B]
    {M : CMatrix (A × B)} (hM : M.PosDef) :
    (partialTraceB M).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · exact partialTraceB_isHermitian hM.isHermitian
  · intro v hv
    let lift : B → (A × B → ℂ) :=
      fun b x => if x.2 = b then v x.1 else 0
    have hlift_ne (b : B) : lift b ≠ 0 := by
      intro h
      apply hv
      funext a
      have hab := congrFun h (a, b)
      simpa [lift] using hab
    have hpos (b : B) :
        0 < star (lift b) ⬝ᵥ M.mulVec (lift b) :=
      hM.dotProduct_mulVec_pos (hlift_ne b)
    have hidentity :
        star v ⬝ᵥ (partialTraceB M).mulVec v =
          ∑ b, star (lift b) ⬝ᵥ M.mulVec (lift b) := by
      simp [dotProduct, Matrix.mulVec, partialTraceB, lift,
        Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, apply_ite]
      rw [Finset.sum_comm_cycle]
    rw [hidentity]
    exact Finset.sum_pos (fun b _ => hpos b) Finset.univ_nonempty

/-- A positive-definite bipartite state has a positive-definite `B`
marginal whenever the traced subsystem is nonempty. -/
theorem State.marginalB_posDef [Nonempty A]
    (rho : State (A × B)) (hrho : rho.matrix.PosDef) :
    rho.marginalB.matrix.PosDef := by
  rw [State.marginalB_matrix]
  exact partialTraceA_posDef hrho

/-- A positive-definite bipartite state has a positive-definite `A`
marginal whenever the traced subsystem is nonempty. -/
theorem State.marginalA_posDef [Nonempty B]
    (rho : State (A × B)) (hrho : rho.matrix.PosDef) :
    rho.marginalA.matrix.PosDef := by
  rw [State.marginalA_matrix]
  exact partialTraceB_posDef hrho

/-- Relabelling a finite basis preserves strict positive definiteness. -/
theorem State.reindex_posDef
    {Y : Type u} {Z : Type v}
    [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (rho : State Y) (e : Y ≃ Z) (hrho : rho.matrix.PosDef) :
    (rho.reindex e).matrix.PosDef := by
  exact hrho.submatrix e.symm.injective

/-- The `BC` marginal is the ordinary right marginal after reassociating the
tripartite basis. -/
theorem State.reindex_prodAssoc_marginalB_eq_marginalBC
    {C : Type x} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) :
    (rho.reindex (Equiv.prodAssoc A B C)).marginalB =
      rho.marginalBC := by
  apply State.ext
  ext bc bc'
  simp [State.reindex, State.marginalB, State.marginalBC, partialTraceA]

/-- A positive-definite tripartite state has a positive-definite `AB`
marginal. -/
theorem State.marginalAB_posDef
    {C : Type x} [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : State ((A × B) × C)) (hrho : rho.matrix.PosDef) :
    rho.marginalAB.matrix.PosDef := by
  exact State.marginalA_posDef rho hrho

/-- A positive-definite tripartite state has a positive-definite `BC`
marginal. -/
theorem State.marginalBC_posDef
    {C : Type x} [Fintype C] [DecidableEq C] [Nonempty A]
    (rho : State ((A × B) × C)) (hrho : rho.matrix.PosDef) :
    rho.marginalBC.matrix.PosDef := by
  have hreindexed :
      (rho.reindex (Equiv.prodAssoc A B C)).matrix.PosDef :=
    State.reindex_posDef rho (Equiv.prodAssoc A B C) hrho
  have hmarginal :=
    State.marginalB_posDef
      (rho.reindex (Equiv.prodAssoc A B C)) hreindexed
  rw [State.reindex_prodAssoc_marginalB_eq_marginalBC] at hmarginal
  exact hmarginal

/-- A positive-definite tripartite state has a positive-definite middle
marginal. -/
theorem State.marginalBOfABC_posDef
    {C : Type x} [Fintype C] [DecidableEq C]
    [Nonempty A] [Nonempty C]
    (rho : State ((A × B) × C)) (hrho : rho.matrix.PosDef) :
    rho.marginalBOfABC.matrix.PosDef := by
  rw [State.marginalBOfABC_eq]
  exact State.marginalB_posDef rho.marginalAB
    (State.marginalAB_posDef rho hrho)

/-- The full-rank maximally mixed state on a nonempty finite basis. -/
def maximallyMixedState (Y : Type x) [Fintype Y] [DecidableEq Y]
    [Nonempty Y] : State Y where
  matrix := (Fintype.card Y : ℝ)⁻¹ • (1 : CMatrix Y)
  pos :=
    Matrix.PosSemidef.one.smul
      (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card Y)))
  trace_eq_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    simp [Fintype.card_ne_zero]

/-- The maximally mixed state has a strictly positive density matrix. -/
theorem maximallyMixedState_posDef
    (Y : Type x) [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    (maximallyMixedState Y).matrix.PosDef := by
  exact Matrix.PosDef.one.smul
    (inv_pos.mpr (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Y)))

/-- The `B` marginal of a bipartite maximally mixed state is maximally
mixed. -/
theorem maximallyMixedState_marginalB [Nonempty A] [Nonempty B] :
    (maximallyMixedState (A × B)).marginalB =
      maximallyMixedState B := by
  apply State.ext
  ext b b'
  by_cases h : b = b'
  · subst b'
    simp [State.marginalB, partialTraceA, maximallyMixedState,
      Fintype.card_prod]
    field_simp
  · simp [State.marginalB, partialTraceA, maximallyMixedState,
      Fintype.card_prod, h]

/-- The `A` marginal of a bipartite maximally mixed state is maximally
mixed. -/
theorem maximallyMixedState_marginalA [Nonempty A] [Nonempty B] :
    (maximallyMixedState (A × B)).marginalA =
      maximallyMixedState A := by
  apply State.ext
  ext a a'
  by_cases h : a = a'
  · subst a'
    simp [State.marginalA, partialTraceB, maximallyMixedState,
      Fintype.card_prod]
  · simp [State.marginalA, partialTraceB, maximallyMixedState,
      Fintype.card_prod, h]

/-- The `BC` marginal of a tripartite maximally mixed state is maximally
mixed. -/
theorem maximallyMixedState_marginalBC
    {C : Type x} [Fintype C] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C] :
    (maximallyMixedState ((A × B) × C)).marginalBC =
      maximallyMixedState (B × C) := by
  apply State.ext
  ext bc bc'
  by_cases h : bc = bc'
  · subst bc'
    simp [State.marginalBC, maximallyMixedState, Fintype.card_prod]
    field_simp
  · have hfull (a : A) :
        ((a, bc.1), bc.2) ≠ ((a, bc'.1), bc'.2) := by
      intro hEq
      apply h
      apply Prod.ext
      · exact congrArg (fun z => z.1.2) hEq
      · exact congrArg (fun z => z.2) hEq
    simp [State.marginalBC, maximallyMixedState, Fintype.card_prod,
      hfull]
    exact Matrix.one_apply_ne h

/-- The normalized convex combination of two density states. -/
def stateConvexCombination (rho sigma : State X) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : State X where
  matrix := t • rho.matrix + (1 - t) • sigma.matrix
  pos :=
    (rho.pos.smul ht0).add
      (sigma.pos.smul (sub_nonneg.mpr ht1))
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      rho.trace_eq_one, sigma.trace_eq_one]
    simp

/-- Taking the `BC` marginal commutes with a normalized convex
combination. -/
theorem stateConvexCombination_marginalBC
    {C : Type x} [Fintype C] [DecidableEq C]
    (rho sigma : State ((A × B) × C)) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (stateConvexCombination rho sigma t ht0 ht1).marginalBC =
      stateConvexCombination rho.marginalBC sigma.marginalBC
        t ht0 ht1 := by
  apply State.ext
  ext bc bc'
  simp [State.marginalBC, stateConvexCombination,
    Finset.sum_add_distrib, Finset.mul_sum]

/-- A convex combination is positive definite when its right component is
positive definite and has strictly positive weight. -/
theorem stateConvexCombination_posDef_of_right
    (rho sigma : State X) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hsigma : sigma.matrix.PosDef) :
    (stateConvexCombination rho sigma t ht0 ht1.le).matrix.PosDef := by
  exact Matrix.PosDef.posSemidef_add (rho.pos.smul ht0)
    (hsigma.smul (sub_pos.mpr ht1))

/-- The standard full-rank regularization
`(1 - 1/(n+2))ρ + (1/(n+2))I/d` of a density state. -/
def stateRegularization [Nonempty X] (rho : State X) (n : ℕ) : State X :=
  stateConvexCombination rho (maximallyMixedState X)
    (1 - 1 / (n + 2 : ℝ))
    (by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hn : (1 : ℝ) ≤ n + 2 := by linarith
      have hden : (0 : ℝ) < n + 2 := by linarith
      exact sub_nonneg.mpr ((div_le_one hden).2 hn))
    (by
      have hden : (0 : ℝ) ≤ n + 2 := by positivity
      exact sub_le_self _ (one_div_nonneg.mpr hden))

/-- The density matrix of the standard full-rank regularization. -/
@[simp] theorem stateRegularization_matrix [Nonempty X]
    (rho : State X) (n : ℕ) :
    (stateRegularization rho n).matrix =
      (1 - 1 / (n + 2 : ℝ)) • rho.matrix +
        (1 / (n + 2 : ℝ)) • (maximallyMixedState X).matrix := by
  unfold stateRegularization stateConvexCombination
  change
    (1 - 1 / (n + 2 : ℝ)) • rho.matrix +
        (1 - (1 - 1 / (n + 2 : ℝ))) •
          (maximallyMixedState X).matrix =
      (1 - 1 / (n + 2 : ℝ)) • rho.matrix +
        (1 / (n + 2 : ℝ)) • (maximallyMixedState X).matrix
  rw [show (1 : ℝ) - (1 - 1 / (n + 2 : ℝ)) =
      1 / (n + 2 : ℝ) by ring]

/-- Standard regularization is the affine Hermitian functional calculus of
the original density matrix. -/
theorem stateRegularization_matrix_eq_cfc [Nonempty X]
    (rho : State X) (n : ℕ) :
    (stateRegularization rho n).matrix =
      cfc
        (fun x =>
          (1 - 1 / (n + 2 : ℝ)) * x +
            (1 / (n + 2 : ℝ)) * (Fintype.card X : ℝ)⁻¹)
        rho.matrix := by
  rw [rho.pos.isHermitian.cfc_eq,
    hermitian_cfc_affine, stateRegularization_matrix]
  unfold maximallyMixedState
  change
    (1 - 1 / (n + 2 : ℝ)) • rho.matrix +
        (1 / (n + 2 : ℝ)) •
          ((Fintype.card X : ℝ)⁻¹ • (1 : CMatrix X)) =
      (1 - 1 / (n + 2 : ℝ)) • rho.matrix +
        ((1 / (n + 2 : ℝ)) * (Fintype.card X : ℝ)⁻¹) •
          (1 : CMatrix X)
  rw [smul_smul]

/-- Entropy along the standard regularization is the scalar entropy of the
affinely regularized eigenvalues. -/
theorem vonNeumannEntropy_stateRegularization [Nonempty X]
    (rho : State X) (n : ℕ) :
    vonNeumannEntropy (stateRegularization rho n) =
      ∑ i, Real.negMulLog
        ((1 - 1 / (n + 2 : ℝ)) *
            rho.pos.isHermitian.eigenvalues i +
          (1 / (n + 2 : ℝ)) * (Fintype.card X : ℝ)⁻¹) := by
  exact vonNeumannEntropy_of_matrix_eq_cfc rho
    (stateRegularization rho n)
    (fun x =>
      (1 - 1 / (n + 2 : ℝ)) * x +
        (1 / (n + 2 : ℝ)) * (Fintype.card X : ℝ)⁻¹)
    (stateRegularization_matrix_eq_cfc rho n)

/-- Von Neumann entropy of the standard full-rank regularization converges to
the entropy of the original state. -/
theorem tendsto_vonNeumannEntropy_stateRegularization [Nonempty X]
    (rho : State X) :
    Filter.Tendsto
      (fun n => vonNeumannEntropy (stateRegularization rho n))
      Filter.atTop (nhds (vonNeumannEntropy rho)) := by
  have hden :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 2
      tendsto_natCast_atTop_atTop
  have heps :
      Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2))
        Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hterm (i : X) :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.negMulLog
            ((1 - 1 / (n + 2 : ℝ)) *
                rho.pos.isHermitian.eigenvalues i +
              (1 / (n + 2 : ℝ)) * (Fintype.card X : ℝ)⁻¹))
        Filter.atTop
        (nhds
          (Real.negMulLog (rho.pos.isHermitian.eigenvalues i))) := by
    apply Real.continuous_negMulLog.continuousAt.tendsto.comp
    convert
      ((heps.const_sub 1).mul tendsto_const_nhds).add
        (heps.mul tendsto_const_nhds) using 1 <;> ring
  have hsum := tendsto_finsetSum (Finset.univ : Finset X)
    (fun i _ => hterm i)
  rw [vonNeumannEntropy_eq_sum_negMulLog]
  simpa only [vonNeumannEntropy_stateRegularization] using hsum

/-- Every standard regularization has a positive-definite density matrix. -/
theorem stateRegularization_posDef [Nonempty X]
    (rho : State X) (n : ℕ) :
    (stateRegularization rho n).matrix.PosDef := by
  unfold stateRegularization
  exact stateConvexCombination_posDef_of_right
    rho (maximallyMixedState X) (1 - 1 / (n + 2 : ℝ))
    (by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hn : (1 : ℝ) ≤ n + 2 := by linarith
      have hden : (0 : ℝ) < n + 2 := by linarith
      exact sub_nonneg.mpr ((div_le_one hden).2 hn))
    (by
      have hden : (0 : ℝ) < n + 2 := by positivity
      exact sub_lt_self _ (one_div_pos.mpr hden))
    (maximallyMixedState_posDef X)

/-- Standard full-rank regularization commutes with the `B` marginal. -/
theorem stateRegularization_marginalB [Nonempty A] [Nonempty B]
    (rho : State (A × B)) (n : ℕ) :
    (stateRegularization rho n).marginalB =
      stateRegularization rho.marginalB n := by
  have huniform := congrArg State.matrix
    (maximallyMixedState_marginalB (A := A) (B := B))
  rw [State.marginalB_matrix] at huniform
  apply State.ext
  rw [State.marginalB_matrix, stateRegularization_matrix,
    partialTraceA_add, partialTraceA_real_smul,
    partialTraceA_real_smul,
    ← State.marginalB_matrix,
    huniform,
    stateRegularization_matrix]

/-- Standard full-rank regularization commutes with the `A` marginal. -/
theorem stateRegularization_marginalA [Nonempty A] [Nonempty B]
    (rho : State (A × B)) (n : ℕ) :
    (stateRegularization rho n).marginalA =
      stateRegularization rho.marginalA n := by
  have huniform := congrArg State.matrix
    (maximallyMixedState_marginalA (A := A) (B := B))
  rw [State.marginalA_matrix] at huniform
  apply State.ext
  rw [State.marginalA_matrix, stateRegularization_matrix,
    partialTraceB_add, partialTraceB_real_smul,
    partialTraceB_real_smul,
    ← State.marginalA_matrix,
    huniform,
    stateRegularization_matrix]

/-- Standard full-rank regularization commutes with the `AB` marginal of a
tripartite state. -/
theorem stateRegularization_marginalAB
    {C : Type x} [Fintype C] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : State ((A × B) × C)) (n : ℕ) :
    (stateRegularization rho n).marginalAB =
      stateRegularization rho.marginalAB n := by
  simpa only [State.marginalAB_eq_marginalA] using
    stateRegularization_marginalA (A := A × B) (B := C) rho n

/-- Standard full-rank regularization commutes with the `BC` marginal of a
tripartite state. -/
theorem stateRegularization_marginalBC
    {C : Type x} [Fintype C] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : State ((A × B) × C)) (n : ℕ) :
    (stateRegularization rho n).marginalBC =
      stateRegularization rho.marginalBC n := by
  unfold stateRegularization
  rw [stateConvexCombination_marginalBC,
    maximallyMixedState_marginalBC]

/-- Standard full-rank regularization commutes with the middle-system
marginal of a tripartite state. -/
theorem stateRegularization_marginalBOfABC
    {C : Type x} [Fintype C] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : State ((A × B) × C)) (n : ℕ) :
    (stateRegularization rho n).marginalBOfABC =
      stateRegularization rho.marginalBOfABC n := by
  rw [State.marginalBOfABC_eq, stateRegularization_marginalAB,
    stateRegularization_marginalB, State.marginalBOfABC_eq]

/-- Regularize every component of a finite state ensemble by the same
full-rank maximally mixed perturbation. -/
def FiniteStateEnsemble.regularization [Nonempty X]
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι X) (n : ℕ) :
    FiniteStateEnsemble ι X where
  weight := E.weight
  state i := stateRegularization (E.state i) n
  weight_nonneg := E.weight_nonneg
  weight_sum_one := E.weight_sum_one

/-- Regularization preserves a specified finite ensemble average. -/
theorem FiniteStateEnsemble.regularization_isAverage [Nonempty X]
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι X) (rho : State X)
    (hrho : E.IsAverage rho) (n : ℕ) :
    (E.regularization n).IsAverage (stateRegularization rho n) := by
  classical
  unfold FiniteStateEnsemble.IsAverage
  rw [stateRegularization_matrix]
  simp_rw [FiniteStateEnsemble.regularization,
    stateRegularization_matrix]
  rw [hrho]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  have hweight : (∑ i, (E.weight i : ℂ)) = 1 := by
    exact_mod_cast E.weight_sum_one
  have hfirst :
      (∑ i, (E.weight i : ℂ) •
          ((1 - 1 / (n + 2 : ℝ)) • (E.state i).matrix x y)) =
        (1 - 1 / (n + 2 : ℝ)) •
          ∑ i, (E.weight i : ℂ) • (E.state i).matrix x y := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_eq_mul, Complex.real_smul]
    ring
  have hsecond :
      (∑ i, (E.weight i : ℂ) •
          ((1 / (n + 2 : ℝ)) •
            (maximallyMixedState X).matrix x y)) =
        (1 / (n + 2 : ℝ)) •
          (maximallyMixedState X).matrix x y := by
    calc
      _ = (∑ i, (E.weight i : ℂ)) •
          ((1 / (n + 2 : ℝ)) •
            (maximallyMixedState X).matrix x y) :=
        Finset.sum_smul.symm
      _ = _ := by rw [hweight, one_smul]
  rw [hfirst, hsecond]

/-- It suffices to prove conditional-entropy concavity for ensembles whose
average and every component are positive definite. -/
theorem quantumConditionalEntropy_concave_of_posDef_case
    (hposDef :
      ∀ {ι : Type w} [Fintype ι],
        ∀ (E : FiniteStateEnsemble ι (A × B))
          (rho : State (A × B)),
          E.IsAverage rho →
          rho.matrix.PosDef →
          (∀ i, (E.state i).matrix.PosDef) →
          ∑ i, E.weight i *
              quantumConditionalEntropy (E.state i) ≤
            quantumConditionalEntropy rho)
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho) :
    ∑ i, E.weight i * quantumConditionalEntropy (E.state i) ≤
      quantumConditionalEntropy rho := by
  classical
  have hAB : Nonempty (A × B) := rho.nonempty
  letI : Nonempty A := nonempty_prod.mp hAB |>.1
  letI : Nonempty B := nonempty_prod.mp hAB |>.2
  have hconditional (tau : State (A × B)) :
      Filter.Tendsto
        (fun n =>
          quantumConditionalEntropy (stateRegularization tau n))
        Filter.atTop (nhds (quantumConditionalEntropy tau)) := by
    have hjoint := tendsto_vonNeumannEntropy_stateRegularization tau
    have hmarginal :=
      tendsto_vonNeumannEntropy_stateRegularization tau.marginalB
    unfold quantumConditionalEntropy
    convert hjoint.sub hmarginal using 1
    funext n
    rw [stateRegularization_marginalB]
  have hlhs :
      Filter.Tendsto
        (fun n =>
          ∑ i, E.weight i *
            quantumConditionalEntropy
              ((E.regularization n).state i))
        Filter.atTop
        (nhds
          (∑ i, E.weight i *
            quantumConditionalEntropy (E.state i))) := by
    apply tendsto_finsetSum (Finset.univ : Finset ι)
    intro i _
    exact (hconditional (E.state i)).const_mul (E.weight i)
  have hrhs :
      Filter.Tendsto
        (fun n =>
          quantumConditionalEntropy (stateRegularization rho n))
        Filter.atTop (nhds (quantumConditionalEntropy rho)) :=
    hconditional rho
  exact le_of_tendsto_of_tendsto' hlhs hrhs fun n =>
    hposDef (E.regularization n) (stateRegularization rho n)
      (E.regularization_isAverage rho hrho n)
      (stateRegularization_posDef rho n)
      (fun i => stateRegularization_posDef (E.state i) n)

/-- Full spectral strong subadditivity follows from its positive-definite
case by the explicit maximally mixed regularization. -/
theorem vonNeumannEntropyStrongSubadditivity_of_posDef_case
    (hposDef :
      ∀ {C : Type w} [Fintype C] [DecidableEq C],
        ∀ rhoABC : State ((A × B) × C),
          rhoABC.matrix.PosDef →
          vonNeumannEntropy rhoABC +
              vonNeumannEntropy rhoABC.marginalBOfABC ≤
            vonNeumannEntropy rhoABC.marginalAB +
              vonNeumannEntropy rhoABC.marginalBC) :
    VonNeumannEntropyStrongSubadditivity.{u, v, w}
      (A := A) (B := B) := by
  intro C _ _ rhoABC
  have hABC : Nonempty ((A × B) × C) := rhoABC.nonempty
  letI : Nonempty (A × B) := nonempty_prod.mp hABC |>.1
  letI : Nonempty A := nonempty_prod.mp (inferInstance : Nonempty (A × B)) |>.1
  letI : Nonempty B := nonempty_prod.mp (inferInstance : Nonempty (A × B)) |>.2
  letI : Nonempty C := nonempty_prod.mp hABC |>.2
  have hB :
      Filter.Tendsto
        (fun n =>
          vonNeumannEntropy
            (stateRegularization rhoABC n).marginalBOfABC)
        Filter.atTop
        (nhds (vonNeumannEntropy rhoABC.marginalBOfABC)) := by
    convert
      tendsto_vonNeumannEntropy_stateRegularization
        rhoABC.marginalBOfABC using 1
    funext n
    rw [stateRegularization_marginalBOfABC]
  have hAB :
      Filter.Tendsto
        (fun n =>
          vonNeumannEntropy
            (stateRegularization rhoABC n).marginalAB)
        Filter.atTop
        (nhds (vonNeumannEntropy rhoABC.marginalAB)) := by
    convert
      tendsto_vonNeumannEntropy_stateRegularization
        rhoABC.marginalAB using 1
    funext n
    rw [stateRegularization_marginalAB]
  have hBC :
      Filter.Tendsto
        (fun n =>
          vonNeumannEntropy
            (stateRegularization rhoABC n).marginalBC)
        Filter.atTop
        (nhds (vonNeumannEntropy rhoABC.marginalBC)) := by
    convert
      tendsto_vonNeumannEntropy_stateRegularization
        rhoABC.marginalBC using 1
    funext n
    rw [stateRegularization_marginalBC]
  have hlhs :=
    (tendsto_vonNeumannEntropy_stateRegularization rhoABC).add hB
  have hrhs := hAB.add hBC
  exact le_of_tendsto_of_tendsto' hlhs hrhs fun n =>
    hposDef (stateRegularization rhoABC n)
      (stateRegularization_posDef rhoABC n)

/-- Von Neumann entropy of a finite-dimensional density state is nonnegative;
this local form matches the spectral normalization used in this file. -/
theorem vonNeumannEntropy_nonneg (rho : State X) :
    0 ≤ vonNeumannEntropy rho := by
  rw [vonNeumannEntropy_eq_sum_negMulLog]
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (rho.pos.eigenvalues_nonneg i)
  have hi :
      rho.pos.isHermitian.eigenvalues i ≤
        ∑ j, rho.pos.isHermitian.eigenvalues j := by
    simpa using Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset X)) =>
        rho.pos.eigenvalues_nonneg j)
      (Finset.mem_univ i)
  simpa [State.sum_eigenvalues_eq_one] using hi

/-- Conditional entropy is concave for ensembles with a common `B` marginal;
the marginal entropy cancels and ordinary entropy concavity is sufficient. -/
theorem quantumConditionalEntropy_concave_of_constant_marginalB
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho)
    (hmarginal : ∀ i, (E.state i).marginalB = rho.marginalB) :
    ∑ i, E.weight i * quantumConditionalEntropy (E.state i) ≤
      quantumConditionalEntropy rho := by
  have hentropy := vonNeumannEntropy_concave E rho hrho
  have hmarginalEntropy :
      (∑ i, E.weight i *
        vonNeumannEntropy (E.state i).marginalB) =
        vonNeumannEntropy rho.marginalB := by
    simp_rw [hmarginal]
    rw [← Finset.sum_mul, E.weight_sum_one, one_mul]
  unfold quantumConditionalEntropy
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hmarginalEntropy]
  linarith

private theorem sum_eigenvalues_function_eq_sum_eigenvalues₀
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    (∑ i : n, f (hM.eigenvalues i)) =
      ∑ i : Fin (Fintype.card n), f (hM.eigenvalues₀ i) := by
  let e : Fin (Fintype.card n) ≃ n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  have h := e.sum_comp (fun i : n => f (hM.eigenvalues i))
  simpa [e, Matrix.IsHermitian.eigenvalues] using h.symm

/-- Entropy is unchanged by a relabelling of the chosen finite basis. -/
private theorem vonNeumannEntropy_reindex
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (rho : State α) (e : α ≃ β) :
    vonNeumannEntropy (rho.reindex e) = vonNeumannEntropy rho := by
  let f : ℝ → ℝ := fun x => x * Real.log x
  have hchar :
      (rho.reindex e).matrix.charpoly = rho.matrix.charpoly := by
    simpa [State.reindex, Matrix.reindex_apply] using
      (Matrix.charpoly_reindex e rho.matrix)
  have hlists :
      List.ofFn (rho.reindex e).pos.isHermitian.eigenvalues₀ =
        List.ofFn rho.pos.isHermitian.eigenvalues₀ := by
    rw [← (rho.reindex e).pos.isHermitian.sort_roots_charpoly_eq_eigenvalues₀,
      ← rho.pos.isHermitian.sort_roots_charpoly_eq_eigenvalues₀, hchar]
  have hmapped := congrArg (fun l : List ℝ => (l.map f).sum) hlists
  have hsums :
      (∑ i : Fin (Fintype.card β),
          f ((rho.reindex e).pos.isHermitian.eigenvalues₀ i)) =
        ∑ i : Fin (Fintype.card α),
          f (rho.pos.isHermitian.eigenvalues₀ i) := by
    simpa [List.map_ofFn, List.sum_ofFn] using hmapped
  unfold vonNeumannEntropy
  rw [sum_eigenvalues_function_eq_sum_eigenvalues₀
        (rho.reindex e).pos.isHermitian f,
    sum_eigenvalues_function_eq_sum_eigenvalues₀
        rho.pos.isHermitian f,
    hsums]

/-- The only density state on a subsingleton basis has spectrum `{1}`. -/
private theorem vonNeumannEntropy_eq_zero_of_subsingleton
    {α : Type u} [Fintype α] [DecidableEq α] [Subsingleton α]
    (rho : State α) :
    vonNeumannEntropy rho = 0 := by
  letI : Unique α :=
    { default := Classical.choice rho.nonempty
      uniq := fun _ => Subsingleton.elim _ _ }
  have hsum := rho.pos.isHermitian.trace_eq_sum_eigenvalues
  rw [rho.trace_eq_one, Fintype.sum_unique] at hsum
  have heig :
      rho.pos.isHermitian.eigenvalues (default : α) = 1 := by
    apply Complex.ofReal_injective
    simpa using hsum.symm
  unfold vonNeumannEntropy
  rw [Fintype.sum_unique, heig]
  norm_num

private theorem entropy_joint_eq_marginalB_of_subsingleton
    [Subsingleton A] (rho : State (A × B)) :
    vonNeumannEntropy rho = vonNeumannEntropy rho.marginalB := by
  letI : Unique A :=
    { default := Classical.choice rho.marginalA.nonempty
      uniq := fun _ => Subsingleton.elim _ _ }
  let e : B ≃ A × B :=
    { toFun := fun b => (default, b)
      invFun := fun x => x.2
      left_inv := fun _ => rfl
      right_inv := fun x => by
        cases x with
        | mk a b => simp [Subsingleton.elim a default] }
  have hreindex : rho.marginalB.reindex e = rho := by
    apply State.ext
    ext x y
    rcases x with ⟨a, b⟩
    rcases y with ⟨a', b'⟩
    simp [State.reindex, e, State.marginalB, partialTraceA,
      Subsingleton.elim a default, Subsingleton.elim a' default]
  calc
    vonNeumannEntropy rho =
        vonNeumannEntropy (rho.marginalB.reindex e) := by rw [hreindex]
    _ = vonNeumannEntropy rho.marginalB :=
      vonNeumannEntropy_reindex rho.marginalB e

private theorem entropy_joint_eq_marginalA_of_subsingleton
    [Subsingleton B] (rho : State (A × B)) :
    vonNeumannEntropy rho = vonNeumannEntropy rho.marginalA := by
  letI : Unique B :=
    { default := Classical.choice rho.marginalB.nonempty
      uniq := fun _ => Subsingleton.elim _ _ }
  let e : A ≃ A × B :=
    { toFun := fun a => (a, default)
      invFun := fun x => x.1
      left_inv := fun _ => rfl
      right_inv := fun x => by
        cases x with
        | mk a b => simp [Subsingleton.elim b default] }
  have hreindex : rho.marginalA.reindex e = rho := by
    apply State.ext
    ext x y
    rcases x with ⟨a, b⟩
    rcases y with ⟨a', b'⟩
    simp [State.reindex, e, State.marginalA, partialTraceB,
      Subsingleton.elim b default, Subsingleton.elim b' default]
  calc
    vonNeumannEntropy rho =
        vonNeumannEntropy (rho.marginalA.reindex e) := by rw [hreindex]
    _ = vonNeumannEntropy rho.marginalA :=
      vonNeumannEntropy_reindex rho.marginalA e

/-- Conditional entropy is concave without quantum SSA when either subsystem
is subsingleton; it reduces respectively to zero or to ordinary entropy. -/
theorem quantumConditionalEntropy_concave_of_subsingleton
    (hdegenerate : Subsingleton A ∨ Subsingleton B)
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho) :
    ∑ i, E.weight i * quantumConditionalEntropy (E.state i) ≤
      quantumConditionalEntropy rho := by
  rcases hdegenerate with hA | hB
  · letI : Subsingleton A := hA
    have hzero (tau : State (A × B)) :
        quantumConditionalEntropy tau = 0 := by
      unfold quantumConditionalEntropy
      rw [entropy_joint_eq_marginalB_of_subsingleton tau]
      ring
    simp_rw [hzero]
    norm_num
  · letI : Subsingleton B := hB
    have hcollapse (tau : State (A × B)) :
        quantumConditionalEntropy tau = vonNeumannEntropy tau := by
      unfold quantumConditionalEntropy
      rw [vonNeumannEntropy_eq_zero_of_subsingleton tau.marginalB]
      ring
    simp_rw [hcollapse]
    exact vonNeumannEntropy_concave E rho hrho

private theorem quantumMutualInformation_eq_zero_of_subsingleton_left
    [Subsingleton A] (rho : State (A × B)) :
    quantumMutualInformation rho = 0 := by
  unfold quantumMutualInformation
  rw [vonNeumannEntropy_eq_zero_of_subsingleton rho.marginalA,
    entropy_joint_eq_marginalB_of_subsingleton rho]
  ring

private theorem quantumMutualInformation_eq_zero_of_subsingleton_right
    [Subsingleton B] (rho : State (A × B)) :
    quantumMutualInformation rho = 0 := by
  unfold quantumMutualInformation
  rw [vonNeumannEntropy_eq_zero_of_subsingleton rho.marginalB,
    entropy_joint_eq_marginalA_of_subsingleton rho]
  ring

/-- A classical probability distribution, viewed as a diagonal density state. -/
private def diagonalState
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    State α where
  matrix := Matrix.diagonal fun x => (p x : ℂ)
  pos := Matrix.posSemidef_diagonal_iff.mpr fun x => by
    exact_mod_cast hp x
  trace_eq_one := by
    rw [Matrix.trace_diagonal]
    exact_mod_cast hsum

private theorem roots_charpoly_diagonalState
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    (diagonalState p hp hsum).matrix.charpoly.roots =
      Multiset.map (fun x => (p x : ℂ)) Finset.univ.val := by
  rw [show (diagonalState p hp hsum).matrix =
      Matrix.diagonal (fun x => (p x : ℂ)) from rfl,
    Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      Polynomial.X_sub_C_ne_zero _

/-- Spectral entropy of a diagonal state is its Shannon entropy. -/
private theorem vonNeumannEntropy_diagonalState
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    vonNeumannEntropy (diagonalState p hp hsum) =
      -∑ x, p x * Real.log (p x) := by
  let rho := diagonalState p hp hsum
  have hroots := rho.pos.isHermitian.roots_charpoly_eq_eigenvalues
  rw [roots_charpoly_diagonalState p hp hsum] at hroots
  have hmapped := congrArg
    (fun s : Multiset ℂ =>
      (s.map (fun z => z.re * Real.log z.re)).sum) hroots
  have hsums :
      (∑ x, p x * Real.log (p x)) =
        ∑ i, rho.pos.isHermitian.eigenvalues i *
          Real.log (rho.pos.isHermitian.eigenvalues i) := by
    simpa [Multiset.map_map, Function.comp_def, rho] using hmapped
  unfold vonNeumannEntropy
  rw [← hsums]

private noncomputable def entropyKroneckerUnitary
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (U : Matrix.unitaryGroup α ℂ) (V : Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (α × β) ℂ :=
  ⟨Matrix.kronecker (U : CMatrix α) (V : CMatrix β),
    Matrix.kronecker_mem_unitary U.property V.property⟩

private theorem entropy_product_diagonalization
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (rho : State α) (sigma : State β) :
    let U := rho.pos.isHermitian.eigenvectorUnitary
    let V := sigma.pos.isHermitian.eigenvectorUnitary
    let W := entropyKroneckerUnitary U V
    Matrix.conjTranspose (W : CMatrix (α × β)) *
        (rho.prod sigma).matrix * (W : CMatrix (α × β)) =
      Matrix.diagonal (fun ij =>
        ((rho.pos.isHermitian.eigenvalues ij.1 *
          sigma.pos.isHermitian.eigenvalues ij.2 : ℝ) : ℂ)) := by
  dsimp only
  let U := rho.pos.isHermitian.eigenvectorUnitary
  let V := sigma.pos.isHermitian.eigenvectorUnitary
  have hrhoDiagonal :
      Matrix.conjTranspose (U : CMatrix α) * rho.matrix *
          (U : CMatrix α) =
        Matrix.diagonal
          (Complex.ofReal ∘ rho.pos.isHermitian.eigenvalues) := by
    simpa [Matrix.star_eq_conjTranspose] using
      rho.pos.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hsigmaDiagonal :
      Matrix.conjTranspose (V : CMatrix β) * sigma.matrix *
          (V : CMatrix β) =
        Matrix.diagonal
          (Complex.ofReal ∘ sigma.pos.isHermitian.eigenvalues) := by
    simpa [Matrix.star_eq_conjTranspose] using
      sigma.pos.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  change Matrix.conjTranspose
      (Matrix.kronecker (U : CMatrix α) (V : CMatrix β)) *
      Matrix.kronecker rho.matrix sigma.matrix *
      Matrix.kronecker (U : CMatrix α) (V : CMatrix β) = _
  rw [show Matrix.conjTranspose
      (Matrix.kronecker (U : CMatrix α) (V : CMatrix β)) =
        Matrix.kronecker (Matrix.conjTranspose (U : CMatrix α))
          (Matrix.conjTranspose (V : CMatrix β)) by
    exact Matrix.conjTranspose_kronecker _ _]
  change (Matrix.kroneckerMap (fun x y : ℂ => x * y)
      (Matrix.conjTranspose (U : CMatrix α))
      (Matrix.conjTranspose (V : CMatrix β)) *
    Matrix.kroneckerMap (fun x y : ℂ => x * y) rho.matrix sigma.matrix) *
    Matrix.kroneckerMap (fun x y : ℂ => x * y)
      (U : CMatrix α) (V : CMatrix β) = _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [hrhoDiagonal, hsigmaDiagonal,
    Matrix.diagonal_kronecker_diagonal]
  ext ij kl
  simp [Function.comp_apply]

/-- Von Neumann entropy is additive on product density states; this
project-local spectral form is a prerequisite for entropy subadditivity. -/
theorem vonNeumannEntropy_prod
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (rho : State α) (sigma : State β) :
    vonNeumannEntropy (rho.prod sigma) =
      vonNeumannEntropy rho + vonNeumannEntropy sigma := by
  let lambda := rho.pos.isHermitian.eigenvalues
  let mu := sigma.pos.isHermitian.eigenvalues
  let p : α × β → ℝ := fun ij => lambda ij.1 * mu ij.2
  have hp : ∀ ij, 0 ≤ p ij := fun ij =>
    mul_nonneg (rho.pos.eigenvalues_nonneg ij.1)
      (sigma.pos.eigenvalues_nonneg ij.2)
  have hlambdaSum : ∑ i, lambda i = 1 := by
    simpa [lambda] using State.sum_eigenvalues_eq_one rho
  have hmuSum : ∑ j, mu j = 1 := by
    simpa [mu] using State.sum_eigenvalues_eq_one sigma
  have hpSum : ∑ ij, p ij = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [p, ← Finset.mul_sum, hmuSum, mul_one]
    exact hlambdaSum
  let diagonalProduct : State (α × β) := diagonalState p hp hpSum
  let W : Matrix.unitaryGroup (α × β) ℂ :=
    entropyKroneckerUnitary
      rho.pos.isHermitian.eigenvectorUnitary
      sigma.pos.isHermitian.eigenvectorUnitary
  have hdiagonalState :
      entropyUnitaryConjugate (star W) (rho.prod sigma) =
        diagonalProduct := by
    apply State.ext
    simpa [entropyUnitaryConjugate, diagonalProduct, diagonalState,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, W, p, lambda, mu] using
      entropy_product_diagonalization rho sigma
  have hterm (i : α) (j : β) :
      (lambda i * mu j) * Real.log (lambda i * mu j) =
        (lambda i * mu j) *
          (Real.log (lambda i) + Real.log (mu j)) := by
    by_cases hlambda : lambda i = 0
    · simp [hlambda]
    by_cases hmu : mu j = 0
    · simp [hmu]
    rw [Real.log_mul hlambda hmu]
  have hfirst :
      (∑ i, ∑ j, (lambda i * mu j) * Real.log (lambda i)) =
        ∑ i, lambda i * Real.log (lambda i) := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      (∑ j, (lambda i * mu j) * Real.log (lambda i)) =
          (lambda i * Real.log (lambda i)) * ∑ j, mu j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = lambda i * Real.log (lambda i) := by rw [hmuSum, mul_one]
  have hsecond :
      (∑ i, ∑ j, (lambda i * mu j) * Real.log (mu j)) =
        ∑ j, mu j * Real.log (mu j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (∑ i, (lambda i * mu j) * Real.log (mu j)) =
          (mu j * Real.log (mu j)) * ∑ i, lambda i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = mu j * Real.log (mu j) := by rw [hlambdaSum, mul_one]
  have hproductLog :
      (∑ ij, p ij * Real.log (p ij)) =
        (∑ i, lambda i * Real.log (lambda i)) +
          ∑ j, mu j * Real.log (mu j) := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ i, ∑ j, p (i, j) * Real.log (p (i, j))) =
          ∑ i, ∑ j,
            ((lambda i * mu j) * Real.log (lambda i) +
              (lambda i * mu j) * Real.log (mu j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change (lambda i * mu j) * Real.log (lambda i * mu j) =
          (lambda i * mu j) * Real.log (lambda i) +
            (lambda i * mu j) * Real.log (mu j)
        rw [hterm i j]
        ring
      _ = (∑ i, ∑ j,
            (lambda i * mu j) * Real.log (lambda i)) +
          ∑ i, ∑ j,
            (lambda i * mu j) * Real.log (mu j) := by
        simp_rw [Finset.sum_add_distrib]
      _ = _ := by rw [hfirst, hsecond]
  calc
    vonNeumannEntropy (rho.prod sigma) =
        vonNeumannEntropy
          (entropyUnitaryConjugate (star W) (rho.prod sigma)) :=
      (vonNeumannEntropy_entropyUnitaryConjugate
        (star W) (rho.prod sigma)).symm
    _ = vonNeumannEntropy diagonalProduct := by rw [hdiagonalState]
    _ = -∑ ij, p ij * Real.log (p ij) := by
      exact vonNeumannEntropy_diagonalState p hp hpSum
    _ = vonNeumannEntropy rho + vonNeumannEntropy sigma := by
      rw [hproductLog]
      unfold vonNeumannEntropy
      change
        -((∑ i, lambda i * Real.log (lambda i)) +
            ∑ j, mu j * Real.log (mu j)) =
          -(∑ i, lambda i * Real.log (lambda i)) +
            -(∑ j, mu j * Real.log (mu j))
      ring

/-! ## Project-local Mathlib supplement — Positive-definite matrix order -/

section PositiveDefiniteMatrixOrder

open scoped Matrix.Norms.L2Operator

local instance matrixCStarAlgebraForOrder {Y : Type*}
    [Fintype Y] [DecidableEq Y] : CStarAlgebra (CMatrix Y) where
  norm_mul_self_le := Matrix.instCStarRing.norm_mul_self_le

/-- Nonsingular matrix inversion reverses the Loewner order on positive-definite
complex matrices; this is a basic input for the remaining operator inequality. -/
theorem posDef_nonsingInv_antitone
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {M N : CMatrix Y} (hM : M.PosDef) (hN : N.PosDef)
    (hMN : M ≤ N) :
    N⁻¹ ≤ M⁻¹ := by
  let uM : (CMatrix Y)ˣ := hM.isUnit.unit
  let uN : (CMatrix Y)ˣ := hN.isUnit.unit
  have huM : (uM : CMatrix Y) = M := hM.isUnit.unit_spec
  have huN : (uN : CMatrix Y) = N := hN.isUnit.unit_spec
  have hNN : 0 ≤ (uN : CMatrix Y) := by
    rw [huN]
    exact Matrix.nonneg_iff_posSemidef.mpr hN.posSemidef
  have hMinv : 0 ≤ ((uM⁻¹ : (CMatrix Y)ˣ) : CMatrix Y) := by
    rw [Matrix.coe_units_inv, huM]
    exact Matrix.nonneg_iff_posSemidef.mpr hM.inv.posSemidef
  have h := (CStarAlgebra.inv_le_iff hNN hMinv).2 ?_
  · rw [Matrix.coe_units_inv, Matrix.coe_units_inv, huM, huN] at h
    exact h
  · simpa only [Matrix.coe_units_inv, inv_inv, huM, huN] using hMN

end PositiveDefiniteMatrixOrder

/-! ## Project-local Mathlib supplement — SSA operator contractions -/

section SSAOperatorContractions

/-- Conjugating a Loewner inequality by a rectangular complex matrix preserves
the inequality.  This is the order-transport leaf used by the SSA contraction
argument. -/
theorem matrix_sandwich_mono
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {M N : Matrix n n ℂ} (C : Matrix m n ℂ) (hMN : M ≤ N) :
    C * M * C.conjTranspose ≤ C * N * C.conjTranspose := by
  rw [Matrix.le_iff] at hMN ⊢
  have hdistrib :
      C * N * C.conjTranspose - C * M * C.conjTranspose =
        C * (N - M) * C.conjTranspose := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, Finset.sum_mul,
      ← Finset.sum_sub_distrib, mul_sub_left_distrib,
      mul_sub_right_distrib]
  rw [hdistrib]
  exact hMN.mul_mul_conjTranspose_same C

/-- The adjoint-first form of `matrix_sandwich_mono`, needed when transporting
a contraction bound through an isometry. -/
theorem matrix_conjTranspose_sandwich_mono
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {M N : Matrix n n ℂ} (C : Matrix n m ℂ) (hMN : M ≤ N) :
    C.conjTranspose * M * C ≤ C.conjTranspose * N * C := by
  convert matrix_sandwich_mono C.conjTranspose hMN <;>
    rw [Matrix.conjTranspose_conjTranspose]

/-- The range projection `VV†` of a finite-dimensional isometry is bounded by
the identity. -/
theorem matrix_isometry_rangeProjection_le_one
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : V.conjTranspose * V = 1) :
    V * V.conjTranspose ≤ 1 := by
  have hproj :
      (V * V.conjTranspose) * (V * V.conjTranspose) =
        V * V.conjTranspose := by
    calc
      _ = V * (V.conjTranspose * (V * V.conjTranspose)) :=
        Matrix.mul_assoc V V.conjTranspose (V * V.conjTranspose)
      _ = V * ((V.conjTranspose * V) * V.conjTranspose) :=
        congrArg (fun Z => V * Z)
          (Matrix.mul_assoc V.conjTranspose V V.conjTranspose).symm
      _ = V * V.conjTranspose := by rw [hV]; simp
  have hidem :
      (1 - V * V.conjTranspose) * (1 - V * V.conjTranspose) =
        1 - V * V.conjTranspose := by
    calc
      _ = 1 - V * V.conjTranspose - V * V.conjTranspose +
          (V * V.conjTranspose) * (V * V.conjTranspose) := by
        noncomm_ring
      _ = _ := by rw [hproj]; abel
  have hherm :
      (1 - V * V.conjTranspose).conjTranspose =
        1 - V * V.conjTranspose := by
    simp
  have hfactor :
      1 - V * V.conjTranspose =
        (1 - V * V.conjTranspose).conjTranspose *
          (1 - V * V.conjTranspose) := by
    rw [hherm]
    exact hidem.symm
  have hpos : (1 - V * V.conjTranspose).PosSemidef := by
    rw [hfactor]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  exact Matrix.le_iff.mpr hpos

/-- The cross product of two isometries into a common finite-dimensional
space is a contraction in Loewner order. -/
theorem matrix_cross_isometry_contraction_le_one
    {m : Type u} {n : Type v} {k : Type w}
    [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (V : Matrix k m ℂ) (W : Matrix k n ℂ)
    (hV : V.conjTranspose * V = 1)
    (hW : W.conjTranspose * W = 1) :
    (V.conjTranspose * W).conjTranspose *
        (V.conjTranspose * W) ≤ 1 := by
  have hproj : V * V.conjTranspose ≤ 1 :=
    matrix_isometry_rangeProjection_le_one V hV
  have hconj :
      W.conjTranspose * (V * V.conjTranspose) * W ≤
        W.conjTranspose * (1 : Matrix k k ℂ) * W :=
    matrix_conjTranspose_sandwich_mono W hproj
  simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, hW] using hconj

/-- The coefficient matrix of the map
`v ↦ v ⊗ ∑ᵦ |b⟩|b⟩` used in the Lin--Kim--Hsieh SSA isometries. -/
def ssaMapToTensorMES : Matrix ((A × B) × B) A ℂ :=
  fun ijk a =>
    if ijk.1.1 = a then
      if ijk.1.2 = ijk.2 then 1 else 0
    else 0

/-- Contracting a lifted bipartite matrix against the maximally-entangled
index map realizes the partial trace over the right subsystem. -/
theorem ssaMapToTensorMES_contraction (M : CMatrix (A × B)) :
    ssaMapToTensorMES.conjTranspose *
        Matrix.kronecker M (1 : CMatrix B) *
          ssaMapToTensorMES =
      partialTraceB M := by
  ext i j
  simp only [Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [Matrix.conjTranspose_apply, ssaMapToTensorMES,
    Matrix.kronecker, Matrix.one_apply, partialTraceB, apply_ite]

/-- For a positive-definite matrix, sandwiching it between the positive
square roots of its inverse gives the identity. -/
theorem posDef_sqrt_inv_sandwich
    {Y : Type u} [Fintype Y] [DecidableEq Y]
    {M : CMatrix Y} (hM : M.PosDef) :
    CFC.sqrt M⁻¹ * M * CFC.sqrt M⁻¹ = 1 := by
  let S := CFC.sqrt M
  have hM0 : 0 ≤ M :=
    Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hsquare : S * S = M := by
    simpa [S] using CFC.sqrt_mul_sqrt_self M hM0
  have hsunit : IsUnit S := by
    simpa [S] using (CFC.isUnit_sqrt_iff M hM0).2 hM.isUnit
  have hsdet : IsUnit S.det :=
    (Matrix.isUnit_iff_isUnit_det S).mp hsunit
  have hinvsqrt : CFC.sqrt M⁻¹ = S⁻¹ := by
    simpa [S] using hM.posSemidef.inv_sqrt.symm
  rw [hinvsqrt]
  change S⁻¹ * M * S⁻¹ = 1
  rw [← hsquare]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv S hsdet, Matrix.mul_one,
    Matrix.nonsing_inv_mul S hsdet]

/-- For a positive-definite matrix, sandwiching its inverse between the
positive square roots of the matrix gives the identity. -/
theorem posDef_sqrt_inv_sqrt
    {Y : Type u} [Fintype Y] [DecidableEq Y]
    {M : CMatrix Y} (hM : M.PosDef) :
    CFC.sqrt M * M⁻¹ * CFC.sqrt M = 1 := by
  let S := CFC.sqrt M
  have hM0 : 0 ≤ M :=
    Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hsquare : S * S = M := by
    simpa [S] using CFC.sqrt_mul_sqrt_self M hM0
  have hMdet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hSM : S * M = M * S := by
    rw [← hsquare]
    noncomm_ring
  have hcomm : S * M⁻¹ = M⁻¹ * S := by
    calc
      S * M⁻¹ = 1 * (S * M⁻¹) := by rw [Matrix.one_mul]
      _ = (M⁻¹ * M) * (S * M⁻¹) := by
        rw [Matrix.nonsing_inv_mul M hMdet]
      _ = M⁻¹ * (M * S) * M⁻¹ := by noncomm_ring
      _ = M⁻¹ * (S * M) * M⁻¹ := by rw [hSM]
      _ = (M⁻¹ * S) * (M * M⁻¹) := by noncomm_ring
      _ = M⁻¹ * S := by
        rw [Matrix.mul_nonsing_inv M hMdet, Matrix.mul_one]
  change S * M⁻¹ * S = 1
  rw [hcomm, Matrix.mul_assoc, hsquare,
    Matrix.nonsing_inv_mul M hMdet]

/-- Reindexing both axes of a Hermitian matrix by the same equivalence
preserves Hermiticity. -/
theorem matrix_reindex_isHermitian
    {Y : Type u} {Z : Type v} [Fintype Y] [Fintype Z]
    [DecidableEq Y] [DecidableEq Z]
    (M : CMatrix Y) (e : Y ≃ Z) (hM : M.IsHermitian) :
    (Matrix.reindex e e M).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, hM]

/-- Simultaneous reindexing of both axes reflects the Loewner order. -/
theorem matrix_reindex_le_reindex_iff
    {Y : Type u} {Z : Type v} [Fintype Y] [Fintype Z]
    [DecidableEq Y] [DecidableEq Z]
    (e : Y ≃ Z) (M N : CMatrix Y) :
    Matrix.reindex e e M ≤ Matrix.reindex e e N ↔ M ≤ N := by
  rw [Matrix.le_iff, Matrix.le_iff]
  change
    ((N - M).submatrix e.symm e.symm).PosSemidef ↔
      (N - M).PosSemidef
  exact Matrix.posSemidef_submatrix_equiv e.symm

/-- The Kronecker product of Hermitian complex matrices is Hermitian. -/
theorem matrix_kronecker_isHermitian
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (M : CMatrix m) (N : CMatrix n)
    (hM : M.IsHermitian) (hN : N.IsHermitian) :
    (Matrix.kronecker M N).IsHermitian := by
  unfold Matrix.kronecker Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, hM, hN]

/-- Conjugation by an invertible Hermitian matrix reflects as well as
preserves the Loewner order. -/
theorem matrix_sandwich_le_iff_of_isUnit_isHermitian
    {Y : Type u} [Fintype Y] [DecidableEq Y]
    (S : CMatrix Y) (hSunit : IsUnit S) (hSherm : S.IsHermitian)
    {M N : CMatrix Y} :
    S * M * S ≤ S * N * S ↔ M ≤ N := by
  have hdet : IsUnit S.det :=
    (Matrix.isUnit_iff_isUnit_det S).mp hSunit
  constructor
  · intro h
    have h' := matrix_sandwich_mono S⁻¹ h
    have hinvherm : (S⁻¹).conjTranspose = S⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, hSherm]
    simp only [hinvherm, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv S hdet, Matrix.mul_one] at h'
    rw [Matrix.nonsing_inv_mul_cancel_left S M hdet,
      Matrix.nonsing_inv_mul_cancel_left S N hdet] at h'
    exact h'
  · intro h
    have h' := matrix_sandwich_mono S h
    rw [hSherm] at h'
    exact h'

/-- The first canonical SSA isometry, built from a positive square root, a
maximally-entangled index contraction, and the inverse square root of the
right partial trace. -/
def ssaVRho (M : CMatrix (A × B)) : Matrix ((A × B) × B) A ℂ :=
  Matrix.kronecker (CFC.sqrt M) (1 : CMatrix B) *
    ssaMapToTensorMES * CFC.sqrt (partialTraceB M)⁻¹

/-- Entrywise formula for the first SSA isometry. -/
theorem ssaVRho_apply (M : CMatrix (A × B))
    (a a' : A) (b b' : B) :
    ssaVRho M ((a, b), b') a' =
      ∑ x : A,
        CFC.sqrt M (a, b) (x, b') *
          CFC.sqrt (partialTraceB M)⁻¹ x a' := by
  simp only [ssaVRho, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [ssaMapToTensorMES,
    Matrix.kronecker, Matrix.one_apply]

/-- `ssaVRho` is an isometry whenever its bipartite input is positive
definite. -/
theorem ssaVRho_isometry [Nonempty B]
    (M : CMatrix (A × B)) (hM : M.PosDef) :
    (ssaVRho M).conjTranspose * ssaVRho M = 1 := by
  let K := Matrix.kronecker (CFC.sqrt M) (1 : CMatrix B)
  let E := ssaMapToTensorMES (A := A) (B := B)
  let R := CFC.sqrt (partialTraceB M)⁻¹
  have hM0 : 0 ≤ M :=
    Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hsqrtHerm : (CFC.sqrt M).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian
  have hRherm : R.IsHermitian := by
    exact (Matrix.nonneg_iff_posSemidef.mp
      (CFC.sqrt_nonneg (partialTraceB M)⁻¹)).isHermitian
  have hKsq :
      K.conjTranspose * K =
        Matrix.kronecker M (1 : CMatrix B) := by
    dsimp [K]
    rw [Matrix.conjTranspose_kronecker, hsqrtHerm,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      CFC.sqrt_mul_sqrt_self M hM0]
    simp
  have hcore :
      E.conjTranspose * K.conjTranspose * K * E =
        partialTraceB M := by
    calc
      _ = E.conjTranspose * (K.conjTranspose * K) * E := by
        simp only [Matrix.mul_assoc]
      _ = E.conjTranspose *
          Matrix.kronecker M (1 : CMatrix B) * E := by
        rw [hKsq]
      _ = _ := ssaMapToTensorMES_contraction M
  change (K * E * R).conjTranspose * (K * E * R) = 1
  calc
    _ = R * (E.conjTranspose * K.conjTranspose * K * E) * R := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRherm]
      simp only [Matrix.mul_assoc]
    _ = R * partialTraceB M * R := by rw [hcore]
    _ = 1 := posDef_sqrt_inv_sandwich (partialTraceB_posDef hM)

/-- A Kronecker product of finite-dimensional isometries is again an
isometry. -/
theorem matrix_kronecker_isometry
    {m : Type u} {n : Type v} {p : Type w} {q : Type x}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (V : Matrix m n ℂ) (W : Matrix p q ℂ)
    (hV : V.conjTranspose * V = 1)
    (hW : W.conjTranspose * W = 1) :
    (Matrix.kronecker V W).conjTranspose *
        Matrix.kronecker V W = 1 := by
  unfold Matrix.kronecker
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hV, hW]
  simp

/-- Reindexing both the source and target bases of an isometry preserves its
isometry equation. -/
theorem matrix_reindex_isometry
    {m : Type u} {n : Type v} {m' : Type w} {n' : Type x}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq m] [DecidableEq n] [DecidableEq m'] [DecidableEq n']
    (V : Matrix m n ℂ) (em : m ≃ m') (en : n ≃ n')
    (hV : V.conjTranspose * V = 1) :
    (Matrix.reindex em en V).conjTranspose *
        Matrix.reindex em en V = 1 := by
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, hV, Matrix.submatrix_one_equiv]

/-- The coefficient matrix of the symmetric maximally-entangled-index map
used to construct the second SSA isometry. -/
def ssaMapFromTensorMES
    {C : Type w} [Fintype C] [DecidableEq C]
    : Matrix (B × (B × C)) C ℂ :=
  fun ibc c =>
    if ibc.1 = ibc.2.1 then
      if ibc.2.2 = c then 1 else 0
    else 0

/-- Contracting a lifted bipartite matrix against the symmetric
maximally-entangled-index map realizes the partial trace over the left
subsystem. -/
theorem ssaMapFromTensorMES_contraction
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (B × C)) :
    (ssaMapFromTensorMES (B := B) (C := C)).conjTranspose *
        Matrix.kronecker (1 : CMatrix B) M *
          ssaMapFromTensorMES =
      partialTraceA M := by
  ext i j
  simp only [Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [Matrix.conjTranspose_apply, ssaMapFromTensorMES,
    Matrix.kronecker, Matrix.one_apply, partialTraceA, apply_ite]

/-- The second canonical SSA isometry, in the basis ordering used by the
Lin--Kim--Hsieh contraction. -/
def ssaVSigma
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (B × C)) : Matrix (B × (B × C)) C ℂ :=
  Matrix.kronecker (1 : CMatrix B) (CFC.sqrt M) *
    ssaMapFromTensorMES * CFC.sqrt (partialTraceA M)⁻¹

/-- Entrywise formula for the second SSA isometry. -/
theorem ssaVSigma_apply
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (B × C)) (b b' : B) (c c' : C) :
    ssaVSigma M (b', (b, c)) c' =
      ∑ x : C,
        CFC.sqrt M (b, c) (b', x) *
          CFC.sqrt (partialTraceA M)⁻¹ x c' := by
  simp only [ssaVSigma, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [ssaMapFromTensorMES,
    Matrix.kronecker, Matrix.one_apply]

/-- `ssaVSigma` is an isometry whenever its bipartite input is positive
definite. -/
theorem ssaVSigma_isometry
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (M : CMatrix (B × C)) (hM : M.PosDef) :
    (ssaVSigma M).conjTranspose * ssaVSigma M = 1 := by
  let K := Matrix.kronecker (1 : CMatrix B) (CFC.sqrt M)
  let E := ssaMapFromTensorMES (B := B) (C := C)
  let R := CFC.sqrt (partialTraceA M)⁻¹
  have hM0 : 0 ≤ M :=
    Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hsqrtHerm : (CFC.sqrt M).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian
  have hRherm : R.IsHermitian := by
    exact (Matrix.nonneg_iff_posSemidef.mp
      (CFC.sqrt_nonneg (partialTraceA M)⁻¹)).isHermitian
  have hKsq :
      K.conjTranspose * K =
        Matrix.kronecker (1 : CMatrix B) M := by
    dsimp [K]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      hsqrtHerm, ← Matrix.mul_kronecker_mul,
      CFC.sqrt_mul_sqrt_self M hM0]
    simp
  have hcore :
      E.conjTranspose * K.conjTranspose * K * E =
        partialTraceA M := by
    calc
      _ = E.conjTranspose * (K.conjTranspose * K) * E := by
        simp only [Matrix.mul_assoc]
      _ = E.conjTranspose *
          Matrix.kronecker (1 : CMatrix B) M * E := by
        rw [hKsq]
      _ = _ := ssaMapFromTensorMES_contraction M
  change (K * E * R).conjTranspose * (K * E * R) = 1
  calc
    _ = R * (E.conjTranspose * K.conjTranspose * K * E) * R := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRherm]
      simp only [Matrix.mul_assoc]
    _ = R * partialTraceA M * R := by rw [hcore]
    _ = 1 := posDef_sqrt_inv_sandwich (partialTraceA_posDef hM)

/-- The Lin--Kim--Hsieh `W` operator whose contraction inequality drives the
operator extension of strong subadditivity. -/
def ssaWMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (A × B)) (N : CMatrix (B × C)) :
    CMatrix ((A × B) × C) :=
  Matrix.kronecker (CFC.sqrt M) (CFC.sqrt (partialTraceA N)⁻¹) *
    Matrix.reindex (Equiv.prodAssoc A B C).symm
      (Equiv.prodAssoc A B C).symm
      (Matrix.kronecker (CFC.sqrt (partialTraceB M)⁻¹) (CFC.sqrt N))

/-- The positive square-root sandwich used to remove the `W` contraction by
invertible conjugation. -/
def ssaSMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (A × B)) (N : CMatrix (B × C)) :
    CMatrix ((A × B) × C) :=
  Matrix.reindex (Equiv.prodAssoc A B C).symm
    (Equiv.prodAssoc A B C).symm
    (Matrix.kronecker (CFC.sqrt (partialTraceB M)⁻¹) (CFC.sqrt N))

/-- The SSA sandwich matrix is Hermitian. -/
theorem ssaSMatrix_isHermitian
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (A × B)) (N : CMatrix (B × C)) :
    (ssaSMatrix M N).IsHermitian := by
  apply matrix_reindex_isHermitian
  exact matrix_kronecker_isHermitian _ _
    (Matrix.nonneg_iff_posSemidef.mp
      (CFC.sqrt_nonneg (partialTraceB M)⁻¹)).isHermitian
    (Matrix.nonneg_iff_posSemidef.mp
      (CFC.sqrt_nonneg N)).isHermitian

/-- The SSA sandwich matrix is invertible for positive-definite inputs. -/
theorem ssaSMatrix_isUnit
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (M : CMatrix (A × B)) (N : CMatrix (B × C))
    (hM : M.PosDef) (hN : N.PosDef) :
    IsUnit (ssaSMatrix M N) := by
  let R := CFC.sqrt (partialTraceB M)⁻¹
  let Q := CFC.sqrt N
  have hA := partialTraceB_posDef hM
  have hR0 : 0 ≤ (partialTraceB M)⁻¹ :=
    Matrix.nonneg_iff_posSemidef.mpr hA.inv.posSemidef
  have hN0 : 0 ≤ N :=
    Matrix.nonneg_iff_posSemidef.mpr hN.posSemidef
  have hRpsd : R.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hQpsd : Q.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hRunit : IsUnit R := by
    exact (CFC.isUnit_sqrt_iff _ hR0).2 hA.inv.isUnit
  have hQunit : IsUnit Q := by
    exact (CFC.isUnit_sqrt_iff _ hN0).2 hN.isUnit
  have hRpd : R.PosDef := hRpsd.posDef_iff_isUnit.mpr hRunit
  have hQpd : Q.PosDef := hQpsd.posDef_iff_isUnit.mpr hQunit
  have hKpd : (Matrix.kronecker R Q).PosDef :=
    hRpd.kronecker hQpd
  exact (hKpd.submatrix
    (Equiv.prodAssoc A B C).injective).isUnit

/-- The square `W†W` is the conjugation of
`M ⊗ (Tr_B N)⁻¹` by the SSA sandwich matrix. -/
theorem ssaWMatrix_sq_eq_sandwich
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (M : CMatrix (A × B)) (N : CMatrix (B × C))
    (hM : M.PosDef) (hN : N.PosDef) :
    (ssaWMatrix M N).conjTranspose * ssaWMatrix M N =
      ssaSMatrix M N *
        Matrix.kronecker M (partialTraceA N)⁻¹ *
          ssaSMatrix M N := by
  let T :=
    Matrix.kronecker (CFC.sqrt M) (CFC.sqrt (partialTraceA N)⁻¹)
  let S := ssaSMatrix M N
  have hM0 : 0 ≤ M :=
    Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hCInv0 : 0 ≤ (partialTraceA N)⁻¹ :=
    Matrix.nonneg_iff_posSemidef.mpr
      (partialTraceA_posDef hN).inv.posSemidef
  have hT : T.IsHermitian :=
    matrix_kronecker_isHermitian _ _
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.sqrt_nonneg M)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.sqrt_nonneg (partialTraceA N)⁻¹)).isHermitian
  have hS : S.IsHermitian := ssaSMatrix_isHermitian M N
  have hTsq :
      T * T = Matrix.kronecker M (partialTraceA N)⁻¹ := by
    dsimp [T]
    rw [← Matrix.mul_kronecker_mul,
      CFC.sqrt_mul_sqrt_self M hM0,
      CFC.sqrt_mul_sqrt_self (partialTraceA N)⁻¹ hCInv0]
  change (T * S).conjTranspose * (T * S) =
    S * Matrix.kronecker M (partialTraceA N)⁻¹ * S
  rw [Matrix.conjTranspose_mul, hT, hS]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc T T S, hTsq]

/-- The right-hand operator in the pre-inversion Lin--Kim--Hsieh extension
inequality. -/
def ssaIntermediateRHS
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (A × B)) (N : CMatrix (B × C)) :
    CMatrix ((A × B) × C) :=
  Matrix.reindex (Equiv.prodAssoc A B C).symm
    (Equiv.prodAssoc A B C).symm
    (Matrix.kronecker (partialTraceB M) N⁻¹)

/-- Conjugating the pre-inversion right-hand operator by the SSA sandwich
matrix gives the identity. -/
theorem ssaSMatrix_mul_intermediateRHS_mul_ssaSMatrix
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (M : CMatrix (A × B)) (N : CMatrix (B × C))
    (hM : M.PosDef) (hN : N.PosDef) :
    ssaSMatrix M N * ssaIntermediateRHS M N * ssaSMatrix M N = 1 := by
  let e := (Equiv.prodAssoc A B C).symm
  let R := CFC.sqrt (partialTraceB M)⁻¹
  let Q := CFC.sqrt N
  let K := Matrix.kronecker R Q
  let P := Matrix.kronecker (partialTraceB M) N⁻¹
  have hleft : R * partialTraceB M * R = 1 := by
    exact posDef_sqrt_inv_sandwich (partialTraceB_posDef hM)
  have hright : Q * N⁻¹ * Q = 1 := by
    exact posDef_sqrt_inv_sqrt hN
  have hbase : K * P * K = 1 := by
    dsimp [K, P]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hleft, hright]
    simp
  change
    Matrix.reindex e e K * Matrix.reindex e e P *
        Matrix.reindex e e K = 1
  let F := Matrix.reindexAlgEquiv ℂ ℂ e
  change
    F K * F P * F K = 1
  calc
    _ = F (K * P) * F K :=
      congrArg (fun X => X * F K) (F.map_mul K P).symm
    _ = F ((K * P) * K) := (F.map_mul (K * P) K).symm
    _ = F 1 := congrArg F hbase
    _ = 1 := F.map_one

/-- Entrywise expansion of the `W` operator into its three contracted tensor
indices. -/
theorem ssaWMatrix_apply
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (A × B)) (N : CMatrix (B × C))
    (a a' : A) (b b' : B) (c c' : C) :
    ssaWMatrix M N ((a, b), c) ((a', b'), c') =
      ∑ x : A, ∑ y : B, ∑ z : C,
        CFC.sqrt M (a, b) (x, y) *
          CFC.sqrt (partialTraceA N)⁻¹ c z *
          (CFC.sqrt (partialTraceB M)⁻¹ x a' *
            CFC.sqrt N (y, z) (b', c')) := by
  simp only [ssaWMatrix, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [Matrix.reindex, Matrix.kronecker, Matrix.mul_apply]

/-- The `W`-matrix entries are the contraction of the two canonical SSA
isometries over their duplicated middle-system index. -/
theorem ssaWMatrix_apply_eq_sum_ssaVRho_mul_conjTranspose_ssaVSigma
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (A × B)) (N : CMatrix (B × C))
    (a a' : A) (b b' : B) (c c' : C) :
    ssaWMatrix M N ((a, b), c) ((a', b'), c') =
      ∑ y : B,
        ssaVRho M ((a, b), y) a' *
          (ssaVSigma N).conjTranspose c (y, (b', c')) := by
  have hNroot : (CFC.sqrt N).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg N)).isHermitian
  have hCRoot : (CFC.sqrt (partialTraceA N)⁻¹).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp
      (CFC.sqrt_nonneg (partialTraceA N)⁻¹)).isHermitian
  rw [ssaWMatrix_apply]
  simp_rw [ssaVRho_apply, Matrix.conjTranspose_apply, ssaVSigma_apply,
    star_sum, star_mul]
  simp_rw [show ∀ z : C,
      star (CFC.sqrt (partialTraceA N)⁻¹ z c) =
        CFC.sqrt (partialTraceA N)⁻¹ c z by
      intro z
      rw [← Matrix.conjTranspose_apply, hCRoot]]
  simp_rw [show ∀ y : B, ∀ z : C,
      star (CFC.sqrt N (b', c') (y, z)) =
        CFC.sqrt N (y, z) (b', c') by
      intro y z
      rw [← Matrix.conjTranspose_apply, hNroot]]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The first common-codomain SSA isometry, obtained by tensoring `ssaVRho`
with the identity and reassociating its source and target bases. -/
def ssaU1Matrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (A × B)) :
    Matrix ((A × B) × (B × (B × C))) ((A × B) × C) ℂ :=
  Matrix.reindex
    (Equiv.prodAssoc (A × B) B (B × C))
    (Equiv.prodAssoc A B C).symm
    (Matrix.kronecker (ssaVRho M) (1 : CMatrix (B × C)))

/-- The second common-codomain SSA isometry, obtained by tensoring the
identity with `ssaVSigma`. -/
def ssaU2Matrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (N : CMatrix (B × C)) :
    Matrix ((A × B) × (B × (B × C))) ((A × B) × C) ℂ :=
  Matrix.kronecker (1 : CMatrix (A × B)) (ssaVSigma N)

/-- `ssaU1Matrix` is an isometry for a positive-definite bipartite input. -/
theorem ssaU1Matrix_isometry
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (M : CMatrix (A × B)) (hM : M.PosDef) :
    (ssaU1Matrix (C := C) M).conjTranspose *
        ssaU1Matrix (C := C) M = 1 := by
  apply matrix_reindex_isometry
  exact matrix_kronecker_isometry
    (ssaVRho M) (1 : CMatrix (B × C))
    (ssaVRho_isometry M hM) (by simp)

/-- `ssaU2Matrix` is an isometry for a positive-definite bipartite input. -/
theorem ssaU2Matrix_isometry
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (N : CMatrix (B × C)) (hN : N.PosDef) :
    (ssaU2Matrix (A := A) N).conjTranspose *
        ssaU2Matrix (A := A) N = 1 := by
  exact matrix_kronecker_isometry
    (1 : CMatrix (A × B)) (ssaVSigma N)
    (by simp) (ssaVSigma_isometry N hN)

/-- The `W` operator is the cross product of the two common-codomain SSA
isometries. -/
theorem ssaWMatrix_eq_conjTranspose_mul_ssaU
    {C : Type w} [Fintype C] [DecidableEq C]
    (M : CMatrix (A × B)) (N : CMatrix (B × C)) :
    ssaWMatrix M N =
      (ssaU2Matrix (A := A) N).conjTranspose *
        ssaU1Matrix (C := C) M := by
  ext ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
  rw [ssaWMatrix_apply_eq_sum_ssaVRho_mul_conjTranspose_ssaVSigma]
  simp only [ssaU1Matrix, ssaU2Matrix, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.reindex, Matrix.one_apply, ite_and,
    apply_ite]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The Lin--Kim--Hsieh `W` operator is a contraction for positive-definite
bipartite inputs.  This is the central finite-dimensional operator leaf in the
SSA extension argument. -/
theorem ssaWMatrix_sq_le_one
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (M : CMatrix (A × B)) (N : CMatrix (B × C))
    (hM : M.PosDef) (hN : N.PosDef) :
    (ssaWMatrix M N).conjTranspose * ssaWMatrix M N ≤ 1 := by
  rw [ssaWMatrix_eq_conjTranspose_mul_ssaU]
  exact matrix_cross_isometry_contraction_le_one
    (ssaU2Matrix (A := A) N) (ssaU1Matrix (C := C) M)
    (ssaU2Matrix_isometry N hN) (ssaU1Matrix_isometry M hM)

/-- The pre-inversion Lin--Kim--Hsieh operator inequality obtained by
cancelling the invertible `S` sandwich from the `W` contraction. -/
theorem ssaIntermediate_ineq
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (M : CMatrix (A × B)) (N : CMatrix (B × C))
    (hM : M.PosDef) (hN : N.PosDef) :
    Matrix.kronecker M (partialTraceA N)⁻¹ ≤
      ssaIntermediateRHS M N := by
  let S := ssaSMatrix M N
  have hW := ssaWMatrix_sq_le_one M N hM hN
  rw [ssaWMatrix_sq_eq_sandwich M N hM hN] at hW
  have hright :=
    ssaSMatrix_mul_intermediateRHS_mul_ssaSMatrix M N hM hN
  rw [← hright] at hW
  exact
    (matrix_sandwich_le_iff_of_isUnit_isHermitian S
      (ssaSMatrix_isUnit M N hM hN)
      (ssaSMatrix_isHermitian M N)).mp hW

/-- The Lin--Kim--Hsieh operator extension of strong subadditivity:
`(Tr_B M)⁻¹ ⊗ N ≤ M⁻¹ ⊗ Tr_B N`, with the canonical associator reindexing. -/
theorem ssaOperatorExtension
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (M : CMatrix (A × B)) (N : CMatrix (B × C))
    (hM : M.PosDef) (hN : N.PosDef) :
    Matrix.kronecker (partialTraceB M)⁻¹ N ≤
      Matrix.reindex (Equiv.prodAssoc A B C)
        (Equiv.prodAssoc A B C)
        (Matrix.kronecker M⁻¹ (partialTraceA N)) := by
  let e := (Equiv.prodAssoc A B C).symm
  let L := Matrix.kronecker M (partialTraceA N)⁻¹
  let P := Matrix.kronecker (partialTraceB M) N⁻¹
  let R := Matrix.reindex e e P
  have hA := partialTraceB_posDef hM
  have hC := partialTraceA_posDef hN
  have hL : L.PosDef := hM.kronecker hC.inv
  have hP : P.PosDef := hA.kronecker hN.inv
  have hR : R.PosDef :=
    hP.submatrix e.symm.injective
  have hinv : R⁻¹ ≤ L⁻¹ :=
    posDef_nonsingInv_antitone hL hR
      (ssaIntermediate_ineq M N hM hN)
  have hNdet : IsUnit N.det :=
    (Matrix.isUnit_iff_isUnit_det N).mp hN.isUnit
  have hCdet : IsUnit (partialTraceA N).det :=
    (Matrix.isUnit_iff_isUnit_det (partialTraceA N)).mp hC.isUnit
  have hsimplified :
      Matrix.reindex e e
          (Matrix.kronecker (partialTraceB M)⁻¹ N) ≤
        Matrix.kronecker M⁻¹ (partialTraceA N) := by
    simpa [R, L, P, Matrix.inv_reindex, Matrix.inv_kronecker,
      Matrix.nonsing_inv_nonsing_inv N hNdet,
      Matrix.nonsing_inv_nonsing_inv (partialTraceA N) hCdet]
      using hinv
  have htransported :=
    (matrix_reindex_le_reindex_iff
      (Equiv.prodAssoc A B C)
      (Matrix.reindex e e
        (Matrix.kronecker (partialTraceB M)⁻¹ N))
      (Matrix.kronecker M⁻¹ (partialTraceA N))).mpr
      hsimplified
  simpa [e] using htransported

section SSALogarithms

open scoped Matrix.Norms.L2Operator

local instance matrixCStarAlgebraForSSALogarithms
    {Y : Type*} [Fintype Y] [DecidableEq Y] :
    CStarAlgebra (CMatrix Y) where
  norm_mul_self_le := Matrix.instCStarRing.norm_mul_self_le

local instance matrixNormedAlgebraRatForSSALogarithms
    {Y : Type*} [Fintype Y] [DecidableEq Y] :
    NormedAlgebra ℚ (CMatrix Y) :=
  NormedAlgebra.restrictScalars ℚ ℂ (CMatrix Y)

private theorem matrix_cfc_isHermitian
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {M : CMatrix Y} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    (hM.cfc f).IsHermitian := by
  rw [← hM.cfc_eq]
  exact IsSelfAdjoint.cfc

set_option maxHeartbeats 800000
/-- The finite spectral logarithm sends the inverse of a positive-definite
matrix to the negative logarithm, a local CFC identity used by SSA. -/
theorem posDef_cfc_log_inv
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {M : CMatrix Y} (hM : M.PosDef) :
    hM.inv.isHermitian.cfc Real.log =
      -hM.isHermitian.cfc Real.log := by
  let L : CMatrix Y := hM.isHermitian.cfc Real.log
  have hL : L.IsHermitian :=
    matrix_cfc_isHermitian hM.isHermitian Real.log
  have hexp : NormedSpace.exp (-L) = M⁻¹ := by
    rw [Matrix.exp_neg]
    congr 1
    change NormedSpace.exp (hM.isHermitian.cfc Real.log) = M
    rw [← hM.isHermitian.cfc_eq]
    exact CFC.exp_log M hM.isStrictlyPositive
  calc
    hM.inv.isHermitian.cfc Real.log = CFC.log M⁻¹ :=
      (hM.inv.isHermitian.cfc_eq Real.log).symm
    _ = CFC.log (NormedSpace.exp (-L)) := by rw [hexp]
    _ = -L := CFC.log_exp (-L) hL.neg.isSelfAdjoint
    _ = -hM.isHermitian.cfc Real.log := rfl

/-- The finite spectral logarithm of a positive-definite Kronecker product
splits as the sum of the two tensor-factor logarithms. -/
theorem posDef_cfc_log_kronecker
    {Y Z : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    {M : CMatrix Y} {N : CMatrix Z}
    (hM : M.PosDef) (hN : N.PosDef) :
    (hM.kronecker hN).isHermitian.cfc Real.log =
      Matrix.kronecker (hM.isHermitian.cfc Real.log) (1 : CMatrix Z) +
        Matrix.kronecker (1 : CMatrix Y)
          (hN.isHermitian.cfc Real.log) := by
  let LM : CMatrix Y := hM.isHermitian.cfc Real.log
  let LN : CMatrix Z := hN.isHermitian.cfc Real.log
  let H : CMatrix (Y × Z) :=
    Matrix.kronecker LM (1 : CMatrix Z) +
      Matrix.kronecker (1 : CMatrix Y) LN
  have hLM : LM.IsHermitian :=
    matrix_cfc_isHermitian hM.isHermitian Real.log
  have hLN : LN.IsHermitian :=
    matrix_cfc_isHermitian hN.isHermitian Real.log
  have hH : H.IsHermitian := by
    unfold H Matrix.IsHermitian
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_kronecker, hLM, hLN,
      Matrix.conjTranspose_one, Matrix.conjTranspose_one]
  have hcomm :
      Commute (Matrix.kronecker LM (1 : CMatrix Z))
        (Matrix.kronecker (1 : CMatrix Y) LN) := by
    change
      Matrix.kronecker LM (1 : CMatrix Z) *
          Matrix.kronecker (1 : CMatrix Y) LN =
        Matrix.kronecker (1 : CMatrix Y) LN *
          Matrix.kronecker LM (1 : CMatrix Z)
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  have hExpLM : NormedSpace.exp LM = M := by
    change NormedSpace.exp (hM.isHermitian.cfc Real.log) = M
    rw [← hM.isHermitian.cfc_eq]
    exact CFC.exp_log M hM.isStrictlyPositive
  have hExpLN : NormedSpace.exp LN = N := by
    change NormedSpace.exp (hN.isHermitian.cfc Real.log) = N
    rw [← hN.isHermitian.cfc_eq]
    exact CFC.exp_log N hN.isStrictlyPositive
  have hexp : NormedSpace.exp H = Matrix.kronecker M N := by
    rw [show H =
        Matrix.kronecker LM (1 : CMatrix Z) +
          Matrix.kronecker (1 : CMatrix Y) LN by rfl,
      Matrix.exp_add_of_commute _ _ hcomm,
      normedSpace_exp_kronecker_one,
      normedSpace_exp_one_kronecker]
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, hExpLM, hExpLN]
    simp
  calc
    (hM.kronecker hN).isHermitian.cfc Real.log =
        CFC.log (Matrix.kronecker M N) :=
      ((hM.kronecker hN).isHermitian.cfc_eq Real.log).symm
    _ = CFC.log (NormedSpace.exp H) := by rw [hexp]
    _ = H := CFC.log_exp H hH.isSelfAdjoint
    _ = Matrix.kronecker (hM.isHermitian.cfc Real.log)
          (1 : CMatrix Z) +
        Matrix.kronecker (1 : CMatrix Y)
          (hN.isHermitian.cfc Real.log) := rfl

/-- Finite spectral logarithms commute with simultaneous matrix reindexing,
the basis-change identity needed to compare the two SSA operators. -/
theorem posDef_cfc_log_reindex
    {Y Z : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (e : Y ≃ Z) {M : CMatrix Y} (hM : M.PosDef) :
    (hM.submatrix e.symm.injective).isHermitian.cfc Real.log =
      Matrix.reindex e e (hM.isHermitian.cfc Real.log) := by
  let L : CMatrix Y := hM.isHermitian.cfc Real.log
  let H : CMatrix Z := Matrix.reindex e e L
  have hL : L.IsHermitian :=
    matrix_cfc_isHermitian hM.isHermitian Real.log
  have hH : H.IsHermitian := matrix_reindex_isHermitian L e hL
  have hExpL : NormedSpace.exp L = M := by
    change NormedSpace.exp (hM.isHermitian.cfc Real.log) = M
    rw [← hM.isHermitian.cfc_eq]
    exact CFC.exp_log M hM.isStrictlyPositive
  have hexp :
      NormedSpace.exp H = Matrix.reindex e e M := by
    rw [show H = Matrix.reindex e e L by rfl,
      normedSpace_exp_matrix_reindex, hExpL]
  calc
    (hM.submatrix e.symm.injective).isHermitian.cfc Real.log =
        CFC.log (Matrix.reindex e e M) :=
      ((hM.submatrix e.symm.injective).isHermitian.cfc_eq Real.log).symm
    _ = CFC.log (NormedSpace.exp H) := by rw [hexp]
    _ = H := CFC.log_exp H hH.isSelfAdjoint
    _ = Matrix.reindex e e (hM.isHermitian.cfc Real.log) := rfl

set_option maxHeartbeats 200000

/-- Applying operator monotonicity of `log` to the SSA operator extension
gives the additive logarithmic operator inequality used in weak monotonicity. -/
theorem ssaLogOperatorInequality
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (M : CMatrix (A × B)) (N : CMatrix (B × C))
    (hM : M.PosDef) (hN : N.PosDef) :
    Matrix.kronecker
          (-(partialTraceB_posDef hM).isHermitian.cfc Real.log)
          (1 : CMatrix (B × C)) +
        Matrix.kronecker (1 : CMatrix A)
          (hN.isHermitian.cfc Real.log) ≤
      Matrix.reindex (Equiv.prodAssoc A B C)
        (Equiv.prodAssoc A B C)
        (Matrix.kronecker
            (-hM.isHermitian.cfc Real.log) (1 : CMatrix C) +
          Matrix.kronecker (1 : CMatrix (A × B))
            ((partialTraceA_posDef hN).isHermitian.cfc Real.log)) := by
  let hA : (partialTraceB M).PosDef := partialTraceB_posDef hM
  let hC : (partialTraceA N).PosDef := partialTraceA_posDef hN
  let hL : (Matrix.kronecker (partialTraceB M)⁻¹ N).PosDef :=
    hA.inv.kronecker hN
  let hP : (Matrix.kronecker M⁻¹ (partialTraceA N)).PosDef :=
    hM.inv.kronecker hC
  let e := Equiv.prodAssoc A B C
  let hR : (Matrix.reindex e e
      (Matrix.kronecker M⁻¹ (partialTraceA N))).PosDef :=
    hP.submatrix e.symm.injective
  have hlog :=
    Matrix.PosDef.cfc_log_mono hL hR
      (ssaOperatorExtension M N hM hN)
  change
    (hA.inv.kronecker hN).isHermitian.cfc Real.log ≤
      (hP.submatrix e.symm.injective).isHermitian.cfc Real.log at hlog
  rw [posDef_cfc_log_kronecker hA.inv hN,
    posDef_cfc_log_inv hA,
    posDef_cfc_log_reindex e hP] at hlog
  have hPlog :
      hP.isHermitian.cfc Real.log =
        Matrix.kronecker (-hM.isHermitian.cfc Real.log)
            (1 : CMatrix C) +
          Matrix.kronecker (1 : CMatrix (A × B))
            (hC.isHermitian.cfc Real.log) := by
    rw [show hP.isHermitian.cfc Real.log =
        (hM.inv.kronecker hC).isHermitian.cfc Real.log by rfl,
      posDef_cfc_log_kronecker hM.inv hC,
      posDef_cfc_log_inv hM]
  rw [hPlog] at hlog
  simpa [hA, hC, e] using hlog

/-- The logarithmic SSA operator inequality in the left-associated basis,
so its four terms pair directly with the four entropy marginals. -/
theorem ssaLogOperatorInequality_leftAssoc
    {C : Type w} [Fintype C] [DecidableEq C] [Nonempty B]
    (M : CMatrix (A × B)) (N : CMatrix (B × C))
    (hM : M.PosDef) (hN : N.PosDef) :
    Matrix.kronecker
          (Matrix.kronecker
            (-(partialTraceB_posDef hM).isHermitian.cfc Real.log)
            (1 : CMatrix B))
          (1 : CMatrix C) +
        ssaLiftBCMatrix (A := A) (hN.isHermitian.cfc Real.log) ≤
      Matrix.kronecker (-hM.isHermitian.cfc Real.log)
          (1 : CMatrix C) +
        Matrix.kronecker (1 : CMatrix (A × B))
          ((partialTraceA_posDef hN).isHermitian.cfc Real.log) := by
  let e := Equiv.prodAssoc A B C
  let L : CMatrix (A × (B × C)) :=
    Matrix.kronecker
          (-(partialTraceB_posDef hM).isHermitian.cfc Real.log)
          (1 : CMatrix (B × C)) +
        Matrix.kronecker (1 : CMatrix A)
          (hN.isHermitian.cfc Real.log)
  let R : CMatrix ((A × B) × C) :=
    Matrix.kronecker (-hM.isHermitian.cfc Real.log)
          (1 : CMatrix C) +
        Matrix.kronecker (1 : CMatrix (A × B))
          ((partialTraceA_posDef hN).isHermitian.cfc Real.log)
  have hLR : L ≤ Matrix.reindex e e R :=
    ssaLogOperatorInequality M N hM hN
  have htransported :
      Matrix.reindex e.symm e.symm L ≤
        Matrix.reindex e.symm e.symm (Matrix.reindex e e R) :=
    (matrix_reindex_le_reindex_iff e.symm L
      (Matrix.reindex e e R)).mpr hLR
  have hLreindex :
      Matrix.reindex e.symm e.symm L =
        Matrix.kronecker
            (Matrix.kronecker
              (-(partialTraceB_posDef hM).isHermitian.cfc Real.log)
              (1 : CMatrix B))
            (1 : CMatrix C) +
          ssaLiftBCMatrix (A := A) (hN.isHermitian.cfc Real.log) := by
    ext x y
    simp [L, e, Matrix.reindex_apply, Matrix.kronecker,
      ssaLiftBCMatrix, Matrix.one_apply, Prod.ext_iff]
    split_ifs <;> aesop
  rw [hLreindex] at htransported
  simpa [R, e, Matrix.reindex_apply] using htransported

end SSALogarithms

end SSAOperatorContractions

private theorem re_trace_mul_ssaLiftAMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) (T : CMatrix A) :
    Complex.re
        ((rho.matrix *
          Matrix.kronecker
            (Matrix.kronecker T (1 : CMatrix B))
            (1 : CMatrix C)).trace) =
      Complex.re ((rho.marginalAB.marginalA.matrix * T).trace) := by
  rw [show
    Matrix.kronecker
        (Matrix.kronecker T (1 : CMatrix B))
        (1 : CMatrix C) =
      ssaLiftABMatrix (C := C)
        (Matrix.kronecker T (1 : CMatrix B)) by rfl]
  rw [re_trace_mul_ssaLiftABMatrix rho
    (Matrix.kronecker T (1 : CMatrix B))]
  apply congrArg Complex.re
  exact
    (partialTraceB_mul_trace_eq_trace_mul_kronecker_right
      rho.marginalAB.matrix T).symm

private theorem re_trace_mul_ssaLiftCMatrix
    {C : Type w} [Fintype C] [DecidableEq C]
    (rho : State ((A × B) × C)) (T : CMatrix C) :
    Complex.re
        ((rho.matrix *
          Matrix.kronecker (1 : CMatrix (A × B)) T).trace) =
      Complex.re ((rho.marginalB.matrix * T).trace) := by
  apply congrArg Complex.re
  exact
    (partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right
      rho.matrix T).symm

/-! ## Project-local Mathlib supplement — Spectral purification -/

/-- The canonical finite spectral purification
`|ψρ⟩ = ∑ᵢₖ Uᵢₖ √λₖ |i⟩|k⟩` of a density state. -/
def spectralPurification (rho : State X) : PureVector (X × X) where
  amp x :=
    (rho.pos.isHermitian.eigenvectorUnitary : CMatrix X) x.1 x.2 *
      (Real.sqrt (rho.pos.isHermitian.eigenvalues x.2) : ℂ)
  trace_rankOne_eq_one := by
    rw [rankOneMatrix_trace]
    simp only [dotProduct]
    rw [Fintype.sum_prod_type]
    let U := rho.pos.isHermitian.eigenvectorUnitary
    let lambda := rho.pos.isHermitian.eigenvalues
    calc
      (∑ i, ∑ k,
          ((U : CMatrix X) i k * (Real.sqrt (lambda k) : ℂ)) *
            star ((U : CMatrix X) i k *
              (Real.sqrt (lambda k) : ℂ))) =
          ∑ k, (lambda k : ℂ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        calc
          (∑ i,
              ((U : CMatrix X) i k * (Real.sqrt (lambda k) : ℂ)) *
                star ((U : CMatrix X) i k *
                  (Real.sqrt (lambda k) : ℂ))) =
              ∑ i, ((Complex.normSq ((U : CMatrix X) i k) *
                (Real.sqrt (lambda k)) ^ 2 : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [star_mul]
            simp
            rw [Complex.normSq_eq_conj_mul_self]
            ring
          _ = ((∑ i, Complex.normSq ((U : CMatrix X) i k)) *
                (Real.sqrt (lambda k)) ^ 2 : ℝ) := by
            push_cast
            rw [Finset.sum_mul]
          _ = lambda k := by
            rw [entropy_unitary_col_normSq_sum, one_mul, Real.sq_sqrt]
            exact rho.pos.eigenvalues_nonneg k
      _ = 1 := by
        exact_mod_cast State.sum_eigenvalues_eq_one rho

/-- Tracing out the reference system of the spectral purification recovers
the original density state. -/
theorem spectralPurification_marginalA (rho : State X) :
    (spectralPurification rho).state.marginalA = rho := by
  apply State.ext
  ext i j
  simp only [State.marginalA_matrix, partialTraceB,
    PureVector.state_matrix, rankOneMatrix_apply, spectralPurification]
  let U := rho.pos.isHermitian.eigenvectorUnitary
  let lambda := rho.pos.isHermitian.eigenvalues
  calc
    (∑ k,
        ((U : CMatrix X) i k * (Real.sqrt (lambda k) : ℂ)) *
          star ((U : CMatrix X) j k * (Real.sqrt (lambda k) : ℂ))) =
      ∑ k, (U : CMatrix X) i k * (lambda k : ℂ) *
        star ((U : CMatrix X) j k) := by
      apply Finset.sum_congr rfl
      intro k _
      have hsqrt :
          (Real.sqrt (lambda k) : ℂ) *
              (Real.sqrt (lambda k) : ℂ) =
            (lambda k : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        exact Real.mul_self_sqrt (rho.pos.eigenvalues_nonneg k)
      rw [star_mul]
      simp
      calc
        (U : CMatrix X) i k * (Real.sqrt (lambda k) : ℂ) *
            ((Real.sqrt (lambda k) : ℂ) *
              star ((U : CMatrix X) j k)) =
          (U : CMatrix X) i k *
            ((Real.sqrt (lambda k) : ℂ) *
              (Real.sqrt (lambda k) : ℂ)) *
                star ((U : CMatrix X) j k) := by ring
        _ = _ := by rw [hsqrt]; rfl
    _ = ((U : CMatrix X) *
          Matrix.diagonal (Complex.ofReal ∘ lambda) *
            star (U : CMatrix X)) i j := by
      simp [Matrix.mul_apply, Matrix.diagonal_apply]
    _ = rho.matrix i j := by
      dsimp [U, lambda]
      exact congrArg (fun M : CMatrix X => M i j)
        rho.pos.isHermitian.spectral_theorem |>.symm

private theorem entropy_unitary_col_inner_sum
    (U : Matrix.unitaryGroup X ℂ) (k l : X) :
    ∑ i, (U : CMatrix X) i k * star ((U : CMatrix X) i l) =
      if k = l then 1 else 0 := by
  have hunit : star (U : CMatrix X) * (U : CMatrix X) = 1 :=
    Unitary.coe_star_mul_self U
  have h := congrArg (fun M : CMatrix X => M l k) hunit
  dsimp only at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.star_apply, Matrix.one_apply] at h
  simpa [mul_comm, eq_comm] using h

/-- The reference marginal of the spectral purification is diagonal with the
same eigenvalue family as the original state. -/
theorem spectralPurification_marginalB_matrix (rho : State X) :
    (spectralPurification rho).state.marginalB.matrix =
      Matrix.diagonal
        (Complex.ofReal ∘ rho.pos.isHermitian.eigenvalues) := by
  ext k l
  simp only [State.marginalB_matrix, partialTraceA,
    PureVector.state_matrix, rankOneMatrix_apply, spectralPurification]
  let U := rho.pos.isHermitian.eigenvectorUnitary
  let lambda := rho.pos.isHermitian.eigenvalues
  calc
    (∑ i,
        ((U : CMatrix X) i k * (Real.sqrt (lambda k) : ℂ)) *
          star ((U : CMatrix X) i l * (Real.sqrt (lambda l) : ℂ))) =
      (Real.sqrt (lambda k) : ℂ) * (Real.sqrt (lambda l) : ℂ) *
        ∑ i, (U : CMatrix X) i k *
          star ((U : CMatrix X) i l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [star_mul]
      simp
      ring
    _ = Matrix.diagonal (Complex.ofReal ∘ lambda) k l := by
      rw [entropy_unitary_col_inner_sum]
      by_cases hkl : k = l
      · subst l
        simp
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt]
        exact rho.pos.eigenvalues_nonneg k
      · simp [hkl]

/-- The reference marginal of the spectral purification has the same von
Neumann entropy as the purified state. -/
theorem vonNeumannEntropy_spectralPurification_marginalB
    (rho : State X) :
    vonNeumannEntropy (spectralPurification rho).state.marginalB =
      vonNeumannEntropy rho := by
  let lambda := rho.pos.isHermitian.eigenvalues
  have hlambda : ∀ i, 0 ≤ lambda i :=
    fun i => rho.pos.eigenvalues_nonneg i
  have hsum : ∑ i, lambda i = 1 := by
    simpa [lambda] using State.sum_eigenvalues_eq_one rho
  have hstate :
      (spectralPurification rho).state.marginalB =
        diagonalState lambda hlambda hsum := by
    apply State.ext
    rw [spectralPurification_marginalB_matrix]
    rfl
  rw [hstate, vonNeumannEntropy_diagonalState]
  rfl

/-- The coefficient matrix of a finite bipartite pure vector, with the two
subsystem labels used as its row and column indices. -/
def pureCoefficientMatrix
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (psi : PureVector (α × β)) : Matrix α β ℂ :=
  fun a b => psi.amp (a, b)

/-- The first marginal of a pure state is its coefficient matrix times its
conjugate transpose. -/
theorem pureState_marginalA_matrix_eq_coefficient_mul_conjTranspose
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (psi : PureVector (α × β)) :
    psi.state.marginalA.matrix =
      pureCoefficientMatrix psi *
        Matrix.conjTranspose (pureCoefficientMatrix psi) := by
  ext a a'
  simp [State.marginalA, partialTraceB, pureCoefficientMatrix,
    PureVector.state, rankOneMatrix_apply, Matrix.mul_apply]

/-- The second marginal of a pure state is the transpose of the reverse
coefficient-matrix product. -/
theorem pureState_marginalB_matrix_eq_conjTranspose_mul_coefficient_transpose
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (psi : PureVector (α × β)) :
    psi.state.marginalB.matrix =
      (Matrix.conjTranspose (pureCoefficientMatrix psi) *
        pureCoefficientMatrix psi).transpose := by
  ext b b'
  simp [State.marginalB, partialTraceA, pureCoefficientMatrix,
    PureVector.state, rankOneMatrix_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem vonNeumannEntropy_eq_neg_sum_roots
    {Y : Type*} [Fintype Y] [DecidableEq Y] (rho : State Y) :
    vonNeumannEntropy rho =
      -((rho.matrix.charpoly.roots.map
        (fun z : ℂ => z.re * Real.log z.re)).sum) := by
  have hroots := rho.pos.isHermitian.roots_charpoly_eq_eigenvalues
  have hmapped := congrArg
    (fun s : Multiset ℂ =>
      (s.map (fun z : ℂ => z.re * Real.log z.re)).sum) hroots
  unfold vonNeumannEntropy
  calc
    (-∑ i, rho.pos.isHermitian.eigenvalues i *
        Real.log (rho.pos.isHermitian.eigenvalues i)) =
      -((Multiset.map
          (fun z : ℂ => z.re * Real.log z.re)
          (Multiset.map
            (RCLike.ofReal ∘ rho.pos.isHermitian.eigenvalues)
            Finset.univ.val)).sum) := by
        simp [Multiset.map_map]
    _ = _ := congrArg Neg.neg hmapped.symm

private theorem rootEntropySum_X_pow_mul
    (p : Polynomial ℂ) (n : ℕ) (hp : p ≠ 0) :
    (((Polynomial.X ^ n * p).roots.map
      (fun z : ℂ => z.re * Real.log z.re)).sum) =
      ((p.roots.map
        (fun z : ℂ => z.re * Real.log z.re)).sum) := by
  rw [Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero n Polynomial.X_ne_zero) hp),
    Polynomial.roots_X_pow, Multiset.map_add, Multiset.sum_add]
  have hz :
      (Multiset.map (fun z : ℂ => z.re * Real.log z.re)
        (n • ({0} : Multiset ℂ))).sum = 0 := by
    rw [Multiset.map_nsmul, Multiset.map_singleton,
      Multiset.sum_nsmul]
    simp
  rw [hz, zero_add]

/-- The two reduced density states of every finite bipartite pure vector have
equal von Neumann entropy, including unequal subsystem dimensions. -/
theorem vonNeumannEntropy_pure_marginals_eq
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (psi : PureVector (α × β)) :
    vonNeumannEntropy psi.state.marginalA =
      vonNeumannEntropy psi.state.marginalB := by
  rw [vonNeumannEntropy_eq_neg_sum_roots,
    vonNeumannEntropy_eq_neg_sum_roots,
    pureState_marginalA_matrix_eq_coefficient_mul_conjTranspose,
    pureState_marginalB_matrix_eq_conjTranspose_mul_coefficient_transpose,
    Matrix.charpoly_transpose]
  congr 1
  let C := pureCoefficientMatrix psi
  by_cases hcard : Fintype.card β ≤ Fintype.card α
  · have hpoly :=
      Matrix.charpoly_mul_comm_of_le C C.conjTranspose hcard
    rw [hpoly]
    exact rootEntropySum_X_pow_mul _ _
      (Matrix.charpoly_monic (C.conjTranspose * C)).ne_zero
  · have hcard' : Fintype.card α ≤ Fintype.card β :=
      Nat.le_of_not_ge hcard
    have hpoly :=
      Matrix.charpoly_mul_comm_of_le C.conjTranspose C hcard'
    rw [hpoly]
    symm
    exact rootEntropySum_X_pow_mul _ _
      (Matrix.charpoly_monic (C * C.conjTranspose)).ne_zero

/-- Relabel the physical half of the canonical purification along an
arbitrary finite basis equivalence. -/
def spectralPurificationReindex
    {Y : Type v} [Fintype Y] [DecidableEq Y]
    (rho : State X) (e : X ≃ Y) : PureVector (Y × X) :=
  (spectralPurification rho).reindex
    (Equiv.prodCongr e (Equiv.refl X))

/-- The physical marginal of a relabelled spectral purification is the
correspondingly relabelled original state. -/
theorem spectralPurificationReindex_marginalA
    {Y : Type v} [Fintype Y] [DecidableEq Y]
    (rho : State X) (e : X ≃ Y) :
    (spectralPurificationReindex rho e).state.marginalA =
      rho.reindex e := by
  unfold spectralPurificationReindex
  rw [PureVector.reindex_state,
    State.marginalA_reindex_prodCongr,
    spectralPurification_marginalA]

/-- The reference marginal of every relabelled spectral purification has the
same entropy as the original state. -/
theorem vonNeumannEntropy_spectralPurificationReindex_marginalB
    {Y : Type v} [Fintype Y] [DecidableEq Y]
    (rho : State X) (e : X ≃ Y) :
    vonNeumannEntropy
        (spectralPurificationReindex rho e).state.marginalB =
      vonNeumannEntropy rho := by
  calc
    vonNeumannEntropy
        (spectralPurificationReindex rho e).state.marginalB =
      vonNeumannEntropy
        (spectralPurificationReindex rho e).state.marginalA :=
      (vonNeumannEntropy_pure_marginals_eq
        (spectralPurificationReindex rho e)).symm
    _ = vonNeumannEntropy (rho.reindex e) := by
      rw [spectralPurificationReindex_marginalA]
    _ = vonNeumannEntropy rho :=
      vonNeumannEntropy_reindex rho e

/-- Successively tracing the first two factors of a tripartite state agrees
with tracing them together. -/
theorem State.marginalBC_marginalB_eq_marginalB
    {P : Type u} {Q : Type v} {R : Type w}
    [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R]
    (rho : State ((P × Q) × R)) :
    rho.marginalBC.marginalB = rho.marginalB := by
  apply State.ext
  ext r r'
  simp only [State.marginalB_matrix, partialTraceA, State.marginalBC]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type (fun pq : P × Q =>
    rho.matrix (pq, r) (pq, r'))).symm

/-- The first factor of the `QR` marginal is the middle marginal of a
tripartite state. -/
theorem State.marginalBC_marginalA_eq_marginalBOfABC
    {P : Type u} {Q : Type v} {R : Type w}
    [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R]
    (rho : State ((P × Q) × R)) :
    rho.marginalBC.marginalA = rho.marginalBOfABC := by
  apply State.ext
  ext q q'
  simp only [State.marginalA_matrix, partialTraceB,
    State.marginalBOfABC, State.marginalAB,
    State.marginalB_matrix, partialTraceA, State.marginalBC]
  rw [Finset.sum_comm]

private def purificationA_BCR_equiv
    {C : Type w} :
    ((((A × B) × C) × ((A × B) × C))) ≃
      A × ((B × C) × ((A × B) × C)) where
  toFun x :=
    (x.1.1.1, ((x.1.1.2, x.1.2), x.2))
  invFun x :=
    (((x.1, x.2.1.1), x.2.1.2), x.2.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- The `BCR` marginal obtained by purifying `rhoABC` and tracing out `A`;
this is the state used to convert weak monotonicity into SSA. -/
def spectralPurificationBCR
    {C : Type w} [Fintype C] [DecidableEq C]
    (rhoABC : State ((A × B) × C)) :
    State ((B × C) × ((A × B) × C)) :=
  ((spectralPurification rhoABC).reindex
    (purificationA_BCR_equiv (A := A) (B := B) (C := C))).state.marginalB

/-- The `BC` marginal of the purified `BCR` state is the original `BC`
marginal. -/
theorem spectralPurificationBCR_marginalA
    {C : Type w} [Fintype C] [DecidableEq C]
    (rhoABC : State ((A × B) × C)) :
    (spectralPurificationBCR rhoABC).marginalA =
      rhoABC.marginalBC := by
  apply State.ext
  ext bc bc'
  simp only [spectralPurificationBCR, State.marginalA_matrix,
    partialTraceB, State.marginalB_matrix, partialTraceA,
    PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.reindex_amp, purificationA_BCR_equiv,
    Equiv.coe_fn_symm_mk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hpur := congrArg
    (fun s : State ((A × B) × C) =>
      s.matrix ((a, bc.1), bc.2) ((a, bc'.1), bc'.2))
    (spectralPurification_marginalA rhoABC)
  simpa [State.marginalA, partialTraceB, PureVector.state,
    rankOneMatrix_apply] using hpur

/-- The reference marginal of the purified `BCR` state is the reference
marginal of the original spectral purification. -/
theorem spectralPurificationBCR_marginalB
    {C : Type w} [Fintype C] [DecidableEq C]
    (rhoABC : State ((A × B) × C)) :
    (spectralPurificationBCR rhoABC).marginalB =
      (spectralPurification rhoABC).state.marginalB := by
  apply State.ext
  ext r r'
  simp only [spectralPurificationBCR, State.marginalB_matrix,
    partialTraceA, PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.reindex_amp, purificationA_BCR_equiv,
    Equiv.coe_fn_symm_mk]
  let e : ((B × C) × A) ≃ ((A × B) × C) :=
    { toFun := fun x => ((x.2, x.1.1), x.1.2)
      invFun := fun x => ((x.1.2, x.2), x.1.1)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  calc
    (∑ bc : B × C, ∑ a : A,
      (spectralPurification rhoABC).amp
          (((a, bc.1), bc.2), r) *
        star ((spectralPurification rhoABC).amp
          (((a, bc.1), bc.2), r'))) =
      ∑ x : (B × C) × A,
      (spectralPurification rhoABC).amp
          (((x.2, x.1.1), x.1.2), r) *
        star ((spectralPurification rhoABC).amp
          (((x.2, x.1.1), x.1.2), r')) := by
      exact (Fintype.sum_prod_type (fun x : (B × C) × A =>
        (spectralPurification rhoABC).amp
            (((x.2, x.1.1), x.1.2), r) *
          star ((spectralPurification rhoABC).amp
            (((x.2, x.1.1), x.1.2), r')))).symm
    _ = _ := Fintype.sum_equiv e
      (fun x : (B × C) × A =>
        (spectralPurification rhoABC).amp
            (((x.2, x.1.1), x.1.2), r) *
          star ((spectralPurification rhoABC).amp
            (((x.2, x.1.1), x.1.2), r')))
      (fun x : (A × B) × C =>
        (spectralPurification rhoABC).amp (x, r) *
          star ((spectralPurification rhoABC).amp (x, r')))
      (fun x => by rfl)

private def purificationAB_CR_equiv
    {C : Type w} :
    ((((A × B) × C) × ((A × B) × C))) ≃
      (A × B) × (C × ((A × B) × C)) where
  toFun x := (x.1.1, (x.1.2, x.2))
  invFun x := ((x.1, x.2.1), x.2.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

private def spectralPurificationAB_CR
    {C : Type w} [Fintype C] [DecidableEq C]
    (rhoABC : State ((A × B) × C)) :
    PureVector ((A × B) × (C × ((A × B) × C))) :=
  (spectralPurification rhoABC).reindex
    (purificationAB_CR_equiv (A := A) (B := B) (C := C))

private theorem spectralPurificationAB_CR_marginalA
    {C : Type w} [Fintype C] [DecidableEq C]
    (rhoABC : State ((A × B) × C)) :
    (spectralPurificationAB_CR rhoABC).state.marginalA =
      rhoABC.marginalAB := by
  apply State.ext
  ext ab ab'
  simp only [spectralPurificationAB_CR, State.marginalA_matrix,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.reindex_amp, purificationAB_CR_equiv,
    Equiv.coe_fn_symm_mk, State.marginalAB]
  have hpur := congrArg
    (fun s : State ((A × B) × C) =>
      ∑ c : C, s.matrix (ab, c) (ab', c))
    (spectralPurification_marginalA rhoABC)
  simpa [State.marginalA, partialTraceB, PureVector.state,
    rankOneMatrix_apply, Fintype.sum_prod_type] using hpur

private theorem spectralPurificationBCR_marginalBC_eq
    {C : Type w} [Fintype C] [DecidableEq C]
    (rhoABC : State ((A × B) × C)) :
    (spectralPurificationBCR rhoABC).marginalBC =
      (spectralPurificationAB_CR rhoABC).state.marginalB := by
  apply State.ext
  ext cr cr'
  simp only [spectralPurificationBCR, spectralPurificationAB_CR,
    State.marginalBC, State.marginalB_matrix, partialTraceA,
    PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.reindex_amp, purificationA_BCR_equiv,
    purificationAB_CR_equiv, Equiv.coe_fn_symm_mk]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type (fun ab : A × B =>
    (spectralPurification rhoABC).amp ((ab, cr.1), cr.2) *
      star ((spectralPurification rhoABC).amp
        ((ab, cr'.1), cr'.2)))).symm

/-- The `CR` marginal of the purified `BCR` state has the entropy of the
original `AB` marginal, the complementary-entropy identity needed for SSA. -/
theorem vonNeumannEntropy_spectralPurificationBCR_marginalBC
    {C : Type w} [Fintype C] [DecidableEq C]
    (rhoABC : State ((A × B) × C)) :
    vonNeumannEntropy (spectralPurificationBCR rhoABC).marginalBC =
      vonNeumannEntropy rhoABC.marginalAB := by
  rw [spectralPurificationBCR_marginalBC_eq]
  calc
    vonNeumannEntropy
        (spectralPurificationAB_CR rhoABC).state.marginalB =
      vonNeumannEntropy
        (spectralPurificationAB_CR rhoABC).state.marginalA :=
      (vonNeumannEntropy_pure_marginals_eq
        (spectralPurificationAB_CR rhoABC)).symm
    _ = vonNeumannEntropy rhoABC.marginalAB := by
      rw [spectralPurificationAB_CR_marginalA]

/-- Positive-definite weak monotonicity follows by pairing the logarithmic
SSA operator extension with the tripartite density matrix. -/
theorem vonNeumannEntropyWeakMonotonicity_posDef
    {P : Type u} {Q : Type v} {R : Type w}
    [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R]
    [Nonempty P] [Nonempty Q] [Nonempty R]
    (tau : State ((P × Q) × R)) (htau : tau.matrix.PosDef) :
    vonNeumannEntropy tau.marginalAB.marginalA +
          vonNeumannEntropy tau.marginalBC.marginalB ≤
        vonNeumannEntropy tau.marginalAB +
          vonNeumannEntropy tau.marginalBC := by
  let hAB : tau.marginalAB.matrix.PosDef :=
    State.marginalAB_posDef tau htau
  let hBC : tau.marginalBC.matrix.PosDef :=
    State.marginalBC_posDef tau htau
  have hop :=
    ssaLogOperatorInequality_leftAssoc
      tau.marginalAB.matrix tau.marginalBC.matrix hAB hBC
  have hop' :
      Matrix.kronecker
            (Matrix.kronecker
              (-tau.marginalAB.marginalA.spectralLogMatrix)
              (1 : CMatrix Q))
            (1 : CMatrix R) +
          ssaLiftBCMatrix (A := P)
            tau.marginalBC.spectralLogMatrix ≤
        ssaLiftABMatrix (C := R)
            (-tau.marginalAB.spectralLogMatrix) +
          Matrix.kronecker (1 : CMatrix (P × Q))
            tau.marginalBC.marginalB.spectralLogMatrix := by
    simpa [hAB, hBC, State.spectralLogMatrix, ssaLiftABMatrix]
      using hop
  have htrace :=
    Matrix.PosSemidef.re_trace_mul_mono_right tau.pos hop'
  rw [mul_add, mul_add, Matrix.trace_add, Matrix.trace_add,
    Complex.add_re, Complex.add_re,
    re_trace_mul_ssaLiftAMatrix,
    re_trace_mul_ssaLiftBCMatrix,
    re_trace_mul_ssaLiftABMatrix,
    re_trace_mul_ssaLiftCMatrix] at htrace
  rw [← State.marginalBC_marginalB_eq_marginalB tau] at htrace
  simp only [mul_neg, Matrix.trace_neg, Complex.neg_re] at htrace
  rw [vonNeumannEntropy_eq_neg_re_trace_mul_spectralLogMatrix,
    vonNeumannEntropy_eq_neg_re_trace_mul_spectralLogMatrix,
    vonNeumannEntropy_eq_neg_re_trace_mul_spectralLogMatrix,
    vonNeumannEntropy_eq_neg_re_trace_mul_spectralLogMatrix]
  linarith

/-- Weak monotonicity for arbitrary density states follows from its
positive-definite case by the same maximally mixed regularization as SSA. -/
theorem vonNeumannEntropyWeakMonotonicity_of_posDef_case
    {P : Type u} {Q : Type v} {R : Type w}
    [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R]
    (hposDef :
      ∀ tau : State ((P × Q) × R),
        tau.matrix.PosDef →
        vonNeumannEntropy tau.marginalAB.marginalA +
              vonNeumannEntropy tau.marginalBC.marginalB ≤
            vonNeumannEntropy tau.marginalAB +
              vonNeumannEntropy tau.marginalBC)
    (rho : State ((P × Q) × R)) :
    vonNeumannEntropy rho.marginalAB.marginalA +
          vonNeumannEntropy rho.marginalBC.marginalB ≤
        vonNeumannEntropy rho.marginalAB +
          vonNeumannEntropy rho.marginalBC := by
  have hPQR : Nonempty ((P × Q) × R) := rho.nonempty
  letI : Nonempty (P × Q) := nonempty_prod.mp hPQR |>.1
  letI : Nonempty P :=
    nonempty_prod.mp (inferInstance : Nonempty (P × Q)) |>.1
  letI : Nonempty Q :=
    nonempty_prod.mp (inferInstance : Nonempty (P × Q)) |>.2
  letI : Nonempty R := nonempty_prod.mp hPQR |>.2
  have hB :
      Filter.Tendsto
        (fun n =>
          vonNeumannEntropy
            (stateRegularization rho n).marginalAB.marginalA)
        Filter.atTop
        (nhds (vonNeumannEntropy rho.marginalAB.marginalA)) := by
    convert
      tendsto_vonNeumannEntropy_stateRegularization
        rho.marginalAB.marginalA using 1
    funext n
    rw [stateRegularization_marginalAB,
      stateRegularization_marginalA]
  have hR :
      Filter.Tendsto
        (fun n =>
          vonNeumannEntropy
            (stateRegularization rho n).marginalBC.marginalB)
        Filter.atTop
        (nhds (vonNeumannEntropy rho.marginalBC.marginalB)) := by
    convert
      tendsto_vonNeumannEntropy_stateRegularization
        rho.marginalBC.marginalB using 1
    funext n
    rw [stateRegularization_marginalBC,
      stateRegularization_marginalB]
  have hAB :
      Filter.Tendsto
        (fun n =>
          vonNeumannEntropy (stateRegularization rho n).marginalAB)
        Filter.atTop
        (nhds (vonNeumannEntropy rho.marginalAB)) := by
    convert
      tendsto_vonNeumannEntropy_stateRegularization
        rho.marginalAB using 1
    funext n
    rw [stateRegularization_marginalAB]
  have hBC :
      Filter.Tendsto
        (fun n =>
          vonNeumannEntropy (stateRegularization rho n).marginalBC)
        Filter.atTop
        (nhds (vonNeumannEntropy rho.marginalBC)) := by
    convert
      tendsto_vonNeumannEntropy_stateRegularization
        rho.marginalBC using 1
    funext n
    rw [stateRegularization_marginalBC]
  exact le_of_tendsto_of_tendsto' (hB.add hR) (hAB.add hBC) fun n =>
    hposDef (stateRegularization rho n)
      (stateRegularization_posDef rho n)

/-- Weak monotonicity on the canonical purified `BCR` systems implies full
finite-dimensional strong subadditivity. -/
theorem vonNeumannEntropyStrongSubadditivity_of_weakMonotonicity
    (hwm :
      ∀ {C : Type w} [Fintype C] [DecidableEq C],
        ∀ tau : State ((B × C) × ((A × B) × C)),
          vonNeumannEntropy tau.marginalAB.marginalA +
              vonNeumannEntropy tau.marginalBC.marginalB ≤
            vonNeumannEntropy tau.marginalAB +
              vonNeumannEntropy tau.marginalBC) :
    VonNeumannEntropyStrongSubadditivity.{u, v, w}
      (A := A) (B := B) := by
  intro C _ _ rhoABC
  let tau := spectralPurificationBCR rhoABC
  have htauBC : tau.marginalAB = rhoABC.marginalBC := by
    exact spectralPurificationBCR_marginalA rhoABC
  have htauB :
      tau.marginalAB.marginalA = rhoABC.marginalBOfABC := by
    rw [htauBC]
    exact State.marginalBC_marginalA_eq_marginalBOfABC rhoABC
  have htauR : tau.marginalBC.marginalB =
      (spectralPurification rhoABC).state.marginalB := by
    rw [State.marginalBC_marginalB_eq_marginalB]
    exact spectralPurificationBCR_marginalB rhoABC
  have htauREntropy :
      vonNeumannEntropy tau.marginalBC.marginalB =
        vonNeumannEntropy rhoABC := by
    rw [htauR]
    exact vonNeumannEntropy_spectralPurification_marginalB rhoABC
  have htauCREntropy :
      vonNeumannEntropy tau.marginalBC =
        vonNeumannEntropy rhoABC.marginalAB :=
    vonNeumannEntropy_spectralPurificationBCR_marginalBC rhoABC
  have h := hwm tau
  rw [htauB, htauREntropy, htauBC, htauCREntropy] at h
  linarith

/-- Positive-definite weak monotonicity is sufficient for full
finite-dimensional strong subadditivity. -/
theorem vonNeumannEntropyStrongSubadditivity_of_posDef_weakMonotonicity
    (hwmPosDef :
      ∀ {C : Type w} [Fintype C] [DecidableEq C],
        ∀ tau : State ((B × C) × ((A × B) × C)),
          tau.matrix.PosDef →
          vonNeumannEntropy tau.marginalAB.marginalA +
                vonNeumannEntropy tau.marginalBC.marginalB ≤
              vonNeumannEntropy tau.marginalAB +
                vonNeumannEntropy tau.marginalBC) :
    VonNeumannEntropyStrongSubadditivity.{u, v, w}
      (A := A) (B := B) := by
  apply vonNeumannEntropyStrongSubadditivity_of_weakMonotonicity
  intro C _ _ tau
  exact vonNeumannEntropyWeakMonotonicity_of_posDef_case
    (fun omega homega => hwmPosDef omega homega) tau

private def pointProbability
    {α : Type*} [DecidableEq α] (x : α) : α → ℝ :=
  Pi.single x 1

private def pairProbability
    {α : Type*} [DecidableEq α] (x y : α) : α → ℝ :=
  Pi.single x (1 / 2) + Pi.single y (1 / 2)

private def rectangleProbability
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a₀ a₁ : α) (b₀ b₁ : β) : α × β → ℝ :=
  Pi.single (a₀, b₀) (1 / 4) + Pi.single (a₀, b₁) (1 / 4) +
    Pi.single (a₁, b₀) (1 / 4) + Pi.single (a₁, b₁) (1 / 4)

private def pointState
    {α : Type*} [Fintype α] [DecidableEq α] (x : α) : State α :=
  diagonalState (pointProbability x)
    (by
      intro z
      simp only [pointProbability, Pi.single_apply]
      split_ifs <;> norm_num)
    (by simp [pointProbability])

private def pairState
    {α : Type*} [Fintype α] [DecidableEq α] (x y : α) : State α :=
  diagonalState (pairProbability x y)
    (by
      intro z
      simp only [pairProbability, Pi.add_apply, Pi.single_apply]
      split_ifs <;> norm_num)
    (by
      simp [pairProbability, Finset.sum_add_distrib]
      norm_num)

private def rectangleState
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (a₀ a₁ : α) (b₀ b₁ : β) : State (α × β) :=
  diagonalState (rectangleProbability a₀ a₁ b₀ b₁)
    (by
      intro z
      simp only [rectangleProbability, Pi.add_apply, Pi.single_apply]
      split_ifs <;> norm_num)
    (by
      simp [rectangleProbability, Finset.sum_add_distrib]
      norm_num)

private theorem vonNeumannEntropy_pointState
    {α : Type*} [Fintype α] [DecidableEq α] (x : α) :
    vonNeumannEntropy (pointState x) = 0 := by
  unfold pointState
  rw [vonNeumannEntropy_diagonalState]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro z _
  by_cases h : z = x
  · subst z
    simp [pointProbability]
  · simp [pointProbability, h]

private theorem vonNeumannEntropy_pairState
    {α : Type*} [Fintype α] [DecidableEq α]
    (x y : α) (hxy : x ≠ y) :
    vonNeumannEntropy (pairState x y) = -Real.log (1 / 2) := by
  unfold pairState
  rw [vonNeumannEntropy_diagonalState]
  let c : ℝ := (1 / 2) * Real.log (1 / 2)
  have hf : ∀ z, pairProbability x y z * Real.log (pairProbability x y z) =
      (Pi.single x c : α → ℝ) z + (Pi.single y c : α → ℝ) z := by
    intro z
    by_cases hx : z = x
    · subst z
      simp [pairProbability, c, hxy]
    · by_cases hy : z = y
      · subst z
        simp [pairProbability, c, hxy]
      · simp [pairProbability, c, hx, hy]
  rw [show (∑ z, pairProbability x y z *
      Real.log (pairProbability x y z)) =
      ∑ z, ((Pi.single x c : α → ℝ) z +
        (Pi.single y c : α → ℝ) z) from
      Finset.sum_congr rfl fun z _ => hf z]
  rw [Finset.sum_add_distrib]
  simp [c]
  ring

private theorem vonNeumannEntropy_rectangleState
    {α : Type*} {β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (a₀ a₁ : α) (b₀ b₁ : β) (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    vonNeumannEntropy (rectangleState a₀ a₁ b₀ b₁) =
      -Real.log (1 / 4) := by
  unfold rectangleState
  rw [vonNeumannEntropy_diagonalState]
  let c : ℝ := (1 / 4) * Real.log (1 / 4)
  have hf : ∀ z, rectangleProbability a₀ a₁ b₀ b₁ z *
      Real.log (rectangleProbability a₀ a₁ b₀ b₁ z) =
      (Pi.single (a₀, b₀) c : α × β → ℝ) z +
      (Pi.single (a₀, b₁) c : α × β → ℝ) z +
      (Pi.single (a₁, b₀) c : α × β → ℝ) z +
      (Pi.single (a₁, b₁) c : α × β → ℝ) z := by
    intro z
    by_cases h00 : z = (a₀, b₀)
    · subst z
      simp [rectangleProbability, c, ha, hb]
    · by_cases h01 : z = (a₀, b₁)
      · subst z
        simp [rectangleProbability, c, ha, hb]
      · by_cases h10 : z = (a₁, b₀)
        · subst z
          simp [rectangleProbability, c, ha, hb]
        · by_cases h11 : z = (a₁, b₁)
          · subst z
            simp [rectangleProbability, c, ha, hb]
          · simp [rectangleProbability, c, h00, h01, h10, h11]
  rw [show (∑ z, rectangleProbability a₀ a₁ b₀ b₁ z *
      Real.log (rectangleProbability a₀ a₁ b₀ b₁ z)) =
      ∑ z, ((Pi.single (a₀, b₀) c : α × β → ℝ) z +
        (Pi.single (a₀, b₁) c : α × β → ℝ) z +
        (Pi.single (a₁, b₀) c : α × β → ℝ) z +
        (Pi.single (a₁, b₁) c : α × β → ℝ) z) from
      Finset.sum_congr rfl fun z _ => hf z]
  simp only [Finset.sum_add_distrib]
  simp [c]
  ring

private theorem sum_single_prod_right
    {α β R : Type*} [Fintype β]
    [DecidableEq α] [DecidableEq β] [AddCommMonoid R]
    (a a₀ : α) (b₀ : β) (c : R) :
    (∑ b : β, (Pi.single (a₀, b₀) c : α × β → R) (a, b)) =
      (Pi.single a₀ c : α → R) a := by
  by_cases h : a = a₀
  · subst a
    have hf :
        (fun b : β =>
          (Pi.single (a₀, b₀) c : α × β → R) (a₀, b)) =
          Pi.single b₀ c := by
      funext b
      by_cases hb : b = b₀
      · subst b
        rw [Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne
            (fun hab => hb (congrArg Prod.snd hab)),
          Pi.single_eq_of_ne hb]
    rw [hf]
    simp
  · have hpair : ∀ b : β, (a, b) ≠ (a₀, b₀) :=
      fun _ hab => h (congrArg Prod.fst hab)
    simp_rw [Pi.single_apply, if_neg (hpair _)]
    rw [if_neg h]
    simp

private theorem sum_single_prod_left
    {α β R : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] [AddCommMonoid R]
    (b b₀ : β) (a₀ : α) (c : R) :
    (∑ a : α, (Pi.single (a₀, b₀) c : α × β → R) (a, b)) =
      (Pi.single b₀ c : β → R) b := by
  by_cases h : b = b₀
  · subst b
    have hf :
        (fun a : α =>
          (Pi.single (a₀, b₀) c : α × β → R) (a, b₀)) =
          Pi.single a₀ c := by
      funext a
      by_cases ha : a = a₀
      · subst a
        rw [Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne
            (fun hab => ha (congrArg Prod.fst hab)),
          Pi.single_eq_of_ne ha]
    rw [hf]
    simp
  · have hpair : ∀ a : α, (a, b) ≠ (a₀, b₀) :=
      fun _ hab => h (congrArg Prod.snd hab)
    simp_rw [Pi.single_apply, if_neg (hpair _)]
    rw [if_neg h]
    simp

private theorem pointState_marginalA
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (x : α × β) :
    (pointState x).marginalA = pointState x.1 := by
  rcases x with ⟨x₁, x₂⟩
  apply State.ext
  ext a a'
  simp only [pointState, diagonalState, State.marginalA, partialTraceB]
  by_cases h : a = a'
  · subst a'
    simp only [Matrix.diagonal_apply_eq]
    have hreal := sum_single_prod_right a x₁ x₂ (1 : ℝ)
    exact_mod_cast hreal
  · simp [h]

private theorem pointState_marginalB
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (x : α × β) :
    (pointState x).marginalB = pointState x.2 := by
  rcases x with ⟨x₁, x₂⟩
  apply State.ext
  ext b b'
  simp only [pointState, diagonalState, State.marginalB, partialTraceA]
  by_cases h : b = b'
  · subst b'
    simp only [Matrix.diagonal_apply_eq]
    have hreal := sum_single_prod_left b x₂ x₁ (1 : ℝ)
    exact_mod_cast hreal
  · simp [h]

private theorem pairState_marginalA
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (x y : α × β) :
    (pairState x y).marginalA = pairState x.1 y.1 := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  apply State.ext
  ext a a'
  simp only [pairState, diagonalState, State.marginalA, partialTraceB]
  by_cases h : a = a'
  · subst a'
    simp only [Matrix.diagonal_apply_eq]
    have hreal :
        (∑ b, pairProbability (x₁, x₂) (y₁, y₂) (a, b)) =
          pairProbability x₁ y₁ a := by
      simp only [pairProbability, Pi.add_apply, Finset.sum_add_distrib]
      rw [sum_single_prod_right a x₁ x₂ (1 / 2 : ℝ),
        sum_single_prod_right a y₁ y₂ (1 / 2 : ℝ)]
    exact_mod_cast hreal
  · simp [h]

private theorem pairState_marginalB
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (x y : α × β) :
    (pairState x y).marginalB = pairState x.2 y.2 := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  apply State.ext
  ext b b'
  simp only [pairState, diagonalState, State.marginalB, partialTraceA]
  by_cases h : b = b'
  · subst b'
    simp only [Matrix.diagonal_apply_eq]
    have hreal :
        (∑ a, pairProbability (x₁, x₂) (y₁, y₂) (a, b)) =
          pairProbability x₂ y₂ b := by
      simp only [pairProbability, Pi.add_apply, Finset.sum_add_distrib]
      rw [sum_single_prod_left b x₂ x₁ (1 / 2 : ℝ),
        sum_single_prod_left b y₂ y₁ (1 / 2 : ℝ)]
    exact_mod_cast hreal
  · simp [h]

private theorem rectangleState_marginalA
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (a₀ a₁ : α) (b₀ b₁ : β) :
    (rectangleState a₀ a₁ b₀ b₁).marginalA = pairState a₀ a₁ := by
  apply State.ext
  ext a a'
  simp only [rectangleState, pairState, diagonalState,
    State.marginalA, partialTraceB]
  by_cases h : a = a'
  · subst a'
    simp only [Matrix.diagonal_apply_eq]
    have hreal :
        (∑ b, rectangleProbability a₀ a₁ b₀ b₁ (a, b)) =
          pairProbability a₀ a₁ a := by
      simp only [rectangleProbability, pairProbability,
        Pi.add_apply, Finset.sum_add_distrib]
      rw [sum_single_prod_right a a₀ b₀ (1 / 4 : ℝ),
        sum_single_prod_right a a₀ b₁ (1 / 4 : ℝ),
        sum_single_prod_right a a₁ b₀ (1 / 4 : ℝ),
        sum_single_prod_right a a₁ b₁ (1 / 4 : ℝ)]
      by_cases ha₀ : a = a₀
      · subst a
        by_cases ha₁ : a₀ = a₁
        · subst a₁
          simp
          norm_num
        · simp [ha₁]
          norm_num
      · by_cases ha₁ : a = a₁
        · subst a
          simp [ha₀]
          norm_num
        · simp [ha₀, ha₁]
    exact_mod_cast hreal
  · simp [h]

private theorem rectangleState_marginalB
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (a₀ a₁ : α) (b₀ b₁ : β) :
    (rectangleState a₀ a₁ b₀ b₁).marginalB = pairState b₀ b₁ := by
  apply State.ext
  ext b b'
  simp only [rectangleState, pairState, diagonalState,
    State.marginalB, partialTraceA]
  by_cases h : b = b'
  · subst b'
    simp only [Matrix.diagonal_apply_eq]
    have hreal :
        (∑ a, rectangleProbability a₀ a₁ b₀ b₁ (a, b)) =
          pairProbability b₀ b₁ b := by
      simp only [rectangleProbability, pairProbability,
        Pi.add_apply, Finset.sum_add_distrib]
      rw [sum_single_prod_left b b₀ a₀ (1 / 4 : ℝ),
        sum_single_prod_left b b₁ a₀ (1 / 4 : ℝ),
        sum_single_prod_left b b₀ a₁ (1 / 4 : ℝ),
        sum_single_prod_left b b₁ a₁ (1 / 4 : ℝ)]
      by_cases hb₀ : b = b₀
      · subst b
        by_cases hb₁ : b₀ = b₁
        · subst b₁
          simp
          norm_num
        · simp [hb₁]
          norm_num
      · by_cases hb₁ : b = b₁
        · subst b
          simp [hb₀]
          norm_num
        · simp [hb₀, hb₁]
    exact_mod_cast hreal
  · simp [h]

private theorem quantumMutualInformation_pointState
    (x : A × B) :
    quantumMutualInformation (pointState x) = 0 := by
  unfold quantumMutualInformation
  rw [pointState_marginalA, pointState_marginalB,
    vonNeumannEntropy_pointState, vonNeumannEntropy_pointState,
    vonNeumannEntropy_pointState]
  ring

private theorem quantumMutualInformation_pairState
    (x y : A × B) (hx : x.1 ≠ y.1) (hy : x.2 ≠ y.2) :
    quantumMutualInformation (pairState x y) = -Real.log (1 / 2) := by
  have hxy : x ≠ y := fun h => hx (congrArg Prod.fst h)
  unfold quantumMutualInformation
  rw [pairState_marginalA, pairState_marginalB,
    vonNeumannEntropy_pairState x.1 y.1 hx,
    vonNeumannEntropy_pairState x.2 y.2 hy,
    vonNeumannEntropy_pairState x y hxy]
  ring

private theorem quantumMutualInformation_rectangleState
    (a₀ a₁ : A) (b₀ b₁ : B) (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    quantumMutualInformation (rectangleState a₀ a₁ b₀ b₁) = 0 := by
  unfold quantumMutualInformation
  rw [rectangleState_marginalA, rectangleState_marginalB,
    vonNeumannEntropy_pairState a₀ a₁ ha,
    vonNeumannEntropy_pairState b₀ b₁ hb,
    vonNeumannEntropy_rectangleState a₀ a₁ b₀ b₁ ha hb]
  have hquarter : (1 / 4 : ℝ) = (1 / 2) * (1 / 2) := by norm_num
  rw [hquarter, Real.log_mul (by norm_num) (by norm_num)]
  ring

private theorem pairState_matrix_eq_half_pointStates
    {α : Type*} [Fintype α] [DecidableEq α]
    (x y : α) :
    (pairState x y).matrix =
      ((1 / 2 : ℝ) : ℂ) • (pointState x).matrix +
        ((1 / 2 : ℝ) : ℂ) • (pointState y).matrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [pairState, pointState, diagonalState,
      Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply,
      pairProbability, pointProbability, Pi.add_apply, Complex.ofReal_add]
    by_cases hix : i = x
    · subst i
      by_cases hxy : x = y
      · subst y
        simp
      · simp [hxy]
    · by_cases hiy : i = y
      · subst i
        simp [hix]
      · simp [hix, hiy]
  · simp [pairState, pointState, diagonalState, hij]

private theorem rectangleState_matrix_eq_half_pairStates
    (a₀ a₁ : A) (b₀ b₁ : B) (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    (rectangleState a₀ a₁ b₀ b₁).matrix =
      ((1 / 2 : ℝ) : ℂ) • (pairState (a₀, b₀) (a₁, b₁)).matrix +
        ((1 / 2 : ℝ) : ℂ) • (pairState (a₀, b₁) (a₁, b₀)).matrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [rectangleState, pairState, diagonalState,
      Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply,
      rectangleProbability, pairProbability, Pi.add_apply,
      Complex.ofReal_add]
    by_cases h00 : i = (a₀, b₀)
    · subst i
      simp [ha, hb]
      norm_num
    · by_cases h01 : i = (a₀, b₁)
      · subst i
        simp [ha, hb]
        norm_num
      · by_cases h10 : i = (a₁, b₀)
        · subst i
          simp [ha, hb]
          norm_num
        · by_cases h11 : i = (a₁, b₁)
          · subst i
            simp [ha, hb]
            norm_num
          · simp [h00, h01, h10, h11]
  · simp [rectangleState, pairState, diagonalState, hij]

private theorem vonNeumannEntropy_classicalExtension
    {Y : Type u} {ι : Type w}
    [Fintype Y] [DecidableEq Y] [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (sigma : ι → State Y)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    vonNeumannEntropy (State.classicalExtension p sigma hp hsum) =
      -∑ i, p i * Real.log (p i) +
        ∑ i, p i * vonNeumannEntropy (sigma i) := by
  unfold vonNeumannEntropy
  rw [State.sum_mul_log_eigenvalues_classicalExtension p sigma hp hsum,
    Finset.sum_add_distrib]
  have hneg :
      (∑ i, -(p i * ∑ j,
        (sigma i).pos.isHermitian.eigenvalues j *
          Real.log ((sigma i).pos.isHermitian.eigenvalues j))) =
        -(∑ i, p i * ∑ j,
          (sigma i).pos.isHermitian.eigenvalues j *
            Real.log ((sigma i).pos.isHermitian.eigenvalues j)) := by
    exact
      (Finset.sum_neg_distrib (s := Finset.univ) (fun i =>
        p i * ∑ j, (sigma i).pos.isHermitian.eigenvalues j *
          Real.log ((sigma i).pos.isHermitian.eigenvalues j)))
  simp_rw [mul_neg]
  rw [hneg]
  ring

/-- The internal reduction from finite-dimensional strong subadditivity to
concavity of conditional entropy for finite convex ensembles. -/
private theorem quantumConditionalEntropy_concave_of_strongSubadditivity
    (hstrongSubadditivity :
      VonNeumannEntropyStrongSubadditivity.{u, v, x} (A := A) (B := B))
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho) :
    ∑ i, E.weight i * quantumConditionalEntropy (E.state i) ≤
      quantumConditionalEntropy rho := by
  classical
  let C : Type x := ULift.{x, 0} (Fin (Fintype.card ι))
  let e : ι ≃ C :=
    (Fintype.equivFin ι).trans Equiv.ulift.symm
  let pC : C → ℝ := fun c => E.weight (e.symm c)
  let sigmaC : C → State (A × B) := fun c => E.state (e.symm c)
  have hpC : ∀ c, 0 ≤ pC c := fun c => E.weight_nonneg (e.symm c)
  have hsumC : ∑ c, pC c = 1 := by
    rw [← E.weight_sum_one]
    exact (Fintype.sum_equiv e E.weight pC (fun i => by simp [pC])).symm
  have hrhoC :
      rho.matrix = ∑ c, (pC c : ℂ) • (sigmaC c).matrix := by
    rw [hrho]
    exact Fintype.sum_equiv e
      (fun i => (E.weight i : ℂ) • (E.state i).matrix)
      (fun c => (pC c : ℂ) • (sigmaC c).matrix)
      (fun i => by simp [pC, sigmaC])
  let rhoABCC : State ((A × B) × C) :=
    State.classicalExtension pC sigmaC hpC hsumC
  have hABC_AB : rhoABCC.marginalAB = rho := by
    exact State.classicalExtension_marginalAB_eq_of_matrix_eq
      pC sigmaC rho hpC hsumC hrhoC
  have hABC_B : rhoABCC.marginalBOfABC = rho.marginalB := by
    exact State.classicalExtension_marginalBOfABC_eq_of_matrix_eq
      pC sigmaC rho hpC hsumC hrhoC
  have hABC_BC :
      rhoABCC.marginalBC =
        State.classicalExtension pC
          (fun c => (sigmaC c).marginalB) hpC hsumC := by
    exact State.classicalExtension_marginalBC pC sigmaC hpC hsumC
  have hEntropyABCC :
      vonNeumannEntropy rhoABCC =
        -∑ c, pC c * Real.log (pC c) +
          ∑ c, pC c * vonNeumannEntropy (sigmaC c) := by
    exact vonNeumannEntropy_classicalExtension pC sigmaC hpC hsumC
  have hEntropyBCC :
      vonNeumannEntropy rhoABCC.marginalBC =
        -∑ c, pC c * Real.log (pC c) +
          ∑ c, pC c * vonNeumannEntropy (sigmaC c).marginalB := by
    rw [hABC_BC]
    exact vonNeumannEntropy_classicalExtension pC
      (fun c => (sigmaC c).marginalB) hpC hsumC
  have hShannon :
      (∑ c, pC c * Real.log (pC c)) =
        ∑ i, E.weight i * Real.log (E.weight i) := by
    symm
    exact Fintype.sum_equiv e
      (fun i => E.weight i * Real.log (E.weight i))
      (fun c => pC c * Real.log (pC c))
      (fun i => by simp [pC])
  have hWeightedAB :
      (∑ c, pC c * vonNeumannEntropy (sigmaC c)) =
        ∑ i, E.weight i * vonNeumannEntropy (E.state i) := by
    symm
    exact Fintype.sum_equiv e
      (fun i => E.weight i * vonNeumannEntropy (E.state i))
      (fun c => pC c * vonNeumannEntropy (sigmaC c))
      (fun i => by simp [pC, sigmaC])
  have hWeightedB :
      (∑ c, pC c * vonNeumannEntropy (sigmaC c).marginalB) =
        ∑ i, E.weight i * vonNeumannEntropy (E.state i).marginalB := by
    symm
    exact Fintype.sum_equiv e
      (fun i => E.weight i * vonNeumannEntropy (E.state i).marginalB)
      (fun c => pC c * vonNeumannEntropy (sigmaC c).marginalB)
      (fun i => by simp [pC, sigmaC])
  have hssa := hstrongSubadditivity (C := C) rhoABCC
  rw [hABC_AB, hABC_B, hEntropyABCC, hEntropyBCC,
    hShannon, hWeightedAB, hWeightedB] at hssa
  unfold quantumConditionalEntropy
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  linarith

/-- Concavity of conditional entropy for every finite convex ensemble of
bipartite density states.  This is the unconditional governing entropy fact
supplied by the source problem. -/
theorem quantumConditionalEntropy_concave
    {ι : Type w} [Fintype ι]
    (E : FiniteStateEnsemble ι (A × B)) (rho : State (A × B))
    (hrho : E.IsAverage rho) :
    ∑ i, E.weight i * quantumConditionalEntropy (E.state i) ≤
      quantumConditionalEntropy rho := by
  classical
  by_cases hdegenerate : Subsingleton A ∨ Subsingleton B
  · exact quantumConditionalEntropy_concave_of_subsingleton
      hdegenerate E rho hrho
  · by_cases hmarginal :
        ∀ i, (E.state i).marginalB = rho.marginalB
    · exact quantumConditionalEntropy_concave_of_constant_marginalB
        E rho hrho hmarginal
    · apply
        quantumConditionalEntropy_concave_of_strongSubadditivity.{u, v, w, w}
      · apply
          vonNeumannEntropyStrongSubadditivity_of_posDef_weakMonotonicity.{u, v, w}
        intro C _ _ tau htau
        have hBCR : Nonempty ((B × C) × ((A × B) × C)) :=
          tau.nonempty
        letI : Nonempty (B × C) := nonempty_prod.mp hBCR |>.1
        letI : Nonempty B :=
          nonempty_prod.mp (inferInstance : Nonempty (B × C)) |>.1
        letI : Nonempty C :=
          nonempty_prod.mp (inferInstance : Nonempty (B × C)) |>.2
        letI : Nonempty ((A × B) × C) :=
          nonempty_prod.mp hBCR |>.2
        exact vonNeumannEntropyWeakMonotonicity_posDef tau htau
      · exact hrho

/-- If either subsystem has at most one basis element, quantum mutual
information is both convex and concave.  For a one-dimensional subsystem it is
identically zero; if a subsystem is empty, there are no density states and the
two curvature predicates hold vacuously. -/
theorem quantumMutualInformation_convex_and_concave_of_subsingleton
    (hdegenerate : Subsingleton A ∨ Subsingleton B) :
    ConvexOnDensityStates
        (quantumMutualInformation (A := A) (B := B)) ∧
      ConcaveOnDensityStates
        (quantumMutualInformation (A := A) (B := B)) := by
  rcases hdegenerate with hA | hB
  · letI : Subsingleton A := hA
    constructor
    · intro rho sigma mix t _ _ _
      rw [quantumMutualInformation_eq_zero_of_subsingleton_left rho,
        quantumMutualInformation_eq_zero_of_subsingleton_left sigma,
        quantumMutualInformation_eq_zero_of_subsingleton_left mix]
      norm_num
    · intro rho sigma mix t _ _ _
      rw [quantumMutualInformation_eq_zero_of_subsingleton_left rho,
        quantumMutualInformation_eq_zero_of_subsingleton_left sigma,
        quantumMutualInformation_eq_zero_of_subsingleton_left mix]
      norm_num
  · letI : Subsingleton B := hB
    constructor
    · intro rho sigma mix t _ _ _
      rw [quantumMutualInformation_eq_zero_of_subsingleton_right rho,
        quantumMutualInformation_eq_zero_of_subsingleton_right sigma,
        quantumMutualInformation_eq_zero_of_subsingleton_right mix]
      norm_num
    · intro rho sigma mix t _ _ _
      rw [quantumMutualInformation_eq_zero_of_subsingleton_right rho,
        quantumMutualInformation_eq_zero_of_subsingleton_right sigma,
        quantumMutualInformation_eq_zero_of_subsingleton_right mix]
      norm_num

/-- Quantum mutual information is neither convex nor concave as a function of
the joint density state when both finite subsystems are nontrivial. -/
theorem quantumMutualInformation_neither_convex_nor_concave_of_nontrivial
    [Nontrivial A] [Nontrivial B] :
    ¬ ConvexOnDensityStates
        (quantumMutualInformation (A := A) (B := B)) ∧
      ¬ ConcaveOnDensityStates
        (quantumMutualInformation (A := A) (B := B)) := by
  obtain ⟨a₀, a₁, ha⟩ := exists_pair_ne A
  obtain ⟨b₀, b₁, hb⟩ := exists_pair_ne B
  have hentropyPositive : 0 < -Real.log (1 / 2 : ℝ) :=
    neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  constructor
  · intro hconvex
    have hmix :
        (pairState (a₀, b₀) (a₁, b₁)).matrix =
          (((1 / 2 : ℝ) : ℂ) • (pointState (a₀, b₀)).matrix) +
            ((((1 - (1 / 2 : ℝ)) : ℝ) : ℂ) •
              (pointState (a₁, b₁)).matrix) := by
      convert pairState_matrix_eq_half_pointStates
        (a₀, b₀) (a₁, b₁) using 1
      all_goals norm_num
    have hineq := hconvex
      (pointState (a₀, b₀))
      (pointState (a₁, b₁))
      (pairState (a₀, b₀) (a₁, b₁))
      (1 / 2 : ℝ) (by norm_num) (by norm_num) hmix
    rw [quantumMutualInformation_pointState,
      quantumMutualInformation_pointState,
      quantumMutualInformation_pairState
        (a₀, b₀) (a₁, b₁) ha hb] at hineq
    norm_num at hineq
    linarith
  · intro hconcave
    have hmix :
        (rectangleState a₀ a₁ b₀ b₁).matrix =
          (((1 / 2 : ℝ) : ℂ) •
              (pairState (a₀, b₀) (a₁, b₁)).matrix) +
            ((((1 - (1 / 2 : ℝ)) : ℝ) : ℂ) •
              (pairState (a₀, b₁) (a₁, b₀)).matrix) := by
      convert rectangleState_matrix_eq_half_pairStates
        a₀ a₁ b₀ b₁ ha hb using 1
      all_goals norm_num
    have hineq := hconcave
      (pairState (a₀, b₀) (a₁, b₁))
      (pairState (a₀, b₁) (a₁, b₀))
      (rectangleState a₀ a₁ b₀ b₁)
      (1 / 2 : ℝ) (by norm_num) (by norm_num) hmix
    rw [quantumMutualInformation_pairState
        (a₀, b₀) (a₁, b₁) ha hb,
      quantumMutualInformation_pairState
        (a₀, b₁) (a₁, b₀) ha hb.symm,
      quantumMutualInformation_rectangleState a₀ a₁ b₀ b₁ ha hb] at hineq
    norm_num at hineq
    linarith

/-- Exhaustive curvature classification of quantum mutual information over
arbitrary finite subsystem basis types.

If either subsystem is subsingleton, mutual information is both convex and
concave.  If both are nontrivial, it is neither convex nor concave.  The latter
branch is the usual positive-dimensional answer requested by the source, while
the first branch records the dimension-degenerate cases rather than excluding
them through additional hypotheses. -/
theorem quantumMutualInformation_curvature_classification :
    ((Subsingleton A ∨ Subsingleton B) ∧
      ConvexOnDensityStates
          (quantumMutualInformation (A := A) (B := B)) ∧
      ConcaveOnDensityStates
          (quantumMutualInformation (A := A) (B := B))) ∨
    ((Nontrivial A ∧ Nontrivial B) ∧
      ¬ ConvexOnDensityStates
          (quantumMutualInformation (A := A) (B := B)) ∧
      ¬ ConcaveOnDensityStates
          (quantumMutualInformation (A := A) (B := B))) := by
  classical
  by_cases hdegenerate : Subsingleton A ∨ Subsingleton B
  · left
    exact
      ⟨hdegenerate,
        quantumMutualInformation_convex_and_concave_of_subsingleton hdegenerate⟩
  · right
    have hA : ¬ Subsingleton A := fun h => hdegenerate (Or.inl h)
    have hB : ¬ Subsingleton B := fun h => hdegenerate (Or.inr h)
    letI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    letI : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
    exact
      ⟨⟨inferInstance, inferInstance⟩,
        quantumMutualInformation_neither_convex_nor_concave_of_nontrivial⟩

end

end QITBench.ConvexityQuantumMutualInformation
