import QAlgBench.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Shared-parameter shift rule for `R_X ⊗ R_Z`

This file models two qubits together with an arbitrary finite-dimensional
spectator register.  The parameterized loss remains complex-valued, exactly as
the trace in the source statement; `HasRealDerivativeAt` is consequently the
derivative of a complex-valued curve with respect to a real parameter.
-/

namespace QAlgFormalized.SharedParameterShiftRuleRXTensorRZ

open QAlgBench

noncomputable section

/-- The register `(ℂ² ⊗ ℂ²) ⊗ K`, with the source statement's tensor nesting. -/
abbrev SystemRegister (K : Register) : Register :=
  Register.prod (Register.prod (Qubits 1) (Qubits 1)) K

/--
A density matrix is Hermitian, positive semidefinite, and has trace one.
Positivity is expressed by nonnegativity of the real quadratic form; Hermiticity
ensures that the corresponding complex quadratic form is real.
-/
def IsDensityMatrix {R : Register} (ρ : HilbertOperator R) : Prop :=
  ρ.conjTranspose = ρ ∧
    (∀ ψ : R.Index → ℂ,
      0 ≤ (∑ i, ∑ j, star (ψ i) * ρ i j * ψ j).re) ∧
    Matrix.trace ρ = 1

/-- An observable is a Hermitian operator. -/
def IsObservable {R : Register} (O : HilbertOperator R) : Prop :=
  O.conjTranspose = O

/-- The Pauli matrix `X = [[0, 1], [1, 0]]`, reused from `QAlgBench.Base`. -/
def pauliX : HilbertOperator (Qubits 1) :=
  (QAlgBench.Gate.X : HilbertOperator (Qubits 1))

/-- The Pauli matrix `Z = [[1, 0], [0, -1]]`, reused from `QAlgBench.Base`. -/
def pauliZ : HilbertOperator (Qubits 1) :=
  QAlgBench.Gate.ZOp

/--
The exact closed form
`R_X(θ) = exp (-i X θ / 2) = cos (θ/2) I - i sin (θ/2) X`.
-/
def rotationX (θ : ℝ) : HilbertOperator (Qubits 1) :=
  (Real.cos (θ / 2) : ℂ) • (1 : HilbertOperator (Qubits 1)) -
    (Complex.I * (Real.sin (θ / 2) : ℂ)) • pauliX

/--
The exact closed form
`R_Z(θ) = exp (-i Z θ / 2) = cos (θ/2) I - i sin (θ/2) Z`.
-/
def rotationZ (θ : ℝ) : HilbertOperator (Qubits 1) :=
  (Real.cos (θ / 2) : ℂ) • (1 : HilbertOperator (Qubits 1)) -
    (Complex.I * (Real.sin (θ / 2) : ℂ)) • pauliZ

/--
The shared-parameter circuit
`V(θ) = (R_X(θ) ⊗ R_Z(θ)) ⊗ I_K`.
-/
def sharedRotation (K : Register) (θ : ℝ) : HilbertOperator (SystemRegister K) :=
  Matrix.kronecker
    (Matrix.kronecker (rotationX θ) (rotationZ θ))
    (1 : HilbertOperator K)

/-- The trace loss `ℒ(θ) = Tr[O V(θ) ρ V(θ)†]`. -/
def loss {K : Register}
    (ρ O : HilbertOperator (SystemRegister K)) (θ : ℝ) : ℂ :=
  Matrix.trace
    (O * sharedRotation K θ * ρ * (sharedRotation K θ).conjTranspose)

/--
`f` has derivative `d` at the real parameter `θ`, for a complex-valued curve.
This difference-quotient formulation supplies the calculus carrier that the
plain `QAlgBench.Base` import does not expose.
-/
def HasRealDerivativeAt (f : ℝ → ℂ) (d : ℂ) (θ : ℝ) : Prop :=
  Filter.Tendsto
    (fun h : ℝ => (f (θ + h) - f θ) / (h : ℂ))
    (nhdsWithin 0 ({0}ᶜ))
    (nhds d)

private def trigQuadratic
    (a₀ aC aS aCC aSS aCS : ℂ) (x : ℝ) : ℂ :=
  a₀ +
    aC * (Real.cos x : ℂ) +
    aS * (Real.sin x : ℂ) +
    aCC * (Real.cos x : ℂ) ^ 2 +
    aSS * (Real.sin x : ℂ) ^ 2 +
    aCS * (Real.cos x : ℂ) * (Real.sin x : ℂ)

private def trigQuadraticDerivative
    (aC aS aCC aSS aCS : ℂ) (x : ℝ) : ℂ :=
  -aC * (Real.sin x : ℂ) +
    aS * (Real.cos x : ℂ) -
    2 * aCC * (Real.cos x : ℂ) * (Real.sin x : ℂ) +
    2 * aSS * (Real.sin x : ℂ) * (Real.cos x : ℂ) +
    aCS * ((Real.cos x : ℂ) ^ 2 - (Real.sin x : ℂ) ^ 2)

private lemma trigQuadratic_hasDerivAt
    (a₀ aC aS aCC aSS aCS : ℂ) (x : ℝ) :
    HasDerivAt
      (trigQuadratic a₀ aC aS aCC aSS aCS)
      (trigQuadraticDerivative aC aS aCC aSS aCS x)
      x := by
  have hcos :
      HasDerivAt (fun y : ℝ => (Real.cos y : ℂ)) (-(Real.sin x : ℝ) : ℂ) x := by
    simpa using (Real.hasDerivAt_cos x).ofReal_comp
  have hsin :
      HasDerivAt (fun y : ℝ => (Real.sin y : ℂ)) (Real.cos x : ℂ) x := by
    simpa using (Real.hasDerivAt_sin x).ofReal_comp
  unfold trigQuadratic trigQuadraticDerivative
  convert
    (((((hasDerivAt_const x a₀).add (hcos.const_mul aC)).add
        (hsin.const_mul aS)).add
        ((hcos.mul hcos).const_mul aCC)).add
        ((hsin.mul hsin).const_mul aSS)).add
        ((hcos.mul hsin).const_mul aCS) using 1 <;> try rfl
  all_goals try { funext y; dsimp; ring }
  all_goals ring

private lemma trigQuadratic_shift
    (a₀ aC aS aCC aSS aCS : ℂ) (x : ℝ) :
    trigQuadraticDerivative aC aS aCC aSS aCS x =
      ((((2 + Real.sqrt 2) / 4 : ℝ) : ℂ) *
          (trigQuadratic a₀ aC aS aCC aSS aCS (x + Real.pi / 4) -
            trigQuadratic a₀ aC aS aCC aSS aCS (x - Real.pi / 4)) +
        (((2 - Real.sqrt 2) / 4 : ℝ) : ℂ) *
          (trigQuadratic a₀ aC aS aCC aSS aCS (x - 3 * Real.pi / 4) -
            trigQuadratic a₀ aC aS aCC aSS aCS (x + 3 * Real.pi / 4))) := by
  have hthree : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrt' : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast hsqrt
  simp only [trigQuadratic, trigQuadraticDerivative, Real.cos_add, Real.cos_sub,
    Real.sin_add, Real.sin_sub, hthree]
  simp only [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_four, Real.sin_pi_div_four,
    neg_mul, zero_mul, one_mul]
  push_cast
  ring_nf
  rw [hsqrt']
  ring

private lemma HasDerivAt.hasRealDerivativeAt
    {f : ℝ → ℂ} {d : ℂ} {x : ℝ} (h : HasDerivAt f d x) :
    HasRealDerivativeAt f d x := by
  unfold HasRealDerivativeAt
  simpa only [div_eq_mul_inv, Complex.ofReal_inv, mul_comm, Complex.real_smul] using
    h.tendsto_slope_zero

private abbrev TwoQubitMatrix :=
  Matrix ((Qubits 1).Index × (Qubits 1).Index)
    ((Qubits 1).Index × (Qubits 1).Index) ℂ

private def innerConstantComponent : TwoQubitMatrix :=
  (1 / 2 : ℂ) •
    (Matrix.kronecker
        (1 : HilbertOperator (Qubits 1)) (1 : HilbertOperator (Qubits 1)) -
      Matrix.kronecker pauliX pauliZ)

private def innerCosComponent : TwoQubitMatrix :=
  (1 / 2 : ℂ) •
    (Matrix.kronecker
        (1 : HilbertOperator (Qubits 1)) (1 : HilbertOperator (Qubits 1)) +
      Matrix.kronecker pauliX pauliZ)

private def innerSinComponent : TwoQubitMatrix :=
  (-Complex.I / 2 : ℂ) •
    (Matrix.kronecker (1 : HilbertOperator (Qubits 1)) pauliZ +
      Matrix.kronecker pauliX (1 : HilbertOperator (Qubits 1)))

private def innerConstantOperator :
    HilbertOperator (Register.prod (Qubits 1) (Qubits 1)) :=
  innerConstantComponent

private def innerCosOperator :
    HilbertOperator (Register.prod (Qubits 1) (Qubits 1)) :=
  innerCosComponent

private def innerSinOperator :
    HilbertOperator (Register.prod (Qubits 1) (Qubits 1)) :=
  innerSinComponent

private abbrev SystemMatrix (K : Register) :=
  Matrix ((Register.prod (Qubits 1) (Qubits 1)).Index × K.Index)
    ((Register.prod (Qubits 1) (Qubits 1)).Index × K.Index) ℂ

private def sharedConstantMatrix (K : Register) : SystemMatrix K :=
  Matrix.kronecker innerConstantOperator (1 : HilbertOperator K)

private def sharedCosMatrix (K : Register) : SystemMatrix K :=
  Matrix.kronecker innerCosOperator (1 : HilbertOperator K)

private def sharedSinMatrix (K : Register) : SystemMatrix K :=
  Matrix.kronecker innerSinOperator (1 : HilbertOperator K)

private def sharedConstantComponent (K : Register) :
    HilbertOperator (SystemRegister K) :=
  sharedConstantMatrix K

private def sharedCosComponent (K : Register) :
    HilbertOperator (SystemRegister K) :=
  sharedCosMatrix K

private def sharedSinComponent (K : Register) :
    HilbertOperator (SystemRegister K) :=
  sharedSinMatrix K

private lemma innerRotation_decomposition (x : ℝ) :
    Matrix.kronecker (rotationX x) (rotationZ x) =
      innerConstantComponent +
        (Real.cos x : ℂ) • innerCosComponent +
        (Real.sin x : ℂ) • innerSinComponent := by
  have hcos :
      Real.cos (x / 2) ^ 2 = (1 + Real.cos x) / 2 := by
    have h := Real.cos_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    linarith
  have hsin :
      Real.sin (x / 2) ^ 2 = (1 - Real.cos x) / 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have hsincos :
      Real.sin (x / 2) * Real.cos (x / 2) = Real.sin x / 2 := by
    have h := Real.sin_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    linarith
  have hcos' :
      (Real.cos (x / 2) : ℂ) ^ 2 = (((1 + Real.cos x) / 2 : ℝ) : ℂ) := by
    exact_mod_cast hcos
  have hsin' :
      (Real.sin (x / 2) : ℂ) ^ 2 = (((1 - Real.cos x) / 2 : ℝ) : ℂ) := by
    exact_mod_cast hsin
  have hsincos' :
      (Real.sin (x / 2) : ℂ) * (Real.cos (x / 2) : ℂ) =
        ((Real.sin x / 2 : ℝ) : ℂ) := by
    exact_mod_cast hsincos
  change
    (Matrix.kronecker (rotationX x) (rotationZ x) :
      Matrix ((Qubits 1).Index × (Qubits 1).Index)
        ((Qubits 1).Index × (Qubits 1).Index) ℂ) =
      (innerConstantComponent +
        (Real.cos x : ℂ) • innerCosComponent +
        (Real.sin x : ℂ) • innerSinComponent :
      Matrix ((Qubits 1).Index × (Qubits 1).Index)
        ((Qubits 1).Index × (Qubits 1).Index) ℂ)
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [rotationX, rotationZ, innerConstantComponent, innerCosComponent,
    innerSinComponent, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  ring_nf
  ring_nf at hcos' hsin' hsincos'
  rw [hcos', hsin']
  have hcross₁ (z₁ z₂ : ℂ) :
      (Real.cos (x * (1 / 2)) : ℂ) * z₁ *
          (Real.sin (x * (1 / 2)) : ℂ) * z₂ =
        ((Real.sin x * (1 / 2) : ℝ) : ℂ) * z₁ * z₂ := by
    calc
      _ = ((Real.cos (x * (1 / 2)) : ℂ) *
          (Real.sin (x * (1 / 2)) : ℂ)) * z₁ * z₂ := by ring
      _ = _ := by rw [hsincos']
  have hcross₂ (z₁ z₂ z₃ : ℂ) :
      (Real.cos (x * (1 / 2)) : ℂ) * z₁ * z₂ *
          (Real.sin (x * (1 / 2)) : ℂ) * z₃ =
        ((Real.sin x * (1 / 2) : ℝ) : ℂ) * z₁ * z₂ * z₃ := by
    calc
      _ = ((Real.cos (x * (1 / 2)) : ℂ) *
          (Real.sin (x * (1 / 2)) : ℂ)) * z₁ * z₂ * z₃ := by ring
      _ = _ := by rw [hsincos']
  rw [hcross₂, hcross₁]
  rw [Complex.I_sq]
  push_cast
  ring

private lemma innerRotation_decomposition_operator (x : ℝ) :
    (Matrix.kronecker (rotationX x) (rotationZ x) :
      HilbertOperator (Register.prod (Qubits 1) (Qubits 1))) =
      innerConstantOperator +
        (Real.cos x : ℂ) • innerCosOperator +
        (Real.sin x : ℂ) • innerSinOperator := by
  exact innerRotation_decomposition x

private lemma sharedRotation_decomposition_matrix (K : Register) (x : ℝ) :
    Matrix.kronecker
        (Matrix.kronecker (rotationX x) (rotationZ x) :
          HilbertOperator (Register.prod (Qubits 1) (Qubits 1)))
        (1 : HilbertOperator K) =
      sharedConstantMatrix K +
        (Real.cos x : ℂ) • sharedCosMatrix K +
        (Real.sin x : ℂ) • sharedSinMatrix K := by
  unfold sharedConstantMatrix sharedCosMatrix sharedSinMatrix
  rw [innerRotation_decomposition_operator]
  unfold Matrix.kronecker
  ext i j
  simp only [Matrix.kroneckerMap_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

private lemma sharedRotation_decomposition (K : Register) (x : ℝ) :
    sharedRotation K x =
      sharedConstantComponent K +
        (Real.cos x : ℂ) • sharedCosComponent K +
        (Real.sin x : ℂ) • sharedSinComponent K := by
  exact sharedRotation_decomposition_matrix K x

private def traceCoefficient {K : Register}
    (ρ O A B : HilbertOperator (SystemRegister K)) : ℂ :=
  Matrix.trace (O * A * ρ * B.conjTranspose)

private lemma traceCoefficient_add_left {K : Register}
    (ρ O A B C : HilbertOperator (SystemRegister K)) :
    traceCoefficient ρ O (A + B) C =
      traceCoefficient ρ O A C + traceCoefficient ρ O B C := by
  simp only [traceCoefficient, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]

private lemma traceCoefficient_add_right {K : Register}
    (ρ O A B C : HilbertOperator (SystemRegister K)) :
    traceCoefficient ρ O A (B + C) =
      traceCoefficient ρ O A B + traceCoefficient ρ O A C := by
  simp only [traceCoefficient, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.trace_add]

private lemma traceCoefficient_smul_left {K : Register}
    (ρ O A B : HilbertOperator (SystemRegister K)) (z : ℂ) :
    traceCoefficient ρ O (z • A) B = z * traceCoefficient ρ O A B := by
  simp only [traceCoefficient, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul]

private lemma traceCoefficient_smul_right {K : Register}
    (ρ O A B : HilbertOperator (SystemRegister K)) (z : ℂ) :
    traceCoefficient ρ O A (z • B) = star z * traceCoefficient ρ O A B := by
  simp only [traceCoefficient, Matrix.conjTranspose_smul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]

private lemma loss_eq_trigQuadratic {K : Register}
    (ρ O : HilbertOperator (SystemRegister K)) (x : ℝ) :
    loss ρ O x =
      trigQuadratic
        (traceCoefficient ρ O
          (sharedConstantComponent K) (sharedConstantComponent K))
        (traceCoefficient ρ O
            (sharedCosComponent K) (sharedConstantComponent K) +
          traceCoefficient ρ O
            (sharedConstantComponent K) (sharedCosComponent K))
        (traceCoefficient ρ O
            (sharedSinComponent K) (sharedConstantComponent K) +
          traceCoefficient ρ O
            (sharedConstantComponent K) (sharedSinComponent K))
        (traceCoefficient ρ O
          (sharedCosComponent K) (sharedCosComponent K))
        (traceCoefficient ρ O
          (sharedSinComponent K) (sharedSinComponent K))
        (traceCoefficient ρ O
            (sharedCosComponent K) (sharedSinComponent K) +
          traceCoefficient ρ O
            (sharedSinComponent K) (sharedCosComponent K))
        x := by
  change traceCoefficient ρ O (sharedRotation K x) (sharedRotation K x) = _
  rw [sharedRotation_decomposition]
  simp only [traceCoefficient_add_left, traceCoefficient_add_right,
    traceCoefficient_smul_left, traceCoefficient_smul_right]
  simp only [RCLike.star_def, Complex.conj_ofReal]
  unfold trigQuadratic
  ring

/--
The four-evaluation parameter-shift identity for the angle shared by the
`R_X` and `R_Z` factors.
-/
theorem sharedParameterShiftRule
    (K : Register)
    (ρ O : HilbertOperator (SystemRegister K))
    (hρ : IsDensityMatrix ρ)
    (hO : IsObservable O)
    (θ : ℝ) :
    HasRealDerivativeAt
      (loss ρ O)
      ((((2 + Real.sqrt 2) / 4 : ℝ) : ℂ) *
          (loss ρ O (θ + Real.pi / 4) -
            loss ρ O (θ - Real.pi / 4)) +
        (((2 - Real.sqrt 2) / 4 : ℝ) : ℂ) *
          (loss ρ O (θ - 3 * Real.pi / 4) -
            loss ρ O (θ + 3 * Real.pi / 4)))
      θ := by
  let a₀ : ℂ :=
    traceCoefficient ρ O
      (sharedConstantComponent K) (sharedConstantComponent K)
  let aC : ℂ :=
    traceCoefficient ρ O
        (sharedCosComponent K) (sharedConstantComponent K) +
      traceCoefficient ρ O
        (sharedConstantComponent K) (sharedCosComponent K)
  let aS : ℂ :=
    traceCoefficient ρ O
        (sharedSinComponent K) (sharedConstantComponent K) +
      traceCoefficient ρ O
        (sharedConstantComponent K) (sharedSinComponent K)
  let aCC : ℂ :=
    traceCoefficient ρ O
      (sharedCosComponent K) (sharedCosComponent K)
  let aSS : ℂ :=
    traceCoefficient ρ O
      (sharedSinComponent K) (sharedSinComponent K)
  let aCS : ℂ :=
    traceCoefficient ρ O
        (sharedCosComponent K) (sharedSinComponent K) +
      traceCoefficient ρ O
        (sharedSinComponent K) (sharedCosComponent K)
  have hloss :
      loss ρ O = trigQuadratic a₀ aC aS aCC aSS aCS := by
    funext x
    simpa [a₀, aC, aS, aCC, aSS, aCS] using
      loss_eq_trigQuadratic ρ O x
  have hderiv :=
    trigQuadratic_hasDerivAt a₀ aC aS aCC aSS aCS θ
  have hshift :=
    trigQuadratic_shift a₀ aC aS aCC aSS aCS θ
  rw [← hloss] at hderiv hshift
  rw [hshift] at hderiv
  exact HasDerivAt.hasRealDerivativeAt hderiv

end

end QAlgFormalized.SharedParameterShiftRuleRXTensorRZ
