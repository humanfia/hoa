import QAlgBench.Base

/-!
# Postselected spectral transformation by trigonometric QSP

This file formalizes the source convention that matrix products are written
from left to right:

`A_{2L} R_z(x) A_{2L-1} ... R_z(x) A_0`.

The controlled sequence uses `C₁(U)` at odd signal positions and
`C₀(U†)` at even signal positions, where positions are counted from the
left starting at one.
-/

namespace QAlgFormalized
namespace PostselectedSpectralTransformationTrigonometricQSP

open scoped BigOperators
open QAlgBench

noncomputable section

/-- The rank-one operator `|ψ⟩⟨φ|`. -/
def ketBra {R : Register} (ψ φ : StateVector R) : HilbertOperator R :=
  fun i j => ψ i * starRingEnd ℂ (φ j)

/-- The displayed spectral sum
`∑ j, exp(i x_j) |ψ_j⟩⟨ψ_j|`. -/
def spectralSum {n : Nat}
    (phases : Fin (2 ^ n) → ℝ)
    (eigenbasis : OrthonormalBasis (Fin (2 ^ n)) ℂ (StateVector (Qubits n))) :
    HilbertOperator (Qubits n) :=
  ∑ j, Complex.exp ((phases j : ℂ) * Complex.I) •
    ketBra (eigenbasis j) (eigenbasis j)

/-- The Laurent/trigonometric polynomial
`P(x) = ∑_{m=-L}^L c_m exp(i m x)`. -/
def trigonometricPolynomial (L : Nat) (coeff : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
    coeff m * Complex.exp ((m : ℂ) * (x : ℂ) * Complex.I)

/-- The source processing gate
`A_ℓ = R_y(θ_ℓ) R_z(φ_ℓ)`. -/
def processingGate {L : Nat}
    (theta phi : Fin (2 * L + 1) → ℝ) (ell : Fin (2 * L + 1)) :
    Gate (Qubits 1) :=
  rotY (theta ell) * rotZStd (phi ell)

/-- Interleave a list of rotations with signals numbered from `position`.
For `[A₂, A₁, A₀]` and initial position one, this is
`A₂ * signal 1 * A₁ * signal 2 * A₀`. -/
def interleavedProduct {R : Register} (signal : Nat → Gate R) :
    List (Gate R) → Nat → Gate R
  | [], _ => 1
  | [gate], _ => gate
  | gate :: next :: tail, position =>
      gate * signal position *
        interleavedProduct signal (next :: tail) (position + 1)
termination_by gates _ => gates.length

/-- The one-qubit trigonometric-QSP product in the exact source order
`A_{2L} R_z(x) A_{2L-1} ... R_z(x) A_0`. -/
def oneQubitQSPSequence (L : Nat)
    (theta phi : Fin (2 * L + 1) → ℝ) (x : ℝ) : Gate (Qubits 1) :=
  interleavedProduct
    (fun _ => rotZStd x)
    (List.ofFn (processingGate theta phi) |>.reverse)
    1

/-- The source convention for integer powers of a unitary:
nonnegative powers use `U`, while
`U^m = (U†)^(-m)` for negative `m`. -/
def unitaryLaurentPower {n : Nat} (U : Gate (Qubits n)) :
    ℤ → HilbertOperator (Qubits n)
  | .ofNat k => (U : HilbertOperator (Qubits n)) ^ k
  | .negSucc k =>
      (U.conjTranspose : HilbertOperator (Qubits n)) ^ (k + 1)

/-- The Laurent-operator expression `∑_{m=-L}^L c_m U^m`. -/
def laurentPolynomialOperator {n : Nat}
    (L : Nat) (coeff : ℤ → ℂ) (U : Gate (Qubits n)) :
    HilbertOperator (Qubits n) :=
  ∑ m ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
    coeff m • unitaryLaurentPower U m

/-- Spectral functional calculus for `P(U)` using the supplied phase-labelled
orthonormal eigenbasis. -/
def spectralPolynomialOperator {n : Nat}
    (L : Nat) (coeff : ℤ → ℂ)
    (phases : Fin (2 ^ n) → ℝ)
    (eigenbasis : OrthonormalBasis (Fin (2 ^ n)) ℂ (StateVector (Qubits n))) :
    HilbertOperator (Qubits n) :=
  ∑ j, trigonometricPolynomial L coeff (phases j) •
    ketBra (eigenbasis j) (eigenbasis j)

/-- Lift the same one-qubit processing gate to the control qubit of the
control-system register. -/
def liftedProcessingGate {L n : Nat}
    (theta phi : Fin (2 * L + 1) → ℝ) (ell : Fin (2 * L + 1)) :
    Gate (Qubits (1 + n)) :=
  Gate.tensor (processingGate theta phi ell) (1 : Gate (Qubits n))

/-- The replacement for the signal gate at a position counted from the left:
`C₁(U)` at odd positions and `C₀(U†)` at even positions. -/
def controlledSpectralSignal {n : Nat} (U : Gate (Qubits n))
    (position : Nat) : Gate (Qubits (1 + n)) :=
  if position % 2 = 1 then
    Gate.controlled U
  else
    Gate.controlledOnZero U.conjTranspose

/-- The controlled spectral circuit `𝓦_U`, with exactly the rotations and
left-to-right replacement order prescribed in the source. -/
def controlledSpectralCircuit {n : Nat}
    (L : Nat) (U : Gate (Qubits n))
    (theta phi : Fin (2 * L + 1) → ℝ) : Gate (Qubits (1 + n)) :=
  interleavedProduct
    (controlledSpectralSignal U)
    (List.ofFn (liftedProcessingGate (n := n) theta phi) |>.reverse)
    1

/-- Normalize a nonzero raw state vector.  The theorem below supplies the
source's nonzero side condition before using this expression. -/
def normalizedVector {R : Register} (ψ : StateVector R) : StateVector R :=
  ((‖ψ‖ : ℂ)⁻¹) • ψ

/-- The unnormalized system branch obtained by preparing the control in
`|0⟩`, running `W`, and projecting the control back onto `⟨0|`. -/
def controlZeroBranch {n : Nat}
    (W : Gate (Qubits (1 + n))) (ψ : StateVector (Qubits n)) :
    StateVector (Qubits n) :=
  HilbertOperator.applyVec
    (projectedBlock 1 n (W : HilbertOperator (Qubits (1 + n)))) ψ

private lemma ketBra_applyVec {R : Register}
    (v w ψ : StateVector R) :
    HilbertOperator.applyVec (ketBra v w) ψ = (inner ℂ w ψ) • v := by
  ext i
  simp only [ketBra, HilbertOperator.applyVec_apply, PiLp.inner_apply,
    RCLike.inner_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma spectralSum_applyVec_basis {n : Nat}
    (phases : Fin (2 ^ n) → ℝ)
    (eigenbasis : OrthonormalBasis (Fin (2 ^ n)) ℂ (StateVector (Qubits n)))
    (j : Fin (2 ^ n)) :
    HilbertOperator.applyVec (spectralSum phases eigenbasis) (eigenbasis j) =
      Complex.exp ((phases j : ℂ) * Complex.I) • eigenbasis j := by
  rw [spectralSum, HilbertOperator.sum_applyVec]
  simp only [HilbertOperator.smul_applyVec, ketBra_applyVec]
  have horth := orthonormal_iff_ite.mp eigenbasis.orthonormal
  simp [horth]

private lemma spectralPolynomialOperator_applyVec_basis {L n : Nat}
    (coeff : ℤ → ℂ) (phases : Fin (2 ^ n) → ℝ)
    (eigenbasis : OrthonormalBasis (Fin (2 ^ n)) ℂ (StateVector (Qubits n)))
    (j : Fin (2 ^ n)) :
    HilbertOperator.applyVec
        (spectralPolynomialOperator L coeff phases eigenbasis) (eigenbasis j) =
      trigonometricPolynomial L coeff (phases j) • eigenbasis j := by
  rw [spectralPolynomialOperator, HilbertOperator.sum_applyVec]
  simp only [HilbertOperator.smul_applyVec, ketBra_applyVec]
  have horth := orthonormal_iff_ite.mp eigenbasis.orthonormal
  simp [horth]

private lemma gate_conjTranspose_applyVec_eigen {n : Nat}
    (U : Gate (Qubits n)) (x : ℝ) (v : StateVector (Qubits n))
    (heig :
      U.applyVec v = Complex.exp ((x : ℂ) * Complex.I) • v) :
    U.conjTranspose.applyVec v =
      Complex.exp ((-x : ℝ) * Complex.I) • v := by
  have h := Gate.conjTranspose_applyVec_applyVec U v
  rw [heig, Gate.applyVec_smul] at h
  calc
    U.conjTranspose.applyVec v =
        1 • U.conjTranspose.applyVec v := by simp
    _ = (Complex.exp (-((x : ℂ) * Complex.I)) *
          Complex.exp ((x : ℂ) * Complex.I)) •
          U.conjTranspose.applyVec v := by
        simp [exp_neg_I_mul_exp_I]
    _ = Complex.exp (-((x : ℂ) * Complex.I)) •
          (Complex.exp ((x : ℂ) * Complex.I) •
            U.conjTranspose.applyVec v) := by
        rw [smul_smul]
    _ = Complex.exp (-((x : ℂ) * Complex.I)) • v := by rw [h]
    _ = Complex.exp ((-x : ℝ) * Complex.I) • v := by
        congr 2 <;> push_cast <;> ring

private def effectiveSignal (x : ℝ) (position : Nat) : Gate (Qubits 1) :=
  if position % 2 = 1 then phaseGate x else phaseGateOnZero (-x)

private def signalPhase (x : ℝ) (position : Nat) : ℂ :=
  if position % 2 = 1 then
    Complex.exp ((x / 2 : ℝ) * Complex.I)
  else
    Complex.exp (-(x / 2 : ℝ) * Complex.I)

private def signalPhaseProduct (x : ℝ) : Nat → Nat → ℂ
  | _, 0 => 1
  | position, count + 1 =>
      signalPhase x position * signalPhaseProduct x (position + 1) count

private lemma controlled_applyVec_tensor_eigen {n : Nat}
    (U : Gate (Qubits n)) (x : ℝ) (v : StateVector (Qubits n))
    (heig :
      U.applyVec v = Complex.exp ((x : ℂ) * Complex.I) • v)
    (control : StateVector (Qubits 1)) :
    (Gate.controlled U).applyVec (StateVector.tensor control v) =
      StateVector.tensor ((phaseGate x).applyVec control) v := by
  change HilbertOperator.applyVec
      (Gate.controlled U : HilbertOperator (Qubits (1 + n)))
      (StateVector.tensor control v) = _
  rw [single_qubit_vec_decomp control, StateVector.add_tensor,
    StateVector.smul_tensor, StateVector.smul_tensor,
    HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul,
    Gate.controlled_applyVec_ket0_tensor,
    Gate.controlled_applyVec_ket1_tensor, heig,
    StateVector.tensor_smul, smul_smul, phaseGate_applyVec,
    StateVector.add_tensor, StateVector.smul_tensor, StateVector.smul_tensor]
  congr 1 <;>
    simp [PureState.ket0, PureState.ket1, PureState.ket_apply,
      PiLp.add_apply, PiLp.smul_apply, mul_comm]

private lemma controlledOnZero_applyVec_tensor_eigen {n : Nat}
    (U : Gate (Qubits n)) (x : ℝ) (v : StateVector (Qubits n))
    (heig :
      U.applyVec v = Complex.exp ((x : ℂ) * Complex.I) • v)
    (control : StateVector (Qubits 1)) :
    (Gate.controlledOnZero U).applyVec (StateVector.tensor control v) =
      StateVector.tensor ((phaseGateOnZero x).applyVec control) v := by
  change HilbertOperator.applyVec
      (Gate.controlledOnZero U : HilbertOperator (Qubits (1 + n)))
      (StateVector.tensor control v) = _
  rw [single_qubit_vec_decomp control, StateVector.add_tensor,
    StateVector.smul_tensor, StateVector.smul_tensor,
    HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul,
    Gate.controlledOnZero_applyVec_ket0_tensor,
    Gate.controlledOnZero_applyVec_ket1_tensor, heig,
    StateVector.tensor_smul, smul_smul, phaseGateOnZero_applyVec,
    StateVector.add_tensor, StateVector.smul_tensor, StateVector.smul_tensor]
  congr 1 <;>
    simp [PureState.ket0, PureState.ket1, PureState.ket_apply,
      PiLp.add_apply, PiLp.smul_apply, mul_comm]

private lemma controlledSpectralSignal_applyVec_eigen {n : Nat}
    (U : Gate (Qubits n)) (x : ℝ) (v : StateVector (Qubits n))
    (heig :
      U.applyVec v = Complex.exp ((x : ℂ) * Complex.I) • v)
    (heigAdj :
      U.conjTranspose.applyVec v =
        Complex.exp ((-x : ℝ) * Complex.I) • v)
    (position : Nat) (control : StateVector (Qubits 1)) :
    (controlledSpectralSignal U position).applyVec
        (StateVector.tensor control v) =
      StateVector.tensor ((effectiveSignal x position).applyVec control) v := by
  unfold controlledSpectralSignal effectiveSignal
  split
  · exact controlled_applyVec_tensor_eigen U x v heig control
  · exact controlledOnZero_applyVec_tensor_eigen
      U.conjTranspose (-x) v (by simpa using heigAdj) control

private lemma interleavedProduct_lifted_applyVec_eigen {n : Nat}
    (U : Gate (Qubits n)) (x : ℝ) (v : StateVector (Qubits n))
    (heig :
      U.applyVec v = Complex.exp ((x : ℂ) * Complex.I) • v)
    (heigAdj :
      U.conjTranspose.applyVec v =
        Complex.exp ((-x : ℝ) * Complex.I) • v)
    (gates : List (Gate (Qubits 1))) (position : Nat)
    (control : StateVector (Qubits 1)) :
    (interleavedProduct (controlledSpectralSignal U)
        (gates.map (fun gate => Gate.tensor gate (1 : Gate (Qubits n))))
        position).applyVec (StateVector.tensor control v) =
      StateVector.tensor
        ((interleavedProduct (effectiveSignal x) gates position).applyVec
          control) v := by
  induction gates generalizing position control with
  | nil => simp [interleavedProduct, Gate.one_applyVec]
  | cons gate tail ih =>
      cases tail with
      | nil =>
          simp [interleavedProduct, Gate.tensor_applyVec_tensor,
            Gate.one_applyVec]
      | cons next tail =>
          simp only [List.map_cons, interleavedProduct, Gate.mul_applyVec]
          have hrec := ih (position + 1) control
          simp only [List.map_cons] at hrec
          rw [hrec,
            controlledSpectralSignal_applyVec_eigen U x v heig heigAdj,
            Gate.tensor_applyVec_tensor, Gate.one_applyVec]

private lemma effectiveSignal_applyVec
    (x : ℝ) (position : Nat) (v : StateVector (Qubits 1)) :
    (effectiveSignal x position).applyVec v =
      signalPhase x position • (rotZStd x).applyVec v := by
  unfold effectiveSignal signalPhase
  split
  · exact phaseGate_applyVec_eq_smul_rotZStd x v
  · exact phaseGateOnZero_applyVec_eq_smul_rotZStd x v

private lemma interleavedProduct_effective_applyVec
    (x : ℝ) (gates : List (Gate (Qubits 1))) (position : Nat)
    (v : StateVector (Qubits 1)) :
    (interleavedProduct (effectiveSignal x) gates position).applyVec v =
      signalPhaseProduct x position (gates.length - 1) •
        (interleavedProduct (fun _ => rotZStd x) gates position).applyVec v := by
  induction gates generalizing position v with
  | nil => simp [interleavedProduct, signalPhaseProduct, Gate.one_applyVec]
  | cons gate tail ih =>
      cases tail with
      | nil => simp [interleavedProduct, signalPhaseProduct]
      | cons next tail =>
          simp only [interleavedProduct, Gate.mul_applyVec]
          rw [ih, Gate.applyVec_smul, effectiveSignal_applyVec,
            Gate.applyVec_smul]
          simp only [List.length_cons, Nat.add_sub_cancel, signalPhaseProduct]
          rw [Gate.applyVec_smul, mul_comm, smul_smul]

private lemma signalPhase_add_two (x : ℝ) (position : Nat) :
    signalPhase x (position + 2) = signalPhase x position := by
  unfold signalPhase
  have hmod : (position + 2) % 2 = position % 2 := by omega
  rw [hmod]

private lemma signalPhaseProduct_add_two
    (x : ℝ) (position count : Nat) :
    signalPhaseProduct x (position + 2) count =
      signalPhaseProduct x position count := by
  induction count generalizing position with
  | zero => rfl
  | succ count ih =>
      simp only [signalPhaseProduct, signalPhase_add_two]
      rw [show position + 2 + 1 = (position + 1) + 2 by omega, ih]

private lemma signalPhaseProduct_even (x : ℝ) (L : Nat) :
    signalPhaseProduct x 1 (2 * L) = 1 := by
  induction L with
  | zero => simp [signalPhaseProduct]
  | succ L ih =>
      rw [Nat.mul_succ]
      simp only [signalPhaseProduct]
      rw [signalPhaseProduct_add_two x 1 (2 * L), ih]
      simp [signalPhase, ← Complex.exp_add]

private lemma controlledSpectralCircuit_applyVec_eigen {L n : Nat}
    (U : Gate (Qubits n))
    (theta phi : Fin (2 * L + 1) → ℝ)
    (x : ℝ) (v : StateVector (Qubits n))
    (heig :
      U.applyVec v = Complex.exp ((x : ℂ) * Complex.I) • v)
    (control : StateVector (Qubits 1)) :
    (controlledSpectralCircuit L U theta phi).applyVec
        (StateVector.tensor control v) =
      StateVector.tensor
        ((oneQubitQSPSequence L theta phi x).applyVec control) v := by
  let gates := (List.ofFn (processingGate theta phi)).reverse
  have hlift :
      (List.ofFn (liftedProcessingGate (n := n) theta phi)).reverse =
        gates.map (fun gate => Gate.tensor gate (1 : Gate (Qubits n))) := by
    dsimp [gates]
    rw [List.map_reverse, List.map_ofFn]
    rfl
  rw [controlledSpectralCircuit, hlift]
  rw [interleavedProduct_lifted_applyVec_eigen U x v heig
    (gate_conjTranspose_applyVec_eigen U x v heig)]
  rw [interleavedProduct_effective_applyVec]
  have hlen : gates.length - 1 = 2 * L := by simp [gates]
  rw [hlen, signalPhaseProduct_even]
  simp [oneQubitQSPSequence, gates]

private lemma projectedBlock_applyVec_apply (n : Nat)
    (W : HilbertOperator (Qubits (1 + n))) (v : StateVector (Qubits n))
    (i : Fin (2 ^ n)) :
    HilbertOperator.applyVec (projectedBlock 1 n W) v i =
      HilbertOperator.applyVec W
        (StateVector.tensor (PureState.ket0 : StateVector (Qubits 1)) v)
        (prodEquiv ((0 : Fin (2 ^ 1)), i)) := by
  rw [HilbertOperator.applyVec_apply, HilbertOperator.applyVec_apply]
  change (∑ j, W (prodEquiv (0, i)) (prodEquiv (0, j)) * v j) = _
  rw [← Equiv.sum_comp (prodEquiv (m := 1) (n := n))
      (fun j => W (prodEquiv (0, i)) j *
        StateVector.tensor (PureState.ket0 : StateVector (Qubits 1)) v j),
    Fintype.sum_prod_type]
  simp [PureState.ket0, PureState.ket_apply]

private lemma pow_applyVec_eigen {R : Register}
    (A : HilbertOperator R) (lambda : ℂ) (v : StateVector R)
    (heig : HilbertOperator.applyVec A v = lambda • v) (k : Nat) :
    HilbertOperator.applyVec (A ^ k) v = lambda ^ k • v := by
  induction k with
  | zero => simp [HilbertOperator.one_applyVec]
  | succ k ih =>
      rw [pow_succ, HilbertOperator.mul_applyVec, heig,
        HilbertOperator.applyVec_smul, ih, smul_smul]
      simp [pow_succ, mul_comm]

private lemma unitaryLaurentPower_applyVec_eigen {n : Nat}
    (U : Gate (Qubits n)) (x : ℝ) (v : StateVector (Qubits n))
    (heig :
      U.applyVec v = Complex.exp ((x : ℂ) * Complex.I) • v)
    (heigAdj :
      U.conjTranspose.applyVec v =
        Complex.exp ((-x : ℝ) * Complex.I) • v)
    (m : ℤ) :
    HilbertOperator.applyVec (unitaryLaurentPower U m) v =
      Complex.exp ((m : ℂ) * (x : ℂ) * Complex.I) • v := by
  cases m with
  | ofNat k =>
      change HilbertOperator.applyVec
          ((U : HilbertOperator (Qubits n)) ^ k) v =
        Complex.exp ((k : ℂ) * (x : ℂ) * Complex.I) • v
      rw [pow_applyVec_eigen _ _ _ heig]
      congr 2
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
  | negSucc k =>
      change HilbertOperator.applyVec
          ((U.conjTranspose : HilbertOperator (Qubits n)) ^ (k + 1)) v = _
      rw [pow_applyVec_eigen _ _ _ heigAdj]
      congr 2
      rw [Int.cast_negSucc, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring

private lemma finset_sum_applyVec {R : Register} {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (A : ι → HilbertOperator R)
    (v : StateVector R) :
    HilbertOperator.applyVec (∑ i ∈ s, A i) v =
      ∑ i ∈ s, HilbertOperator.applyVec (A i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext j
      simp [HilbertOperator.applyVec_apply]
  | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, HilbertOperator.add_applyVec, ih]

private lemma laurentPolynomialOperator_applyVec_eigen {L n : Nat}
    (coeff : ℤ → ℂ) (U : Gate (Qubits n))
    (x : ℝ) (v : StateVector (Qubits n))
    (heig :
      U.applyVec v = Complex.exp ((x : ℂ) * Complex.I) • v)
    (heigAdj :
      U.conjTranspose.applyVec v =
        Complex.exp ((-x : ℝ) * Complex.I) • v) :
    HilbertOperator.applyVec (laurentPolynomialOperator L coeff U) v =
      trigonometricPolynomial L coeff x • v := by
  rw [laurentPolynomialOperator, finset_sum_applyVec]
  simp only [HilbertOperator.smul_applyVec,
    unitaryLaurentPower_applyVec_eigen U x v heig heigAdj, smul_smul]
  rw [← Finset.sum_smul]
  rfl

/-- A trigonometric-QSP amplitude lifts to the exact Laurent spectral
transformation, and successful postselection prepares its normalized action on
every input pure state for which that action is nonzero. -/
theorem postselected_spectral_transformation
    (L n : Nat)
    (U : Gate (Qubits n))
    (phases : Fin (2 ^ n) → ℝ)
    (eigenbasis : OrthonormalBasis (Fin (2 ^ n)) ℂ (StateVector (Qubits n)))
    (theta phi : Fin (2 * L + 1) → ℝ)
    (coeff : ℤ → ℂ)
    (hphase : ∀ j, phases j ∈ Set.Ico (-Real.pi) Real.pi)
    (hspectral :
      (U : HilbertOperator (Qubits n)) = spectralSum phases eigenbasis)
    (hbounded :
      ∀ x : ℝ, ‖trigonometricPolynomial L coeff x‖ ≤ 1)
    (hamplitude :
      ∀ x : ℝ,
        (oneQubitQSPSequence L theta phi x :
          HilbertOperator (Qubits 1)) 0 0 =
          trigonometricPolynomial L coeff x) :
    projectedBlock 1 n
        (controlledSpectralCircuit L U theta phi :
          HilbertOperator (Qubits (1 + n))) =
        spectralPolynomialOperator L coeff phases eigenbasis ∧
      spectralPolynomialOperator L coeff phases eigenbasis =
        laurentPolynomialOperator L coeff U ∧
      ∀ ψ : PureState (Qubits n),
        HilbertOperator.applyVec
            (spectralPolynomialOperator L coeff phases eigenbasis)
            (ψ : StateVector (Qubits n)) ≠ 0 →
        normalizedVector
            (controlZeroBranch (controlledSpectralCircuit L U theta phi)
              (ψ : StateVector (Qubits n))) =
          normalizedVector
            (HilbertOperator.applyVec
              (spectralPolynomialOperator L coeff phases eigenbasis)
              (ψ : StateVector (Qubits n))) := by
  have hUeig : ∀ j : Fin (2 ^ n),
      U.applyVec (eigenbasis j) =
        Complex.exp ((phases j : ℂ) * Complex.I) • eigenbasis j := by
    intro j
    change HilbertOperator.applyVec
        (U : HilbertOperator (Qubits n)) (eigenbasis j) = _
    rw [hspectral, spectralSum_applyVec_basis]
  have hblock :
      projectedBlock 1 n
          (controlledSpectralCircuit L U theta phi :
            HilbertOperator (Qubits (1 + n))) =
        spectralPolynomialOperator L coeff phases eigenbasis := by
    apply HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis eigenbasis
    intro j
    rw [spectralPolynomialOperator_applyVec_basis]
    ext i
    rw [projectedBlock_applyVec_apply]
    change (controlledSpectralCircuit L U theta phi).applyVec
        (StateVector.tensor
          (PureState.ket0 : StateVector (Qubits 1)) (eigenbasis j))
        (prodEquiv (0, i)) =
      (trigonometricPolynomial L coeff (phases j) • eigenbasis j) i
    rw [controlledSpectralCircuit_applyVec_eigen U theta phi
      (phases j) (eigenbasis j) (hUeig j),
      StateVector.tensor_apply_prod]
    change HilbertOperator.applyVec
        (oneQubitQSPSequence L theta phi (phases j) :
          HilbertOperator (Qubits 1))
        (PureState.ket0 : StateVector (Qubits 1)) 0 * eigenbasis j i =
      trigonometricPolynomial L coeff (phases j) * eigenbasis j i
    rw [PureState.ket0, HilbertOperator.applyVec_ket, hamplitude]
  have hlaurent :
      spectralPolynomialOperator L coeff phases eigenbasis =
        laurentPolynomialOperator L coeff U := by
    apply HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis eigenbasis
    intro j
    rw [spectralPolynomialOperator_applyVec_basis,
      laurentPolynomialOperator_applyVec_eigen coeff U (phases j)
        (eigenbasis j) (hUeig j)
        (gate_conjTranspose_applyVec_eigen U (phases j)
          (eigenbasis j) (hUeig j))]
  refine ⟨hblock, hlaurent, ?_⟩
  intro ψ _
  simp [controlZeroBranch, hblock]

end

end PostselectedSpectralTransformationTrigonometricQSP
end QAlgFormalized
