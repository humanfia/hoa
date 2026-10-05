import QAlgBench.Base

open scoped BigOperators

namespace QAlgFormalized

open QAlgBench

noncomputable section

/-- The phase `exp (2 * π * i * r)` appearing in the QFT product factors. -/
def qft8Phase (r : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I)

/--
The normalized one-qubit vector
`(ket 0 + exp (2 * π * i * r) ket 1) / sqrt 2`.
-/
def qft8PhaseQubit (r : ℝ) : StateVector (Qubits 1) :=
  PureState.invSqrt2 •
    ((PureState.ket0 : StateVector (Qubits 1)) +
      qft8Phase r • (PureState.ket1 : StateVector (Qubits 1)))

/--
The action of the eight-point quantum Fourier transform on a computational
basis ket:
`QFT_8 |x> = (1 / sqrt 8) * sum_y exp (2 * π * i * x * y / 8) |y>`.
-/
def qft8Ket (x : Fin 8) : StateVector (Qubits 3) :=
  (Real.sqrt 8 : ℂ)⁻¹ •
    ∑ y : Fin 8,
      Complex.exp
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            (((x : ℕ) : ℂ) * ((y : ℕ) : ℂ) / 8)) •
        (PureState.ket (R := Qubits 3) y : StateVector (Qubits 3))

/--
The corrected big-endian product factorization of `QFT_8 |3>`. The nested
tensor factors are ordered as qubits `2`, `1`, and `0`.
-/
theorem qft8Ket_three_product_factorization :
    qft8Ket 3 =
      StateVector.tensor
        (StateVector.tensor
          (qft8PhaseQubit ((1 : ℝ) / 2))
          (qft8PhaseQubit ((3 : ℝ) / 4)))
        (qft8PhaseQubit ((3 : ℝ) / 8)) := by
  have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 8 = Real.sqrt (4 * 2) := by norm_num
      _ = Real.sqrt 4 * Real.sqrt 2 := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hnorm : ((Real.sqrt 8 : ℂ)⁻¹) =
      PureState.invSqrt2 * (2 : ℂ)⁻¹ := by
    rw [PureState.invSqrt2, hsqrt8]
    push_cast
    field_simp
  have hnorm3 : PureState.invSqrt2 ^ 3 = ((Real.sqrt 8 : ℂ)⁻¹) := by
    calc
      PureState.invSqrt2 ^ 3 =
          PureState.invSqrt2 *
            (PureState.invSqrt2 * PureState.invSqrt2) := by ring
      _ = PureState.invSqrt2 * (2 : ℂ)⁻¹ := by
        rw [PureState.invSqrt2_mul_self]
      _ = ((Real.sqrt 8 : ℂ)⁻¹) := hnorm.symm
  have hphase3 :
      Complex.exp
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (3 * 3 / 8)) =
        qft8Phase ((3 : ℝ) / 8) * qft8Phase ((3 : ℝ) / 4) := by
    rw [qft8Phase, qft8Phase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase4 :
      Complex.exp
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (3 * 4 / 8)) =
        qft8Phase ((1 : ℝ) / 2) := by
    rw [qft8Phase]
    rw [show
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (3 * 4 / 8) =
          (((2 * Real.pi * ((1 : ℝ) / 2) : ℝ) : ℂ) * Complex.I) +
            2 * (Real.pi : ℂ) * Complex.I by
          push_cast
          ring,
      Complex.exp_periodic]
  have hphase5 :
      Complex.exp
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (3 * 5 / 8)) =
        qft8Phase ((3 : ℝ) / 8) * qft8Phase ((1 : ℝ) / 2) := by
    rw [qft8Phase, qft8Phase, ← Complex.exp_add]
    rw [show
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (3 * 5 / 8) =
          ((((2 * Real.pi * ((3 : ℝ) / 8) : ℝ) : ℂ) * Complex.I) +
            (((2 * Real.pi * ((1 : ℝ) / 2) : ℝ) : ℂ) * Complex.I)) +
            2 * (Real.pi : ℂ) * Complex.I by
          push_cast
          ring,
      Complex.exp_periodic]
  have hphase6 :
      Complex.exp
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (3 * 6 / 8)) =
        qft8Phase ((3 : ℝ) / 4) * qft8Phase ((1 : ℝ) / 2) := by
    rw [qft8Phase, qft8Phase, ← Complex.exp_add]
    rw [show
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (3 * 6 / 8) =
          ((((2 * Real.pi * ((3 : ℝ) / 4) : ℝ) : ℂ) * Complex.I) +
            (((2 * Real.pi * ((1 : ℝ) / 2) : ℝ) : ℂ) * Complex.I)) +
            2 * (Real.pi : ℂ) * Complex.I by
          push_cast
          ring,
      Complex.exp_periodic]
  have hphase7 :
      Complex.exp
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (3 * 7 / 8)) =
        qft8Phase ((3 : ℝ) / 8) *
          (qft8Phase ((3 : ℝ) / 4) * qft8Phase ((1 : ℝ) / 2)) := by
    let a : ℂ :=
      (((2 * Real.pi * ((3 : ℝ) / 8) : ℝ) : ℂ) * Complex.I)
    let b : ℂ :=
      (((2 * Real.pi * ((3 : ℝ) / 4) : ℝ) : ℂ) * Complex.I)
    let c : ℂ :=
      (((2 * Real.pi * ((1 : ℝ) / 2) : ℝ) : ℂ) * Complex.I)
    change
      Complex.exp
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (3 * 7 / 8)) =
        Complex.exp a * (Complex.exp b * Complex.exp c)
    rw [← Complex.exp_add, ← Complex.exp_add]
    rw [show
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (3 * 7 / 8) =
          (a + (b + c)) + 2 * (Real.pi : ℂ) * Complex.I by
          dsimp [a, b, c]
          push_cast
          ring,
      Complex.exp_periodic]
  ext y
  fin_cases y <;>
    simp [qft8Ket, qft8PhaseQubit, qft8Phase, StateVector.tensor_apply,
      PureState.ket0, PureState.ket1, PureState.ket_apply,
      PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, prodEquiv,
      finProdFinEquiv, finCongr, Fin.modNat, Fin.divNat, hphase3,
      hphase4, hphase5, hphase6, hphase7]
  all_goals rw [← hnorm3]
  all_goals simp only [← PureState.invSqrt2_mul_self]
  all_goals ring_nf

end

end QAlgFormalized
