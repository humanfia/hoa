import QAlgBench.Base

/-!
# Eigenvectors of modular multiplication in Shor's algorithm

This file formalizes the standard Fourier eigenvectors of the operator
`Uₓ |y⟩ = |xy mod N⟩` on the `N`-dimensional residue register.
-/

namespace QAlgFormalized
namespace EigenvectorsModularMultiplicationShor

open scoped BigOperators

open QAlgBench

noncomputable section

/-- The finite Hilbert-space register whose computational basis is indexed by
the residues `0, ..., N - 1`. -/
def residueRegister (N : ℕ) : Register where
  Index := Fin N
  fintype := inferInstance
  decEq := inferInstance

/-- The residue represented by `x * y mod N`. -/
def modularProductIndex (x N : ℕ) (hN : 0 < N) (y : Fin N) : Fin N :=
  ⟨x * y.val % N, Nat.mod_lt _ hN⟩

/-- The residue represented by `x ^ k mod N`. -/
def modularPowerIndex (x N k : ℕ) (hN : 0 < N) : Fin N :=
  ⟨x ^ k % N, Nat.mod_lt _ hN⟩

/-- The matrix of modular multiplication by `x`.

Its `y`-th column is the computational-basis ket indexed by `x * y mod N`.
Under the coprimality assumption in the main theorem this matrix is a
permutation matrix, although the entrywise definition itself makes sense for
all natural `x` and `N`.
-/
def modularMultiplicationOperator (x N : ℕ) :
    HilbertOperator (residueRegister N) :=
  fun i j => if i.val = x * j.val % N then 1 else 0

/-- The modular multiplication operator has the defining computational-basis
action `Uₓ |y⟩ = |x * y mod N⟩`. -/
theorem modularMultiplicationOperator_apply_ket
    (x N : ℕ) (hN : 0 < N) (y : Fin N) :
    HilbertOperator.applyVec (modularMultiplicationOperator x N)
        (PureState.ket (R := residueRegister N) y :
          StateVector (residueRegister N)) =
      (PureState.ket (R := residueRegister N)
          (modularProductIndex x N hN y) :
        StateVector (residueRegister N)) := by
  ext i
  change Fin N at i
  simp only [HilbertOperator.applyVec_ket, modularMultiplicationOperator,
    PureState.ket_apply]
  congr 1
  apply propext
  constructor
  · exact fun h => Fin.ext h
  · exact fun h => congrArg Fin.val h

/-- The coefficient `exp(-2π i s k / r)` in the Fourier eigenvector. -/
def fourierCoefficient (s k r : ℕ) : ℂ :=
  Complex.exp
    (-(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) * (k : ℂ) / (r : ℂ)))

/-- The claimed eigenvalue `exp(2π i s / r)`. -/
def shorEigenvalue (s r : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) / (r : ℂ))

/-- The normalized Fourier superposition over the modular powers of `x`. -/
def shorEigenvector (x N r : ℕ) (hN : 0 < N) (s : Fin r) :
    StateVector (residueRegister N) :=
  (Real.sqrt (r : ℝ) : ℂ)⁻¹ •
    ∑ k : Fin r,
      fourierCoefficient s.val k.val r •
        (PureState.ket (R := residueRegister N)
            (modularPowerIndex x N k.val hN) :
          StateVector (residueRegister N))

/-- For a positive residue `x < N` coprime to `N`, let `r` be its
multiplicative order modulo `N`.  Every Fourier state indexed by `s < r` is a
nonzero eigenvector of modular multiplication by `x`, with eigenvalue
`exp(2π i s / r)`. -/
theorem shorEigenvector_is_eigenvector
    (x N r : ℕ)
    (hx : 0 < x)
    (hN : 0 < N)
    (hxN : x < N)
    (hcoprime : Nat.Coprime x N)
    (hr : r = orderOf (ZMod.unitOfCoprime x hcoprime))
    (s : Fin r) :
    shorEigenvector x N r hN s ≠ 0 ∧
      HilbertOperator.applyVec (modularMultiplicationOperator x N)
          (shorEigenvector x N r hN s) =
        shorEigenvalue s.val r • shorEigenvector x N r hN s := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hrpos : 0 < r := by
    rw [hr]
    exact orderOf_pos _
  letI : NeZero r := ⟨Nat.ne_of_gt hrpos⟩
  have hpower_injective : Function.Injective
      (fun k : Fin r => modularPowerIndex x N k.val hN) := by
    intro a b hab
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := ZMod.unitOfCoprime x hcoprime)
    · change a.val < orderOf (ZMod.unitOfCoprime x hcoprime)
      simpa only [← hr] using a.isLt
    · change b.val < orderOf (ZMod.unitOfCoprime x hcoprime)
      simpa only [← hr] using b.isLt
    · apply Units.ext
      have hc : ((x ^ a.val : ℕ) : ZMod N) =
          ((x ^ b.val : ℕ) : ZMod N) :=
        (ZMod.natCast_eq_natCast_iff' (x ^ a.val) (x ^ b.val) N).mpr
          (congrArg Fin.val hab)
      simpa only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
        Nat.cast_pow] using hc
  constructor
  · intro hv
    have hcoord := congrArg
      (fun v : StateVector (residueRegister N) =>
        v (modularPowerIndex x N 0 hN)) hv
    simp [shorEigenvector, PureState.ket_apply, hrpos.ne'] at hcoord
    have hsum :
        (∑ k : Fin r,
          @ite ℂ
            ((show (residueRegister N).Index from
                modularPowerIndex x N 0 hN) =
              (show (residueRegister N).Index from
                modularPowerIndex x N k.val hN))
            (Classical.propDecidable _)
            (fourierCoefficient s.val k.val r) 0) = 1 := by
      calc
        _ = @ite ℂ
              ((show (residueRegister N).Index from
                  modularPowerIndex x N 0 hN) =
                (show (residueRegister N).Index from
                  modularPowerIndex x N (0 : Fin r).val hN))
              (Classical.propDecidable _)
              (fourierCoefficient s.val (0 : Fin r).val r) 0 := by
            apply Fintype.sum_eq_single 0
            intro k hk
            rw [if_neg]
            intro hpow
            apply hk
            change modularPowerIndex x N 0 hN =
              modularPowerIndex x N k.val hN at hpow
            exact (hpower_injective hpow).symm
        _ = 1 := by simp [fourierCoefficient]
    rw [hsum] at hcoord
    exact one_ne_zero hcoord
  · have hmul_power (k : ℕ) :
        modularProductIndex x N hN (modularPowerIndex x N k hN) =
          modularPowerIndex x N (k + 1) hN := by
      apply Fin.ext
      simp [modularProductIndex, modularPowerIndex, pow_succ', Nat.mul_mod]
    have h_apply_power (k : ℕ) :
        HilbertOperator.applyVec (modularMultiplicationOperator x N)
            (PureState.ket (R := residueRegister N)
              (modularPowerIndex x N k hN) :
              StateVector (residueRegister N)) =
          (PureState.ket (R := residueRegister N)
            (modularPowerIndex x N (k + 1) hN) :
            StateVector (residueRegister N)) := by
      rw [modularMultiplicationOperator_apply_ket x N hN]
      rw [hmul_power k]
    have h_apply_term (k : Fin r) :
        HilbertOperator.applyVec (modularMultiplicationOperator x N)
            (fourierCoefficient s.val k.val r •
              (PureState.ket (R := residueRegister N)
                (modularPowerIndex x N k.val hN) :
                StateVector (residueRegister N))) =
          fourierCoefficient s.val k.val r •
            (PureState.ket (R := residueRegister N)
              (modularPowerIndex x N (k.val + 1) hN) :
              StateVector (residueRegister N)) := by
      rw [HilbertOperator.applyVec_smul, h_apply_power]
    have hcoeff_succ (k : ℕ) :
        fourierCoefficient s.val k r =
          shorEigenvalue s.val r * fourierCoefficient s.val (k + 1) r := by
      rw [shorEigenvalue, fourierCoefficient, fourierCoefficient,
        ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    have hcoeff_period : fourierCoefficient s.val r r = 1 := by
      rw [fourierCoefficient]
      rw [show
          -(2 * (Real.pi : ℂ) * Complex.I * (s.val : ℂ) * (r : ℂ) /
              (r : ℂ)) =
            (s.val : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I)) by
        field_simp [hrpos.ne']]
      rw [Complex.exp_nat_mul]
      simp [Complex.exp_neg, Complex.exp_two_pi_mul_I]
    have hpower_period :
        modularPowerIndex x N r hN = modularPowerIndex x N 0 hN := by
      apply Fin.ext
      simp only [modularPowerIndex, Fin.val_mk, pow_zero]
      have hu : (ZMod.unitOfCoprime x hcoprime) ^ r = 1 := by
        rw [hr]
        exact pow_orderOf_eq_one _
      apply (ZMod.natCast_eq_natCast_iff' (x ^ r) 1 N).mp
      norm_num
      simpa only [Nat.cast_pow, ZMod.coe_unitOfCoprime,
        Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hu
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrpos.ne'
    have htail :
        (∑ k : Fin n,
          fourierCoefficient s.val k.castSucc.val (n + 1) •
            (PureState.ket (R := residueRegister N)
              (modularPowerIndex x N (k.castSucc.val + 1) hN) :
              StateVector (residueRegister N))) =
          shorEigenvalue s.val (n + 1) •
            ∑ k : Fin n,
              fourierCoefficient s.val k.succ.val (n + 1) •
                (PureState.ket (R := residueRegister N)
                  (modularPowerIndex x N k.succ.val hN) :
                  StateVector (residueRegister N)) := by
      rw [Finset.smul_sum]
      apply Fintype.sum_congr
      intro k
      simp only [Fin.val_castSucc, Fin.val_succ, smul_smul]
      rw [← hcoeff_succ k.val]
    have hhead :
        fourierCoefficient s.val (Fin.last n).val (n + 1) •
            (PureState.ket (R := residueRegister N)
              (modularPowerIndex x N ((Fin.last n).val + 1) hN) :
              StateVector (residueRegister N)) =
          shorEigenvalue s.val (n + 1) •
            (fourierCoefficient s.val (0 : Fin (n + 1)).val (n + 1) •
              (PureState.ket (R := residueRegister N)
                (modularPowerIndex x N (0 : Fin (n + 1)).val hN) :
                StateVector (residueRegister N))) := by
      simp only [Fin.val_last, Fin.val_zero]
      rw [hcoeff_succ n, hcoeff_period, hpower_period]
      simp [fourierCoefficient]
    have hinner :
        (∑ k : Fin (n + 1),
          fourierCoefficient s.val k.val (n + 1) •
            (PureState.ket (R := residueRegister N)
              (modularPowerIndex x N (k.val + 1) hN) :
              StateVector (residueRegister N))) =
          shorEigenvalue s.val (n + 1) •
            ∑ k : Fin (n + 1),
              fourierCoefficient s.val k.val (n + 1) •
                (PureState.ket (R := residueRegister N)
                  (modularPowerIndex x N k.val hN) :
                  StateVector (residueRegister N)) := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ, smul_add]
      rw [htail, hhead, add_comm]
    rw [shorEigenvector]
    rw [HilbertOperator.applyVec_smul, HilbertOperator.applyVec_sum]
    rw [show
      (∑ k : Fin (n + 1),
        HilbertOperator.applyVec (modularMultiplicationOperator x N)
          (fourierCoefficient s.val k.val (n + 1) •
            (PureState.ket (R := residueRegister N)
              (modularPowerIndex x N k.val hN) :
              StateVector (residueRegister N)))) =
        ∑ k : Fin (n + 1),
          fourierCoefficient s.val k.val (n + 1) •
            (PureState.ket (R := residueRegister N)
              (modularPowerIndex x N (k.val + 1) hN) :
              StateVector (residueRegister N)) by
      apply Fintype.sum_congr
      exact h_apply_term]
    rw [hinner]
    simp only [smul_smul]
    rw [mul_comm]

end

end EigenvectorsModularMultiplicationShor
end QAlgFormalized
