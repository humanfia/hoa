import QITBench.Base.OneShot

/-!
# Spectrum and entropy of a single-qubit source

This file formalizes the one-copy average state of the IID source, its two
eigenvalues (including algebraic multiplicity), and its von Neumann entropy.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace QITFormalized.SpectrumEntropySingleQubitSource

open QITBench

noncomputable section

/-- The average density matrix
`ρ = (1 / 4) * [[3, 1], [1, 1]]` of the single-qubit source. -/
def averageDensityMatrix : CMatrix (Fin 2) :=
  (1 / 4 : ℂ) • !![(3 : ℂ), 1; 1, 1]

/-- The one-copy average state of the source. -/
def averageState : State (Fin 2) where
  matrix := averageDensityMatrix
  pos := by
    let B : Matrix (Fin 3) (Fin 2) ℂ :=
      !![(1 / 2 : ℂ), 0; 1 / 2, 0; 1 / 2, 1 / 2]
    have hB := Matrix.posSemidef_conjTranspose_mul_self B
    convert hB using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, averageDensityMatrix, Matrix.mul_apply,
        Matrix.conjTranspose, Fin.sum_univ_succ] <;>
      norm_num [map_inv₀, map_ofNat]
  trace_eq_one := by
    norm_num [averageDensityMatrix, Matrix.trace, Fin.sum_univ_two]

/-- The IID `n`-copy source obtained from the one-copy average state. -/
def iidSource (n : ℕ) : State (TensorPower (Fin 2) n) :=
  averageState.tensorPower n

/-- The larger eigenvalue `(2 + √2) / 4`. -/
def lambdaPlus : ℝ :=
  (2 + Real.sqrt 2) / 4

/-- The smaller eigenvalue `(2 - √2) / 4`. -/
def lambdaMinus : ℝ :=
  (2 - Real.sqrt 2) / 4

/-- Von Neumann entropy in bits, defined as the Shannon entropy of the real
eigenvalues of a finite-dimensional density matrix.  Lean's convention
`Real.log 0 = 0` gives the standard value `0 * log₂ 0 = 0`. -/
def vonNeumannEntropy {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) : ℝ :=
  QITBench.OneShot.schmidtEntropy rho.pos.isHermitian.eigenvalues

/-- The two displayed eigenvalues lie in the probability range, in increasing
order. -/
theorem lambda_bounds :
    0 < lambdaMinus ∧ lambdaMinus < lambdaPlus ∧ lambdaPlus < 1 := by
  norm_num [lambdaMinus, lambdaPlus]
  have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · nlinarith [hs]
  constructor <;> nlinarith [hs]

/-- The two eigenvalues sum to one, as required for the spectrum of a density
matrix. -/
theorem lambda_sum :
    lambdaPlus + lambdaMinus = 1 := by
  unfold lambdaPlus lambdaMinus
  ring

/-- The characteristic polynomial has exactly the requested roots, with
algebraic multiplicity. -/
theorem averageDensityMatrix_eigenvalues :
    averageDensityMatrix.charpoly.roots =
      {(lambdaPlus : ℂ), (lambdaMinus : ℂ)} := by
  have htrace : averageDensityMatrix.trace = 1 := by
    norm_num [averageDensityMatrix, Matrix.trace, Fin.sum_univ_two]
  have hdet : averageDensityMatrix.det = (1 / 8 : ℂ) := by
    norm_num [averageDensityMatrix, Matrix.det_fin_two]
  have hsumc : (lambdaPlus : ℂ) + (lambdaMinus : ℂ) = 1 := by
    exact_mod_cast lambda_sum
  have hprodreal : lambdaPlus * lambdaMinus = 1 / 8 := by
    have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
    unfold lambdaPlus lambdaMinus
    nlinarith
  have hprodc : (lambdaPlus : ℂ) * (lambdaMinus : ℂ) = 1 / 8 := by
    calc
      (lambdaPlus : ℂ) * (lambdaMinus : ℂ) =
          ((lambdaPlus * lambdaMinus : ℝ) : ℂ) := by norm_num
      _ = ((1 / 8 : ℝ) : ℂ) :=
        congrArg (fun x : ℝ => (x : ℂ)) hprodreal
      _ = 1 / 8 := by norm_num
  have hpoly : averageDensityMatrix.charpoly =
      (Polynomial.X - Polynomial.C (lambdaPlus : ℂ)) *
        (Polynomial.X - Polynomial.C (lambdaMinus : ℂ)) := by
    rw [Matrix.charpoly_fin_two, htrace, hdet]
    calc
      Polynomial.X ^ 2 - Polynomial.C 1 * Polynomial.X +
          Polynomial.C (1 / 8) =
          Polynomial.X ^ 2 -
            Polynomial.C ((lambdaPlus : ℂ) + lambdaMinus) * Polynomial.X +
              Polynomial.C ((lambdaPlus : ℂ) * lambdaMinus) := by
                rw [hsumc, hprodc]
      _ = (Polynomial.X - Polynomial.C (lambdaPlus : ℂ)) *
          (Polynomial.X - Polynomial.C (lambdaMinus : ℂ)) := by
        rw [map_add, map_mul]
        ring
  rw [hpoly, Polynomial.roots_mul (mul_ne_zero
    (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _))]
  simp

/-- Equivalently, the operator spectrum is precisely the two requested
eigenvalues. -/
theorem averageDensityMatrix_spectrum :
    spectrum ℂ averageDensityMatrix =
      {(lambdaPlus : ℂ), (lambdaMinus : ℂ)} := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
    ← Polynomial.mem_roots averageDensityMatrix.charpoly_monic.ne_zero,
    averageDensityMatrix_eigenvalues]
  simp

/-- The von Neumann entropy of the source, in bits. -/
theorem averageState_entropy :
    vonNeumannEntropy averageState =
      -lambdaPlus * QITBench.OneShot.log2 lambdaPlus -
        lambdaMinus * QITBench.OneShot.log2 lambdaMinus := by
  let hHerm : Matrix.IsHermitian averageDensityMatrix :=
    averageState.pos.isHermitian
  have hcomplex :
      Multiset.map (fun i : Fin 2 => (hHerm.eigenvalues i : ℂ))
          Finset.univ.val =
        {(lambdaPlus : ℂ), (lambdaMinus : ℂ)} := by
    rw [← averageDensityMatrix_eigenvalues]
    simpa [hHerm] using hHerm.roots_charpoly_eq_eigenvalues.symm
  have heig :
      Multiset.map hHerm.eigenvalues Finset.univ.val =
        {lambdaPlus, lambdaMinus} := by
    apply Multiset.map_injective Complex.ofReal_injective
    simpa [Multiset.map_map] using hcomplex
  let f : ℝ → ℝ := fun x => x * QITBench.OneShot.log2 x
  have hterms := congrArg (Multiset.map f) heig
  have hsum := congrArg Multiset.sum hterms
  simpa [vonNeumannEntropy, QITBench.OneShot.schmidtEntropy, f, hHerm,
    Finset.sum, Multiset.map_map, sub_eq_add_neg, add_comm] using
      congrArg Neg.neg hsum

end

end QITFormalized.SpectrumEntropySingleQubitSource
