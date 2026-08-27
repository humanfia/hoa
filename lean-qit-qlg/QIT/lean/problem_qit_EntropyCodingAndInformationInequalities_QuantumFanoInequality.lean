import QITBench.Base
import QITBench.Base.OneShot
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Quantum Fano inequality

This file formalizes the finite-dimensional quantum Fano inequality.  Distinct
systems are represented by distinct finite basis types; the isomorphisms
`R ≃ A` and `B ≃ A` make the dimension identifications from the source
statement explicit.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace QITFormalized.EntropyCodingAndInformationInequalities.QuantumFanoInequality

open QITBench Matrix

noncomputable section

universe uA uR uB uX

/-- The von Neumann entropy in bits, defined as the Shannon entropy of the
eigenvalues of a finite-dimensional density operator. -/
noncomputable def vonNeumannEntropy
    {X : Type uX} [Fintype X] [DecidableEq X]
    (rho : State X) : ℝ :=
  QITBench.OneShot.schmidtEntropy rho.pos.isHermitian.eigenvalues

/-- The binary entropy in bits.  Mathlib's convention `Real.log 0 = 0`
implements the continuous endpoint convention `0 log₂ 0 = 0`. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  -p * QITBench.OneShot.log2 p -
    (1 - p) * QITBench.OneShot.log2 (1 - p)

private theorem schmidtEntropy_eq_sum_negMulLog_div
    {X : Type*} [Fintype X] (p : X → ℝ) :
    QITBench.OneShot.schmidtEntropy p =
      (∑ i, Real.negMulLog (p i)) / Real.log 2 := by
  unfold QITBench.OneShot.schmidtEntropy QITBench.OneShot.log2
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.negMulLog]
  ring

private theorem sum_negMulLog_le_qaryEntropy_coordinate
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hcard : 2 ≤ Fintype.card X) (i : X) :
    (∑ j, Real.negMulLog (p j)) ≤
      Real.qaryEntropy (Fintype.card X) (1 - p i) := by
  let Z := {j : X // j ≠ i}
  let m := Fintype.card Z
  have hmcard : m = Fintype.card X - 1 := by
    dsimp [m, Z]
    rw [Fintype.card_subtype_compl (fun j : X => j = i)]
    simp
  have hmpos : 0 < m := by omega
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hmpos)
  have hsumZ : ∑ z : Z, p z = 1 - p i := by
    have hsplit := Fintype.sum_eq_add_sum_subtype_ne p i
    rw [hpsum] at hsplit
    linarith
  let c : ℝ := (m : ℝ)⁻¹
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hweights : ∑ _z : Z, c = 1 := by
    simp [c, m, ne_of_gt hmpos]
  have havg : ∑ z : Z, c * ((m : ℝ) * p z) = 1 - p i := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsumZ]
    dsimp [c]
    field_simp [hm0]
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _z : Z => c)
    (p := fun z : Z => (m : ℝ) * p z)
    (fun _z _ => hc) hweights
    (fun z _ =>
      Set.mem_Ici.mpr (mul_nonneg (Nat.cast_nonneg _) (hp0 z)))
  simp only [smul_eq_mul] at hjensen
  rw [havg] at hjensen
  have hpoint (z : Z) :
      c * Real.negMulLog ((m : ℝ) * p z) =
        Real.negMulLog (p z) - p z * Real.log (m : ℝ) := by
    dsimp [c]
    rw [Real.negMulLog_mul]
    simp only [Real.negMulLog]
    field_simp [hm0]
    ring
  have hcomp :
      (∑ z : Z, Real.negMulLog (p z)) ≤
        Real.negMulLog (1 - p i) + (1 - p i) * Real.log (m : ℝ) := by
    calc
      (∑ z : Z, Real.negMulLog (p z)) =
          ∑ z : Z,
            (c * Real.negMulLog ((m : ℝ) * p z) +
              p z * Real.log (m : ℝ)) := by
                apply Finset.sum_congr rfl
                intro z _
                rw [hpoint]
                ring
      _ = (∑ z : Z, c * Real.negMulLog ((m : ℝ) * p z)) +
            (∑ z : Z, p z) * Real.log (m : ℝ) := by
              rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ Real.negMulLog (∑ z : Z, p z) +
            (∑ z : Z, p z) * Real.log (m : ℝ) := by
              rw [hsumZ]
              linarith
      _ = Real.negMulLog (1 - p i) +
            (1 - p i) * Real.log (m : ℝ) := by rw [hsumZ]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j => Real.negMulLog (p j)) i]
  rw [Real.qaryEntropy,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [hmcard] at hcomp
  have hcast :
      ((Fintype.card X - 1 : ℕ) : ℝ) = (Fintype.card X : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast] at hcomp
  norm_num at hcomp ⊢
  linarith

private theorem sum_negMulLog_le_qaryEntropy_weighted
    {X : Type*} [Fintype X] [DecidableEq X]
    (p w : X → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hw0 : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hcard : 0 < Fintype.card X) :
    (∑ j, Real.negMulLog (p j)) ≤
      Real.qaryEntropy (Fintype.card X) (1 - ∑ i, w i * p i) := by
  by_cases htwo : 2 ≤ Fintype.card X
  · have hp1 (i : X) : p i ≤ 1 := by
      rw [← hpsum]
      exact Finset.single_le_sum
        (fun j _ => hp0 j) (Finset.mem_univ i)
    have havg :
        ∑ i, w i * (1 - p i) = 1 - ∑ i, w i * p i := by
      calc
        ∑ i, w i * (1 - p i) =
            ∑ i, (w i - w i * p i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = (∑ i, w i) - ∑ i, w i * p i := by
              rw [Finset.sum_sub_distrib]
        _ = 1 - ∑ i, w i * p i := by rw [hwsum]
    have hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
        (Real.qaryEntropy (Fintype.card X)) :=
      (Real.strictConcaveOn_qaryEntropy
        (q := Fintype.card X)).concaveOn
    have hjensen := hconc.le_map_sum
      (t := Finset.univ) (w := w) (p := fun i => 1 - p i)
      (fun i _ => hw0 i) hwsum
      (fun i _ =>
        Set.mem_Icc.mpr
          ⟨sub_nonneg.mpr (hp1 i), by linarith [hp0 i]⟩)
    simp only [smul_eq_mul] at hjensen
    rw [havg] at hjensen
    calc
      (∑ j, Real.negMulLog (p j)) =
          ∑ i, w i * (∑ j, Real.negMulLog (p j)) := by
            rw [← Finset.sum_mul, hwsum, one_mul]
      _ ≤ ∑ i, w i *
            Real.qaryEntropy (Fintype.card X) (1 - p i) := by
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_left
                (sum_negMulLog_le_qaryEntropy_coordinate
                  p hp0 hpsum htwo i)
                (hw0 i)
      _ ≤ Real.qaryEntropy
            (Fintype.card X) (1 - ∑ i, w i * p i) :=
              hjensen
  · have hcard_one : Fintype.card X = 1 := by omega
    obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcard_one
    letI : Unique X := ⟨⟨i⟩, hi⟩
    have hp : p default = 1 := by simpa using hpsum
    have hw : w default = 1 := by simpa using hwsum
    simp [hp, hw]

/-- The joint `RB` state obtained by applying a channel to the `A` half of a
pure state on `RA`, leaving `R` unchanged. -/
noncomputable def jointOutputState
    {A : Type uA} {R : Type uR} {B : Type uB}
    [Fintype A] [DecidableEq A]
    [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B]
    (psiRA : PureVector (R × A)) (E : Channel A B) :
    State (R × B) :=
  ((Channel.idChannel R).prod E).applyState psiRA.state

/-- Transport the purification vector from `RA` to `RB` along the specified
identification of the output system `B` with the input system `A`. -/
noncomputable def purificationOnOutput
    {A : Type uA} {R : Type uR} {B : Type uB}
    [Fintype A] [DecidableEq A]
    [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B]
    (psiRA : PureVector (R × A)) (eBA : B ≃ A) :
    PureVector (R × B) :=
  psiRA.reindex (Equiv.prodCongr (Equiv.refl R) eBA.symm)

/-- The entanglement fidelity `⟨ψ|ρ|ψ⟩`, represented as a real number.
The real part is mathematically redundant for a positive semidefinite `ρ` but
makes the codomain explicit. -/
noncomputable def entanglementFidelity
    {X : Type uX} [Fintype X] [DecidableEq X]
    (rho : State X) (psi : PureVector X) : ℝ :=
  Complex.re
    (dotProduct (fun i => star (psi.amp i))
      (Matrix.mulVec rho.matrix psi.amp))

private theorem spectralWeights_sum_one
    {X : Type uX} [Fintype X] [DecidableEq X]
    (psi : PureVector X) (U : Matrix.unitaryGroup X ℂ) :
    ∑ i, Complex.normSq
      ((star (U : CMatrix X) *ᵥ psi.amp) i) = 1 := by
  let c : X → ℂ := (star (U : CMatrix X)) *ᵥ psi.amp
  have hU : (U : CMatrix X) * (U : CMatrix X)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Unitary.coe_mul_star_self U)
  have hccomplex : star c ⬝ᵥ c = (1 : ℂ) := by
    dsimp [c]
    rw [Matrix.star_mulVec]
    rw [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    rw [hU, Matrix.vecMul_one]
    have htrace := psi.trace_rankOne_eq_one
    rw [rankOneMatrix_trace] at htrace
    rw [dotProduct_comm]
    exact htrace
  have hre := congrArg Complex.re hccomplex
  simp only [dotProduct] at hre
  rw [Complex.re_sum] at hre
  simp only [Complex.one_re] at hre
  simpa [c, ← Complex.normSq_eq_conj_mul_self] using hre

private theorem entanglementFidelity_eq_spectralWeightedSum
    {X : Type uX} [Fintype X] [DecidableEq X]
    (rho : State X) (psi : PureVector X) :
    entanglementFidelity rho psi =
      ∑ i, Complex.normSq
          (((star
            (rho.pos.isHermitian.eigenvectorUnitary : CMatrix X)) *ᵥ
              psi.amp) i) *
        rho.pos.isHermitian.eigenvalues i := by
  let hA := rho.pos.isHermitian
  let p : X → ℝ := hA.eigenvalues
  let U := hA.eigenvectorUnitary
  let D : CMatrix X := Matrix.diagonal (fun i => (p i : ℂ))
  let c : X → ℂ := (star (U : CMatrix X)) *ᵥ psi.amp
  have hspectral :
      rho.matrix =
        Unitary.conjStarAlgAut ℂ (CMatrix X) U D := by
    simpa [U, D, p] using hA.spectral_theorem
  have hUstar :
      star (U : CMatrix X) = (U : CMatrix X)ᴴ :=
    Matrix.star_eq_conjTranspose _
  have hstarc :
      star c = star psi.amp ᵥ* (U : CMatrix X) := by
    dsimp [c]
    rw [Matrix.star_mulVec]
    rw [hUstar, Matrix.conjTranspose_conjTranspose]
  have hcomplex :
      dotProduct (star psi.amp) (rho.matrix *ᵥ psi.amp) =
        ∑ i, ((Complex.normSq (c i) : ℝ) : ℂ) * (p i : ℂ) := by
    rw [hspectral, Unitary.conjStarAlgAut_apply]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    rw [← hstarc]
    change dotProduct (star c) (D *ᵥ c) = _
    simp only [dotProduct, D, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Pi.star_apply, starRingEnd_apply]
    ring
  unfold entanglementFidelity
  change Complex.re
      (dotProduct (star psi.amp) (rho.matrix *ᵥ psi.amp)) = _
  rw [hcomplex, Complex.re_sum]
  dsimp [c, U, p, hA]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- The exchange entropy of the channel output associated with the chosen
input state and purification. -/
noncomputable def exchangeEntropy
    {X : Type uX} [Fintype X] [DecidableEq X]
    (rho : State X) : ℝ :=
  vonNeumannEntropy rho

private theorem qaryEntropy_div_log_eq_binaryEntropy_add
    (N : ℕ) (x : ℝ) :
    Real.qaryEntropy N (1 - x) / Real.log 2 =
      binaryEntropy x +
        (1 - x) * QITBench.OneShot.log2 ((N : ℝ) - 1) := by
  unfold binaryEntropy QITBench.OneShot.log2 Real.qaryEntropy
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog]
  push_cast
  ring_nf

private theorem vonNeumannEntropy_le_overlap_bound
    {X : Type uX} [Fintype X] [DecidableEq X]
    (rho : State X) (psi : PureVector X) :
    vonNeumannEntropy rho ≤
      binaryEntropy (entanglementFidelity rho psi) +
        (1 - entanglementFidelity rho psi) *
          QITBench.OneShot.log2 ((Fintype.card X : ℝ) - 1) := by
  let hA := rho.pos.isHermitian
  let p : X → ℝ := hA.eigenvalues
  let U := hA.eigenvectorUnitary
  let w : X → ℝ := fun i =>
    Complex.normSq (((star (U : CMatrix X)) *ᵥ psi.amp) i)
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    exact rho.pos.eigenvalues_nonneg i
  have hpsum : ∑ i, p i = 1 := by
    have htrace := hA.trace_eq_sum_eigenvalues
    rw [rho.trace_eq_one] at htrace
    have hre := congrArg Complex.re htrace
    simpa [p, hA] using hre.symm
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    exact Complex.normSq_nonneg _
  have hwsum : ∑ i, w i = 1 := by
    simpa [w, U] using spectralWeights_sum_one psi U
  have hcard : 0 < Fintype.card X :=
    Fintype.card_pos_iff.mpr rho.nonempty
  have hnat :=
    sum_negMulLog_le_qaryEntropy_weighted
      p w hp0 hpsum hw0 hwsum hcard
  have hlog : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  have hoverlap :
      entanglementFidelity rho psi = ∑ i, w i * p i := by
    simpa [w, p, U, hA] using
      entanglementFidelity_eq_spectralWeightedSum rho psi
  unfold vonNeumannEntropy
  rw [schmidtEntropy_eq_sum_negMulLog_div]
  calc
    (∑ i, Real.negMulLog (p i)) / Real.log 2 ≤
        Real.qaryEntropy (Fintype.card X)
          (1 - ∑ i, w i * p i) / Real.log 2 :=
      div_le_div_of_nonneg_right hnat hlog
    _ = binaryEntropy (∑ i, w i * p i) +
        (1 - ∑ i, w i * p i) *
          QITBench.OneShot.log2 ((Fintype.card X : ℝ) - 1) :=
      qaryEntropy_div_log_eq_binaryEntropy_add
        (Fintype.card X) (∑ i, w i * p i)
    _ = binaryEntropy (entanglementFidelity rho psi) +
        (1 - entanglementFidelity rho psi) *
          QITBench.OneShot.log2 ((Fintype.card X : ℝ) - 1) := by
      rw [hoverlap]

/-- The rank-one projector `P = |ψ⟩⟨ψ|`. -/
noncomputable def pureProjector
    {X : Type uX} [Fintype X] [DecidableEq X]
    (psi : PureVector X) : CMatrix X :=
  rankOneMatrix psi.amp

/-- The complementary projector `Q = I - P`. -/
noncomputable def complementProjector
    {X : Type uX} [Fintype X] [DecidableEq X]
    (psi : PureVector X) : CMatrix X :=
  1 - pureProjector psi

/-- A normalized rank-one projector is bounded above by the identity. -/
theorem pureProjector_le_identity
    {X : Type uX} [Fintype X] [DecidableEq X]
    (psi : PureVector X) :
    pureProjector psi ≤ (1 : CMatrix X) := by
  apply IsStarProjection.le_one
  rw [isStarProjection_iff']
  constructor
  · simpa [pureProjector] using psi.state_matrix_mul_self
  · exact rankOneMatrix_conjTranspose psi.amp

/-- The binary POVM `{P,Q}` associated with a normalized pure vector, with
`true` effect `P = |ψ⟩⟨ψ|` and `false` effect `Q = I - P`. -/
noncomputable def binaryPurePartition
    {X : Type uX} [Fintype X] [DecidableEq X]
    (psi : PureVector X) : POVM Bool X :=
  POVM.binaryOfEffect (pureProjector psi)
    (by
      simpa [pureProjector] using rankOneMatrix_pos psi.amp)
    (pureProjector_le_identity psi)

/-- **Quantum Fano inequality.**

For a density operator `rhoA` on a `d`-dimensional system, a normalized
purification `psiRA`, and a quantum channel `E : A ⟶ B`, the exchange entropy
of the joint reference-output state is bounded by the binary entropy of its
entanglement fidelity plus the error weight times `log₂(d² - 1)`.
-/
theorem quantumFanoInequality
    {A : Type uA} {R : Type uR} {B : Type uB}
    [Fintype A] [DecidableEq A]
    [Fintype R] [DecidableEq R]
    [Fintype B] [DecidableEq B]
    (d : ℕ)
    (rhoA : State A)
    (psiRA : PureVector (R × A))
    (hPurifies : psiRA.state.marginalB = rhoA)
    (hDimA : Fintype.card A = d)
    (eRA : R ≃ A)
    (E : Channel A B)
    (eBA : B ≃ A) :
    let rhoRB := jointOutputState psiRA E
    let psiRB := purificationOnOutput psiRA eBA
    let Fe := entanglementFidelity rhoRB psiRB
    exchangeEntropy rhoRB ≤
      binaryEntropy Fe +
        (1 - Fe) * QITBench.OneShot.log2 ((d : ℝ) ^ 2 - 1) := by
  have hcardRB : Fintype.card (R × B) = d ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_congr eRA,
      Fintype.card_congr eBA, hDimA]
    ring
  have hbound :=
    vonNeumannEntropy_le_overlap_bound
      (jointOutputState psiRA E) (purificationOnOutput psiRA eBA)
  simpa [exchangeEntropy, hcardRB] using hbound

end

end QITFormalized.EntropyCodingAndInformationInequalities.QuantumFanoInequality
