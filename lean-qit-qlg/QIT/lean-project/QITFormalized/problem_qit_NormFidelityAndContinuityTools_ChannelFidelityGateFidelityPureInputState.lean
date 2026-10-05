import QITBench.Base
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Channel fidelity and gate fidelity for a pure input state

This file formalizes the Kraus-trace formula for entanglement fidelity, the
existence of a preferred Kraus representation, and the reduction to the usual
pure-state gate fidelity after conjugating a noisy channel by the inverse of a
target unitary.
-/

open scoped ComplexOrder MatrixOrder

namespace QITFormalized.ChannelFidelityGateFidelityPureInputState

open QITBench

universe u v

noncomputable section

variable {d : Type u} [Fintype d] [DecidableEq d]

/-- A fixed finite Kraus family selected from the Choi-positive channel map. -/
noncomputable def canonicalKraus (E : Channel d d) : d × d → CMatrix d :=
  Classical.choose
    (MatrixMap.exists_kraus_of_choi_psd E.map E.completelyPositive)

/-- The selected Kraus family represents the channel map. -/
theorem map_eq_ofKraus_canonicalKraus (E : Channel d d) :
    E.map = MatrixMap.ofKraus (canonicalKraus E) := by
  exact Classical.choose_spec
    (MatrixMap.exists_kraus_of_choi_psd E.map E.completelyPositive)

/-- Entanglement fidelity, defined using a fixed Kraus representation of the
channel. Representation independence is stated below. -/
noncomputable def entanglementFidelity (ρ : State d) (E : Channel d d) : ℝ :=
  ∑ i : d × d,
    Complex.normSq ((ρ.matrix * canonicalKraus E i).trace)

private theorem krausTraceSum_eq_choiPairing
    (ρ : State d) {κ : Type v} [Fintype κ] (K : κ → CMatrix d) :
    ((∑ k : κ, Complex.normSq ((ρ.matrix * K k).trace) : ℝ) : ℂ) =
      ∑ i : d, ∑ j : d, ∑ p : d, ∑ q : d,
        ρ.matrix q p * ρ.matrix i j *
          MatrixMap.choi (MatrixMap.ofKraus K) (i, j) (p, q) := by
  classical
  have hρ (i j : d) :
      (starRingEnd ℂ) (ρ.matrix i j) = ρ.matrix j i := by
    change star (ρ.matrix i j) = ρ.matrix j i
    exact ρ.pos.isHermitian.apply j i
  have hexpand :
      ((∑ k : κ, Complex.normSq ((ρ.matrix * K k).trace) : ℝ) : ℂ) =
        ∑ k : κ, ∑ i : d, ∑ j : d, ∑ p : d, ∑ q : d,
          ρ.matrix q p * ρ.matrix i j * K k j i *
            (starRingEnd ℂ) (K k q p) := by
    simp only [Complex.ofReal_sum]
    simp_rw [Complex.normSq_eq_conj_mul_self]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, hρ]
    simp only [Finset.sum_mul, Finset.mul_sum]
    repeat' apply Finset.sum_congr rfl; intro x hx
    ring
  have hchoi :
      (∑ i : d, ∑ j : d, ∑ p : d, ∑ q : d,
          ρ.matrix q p * ρ.matrix i j *
            MatrixMap.choi (MatrixMap.ofKraus K) (i, j) (p, q)) =
        ∑ i : d, ∑ j : d, ∑ p : d, ∑ q : d, ∑ k : κ,
          ρ.matrix q p * ρ.matrix i j * K k j i *
            (starRingEnd ℂ) (K k q p) := by
    rw [MatrixMap.choi_ofKraus]
    simp only [Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply,
      Finset.mul_sum, RCLike.star_def]
    repeat' apply Finset.sum_congr rfl; intro x hx
    ring
  rw [hexpand, hchoi]
  calc
    _ = ∑ i : d, ∑ k : κ, ∑ j : d, ∑ p : d, ∑ q : d,
          ρ.matrix q p * ρ.matrix i j * K k j i *
            (starRingEnd ℂ) (K k q p) := Finset.sum_comm
    _ = ∑ i : d, ∑ j : d, ∑ k : κ, ∑ p : d, ∑ q : d,
          ρ.matrix q p * ρ.matrix i j * K k j i *
            (starRingEnd ℂ) (K k q p) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ i : d, ∑ j : d, ∑ p : d, ∑ k : κ, ∑ q : d,
          ρ.matrix q p * ρ.matrix i j * K k j i *
            (starRingEnd ℂ) (K k q p) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm

/-- Entanglement fidelity has the Kraus-trace formula for every finite Kraus
representation of the channel. -/
theorem entanglementFidelity_eq_kraus_sum
    (ρ : State d) (E : Channel d d)
    {κ : Type v} [Fintype κ] (K : κ → CMatrix d)
    (hK : E.map = MatrixMap.ofKraus K) :
    entanglementFidelity ρ E =
      ∑ i : κ, Complex.normSq ((ρ.matrix * K i).trace) := by
  unfold entanglementFidelity
  apply Complex.ofReal_injective
  rw [krausTraceSum_eq_choiPairing ρ (canonicalKraus E),
    krausTraceSum_eq_choiPairing ρ K]
  rw [(map_eq_ofKraus_canonicalKraus E).symm.trans hK]

private def mixKraus {κ : Type v} [Fintype κ]
    (W : Matrix κ κ ℂ) (K : κ → CMatrix d) (a : κ) : CMatrix d :=
  ∑ i : κ, W a i • K i

private theorem ofKraus_mixKraus
    {κ : Type v} [Fintype κ] [DecidableEq κ]
    (W : Matrix.unitaryGroup κ ℂ) (K : κ → CMatrix d) :
    MatrixMap.ofKraus (mixKraus (W : Matrix κ κ ℂ) K) =
      MatrixMap.ofKraus K := by
  have hW (j i : κ) :
      (∑ a : κ, star ((W : Matrix κ κ ℂ) a j) *
        (W : Matrix κ κ ℂ) a i) = if j = i then 1 else 0 := by
    have hentry :=
      congrFun (congrFun (Matrix.UnitaryGroup.star_mul_self W) j) i
    simpa [Matrix.star_eq_conjTranspose, Matrix.mul_apply] using hentry
  apply LinearMap.ext
  intro X
  change
    (∑ a : κ, mixKraus (W : Matrix κ κ ℂ) K a * X *
      Matrix.conjTranspose (mixKraus (W : Matrix κ κ ℂ) K a)) =
        ∑ i : κ, K i * X * Matrix.conjTranspose (K i)
  simp only [mixKraus, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  calc
    _ = ∑ j : κ, ∑ a : κ, ∑ i : κ,
          (star ((W : Matrix κ κ ℂ) a j) *
            (W : Matrix κ κ ℂ) a i) •
              (K i * X * Matrix.conjTranspose (K j)) := Finset.sum_comm
    _ = ∑ j : κ, ∑ i : κ, ∑ a : κ,
          (star ((W : Matrix κ κ ℂ) a j) *
            (W : Matrix κ κ ℂ) a i) •
              (K i * X * Matrix.conjTranspose (K j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ j : κ, ∑ i : κ,
          ((∑ a : κ, star ((W : Matrix κ κ ℂ) a j) *
            (W : Matrix κ κ ℂ) a i) •
              (K i * X * Matrix.conjTranspose (K j))) := by
      simp only [Finset.sum_smul]
    _ = _ := by
      simp only [hW]
      simp

/-- A Kraus family may be chosen so that only one distinguished Kraus
operator contributes to the entanglement fidelity. -/
theorem exists_preferred_krausRepresentation
    (ρ : State d) (E : Channel d d)
    {κ : Type v} [Fintype κ] (K : κ → CMatrix d)
    (hK : E.map = MatrixMap.ofKraus K) :
    ∃ (Kpreferred : κ → CMatrix d) (first : κ),
      E.map = MatrixMap.ofKraus Kpreferred ∧
      entanglementFidelity ρ E =
        Complex.normSq ((ρ.matrix * Kpreferred first).trace) := by
  classical
  letI : Nonempty κ := by
    by_contra hκ
    haveI : IsEmpty κ := not_nonempty_iff.mp hκ
    have htrace := E.tracePreserving ρ.matrix
    rw [hK] at htrace
    simp [MatrixMap.ofKraus, ρ.trace_eq_one] at htrace
  let first : κ := Classical.choice (inferInstance : Nonempty κ)
  let z : EuclideanSpace ℂ κ :=
    WithLp.toLp 2 (fun i => (ρ.matrix * K i).trace)
  by_cases hz : z = 0
  · refine ⟨K, first, hK, ?_⟩
    rw [entanglementFidelity_eq_kraus_sum ρ E K hK]
    have hz_apply (i : κ) : (ρ.matrix * K i).trace = 0 := by
      have h := congrArg (fun w : EuclideanSpace ℂ κ => w i) hz
      simpa [z, PiLp.toLp_apply] using h
    simp [hz_apply]
  · let w : EuclideanSpace ℂ κ := (‖z‖ : ℂ)⁻¹ • z
    have hznorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hw_norm : ‖w‖ = 1 := by
      simp [w, norm_smul, hznorm]
    have hw_orth :
        Orthonormal ℂ (({first} : Set κ).restrict (fun _ => w)) := by
      rw [orthonormal_subsingleton_iff]
      intro i
      simpa using hw_norm
    obtain ⟨b, hb⟩ :=
      hw_orth.exists_orthonormalBasis_extension_of_card_eq
        (E := EuclideanSpace ℂ κ) (ι := κ) (by simp)
    have hbfirst : b first = w := hb first (by simp)
    let M : Matrix.unitaryGroup κ ℂ :=
      ⟨(EuclideanSpace.basisFun κ ℂ).toBasis.toMatrix b,
        (EuclideanSpace.basisFun κ ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
    let W := M⁻¹
    let Kpreferred : κ → CMatrix d :=
      mixKraus (W : Matrix κ κ ℂ) K
    have hcoeff :
        ∑ i : κ, (W : Matrix κ κ ℂ) first i * z i =
          (‖z‖ : ℂ) := by
      have hWfirst (i : κ) :
          (W : Matrix κ κ ℂ) first i = star (b first i) := by
        simp [W, M, Module.Basis.toMatrix]
      simp_rw [hWfirst, hbfirst]
      simp only [w, PiLp.smul_apply, smul_eq_mul, map_mul, map_inv₀,
        RCLike.star_def]
      have hstarNorm :
          (starRingEnd ℂ) (‖z‖ : ℂ) = (‖z‖ : ℂ) := by
        change star (‖z‖ : ℂ) = (‖z‖ : ℂ)
        simp
      rw [hstarNorm]
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [show (∑ i : κ, (starRingEnd ℂ) (z i) * z i) =
          (‖z‖ : ℂ) ^ 2 by
        calc
          _ = ∑ i : κ, z i * (starRingEnd ℂ) (z i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by
            simpa only [PiLp.inner_apply, RCLike.inner_apply] using
              (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z)]
      have hznorm' : (‖z‖ : ℂ) ≠ 0 := by
        exact_mod_cast hznorm
      field_simp
    have htrace :
        (ρ.matrix * Kpreferred first).trace = (‖z‖ : ℂ) := by
      calc
        _ = ∑ i : κ, (W : Matrix κ κ ℂ) first i *
              (ρ.matrix * K i).trace := by
          simp [Kpreferred, mixKraus, Matrix.mul_sum, Matrix.trace_sum,
            Matrix.trace_smul, smul_eq_mul]
        _ = _ := by simpa [z, PiLp.toLp_apply] using hcoeff
    have hsumNormSq :
        (∑ i : κ, Complex.normSq (z i)) =
          Complex.normSq (‖z‖ : ℂ) := by
      apply Complex.ofReal_injective
      simp only [Complex.ofReal_sum]
      simp_rw [Complex.normSq_eq_conj_mul_self]
      have hsum :
          (∑ i : κ, (starRingEnd ℂ) (z i) * z i) =
            (‖z‖ : ℂ) ^ 2 := by
        calc
          _ = ∑ i : κ, z i * (starRingEnd ℂ) (z i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by
            simpa only [PiLp.inner_apply, RCLike.inner_apply] using
              (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z)
      rw [hsum]
      norm_num [Complex.normSq]
      ring
    refine
      ⟨Kpreferred, first,
        hK.trans (ofKraus_mixKraus W K).symm, ?_⟩
    rw [entanglementFidelity_eq_kraus_sum ρ E K hK, htrace]
    simpa [z, PiLp.toLp_apply] using hsumNormSq

/-- The linear map obtained by correcting the output of `E` with the inverse
of the target unitary `U`. -/
def effectiveMap (E : Channel d d) (U : Matrix.unitaryGroup d ℂ) :
    MatrixMap d d where
  toFun X :=
    Matrix.conjTranspose (U : CMatrix d) * E.map X * (U : CMatrix d)
  map_add' X Y := by
    simp only [map_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    change
      Matrix.conjTranspose (U : CMatrix d) * E.map (c • X) *
          (U : CMatrix d) =
        c • (Matrix.conjTranspose (U : CMatrix d) * E.map X *
          (U : CMatrix d))
    rw [map_smul]
    simp only [Matrix.mul_smul, Matrix.smul_mul]

private theorem effectiveMap_eq_ofKraus
    (E : Channel d d) (U : Matrix.unitaryGroup d ℂ)
    {κ : Type v} [Fintype κ] (K : κ → CMatrix d)
    (hK : E.map = MatrixMap.ofKraus K) :
    effectiveMap E U =
      MatrixMap.ofKraus
        (fun i => Matrix.conjTranspose (U : CMatrix d) * K i) := by
  apply LinearMap.ext
  intro X
  change
    Matrix.conjTranspose (U : CMatrix d) * E.map X * (U : CMatrix d) = _
  rw [hK]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mul_assoc]

/-- Unitary output correction preserves complete positivity. -/
theorem effectiveMap_isCompletelyPositive
    (E : Channel d d) (U : Matrix.unitaryGroup d ℂ) :
    MatrixMap.IsCompletelyPositive (effectiveMap E U) := by
  rw [effectiveMap_eq_ofKraus E U (canonicalKraus E)
    (map_eq_ofKraus_canonicalKraus E)]
  exact MatrixMap.ofKraus_completelyPositive _

/-- Unitary output correction preserves the trace. -/
theorem effectiveMap_isTracePreserving
    (E : Channel d d) (U : Matrix.unitaryGroup d ℂ) :
    MatrixMap.IsTracePreserving (effectiveMap E U) := by
  intro X
  change
    (Matrix.conjTranspose (U : CMatrix d) * E.map X *
      (U : CMatrix d)).trace = X.trace
  calc
    _ = (((U : CMatrix d) * Matrix.conjTranspose (U : CMatrix d)) *
          E.map X).trace := by
      rw [Matrix.trace_mul_cycle]
    _ = (E.map X).trace := by
      rw [show
        (U : CMatrix d) * Matrix.conjTranspose (U : CMatrix d) = 1 by
          simpa [Matrix.star_eq_conjTranspose] using U.property.2]
      simp
    _ = X.trace := E.tracePreserving X

/-- Unitary output correction maps positive semidefinite matrices to positive
semidefinite matrices. -/
theorem effectiveMap_mapsPositive
    (E : Channel d d) (U : Matrix.unitaryGroup d ℂ) :
    ∀ X : CMatrix d, X.PosSemidef → (effectiveMap E U X).PosSemidef := by
  intro X hX
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same
    (E.mapsPositive X hX) (U : CMatrix d)

/-- The effective noisy channel
`ρ ↦ U† E(ρ) U` relative to a target unitary gate `U`. -/
noncomputable def effectiveChannel
    (E : Channel d d) (U : Matrix.unitaryGroup d ℂ) : Channel d d where
  map := effectiveMap E U
  completelyPositive := effectiveMap_isCompletelyPositive E U
  tracePreserving := effectiveMap_isTracePreserving E U
  mapsPositive := effectiveMap_mapsPositive E U

/-- The effective channel acts by the stated unitary output correction. -/
theorem effectiveChannel_apply
    (E : Channel d d) (U : Matrix.unitaryGroup d ℂ) (ρ : State d) :
    (effectiveChannel E U).map ρ.matrix =
      Matrix.conjTranspose (U : CMatrix d) * E.map ρ.matrix *
        (U : CMatrix d) := by
  rfl

/-- The standard pure-state gate fidelity
`⟨ψ| U† E(|ψ⟩⟨ψ|) U |ψ⟩`.

The matrix expectation is complex-valued syntactically; its real part is the
real fidelity scalar. -/
noncomputable def pureStateGateFidelity
    (ψ : PureVector d) (E : Channel d d)
    (U : Matrix.unitaryGroup d ℂ) : ℝ :=
  Complex.re
    ((ψ.state.matrix *
      (Matrix.conjTranspose (U : CMatrix d) * E.map ψ.state.matrix *
        (U : CMatrix d))).trace)

private theorem pureState_sandwich (ψ : PureVector d) (A : CMatrix d) :
    ψ.state.matrix * A * ψ.state.matrix =
      (ψ.state.matrix * A).trace • ψ.state.matrix := by
  ext r s
  simp only [PureVector.state_matrix, rankOneMatrix_apply, Matrix.mul_apply,
    Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pureState_trace_conjTranspose
    (ψ : PureVector d) (A : CMatrix d) :
    (ψ.state.matrix * Matrix.conjTranspose A).trace =
      star ((ψ.state.matrix * A).trace) := by
  calc
    _ = (Matrix.conjTranspose A * ψ.state.matrix).trace :=
      Matrix.trace_mul_comm _ _
    _ = (Matrix.conjTranspose (ψ.state.matrix * A)).trace := by
      rw [Matrix.conjTranspose_mul, ψ.state_matrix_conjTranspose]
    _ = _ := Matrix.trace_conjTranspose _

private theorem normSq_pureState_trace_eq_re_sandwich
    (ψ : PureVector d) (A : CMatrix d) :
    Complex.normSq ((ψ.state.matrix * A).trace) =
      Complex.re ((ψ.state.matrix * A * ψ.state.matrix *
        Matrix.conjTranspose A).trace) := by
  have hcomplex :
      (ψ.state.matrix * A * ψ.state.matrix *
          Matrix.conjTranspose A).trace =
        (Complex.normSq ((ψ.state.matrix * A).trace) : ℂ) := by
    calc
      _ = (((ψ.state.matrix * A).trace • ψ.state.matrix) *
          Matrix.conjTranspose A).trace := by
        rw [pureState_sandwich]
      _ = (ψ.state.matrix * A).trace *
          (ψ.state.matrix * Matrix.conjTranspose A).trace := by
        simp [Matrix.trace_smul, smul_eq_mul]
      _ = (ψ.state.matrix * A).trace *
          star ((ψ.state.matrix * A).trace) := by
        rw [pureState_trace_conjTranspose]
      _ = _ := by
        rw [RCLike.star_def, Complex.normSq_eq_conj_mul_self]
        ring
  rw [hcomplex]
  simp

/-- For a pure input state, entanglement fidelity of the effective noisy
channel is the standard pure-state gate fidelity. -/
theorem entanglementFidelity_effectiveChannel_eq_pureStateGateFidelity
    (ρ : State d) (ψ : PureVector d) (hρ : ρ = ψ.state)
    (E : Channel d d)
    {κ : Type v} [Fintype κ] (K : κ → CMatrix d)
    (hK : E.map = MatrixMap.ofKraus K)
    (U : Matrix.unitaryGroup d ℂ) :
    entanglementFidelity ρ (effectiveChannel E U) =
      pureStateGateFidelity ψ E U := by
  subst ρ
  let A : κ → CMatrix d :=
    fun i => Matrix.conjTranspose (U : CMatrix d) * K i
  have hEffective :
      (effectiveChannel E U).map = MatrixMap.ofKraus A := by
    change effectiveMap E U = MatrixMap.ofKraus A
    exact effectiveMap_eq_ofKraus E U K hK
  rw [entanglementFidelity_eq_kraus_sum
    ψ.state (effectiveChannel E U) A hEffective]
  unfold pureStateGateFidelity
  change
    (∑ i : κ, Complex.normSq ((ψ.state.matrix * A i).trace)) =
      Complex.re
        ((ψ.state.matrix * effectiveMap E U ψ.state.matrix).trace)
  rw [effectiveMap_eq_ofKraus E U K hK]
  change
    (∑ i : κ, Complex.normSq ((ψ.state.matrix * A i).trace)) =
      Complex.re
        ((ψ.state.matrix *
          (∑ i : κ, A i * ψ.state.matrix *
            Matrix.conjTranspose (A i))).trace)
  rw [Matrix.mul_sum, Matrix.trace_sum]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Matrix.mul_assoc] using
    normSq_pureState_trace_eq_re_sandwich ψ (A i)

end

end QITFormalized.ChannelFidelityGateFidelityPureInputState
