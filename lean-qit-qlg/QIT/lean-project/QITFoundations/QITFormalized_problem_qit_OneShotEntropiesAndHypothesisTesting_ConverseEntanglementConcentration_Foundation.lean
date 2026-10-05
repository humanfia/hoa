import QITBench.Base.OneShot

/-!
# Foundation for the converse to entanglement concentration

This file supplies the recursive finite-round LOCC semantics used by the
formalization target and begins the missing operational bridge by connecting
that semantics to the product-Kraus `LOCCProtocol` surface in `QITBench`.
-/

open scoped BigOperators ComplexOrder MatrixOrder Topology
open Filter

namespace QITFormalized.OneShotEntropiesAndHypothesisTesting.ConverseEntanglementConcentration

open QITBench QITBench.OneShot

noncomputable section

universe u v w x y z

/-! ## Project-local Mathlib supplement — finite-round LOCC -/

/-- A finite-outcome local quantum instrument, with one Kraus label per
classical outcome branch. -/
structure LocalInstrument
    (X : Type u) (A : Type v) (A' : Type w)
    [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A]
    [Fintype A'] [DecidableEq A'] where
  krausCount : ℕ
  outcome : Fin krausCount → X
  kraus : Fin krausCount → Matrix A' A ℂ
  tracePreserving :
    MatrixMap.IsTracePreserving (MatrixMap.ofKraus kraus)

namespace LocalInstrument

variable
    {X : Type u} {A : Type v} {A' : Type w}
    [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A]
    [Fintype A'] [DecidableEq A']

/-- The completely positive branch map selected by a classical instrument
outcome. -/
noncomputable def branchMap (I : LocalInstrument X A A') (x : X) :
    MatrixMap A A' := by
  exact MatrixMap.ofKraus
    (fun k : {k : Fin I.krausCount // I.outcome k = x} => I.kraus k.1)

end LocalInstrument

/-- Semantics of an Alice-to-Bob finite-outcome conditional LOCC round. -/
noncomputable def leftConditionalMap
    {X : Type u} {A : Type v} {A₁ : Type w}
    {B : Type x} {A' : Type y} {B' : Type z}
    [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A]
    [Fintype A₁] [DecidableEq A₁]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (I : LocalInstrument X A A₁)
    (next : X → Channel (A₁ × B) (A' × B')) :
    MatrixMap (A × B) (A' × B') :=
  ∑ outcome : X,
    (next outcome).map.comp
      (MatrixMap.kron (I.branchMap outcome)
        (LinearMap.id : MatrixMap B B))

/-- Semantics of a Bob-to-Alice finite-outcome conditional LOCC round. -/
noncomputable def rightConditionalMap
    {X : Type u} {A : Type v} {B : Type w}
    {B₁ : Type x} {A' : Type y} {B' : Type z}
    [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype B₁] [DecidableEq B₁]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (I : LocalInstrument X B B₁)
    (next : X → Channel (A × B₁) (A' × B')) :
    MatrixMap (A × B) (A' × B') :=
  ∑ outcome : X,
    (next outcome).map.comp
      (MatrixMap.kron (LinearMap.id : MatrixMap A A)
        (I.branchMap outcome))

/-- `Λ` admits a finite adaptive LOCC implementation with at most `rounds`
classical-message rounds. -/
def IsLOCCInRounds
    (rounds : ℕ)
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (Λ : Channel (A × B) (A' × B')) : Prop :=
  match rounds with
  | 0 =>
      ∃ (left : Channel A A') (right : Channel B B'),
        Λ.map = (left.prod right).map
  | rounds + 1 =>
      (∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X)
          (A₁ : Type u) (_ : Fintype A₁) (_ : DecidableEq A₁)
          (I : LocalInstrument X A A₁)
          (next : X → Channel (A₁ × B) (A' × B')),
          (∀ outcome : X, IsLOCCInRounds rounds (next outcome)) ∧
            Λ.map = leftConditionalMap I next) ∨
      (∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X)
          (B₁ : Type v) (_ : Fintype B₁) (_ : DecidableEq B₁)
          (I : LocalInstrument X B B₁)
          (next : X → Channel (A × B₁) (A' × B')),
          (∀ outcome : X, IsLOCCInRounds rounds (next outcome)) ∧
            Λ.map = rightConditionalMap I next)
termination_by rounds

/-- A channel is finite-round LOCC when it has a finite recursive
instrument-and-communication certificate. -/
def IsFiniteRoundLOCC
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (Λ : Channel (A × B) (A' × B')) : Prop :=
  ∃ rounds : ℕ, IsLOCCInRounds rounds Λ

/-! ## Project-local Mathlib supplement — entropy and asymptotic reduction -/

/-- The finite-dimensional von Neumann entropy in bits. -/
noncomputable def vonNeumannEntropy
    {A : Type u} [Fintype A] [DecidableEq A]
    (ρ : State A) : ℝ :=
  -∑ i : A,
    ρ.pos.isHermitian.eigenvalues i * log2 (ρ.pos.isHermitian.eigenvalues i)

/-- Entanglement entropy of a normalized bipartite pure state. -/
noncomputable def entanglementEntropy
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) : ℝ :=
  vonNeumannEntropy ψ.state.marginalA

/-- Convergence of a real sequence to one eventually puts it strictly above
every fixed constant below one. -/
theorem eventually_lt_of_tendsto_one
    (f : ℕ → ℝ)
    (hf : Tendsto f atTop (𝓝 1))
    {c : ℝ} (hc : c < 1) :
    ∀ᶠ n in atTop, c < f n :=
  hf (Ioi_mem_nhds hc)

/-- A uniform fidelity gap above every forbidden rate converts convergence
to unit fidelity into the eventual-upper-bound form of the asymptotic rate
converse. -/
theorem asymptoticRateAtMost_of_eventual_fidelity_gap
    (entropy : ℝ)
    (M : ℕ → ℕ)
    (fidelity : ℕ → ℝ)
    (hfidelity : Tendsto fidelity atTop (𝓝 1))
    (hgap : ∀ R : ℝ,
      entropy < R →
        ∃ c : ℝ, c < 1 ∧
          ∀ᶠ n in atTop,
            concentrationRate M n > R → fidelity n ≤ c) :
    AsymptoticRateAtMost entropy M := by
  intro R hR
  obtain ⟨c, hc, hgapR⟩ := hgap R hR
  have hfidelityR := eventually_lt_of_tendsto_one fidelity hfidelity hc
  filter_upwards [hfidelityR, hgapR] with n hcfidelity hn
  by_contra hnR
  exact (not_lt_of_ge (hn (lt_of_not_ge hnR))) hcfidelity

private theorem ofKraus_product
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    {κ : Type y} {ι : Type z} [Fintype κ] [Fintype ι]
    (K : κ → Matrix A' A ℂ) (L : ι → Matrix B' B ℂ) :
    MatrixMap.ofKraus
        (fun ki : κ × ι => Matrix.kronecker (K ki.1) (L ki.2)) =
      MatrixMap.kron (MatrixMap.ofKraus K) (MatrixMap.ofKraus L) := by
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single (MatrixMap.ofKraus _) X,
    MatrixMap.map_eq_sum_single (MatrixMap.kron _ _) X]
  apply Finset.sum_congr rfl
  intro ab _
  apply Finset.sum_congr rfl
  intro ab' _
  congr 1
  rw [QITBench.single_prod_eq_kronecker_single,
    MatrixMap.kron_apply_kronecker]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Fintype.sum_prod_type]
  ext a'b' a'b''
  simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

private theorem ofKraus_one_eq_id
    {A : Type u} [Fintype A] [DecidableEq A] :
    MatrixMap.ofKraus (fun _ : Unit => (1 : CMatrix A)) =
      (LinearMap.id : MatrixMap A A) := by
  ext X i j
  simp [MatrixMap.ofKraus]

private theorem ofKraus_kron_id
    {A : Type u} {B : Type v} {A' : Type w}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    {κ : Type y} [Fintype κ]
    (K : κ → Matrix A' A ℂ) :
    MatrixMap.ofKraus
        (fun k : κ => Matrix.kronecker (K k) (1 : CMatrix B)) =
      MatrixMap.kron (MatrixMap.ofKraus K)
        (LinearMap.id : MatrixMap B B) := by
  calc
    MatrixMap.ofKraus
        (fun k : κ => Matrix.kronecker (K k) (1 : CMatrix B)) =
        MatrixMap.ofKraus (fun ku : κ × Unit =>
          Matrix.kronecker (K ku.1) (1 : CMatrix B)) := by
            ext X i j
            simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk]
            rw [Fintype.sum_prod_type]
            simp
    _ = MatrixMap.kron (MatrixMap.ofKraus K)
          (MatrixMap.ofKraus (fun _ : Unit => (1 : CMatrix B))) :=
      ofKraus_product K (fun _ : Unit => (1 : CMatrix B))
    _ = MatrixMap.kron (MatrixMap.ofKraus K)
          (LinearMap.id : MatrixMap B B) := by rw [ofKraus_one_eq_id]

private theorem ofKraus_id_kron
    {A : Type u} {B : Type v} {B' : Type w}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B']
    {κ : Type y} [Fintype κ]
    (K : κ → Matrix B' B ℂ) :
    MatrixMap.ofKraus
        (fun k : κ => Matrix.kronecker (1 : CMatrix A) (K k)) =
      MatrixMap.kron (LinearMap.id : MatrixMap A A)
        (MatrixMap.ofKraus K) := by
  calc
    MatrixMap.ofKraus
        (fun k : κ => Matrix.kronecker (1 : CMatrix A) (K k)) =
        MatrixMap.ofKraus (fun uk : Unit × κ =>
          Matrix.kronecker (1 : CMatrix A) (K uk.2)) := by
            ext X i j
            simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk]
            rw [Fintype.sum_prod_type]
            simp
    _ = MatrixMap.kron
          (MatrixMap.ofKraus (fun _ : Unit => (1 : CMatrix A)))
          (MatrixMap.ofKraus K) :=
      ofKraus_product (fun _ : Unit => (1 : CMatrix A)) K
    _ = MatrixMap.kron (LinearMap.id : MatrixMap A A)
          (MatrixMap.ofKraus K) := by rw [ofKraus_one_eq_id]

private theorem ofKraus_reindex
    {A : Type u} {A' : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype A'] [DecidableEq A']
    {κ : Type w} {ι : Type x} [Fintype κ] [Fintype ι]
    (e : κ ≃ ι) (K : κ → Matrix A' A ℂ) :
    MatrixMap.ofKraus (fun i : ι => K (e.symm i)) =
      MatrixMap.ofKraus K := by
  apply LinearMap.ext
  intro Z
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk]
  exact e.symm.sum_comp
    (fun k => K k * Z * (K k).conjTranspose)

private theorem exists_separable_protocol_of_leftConditional
    {X : Type u} {A : Type v} {A₁ : Type w}
    {B : Type x} {A' : Type y} {B' : Type z}
    [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A]
    [Fintype A₁] [DecidableEq A₁]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (I : LocalInstrument X A A₁)
    (next : X → Channel (A₁ × B) (A' × B'))
    (hnext : ∀ outcome : X,
      ∃ P : LOCCProtocol.{w, x, y, z, 0} A₁ B A' B',
        P.channel.map = (next outcome).map)
    (Λ : Channel (A × B) (A' × B'))
    (hΛ : Λ.map = leftConditionalMap I next) :
    ∃ P : LOCCProtocol.{v, x, y, z, 0} A B A' B',
      P.channel.map = Λ.map := by
  classical
  choose P hP using hnext
  letI protocolIndexFintype (outcome : X) :
      Fintype (P outcome).KrausIndex :=
    (P outcome).fintypeKrausIndex
  let Branch (outcome : X) :=
    {k : Fin I.krausCount // I.outcome k = outcome}
  let Index := Σ outcome : X, Branch outcome × (P outcome).KrausIndex
  letI : Fintype Index := by
    dsimp only [Index, Branch]
    infer_instance
  let leftKraus : Index → Matrix A' A ℂ :=
    fun index =>
      (P index.1).leftKraus index.2.2 * I.kraus index.2.1.1
  let rightKraus : Index → Matrix B' B ℂ :=
    fun index => (P index.1).rightKraus index.2.2
  have hbranch (outcome : X) :
      MatrixMap.ofKraus
          (fun kp : Branch outcome × (P outcome).KrausIndex =>
            Matrix.kronecker
              ((P outcome).leftKraus kp.2 * I.kraus kp.1.1)
              ((P outcome).rightKraus kp.2)) =
        (next outcome).map.comp
          (MatrixMap.kron (I.branchMap outcome)
            (LinearMap.id : MatrixMap B B)) := by
    rw [← hP outcome]
    change MatrixMap.ofKraus _ =
      (MatrixMap.ofKraus (P outcome).productKraus).comp
        (MatrixMap.kron
          (MatrixMap.ofKraus
            (fun k : Branch outcome => I.kraus k.1))
          (LinearMap.id : MatrixMap B B))
    rw [← ofKraus_kron_id
      (fun k : Branch outcome => I.kraus k.1)]
    rw [MatrixMap.ofKraus_comp_ofKraus]
    congr 1
    funext kp
    change
      Matrix.kronecker
          ((P outcome).leftKraus kp.2 * I.kraus kp.1.1)
          ((P outcome).rightKraus kp.2) =
        Matrix.kronecker
            ((P outcome).leftKraus kp.2)
            ((P outcome).rightKraus kp.2) *
          Matrix.kronecker (I.kraus kp.1.1) (1 : CMatrix B)
    simpa using
      (Matrix.mul_kronecker_mul
        ((P outcome).leftKraus kp.2) (I.kraus kp.1.1)
        ((P outcome).rightKraus kp.2) (1 : CMatrix B))
  have hsplit :
      MatrixMap.ofKraus
          (fun index : Index =>
            Matrix.kronecker (leftKraus index) (rightKraus index)) =
        ∑ outcome : X,
          MatrixMap.ofKraus
            (fun kp : Branch outcome × (P outcome).KrausIndex =>
              Matrix.kronecker
                ((P outcome).leftKraus kp.2 * I.kraus kp.1.1)
                ((P outcome).rightKraus kp.2)) := by
    apply LinearMap.ext
    intro Z
    simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.sum_apply]
    change
      (∑ index : Σ outcome : X,
          Branch outcome × (P outcome).KrausIndex,
        Matrix.kronecker
              ((P index.1).leftKraus index.2.2 *
                I.kraus index.2.1.1)
              ((P index.1).rightKraus index.2.2) *
            Z *
          (Matrix.kronecker
              ((P index.1).leftKraus index.2.2 *
                I.kraus index.2.1.1)
              ((P index.1).rightKraus index.2.2)).conjTranspose) =
        ∑ outcome : X, ∑ kp :
            Branch outcome × (P outcome).KrausIndex,
          Matrix.kronecker
                ((P outcome).leftKraus kp.2 * I.kraus kp.1.1)
                ((P outcome).rightKraus kp.2) *
              Z *
            (Matrix.kronecker
                ((P outcome).leftKraus kp.2 * I.kraus kp.1.1)
                ((P outcome).rightKraus kp.2)).conjTranspose
    exact Fintype.sum_sigma
      (fun index : Σ outcome : X,
          Branch outcome × (P outcome).KrausIndex =>
        Matrix.kronecker
              ((P index.1).leftKraus index.2.2 *
                I.kraus index.2.1.1)
              ((P index.1).rightKraus index.2.2) *
            Z *
          (Matrix.kronecker
              ((P index.1).leftKraus index.2.2 *
                I.kraus index.2.1.1)
              ((P index.1).rightKraus index.2.2)).conjTranspose)
  have hmap :
      MatrixMap.ofKraus
          (fun index : Index =>
            Matrix.kronecker (leftKraus index) (rightKraus index)) =
        leftConditionalMap I next := by
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro outcome _
    exact hbranch outcome
  let indexEquiv : Index ≃ Fin (Fintype.card Index) :=
    Fintype.equivFin Index
  have hreindex :
      MatrixMap.ofKraus
          (fun k : Fin (Fintype.card Index) =>
            Matrix.kronecker
              (leftKraus (indexEquiv.symm k))
              (rightKraus (indexEquiv.symm k))) =
        MatrixMap.ofKraus
          (fun index : Index =>
            Matrix.kronecker (leftKraus index) (rightKraus index)) :=
    ofKraus_reindex indexEquiv
      (fun index : Index =>
        Matrix.kronecker (leftKraus index) (rightKraus index))
  let protocol : LOCCProtocol.{v, x, y, z, 0} A B A' B' := {
    KrausIndex := Fin (Fintype.card Index)
    fintypeKrausIndex := inferInstance
    leftKraus := fun k => leftKraus (indexEquiv.symm k)
    rightKraus := fun k => rightKraus (indexEquiv.symm k)
    tracePreserving := by
      rw [hreindex, hmap, ← hΛ]
      exact Λ.tracePreserving
  }
  refine ⟨protocol, ?_⟩
  change
    MatrixMap.ofKraus
        (fun k : Fin (Fintype.card Index) =>
          Matrix.kronecker
            (leftKraus (indexEquiv.symm k))
            (rightKraus (indexEquiv.symm k))) =
      Λ.map
  rw [hreindex]
  exact hmap.trans hΛ.symm

private theorem exists_separable_protocol_of_rightConditional
    {X : Type u} {A : Type v} {B : Type w}
    {B₁ : Type x} {A' : Type y} {B' : Type z}
    [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype B₁] [DecidableEq B₁]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (I : LocalInstrument X B B₁)
    (next : X → Channel (A × B₁) (A' × B'))
    (hnext : ∀ outcome : X,
      ∃ P : LOCCProtocol.{v, x, y, z, 0} A B₁ A' B',
        P.channel.map = (next outcome).map)
    (Λ : Channel (A × B) (A' × B'))
    (hΛ : Λ.map = rightConditionalMap I next) :
    ∃ P : LOCCProtocol.{v, w, y, z, 0} A B A' B',
      P.channel.map = Λ.map := by
  classical
  choose P hP using hnext
  letI protocolIndexFintype (outcome : X) :
      Fintype (P outcome).KrausIndex :=
    (P outcome).fintypeKrausIndex
  let Branch (outcome : X) :=
    {k : Fin I.krausCount // I.outcome k = outcome}
  let Index := Σ outcome : X, Branch outcome × (P outcome).KrausIndex
  letI : Fintype Index := by
    dsimp only [Index, Branch]
    infer_instance
  let leftKraus : Index → Matrix A' A ℂ :=
    fun index => (P index.1).leftKraus index.2.2
  let rightKraus : Index → Matrix B' B ℂ :=
    fun index =>
      (P index.1).rightKraus index.2.2 * I.kraus index.2.1.1
  have hbranch (outcome : X) :
      MatrixMap.ofKraus
          (fun kp : Branch outcome × (P outcome).KrausIndex =>
            Matrix.kronecker
              ((P outcome).leftKraus kp.2)
              ((P outcome).rightKraus kp.2 * I.kraus kp.1.1)) =
        (next outcome).map.comp
          (MatrixMap.kron (LinearMap.id : MatrixMap A A)
            (I.branchMap outcome)) := by
    rw [← hP outcome]
    change MatrixMap.ofKraus _ =
      (MatrixMap.ofKraus (P outcome).productKraus).comp
        (MatrixMap.kron
          (LinearMap.id : MatrixMap A A)
          (MatrixMap.ofKraus
            (fun k : Branch outcome => I.kraus k.1)))
    rw [← ofKraus_id_kron
      (fun k : Branch outcome => I.kraus k.1)]
    rw [MatrixMap.ofKraus_comp_ofKraus]
    congr 1
    funext kp
    change
      Matrix.kronecker
          ((P outcome).leftKraus kp.2)
          ((P outcome).rightKraus kp.2 * I.kraus kp.1.1) =
        Matrix.kronecker
            ((P outcome).leftKraus kp.2)
            ((P outcome).rightKraus kp.2) *
          Matrix.kronecker (1 : CMatrix A) (I.kraus kp.1.1)
    simpa using
      (Matrix.mul_kronecker_mul
        ((P outcome).leftKraus kp.2) (1 : CMatrix A)
        ((P outcome).rightKraus kp.2) (I.kraus kp.1.1))
  have hsplit :
      MatrixMap.ofKraus
          (fun index : Index =>
            Matrix.kronecker (leftKraus index) (rightKraus index)) =
        ∑ outcome : X,
          MatrixMap.ofKraus
            (fun kp : Branch outcome × (P outcome).KrausIndex =>
              Matrix.kronecker
                ((P outcome).leftKraus kp.2)
                ((P outcome).rightKraus kp.2 * I.kraus kp.1.1)) := by
    apply LinearMap.ext
    intro Z
    simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.sum_apply]
    change
      (∑ index : Σ outcome : X,
          Branch outcome × (P outcome).KrausIndex,
        Matrix.kronecker
              ((P index.1).leftKraus index.2.2)
              ((P index.1).rightKraus index.2.2 *
                I.kraus index.2.1.1) *
            Z *
          (Matrix.kronecker
              ((P index.1).leftKraus index.2.2)
              ((P index.1).rightKraus index.2.2 *
                I.kraus index.2.1.1)).conjTranspose) =
        ∑ outcome : X, ∑ kp :
            Branch outcome × (P outcome).KrausIndex,
          Matrix.kronecker
                ((P outcome).leftKraus kp.2)
                ((P outcome).rightKraus kp.2 * I.kraus kp.1.1) *
              Z *
            (Matrix.kronecker
                ((P outcome).leftKraus kp.2)
                ((P outcome).rightKraus kp.2 *
                  I.kraus kp.1.1)).conjTranspose
    exact Fintype.sum_sigma
      (fun index : Σ outcome : X,
          Branch outcome × (P outcome).KrausIndex =>
        Matrix.kronecker
              ((P index.1).leftKraus index.2.2)
              ((P index.1).rightKraus index.2.2 *
                I.kraus index.2.1.1) *
            Z *
          (Matrix.kronecker
              ((P index.1).leftKraus index.2.2)
              ((P index.1).rightKraus index.2.2 *
                I.kraus index.2.1.1)).conjTranspose)
  have hmap :
      MatrixMap.ofKraus
          (fun index : Index =>
            Matrix.kronecker (leftKraus index) (rightKraus index)) =
        rightConditionalMap I next := by
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro outcome _
    exact hbranch outcome
  let indexEquiv : Index ≃ Fin (Fintype.card Index) :=
    Fintype.equivFin Index
  have hreindex :
      MatrixMap.ofKraus
          (fun k : Fin (Fintype.card Index) =>
            Matrix.kronecker
              (leftKraus (indexEquiv.symm k))
              (rightKraus (indexEquiv.symm k))) =
        MatrixMap.ofKraus
          (fun index : Index =>
            Matrix.kronecker (leftKraus index) (rightKraus index)) :=
    ofKraus_reindex indexEquiv
      (fun index : Index =>
        Matrix.kronecker (leftKraus index) (rightKraus index))
  let protocol : LOCCProtocol.{v, w, y, z, 0} A B A' B' := {
    KrausIndex := Fin (Fintype.card Index)
    fintypeKrausIndex := inferInstance
    leftKraus := fun k => leftKraus (indexEquiv.symm k)
    rightKraus := fun k => rightKraus (indexEquiv.symm k)
    tracePreserving := by
      rw [hreindex, hmap, ← hΛ]
      exact Λ.tracePreserving
  }
  refine ⟨protocol, ?_⟩
  change
    MatrixMap.ofKraus
        (fun k : Fin (Fintype.card Index) =>
          Matrix.kronecker
            (leftKraus (indexEquiv.symm k))
            (rightKraus (indexEquiv.symm k))) =
      Λ.map
  rw [hreindex]
  exact hmap.trans hΛ.symm

private theorem exists_separable_protocol_of_product
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (left : Channel A A') (right : Channel B B')
    (Λ : Channel (A × B) (A' × B'))
    (hΛ : Λ.map = (left.prod right).map) :
    ∃ P : LOCCProtocol.{u, v, w, x, 0} A B A' B',
      P.channel.map = Λ.map := by
  classical
  obtain ⟨K, hK⟩ :=
    MatrixMap.exists_kraus_of_choi_psd left.map left.completelyPositive
  obtain ⟨L, hL⟩ :=
    MatrixMap.exists_kraus_of_choi_psd right.map right.completelyPositive
  let Index := (A × A') × (B × B')
  let leftKraus : Index → Matrix A' A ℂ := fun index => K index.1
  let rightKraus : Index → Matrix B' B ℂ := fun index => L index.2
  have hmap :
      MatrixMap.ofKraus
          (fun index : Index =>
            Matrix.kronecker (leftKraus index) (rightKraus index)) =
        Λ.map := by
    calc
      MatrixMap.ofKraus
          (fun index : Index =>
            Matrix.kronecker (leftKraus index) (rightKraus index)) =
          MatrixMap.kron (MatrixMap.ofKraus K)
            (MatrixMap.ofKraus L) :=
        ofKraus_product K L
      _ = MatrixMap.kron left.map right.map := by rw [hK, hL]
      _ = (left.prod right).map := rfl
      _ = Λ.map := hΛ.symm
  let indexEquiv : Index ≃ Fin (Fintype.card Index) :=
    Fintype.equivFin Index
  have hreindex :
      MatrixMap.ofKraus
          (fun k : Fin (Fintype.card Index) =>
            Matrix.kronecker
              (leftKraus (indexEquiv.symm k))
              (rightKraus (indexEquiv.symm k))) =
        MatrixMap.ofKraus
          (fun index : Index =>
            Matrix.kronecker (leftKraus index) (rightKraus index)) :=
    ofKraus_reindex indexEquiv
      (fun index : Index =>
        Matrix.kronecker (leftKraus index) (rightKraus index))
  let protocol : LOCCProtocol.{u, v, w, x, 0} A B A' B' := {
    KrausIndex := Fin (Fintype.card Index)
    fintypeKrausIndex := inferInstance
    leftKraus := fun k => leftKraus (indexEquiv.symm k)
    rightKraus := fun k => rightKraus (indexEquiv.symm k)
    tracePreserving := by
      rw [hreindex, hmap]
      exact Λ.tracePreserving
  }
  refine ⟨protocol, ?_⟩
  change
    MatrixMap.ofKraus
        (fun k : Fin (Fintype.card Index) =>
          Matrix.kronecker
            (leftKraus (indexEquiv.symm k))
            (rightKraus (indexEquiv.symm k))) =
      Λ.map
  rw [hreindex]
  exact hmap

/-- Every recursive finite-round LOCC certificate expands to the concrete
finite product-Kraus protocol surface used by `QITBench.OneShot`. -/
theorem IsLOCCInRounds.exists_separable_protocol
    {rounds : ℕ}
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    {Λ : Channel (A × B) (A' × B')}
    (hΛ : IsLOCCInRounds rounds Λ) :
    ∃ P : LOCCProtocol.{u, v, w, x, 0} A B A' B',
      P.channel.map = Λ.map := by
  induction rounds generalizing A B A' B' with
  | zero =>
      simp only [IsLOCCInRounds] at hΛ
      rcases hΛ with ⟨left, right, hprod⟩
      exact exists_separable_protocol_of_product left right Λ hprod
  | succ rounds ih =>
      simp only [IsLOCCInRounds] at hΛ
      rcases hΛ with hleft | hright
      · rcases hleft with
          ⟨X, fintypeX, decidableEqX, A₁, fintypeA₁, decidableEqA₁,
            I, next, hnext, hmap⟩
        letI : Fintype X := fintypeX
        letI : DecidableEq X := decidableEqX
        letI : Fintype A₁ := fintypeA₁
        letI : DecidableEq A₁ := decidableEqA₁
        exact exists_separable_protocol_of_leftConditional
          I next (fun outcome => ih (hnext outcome)) Λ hmap
      · rcases hright with
          ⟨X, fintypeX, decidableEqX, B₁, fintypeB₁, decidableEqB₁,
            I, next, hnext, hmap⟩
        letI : Fintype X := fintypeX
        letI : DecidableEq X := decidableEqX
        letI : Fintype B₁ := fintypeB₁
        letI : DecidableEq B₁ := decidableEqB₁
        exact exists_separable_protocol_of_rightConditional
          I next (fun outcome => ih (hnext outcome)) Λ hmap

/-- Every finite-round LOCC channel has a finite product-Kraus
`LOCCProtocol` representation with the same matrix map. -/
theorem IsFiniteRoundLOCC.exists_separable_protocol
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    {Λ : Channel (A × B) (A' × B')}
    (hΛ : IsFiniteRoundLOCC Λ) :
    ∃ P : LOCCProtocol.{u, v, w, x, 0} A B A' B',
      P.channel.map = Λ.map := by
  obtain ⟨rounds, hrounds⟩ := hΛ
  exact hrounds.exists_separable_protocol

/-- A finite-round LOCC output on any input state is exactly the output of a
finite product-Kraus `LOCCProtocol` on that same state. -/
theorem IsFiniteRoundLOCC.exists_separable_protocol_applyState_eq
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    {Λ : Channel (A × B) (A' × B')}
    (hΛ : IsFiniteRoundLOCC Λ)
    (ρ : State (A × B)) :
    ∃ P : LOCCProtocol.{u, v, w, x, 0} A B A' B',
      P.channel.applyState ρ = Λ.applyState ρ := by
  obtain ⟨P, hP⟩ := hΛ.exists_separable_protocol
  refine ⟨P, State.ext ?_⟩
  exact LinearMap.congr_fun hP ρ.matrix

/-! ## Project-local Mathlib supplement — pure-target fidelity bridge -/

/-- The squared Euclidean norm of a finite complex amplitude vector, used to
state branch-normalization identities without choosing a bundled normed space. -/
noncomputable def amplitudeSquaredNorm
    {X : Type u} [Fintype X] (z : X → ℂ) : ℝ :=
  ∑ i : X, ‖z i‖ ^ 2

/-- Squared amplitude norms are nonnegative. -/
theorem amplitudeSquaredNorm_nonneg
    {X : Type u} [Fintype X] (z : X → ℂ) :
    0 ≤ amplitudeSquaredNorm z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The trace of a rank-one kernel is the real squared norm of its amplitude. -/
theorem rankOneMatrix_trace_eq_amplitudeSquaredNorm
    {X : Type u} [Fintype X] (z : X → ℂ) :
    (rankOneMatrix z).trace = ((amplitudeSquaredNorm z : ℝ) : ℂ) := by
  simp only [rankOneMatrix_trace, amplitudeSquaredNorm, dotProduct,
    Complex.star_def, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Taking real parts identifies the squared amplitude norm with the trace of
its rank-one kernel. -/
theorem amplitudeSquaredNorm_eq_re_trace_rankOne
    {X : Type u} [Fintype X] (z : X → ℂ) :
    amplitudeSquaredNorm z =
      Complex.re (rankOneMatrix z).trace := by
  rw [rankOneMatrix_trace_eq_amplitudeSquaredNorm]
  rfl

/-- The canonical maximally-entangled amplitude has squared norm one at every
positive target rank. -/
theorem amplitudeSquaredNorm_maximallyEntangledVector
    (M : ℕ) (hM : 0 < M) :
    amplitudeSquaredNorm (maximallyEntangledVector M) = 1 := by
  rw [amplitudeSquaredNorm_eq_re_trace_rankOne, rankOneMatrix_trace]
  simp only [dotProduct, maximallyEntangledVector]
  rw [Fintype.sum_prod_type]
  simp
  have hsqrt : Real.sqrt (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hM))
  field_simp
  exact Real.sq_sqrt (Nat.cast_nonneg M)

/-- The amplitude of every bundled `PureVector` has squared norm one. -/
theorem amplitudeSquaredNorm_pureVector
    {X : Type u} [Fintype X] [DecidableEq X]
    (φ : PureVector X) :
    amplitudeSquaredNorm φ.amp = 1 := by
  rw [amplitudeSquaredNorm_eq_re_trace_rankOne,
    φ.trace_rankOne_eq_one]
  rfl

private theorem complex_norm_sq_eq_re_star_mul (w : ℂ) :
    ‖w‖ ^ 2 = Complex.re (star w * w) := by
  rw [Complex.sq_norm]
  have h := Complex.normSq_eq_conj_mul_self (z := w)
  exact_mod_cast congrArg Complex.re h

/-- Projecting one subsystem of a bipartite pure amplitude onto a marginal
eigenvector has squared norm equal to the corresponding eigenvalue. -/
theorem marginalEigenvector_projected_amplitudeSquaredNorm
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (i : A) :
    amplitudeSquaredNorm
        (fun b => ∑ a : A,
          star
              (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i a) *
            ψ.amp (a, b)) =
      ψ.state.marginalA.pos.isHermitian.eigenvalues i := by
  rw [Matrix.IsHermitian.eigenvalues_eq]
  simp only [amplitudeSquaredNorm, Matrix.mulVec, dotProduct]
  simp only [State.marginalA, partialTraceB, PureVector.state,
    rankOneMatrix_apply]
  simp_rw [complex_norm_sq_eq_re_star_mul]
  rw [← Complex.re_sum]
  apply congrArg Complex.re
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a' _
  rw [star_mul, star_star]
  simp only [Pi.star_apply]
  ring

/-- The pure amplitude component selected by one eigenvector of Alice's
marginal state. -/
noncomputable def marginalEigenvectorAmplitude
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (i : A) :
    A × B → ℂ :=
  fun ab =>
    ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i ab.1 *
      ∑ a : A,
        star
            (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i a) *
          ψ.amp (a, ab.2)

/-- Summing all marginal-eigenvector amplitude components reconstructs the
original bipartite pure amplitude. -/
theorem sum_marginalEigenvectorAmplitude
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) :
    ∑ i : A, marginalEigenvectorAmplitude ψ i = ψ.amp := by
  funext ab
  let e := ψ.state.marginalA.pos.isHermitian.eigenvectorBasis
  let q : EuclideanSpace ℂ A :=
    WithLp.toLp 2 (fun a => ψ.amp (a, ab.2))
  have h :=
    congrArg (fun x : EuclideanSpace ℂ A => x ab.1)
      (e.sum_repr' q)
  have h' :
      ψ.amp ab =
        ∑ i : A, inner ℂ (e i) q * e i ab.1 := by
    simpa [q] using h.symm
  rw [h']
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change
    marginalEigenvectorAmplitude ψ i ab =
      inner ℂ (e i) q * e i ab.1
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  dsimp [marginalEigenvectorAmplitude, q, e]
  simp only [dotProduct, starRingEnd_apply, Pi.star_apply]
  change
    ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i ab.1 *
          (∑ x : A,
            star
                (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i x) *
              ψ.amp (x, ab.2)) =
      (∑ x : A,
          ψ.amp (x, ab.2) *
            star
              (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i x)) *
        ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i ab.1
  have hsum :
      (∑ x : A,
          ψ.amp (x, ab.2) *
            star
              (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i x)) =
        ∑ x : A,
          star
              (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i x) *
            ψ.amp (x, ab.2) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  ring

/-- A single marginal-eigenvector amplitude component has squared norm equal
to its marginal eigenvalue. -/
theorem marginalEigenvectorAmplitude_amplitudeSquaredNorm
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (i : A) :
    amplitudeSquaredNorm (marginalEigenvectorAmplitude ψ i) =
      ψ.state.marginalA.pos.isHermitian.eigenvalues i := by
  have he :
      amplitudeSquaredNorm
          (fun a =>
            ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i a) =
        1 := by
    rw [amplitudeSquaredNorm, ← PiLp.norm_sq_eq_of_L2]
    rw [
      ψ.state.marginalA.pos.isHermitian.eigenvectorBasis.orthonormal.1 i]
    norm_num
  have hc :=
    marginalEigenvector_projected_amplitudeSquaredNorm ψ i
  rw [amplitudeSquaredNorm, Fintype.sum_prod_type]
  simp only [marginalEigenvectorAmplitude, norm_mul, mul_pow]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  change
    amplitudeSquaredNorm
          (fun a =>
            ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i a) *
        amplitudeSquaredNorm
          (fun b =>
            ∑ a : A,
              star
                  (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i a) *
                ψ.amp (a, b)) =
      _
  rw [he, hc, one_mul]

/-- Spectral truncation of a bipartite pure amplitude to a finite set of
Alice-marginal eigenvectors. -/
noncomputable def marginalSpectralTruncation
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (S : Finset A) :
    A × B → ℂ :=
  ∑ i ∈ S, marginalEigenvectorAmplitude ψ i

/-- A marginal spectral truncation and its complementary truncation sum to
the original pure amplitude. -/
theorem marginalSpectralTruncation_add_compl
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (S : Finset A) :
    marginalSpectralTruncation ψ S +
        marginalSpectralTruncation ψ (Finset.univ \ S) =
      ψ.amp := by
  unfold marginalSpectralTruncation
  calc
    (∑ i ∈ S, marginalEigenvectorAmplitude ψ i) +
          ∑ i ∈ Finset.univ \ S, marginalEigenvectorAmplitude ψ i =
        ∑ i : A, marginalEigenvectorAmplitude ψ i := by
      rw [add_comm]
      exact Finset.sum_sdiff (Finset.subset_univ S)
    _ = ψ.amp := sum_marginalEigenvectorAmplitude ψ

/-- Orthogonal finite amplitudes have additive squared norms. -/
theorem amplitudeSquaredNorm_add_of_dotProduct_eq_zero
    {X : Type u} [Fintype X] (z w : X → ℂ)
    (hzw : (fun x => star (z x)) ⬝ᵥ w = 0) :
    amplitudeSquaredNorm (z + w) =
      amplitudeSquaredNorm z + amplitudeSquaredNorm w := by
  let zE : EuclideanSpace ℂ X := WithLp.toLp 2 z
  let wE : EuclideanSpace ℂ X := WithLp.toLp 2 w
  have hinner : inner ℂ zE wE = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    dsimp [zE, wE]
    simp only [dotProduct, Pi.star_apply] at hzw ⊢
    calc
      (∑ x : X, w x * star (z x)) =
          ∑ x : X, star (z x) * w x := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := hzw
  have hnorm :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero zE wE hinner
  have hamp (f : X → ℂ) :
      amplitudeSquaredNorm f = ‖WithLp.toLp 2 f‖ ^ 2 := by
    rw [amplitudeSquaredNorm, ← PiLp.norm_sq_eq_of_L2]
  rw [hamp, hamp, hamp]
  have hadd : WithLp.toLp 2 (z + w) = zE + wE := by
    rfl
  rw [hadd]
  simpa [pow_two] using hnorm

/-- Distinct marginal-eigenvector amplitude components are orthogonal. -/
theorem marginalEigenvectorAmplitude_dotProduct_eq_zero
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) {i j : A} (hij : i ≠ j) :
    (fun ab => star (marginalEigenvectorAmplitude ψ i ab)) ⬝ᵥ
        marginalEigenvectorAmplitude ψ j =
      0 := by
  let e := ψ.state.marginalA.pos.isHermitian.eigenvectorBasis
  let c : A → B → ℂ :=
    fun k b => ∑ a : A, star (e k a) * ψ.amp (a, b)
  have hfactor :
      (∑ a : A, star (e i a) * e j a) = 0 := by
    calc
      (∑ a : A, star (e i a) * e j a) =
          ∑ a : A, e j a * star (e i a) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = inner ℂ (e i) (e j) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp only [dotProduct, Pi.star_apply]
      _ = 0 := by rw [e.inner_eq_ite, if_neg hij]
  rw [dotProduct, Fintype.sum_prod_type]
  change
    (∑ a : A, ∑ b : B,
      star (e i a * c i b) * (e j a * c j b)) =
      0
  simp only [star_mul]
  calc
    (∑ a : A, ∑ b : B,
        star (c i b) * star (e i a) * (e j a * c j b)) =
        (∑ a : A, star (e i a) * e j a) *
          ∑ b : B, star (c i b) * c j b := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = 0 := by rw [hfactor, zero_mul]

/-- The squared norm of a marginal spectral truncation is the sum of the
selected marginal eigenvalues. -/
theorem marginalSpectralTruncation_amplitudeSquaredNorm
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (S : Finset A) :
    amplitudeSquaredNorm (marginalSpectralTruncation ψ S) =
      ∑ i ∈ S,
        ψ.state.marginalA.pos.isHermitian.eigenvalues i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [marginalSpectralTruncation, amplitudeSquaredNorm]
  | @insert i S hi ih =>
      have horth :
          (fun ab => star (marginalEigenvectorAmplitude ψ i ab)) ⬝ᵥ
              marginalSpectralTruncation ψ S =
            0 := by
        unfold marginalSpectralTruncation
        rw [dotProduct_sum]
        apply Finset.sum_eq_zero
        intro j hj
        apply marginalEigenvectorAmplitude_dotProduct_eq_zero ψ
        intro hij
        apply hi
        rwa [hij]
      have hadd :=
        amplitudeSquaredNorm_add_of_dotProduct_eq_zero
          (marginalEigenvectorAmplitude ψ i)
          (marginalSpectralTruncation ψ S) horth
      calc
        amplitudeSquaredNorm
            (marginalSpectralTruncation ψ (insert i S)) =
            amplitudeSquaredNorm
              (marginalEigenvectorAmplitude ψ i +
                marginalSpectralTruncation ψ S) := by
          congr 1
          simp [marginalSpectralTruncation, hi]
        _ =
            amplitudeSquaredNorm
                (marginalEigenvectorAmplitude ψ i) +
              amplitudeSquaredNorm
                (marginalSpectralTruncation ψ S) :=
          hadd
        _ =
            ψ.state.marginalA.pos.isHermitian.eigenvalues i +
              ∑ j ∈ S,
                ψ.state.marginalA.pos.isHermitian.eigenvalues j := by
          rw [marginalEigenvectorAmplitude_amplitudeSquaredNorm, ih]
        _ =
            ∑ j ∈ insert i S,
              ψ.state.marginalA.pos.isHermitian.eigenvalues j := by
          rw [Finset.sum_insert hi]

/-- The complementary marginal spectral truncation has exactly the discarded
eigenvalue mass. -/
theorem marginalSpectralTruncation_compl_amplitudeSquaredNorm
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (S : Finset A) :
    amplitudeSquaredNorm
        (marginalSpectralTruncation ψ (Finset.univ \ S)) =
      1 -
        ∑ i ∈ S,
          ψ.state.marginalA.pos.isHermitian.eigenvalues i := by
  rw [marginalSpectralTruncation_amplitudeSquaredNorm]
  have htotal :
      (∑ i : A,
        ψ.state.marginalA.pos.isHermitian.eigenvalues i) =
        1 := by
    have h :=
      ψ.state.marginalA.pos.isHermitian.trace_eq_sum_eigenvalues
    rw [ψ.state.marginalA.trace_eq_one] at h
    apply Complex.ofReal_injective
    simpa using h.symm
  have hsplit :=
    Finset.sum_sdiff (Finset.subset_univ S)
      (f :=
        fun i : A =>
          ψ.state.marginalA.pos.isHermitian.eigenvalues i)
  rw [htotal] at hsplit
  linarith

/-- The coefficient matrix of a marginal spectral truncation has rank at most
the number of selected eigenvectors. -/
theorem marginalSpectralTruncation_rank_le_card
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ψ : PureVector (A × B)) (S : Finset A) :
    Matrix.rank
        (fun a b =>
          marginalSpectralTruncation ψ S (a, b) :
          Matrix A B ℂ) ≤
      S.card := by
  let L : Matrix A {i // i ∈ S} ℂ :=
    fun a i =>
      ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i.1 a
  let R : Matrix {i // i ∈ S} B ℂ :=
    fun i b =>
      ∑ a : A,
        star
            (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i.1 a) *
          ψ.amp (a, b)
  have hfactor :
      (fun a b =>
        marginalSpectralTruncation ψ S (a, b) :
        Matrix A B ℂ) =
        L * R := by
    ext a b
    simp only [marginalSpectralTruncation, Finset.sum_apply,
      marginalEigenvectorAmplitude, Matrix.mul_apply, L, R]
    rw [Finset.sum_subtype S (by intro x; rfl)]
  rw [hfactor]
  exact
    (Matrix.rank_mul_le_left L R).trans (by
      simpa using Matrix.rank_le_card_width L)

/-- Applying a tensor product of two local matrices cannot increase the rank
of the bipartite coefficient matrix. -/
theorem kronecker_mulVec_coefficientMatrix_rank_le
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B']
    (L : Matrix A' A ℂ) (R : Matrix B' B ℂ)
    (z : A × B → ℂ) :
    Matrix.rank
        (fun a' b' =>
          (Matrix.kronecker L R).mulVec z (a', b') :
          Matrix A' B' ℂ) ≤
      Matrix.rank
        (fun a b => z (a, b) : Matrix A B ℂ) := by
  let Z : Matrix A B ℂ := fun a b => z (a, b)
  have hmatrix :
      (fun a' b' =>
        (Matrix.kronecker L R).mulVec z (a', b') :
        Matrix A' B' ℂ) =
        L * (Z * R.transpose) := by
    ext a' b'
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.transpose_apply, Z]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change
      (L a' a * R b' b) * z (a, b) =
        L a' a * (z (a, b) * R b' b)
    ring
  rw [hmatrix]
  exact
    (Matrix.rank_mul_le_right L (Z * R.transpose)).trans
      (Matrix.rank_mul_le_left Z R.transpose)

/-- Every product-Kraus branch of a concrete LOCC protocol preserves the
Schmidt-rank upper bound of an input amplitude. -/
theorem LOCCProtocol.productKraus_coefficientMatrix_rank_le
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (P : LOCCProtocol.{u, v, w, x, 0} A B A' B')
    (k : P.KrausIndex) (z : A × B → ℂ) :
    Matrix.rank
        (fun a' b' =>
          (P.productKraus k).mulVec z (a', b') :
          Matrix A' B' ℂ) ≤
      Matrix.rank
        (fun a b => z (a, b) : Matrix A B ℂ) := by
  simpa [LOCCProtocol.productKraus] using
    kronecker_mulVec_coefficientMatrix_rank_le
      (P.leftKraus k) (P.rightKraus k) z

/-- The squared norm of a product amplitude factors into the squared norms of
its local amplitudes. -/
theorem amplitudeSquaredNorm_product
    {A : Type u} {B : Type v}
    [Fintype A] [Fintype B]
    (a : A → ℂ) (b : B → ℂ) :
    amplitudeSquaredNorm
        (fun ab : A × B => a ab.1 * b ab.2) =
      amplitudeSquaredNorm a * amplitudeSquaredNorm b := by
  rw [amplitudeSquaredNorm, Fintype.sum_prod_type]
  simp only [norm_mul, mul_pow]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rfl

/-- A Kronecker product sends a product amplitude to the product of the two
local matrix-vector images. -/
theorem kronecker_mulVec_product
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B']
    (L : Matrix A' A ℂ) (R : Matrix B' B ℂ)
    (a : A → ℂ) (b : B → ℂ) :
    (Matrix.kronecker L R).mulVec
        (fun ab : A × B => a ab.1 * b ab.2) =
      fun ab : A' × B' =>
        L.mulVec a ab.1 * R.mulVec b ab.2 := by
  funext ab'
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change
    (L ab'.1 i * R ab'.2 j) * (a i * b j) =
      (L ab'.1 i * a i) * (R ab'.2 j * b j)
  ring

/-- The squared norm of a finite scalar sum is bounded by the number of
summands times the sum of their squared norms. -/
theorem norm_finset_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type u} (S : Finset ι) (c : ι → ℂ) :
    ‖∑ i ∈ S, c i‖ ^ 2 ≤
      (S.card : ℝ) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
  have htri :
      ‖∑ i ∈ S, c i‖ ≤ ∑ i ∈ S, ‖c i‖ :=
    norm_sum_le _ _
  have hc :=
    Real.sum_mul_le_sqrt_mul_sqrt S
      (fun _ => (1 : ℝ)) (fun i => ‖c i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul,
    mul_one] at hc
  have hbound := htri.trans hc
  have hsum_nonneg :
      0 ≤ ∑ i ∈ S, ‖c i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcard_nonneg : 0 ≤ (S.card : ℝ) :=
    Nat.cast_nonneg _
  have hsqrtCard := Real.sq_sqrt hcard_nonneg
  have hsqrtSum := Real.sq_sqrt hsum_nonneg
  have hnorm := norm_nonneg (∑ i ∈ S, c i)
  have hsqrtCardNonneg := Real.sqrt_nonneg (S.card : ℝ)
  have hsqrtSumNonneg :=
    Real.sqrt_nonneg (∑ i ∈ S, ‖c i‖ ^ 2)
  nlinarith

private theorem conjugate_dotProduct_self_eq_amplitudeSquaredNorm
    {X : Type u} [Fintype X] (z : X → ℂ) :
    (fun i => star (z i)) ⬝ᵥ z =
      ((amplitudeSquaredNorm z : ℝ) : ℂ) := by
  simp only [amplitudeSquaredNorm, dotProduct, Complex.star_def,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem rankOneMatrix_mul_self
    {X : Type u} [Fintype X] (z : X → ℂ) :
    rankOneMatrix z * rankOneMatrix z =
      ((amplitudeSquaredNorm z : ℝ) : ℂ) • rankOneMatrix z := by
  unfold rankOneMatrix
  rw [Matrix.vecMulVec_mul_vecMulVec,
    conjugate_dotProduct_self_eq_amplitudeSquaredNorm]
  ext i j
  change
    z i * (↑(amplitudeSquaredNorm z) * star (z j)) =
      ↑(amplitudeSquaredNorm z) * (z i * star (z j))
  ring

private theorem matrixSqrt_rankOneMatrix_of_pos
    {X : Type u} [Fintype X] [DecidableEq X] (z : X → ℂ)
    (hz : 0 < amplitudeSquaredNorm z) :
    matrixSqrt (rankOneMatrix z) =
      (Real.sqrt (amplitudeSquaredNorm z))⁻¹ • rankOneMatrix z := by
  unfold matrixSqrt
  apply CFC.sqrt_unique
  · rw [Matrix.smul_mul, Matrix.mul_smul, rankOneMatrix_mul_self]
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    have hsqrt : Real.sqrt (amplitudeSquaredNorm z) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hz)
    have hcoefficientReal :
        (Real.sqrt (amplitudeSquaredNorm z))⁻¹ *
            ((Real.sqrt (amplitudeSquaredNorm z))⁻¹ *
              amplitudeSquaredNorm z) =
          1 := by
      field_simp
      exact (Real.sq_sqrt hz.le).symm
    let c : ℂ :=
      (((Real.sqrt (amplitudeSquaredNorm z))⁻¹ : ℝ) : ℂ)
    let q : ℂ := ((amplitudeSquaredNorm z : ℝ) : ℂ)
    have hcoefficient : c * (c * q) = 1 := by
      dsimp [c, q]
      exact_mod_cast hcoefficientReal
    have hscaled :=
      congrArg (fun d : ℂ => d * rankOneMatrix z i j) hcoefficient
    dsimp [c, q] at hscaled
    simpa only [mul_assoc, one_mul] using hscaled
  · rw [Matrix.nonneg_iff_posSemidef]
    exact
      (rankOneMatrix_pos z).smul
        (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- The CFC square root of an arbitrary rank-one kernel has the expected
normalization, including the zero-vector case. -/
theorem matrixSqrt_rankOneMatrix
    {X : Type u} [Fintype X] [DecidableEq X] (z : X → ℂ) :
    matrixSqrt (rankOneMatrix z) =
      (Real.sqrt (amplitudeSquaredNorm z))⁻¹ • rankOneMatrix z := by
  rcases (amplitudeSquaredNorm_nonneg z).eq_or_lt with hz | hz
  · have hsum : (∑ i : X, ‖z i‖ ^ 2) = 0 := by
      simpa [amplitudeSquaredNorm] using hz.symm
    have hz0 : z = 0 := by
      funext i
      have hall :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_ : j ∈ (Finset.univ : Finset X)) =>
            sq_nonneg ‖z j‖)).mp hsum
      have hi : ‖z i‖ ^ 2 = 0 := hall i (Finset.mem_univ i)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
    subst z
    simp [matrixSqrt, amplitudeSquaredNorm, rankOneMatrix]
  · exact matrixSqrt_rankOneMatrix_of_pos z hz

/-- The trace of the square root of a rank-one kernel is the Euclidean norm
of its amplitude. -/
theorem trace_matrixSqrt_rankOneMatrix
    {X : Type u} [Fintype X] [DecidableEq X] (z : X → ℂ) :
    Complex.re (matrixSqrt (rankOneMatrix z)).trace =
      Real.sqrt (amplitudeSquaredNorm z) := by
  rw [matrixSqrt_rankOneMatrix, Matrix.trace_smul,
    rankOneMatrix_trace_eq_amplitudeSquaredNorm]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rcases (amplitudeSquaredNorm_nonneg z).eq_or_lt with hz | hz
  · rw [← hz]
    simp
  · have hsqrt : Real.sqrt (amplitudeSquaredNorm z) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hz)
    field_simp
    exact (Real.sq_sqrt hz.le).symm

private theorem mul_rankOneMatrix_mul_conjTranspose_foundation
    {I : Type u} {O : Type v}
    [Fintype I] [Fintype O]
    (K : Matrix O I ℂ) (z : I → ℂ) :
    K * rankOneMatrix z * Matrix.conjTranspose K =
      rankOneMatrix (K.mulVec z) := by
  unfold rankOneMatrix
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  exact (Matrix.star_mulVec K z).symm

/-- Fidelity against a rank-one target is the square root of the squared norm
obtained by applying the source matrix square root to the target amplitude. -/
theorem quantumFidelity_rankOneMatrix
    {X : Type u} [Fintype X] [DecidableEq X]
    (ρ : CMatrix X) (z : X → ℂ) :
    quantumFidelity ρ (rankOneMatrix z) =
      Real.sqrt (amplitudeSquaredNorm ((matrixSqrt ρ).mulVec z)) := by
  have hsqrtPos :
      (matrixSqrt ρ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)
  have hinner :
      matrixSqrt ρ * rankOneMatrix z * matrixSqrt ρ =
        rankOneMatrix ((matrixSqrt ρ).mulVec z) := by
    simpa [hsqrtPos.isHermitian.eq] using
      mul_rankOneMatrix_mul_conjTranspose_foundation
        (matrixSqrt ρ) z
  rw [quantumFidelity, hinner]
  exact trace_matrixSqrt_rankOneMatrix _

/-- A positive source matrix turns the pure-target fidelity formula into the
usual square root of the Born overlap. -/
theorem quantumFidelity_rankOneMatrix_eq_sqrt_trace
    {X : Type u} [Fintype X] [DecidableEq X]
    (ρ : CMatrix X) (hρ : ρ.PosSemidef) (z : X → ℂ) :
    quantumFidelity ρ (rankOneMatrix z) =
      Real.sqrt (Complex.re (ρ * rankOneMatrix z).trace) := by
  rw [quantumFidelity_rankOneMatrix]
  congr 1
  rw [amplitudeSquaredNorm_eq_re_trace_rankOne]
  have hsqrtPos :
      (matrixSqrt ρ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)
  have hrank :
      rankOneMatrix ((matrixSqrt ρ).mulVec z) =
        matrixSqrt ρ * rankOneMatrix z * matrixSqrt ρ := by
    simpa [hsqrtPos.isHermitian.eq] using
      (mul_rankOneMatrix_mul_conjTranspose_foundation
        (matrixSqrt ρ) z).symm
  rw [hrank, Matrix.trace_mul_cycle]
  have hsquare : matrixSqrt ρ * matrixSqrt ρ = ρ := by
    simpa [pow_two] using CFC.sq_sqrt ρ hρ.nonneg
  rw [hsquare]

/-- The trace overlap of two rank-one kernels is the squared magnitude of
their amplitude inner product. -/
theorem re_trace_rankOneMatrix_mul_rankOneMatrix
    {X : Type u} [Fintype X] (z φ : X → ℂ) :
    Complex.re (rankOneMatrix z * rankOneMatrix φ).trace =
      ‖(fun i => star (φ i)) ⬝ᵥ z‖ ^ 2 := by
  unfold rankOneMatrix
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec]
  simp only [dotProduct_smul, smul_eq_mul]
  let c : ℂ := (fun i => star (φ i)) ⬝ᵥ z
  have hc1 : z ⬝ᵥ (fun i => star (φ i)) = c :=
    dotProduct_comm _ _
  have hc2 : (fun i => star (z i)) ⬝ᵥ φ = star c := by
    dsimp [c]
    simp only [dotProduct, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul]
    simp
    ring
  rw [hc1, hc2]
  change Complex.re (star c * c) = ‖c‖ ^ 2
  rw [mul_comm, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  norm_cast

/-- The overlap with the canonical maximally-entangled vector is the diagonal
trace of the bipartite coefficient matrix, divided by `sqrt M`. -/
theorem maximallyEntangled_inner_eq_inv_sqrt_mul_diagonal_sum
    (M : ℕ) (z : Fin M × Fin M → ℂ) :
    (fun i => star (maximallyEntangledVector M i)) ⬝ᵥ z =
      (((Real.sqrt (M : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ i : Fin M, z (i, i) := by
  simp only [dotProduct]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [maximallyEntangledVector]
  · intro j _ hji
    simp [maximallyEntangledVector, Ne.symm hji]
  · simp

/-- The squared diagonal trace is bounded by the ambient dimension times the
squared coefficient norm; the converse needs the sharper rank replacement. -/
theorem diagonal_sum_norm_sq_le_card_mul_amplitudeSquaredNorm
    (M : ℕ) (z : Fin M × Fin M → ℂ) :
    ‖∑ i : Fin M, z (i, i)‖ ^ 2 ≤
      (M : ℝ) * amplitudeSquaredNorm z := by
  let diagonal : Fin M × Fin M → ℂ :=
    fun ij => if ij.1 = ij.2 then 1 else 0
  have hinner :
      (fun ij => star (diagonal ij)) ⬝ᵥ z =
        ∑ i : Fin M, z (i, i) := by
    simp only [dotProduct]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [diagonal]
    · intro j _ hji
      simp [diagonal, Ne.symm hji]
    · simp
  have hdiagonal :
      amplitudeSquaredNorm diagonal = (M : ℝ) := by
    rw [amplitudeSquaredNorm, Fintype.sum_prod_type]
    calc
      (∑ i : Fin M, ∑ j : Fin M, ‖diagonal (i, j)‖ ^ 2) =
          ∑ i : Fin M, 1 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · simp [diagonal]
        · intro j _ hji
          simp [diagonal, Ne.symm hji]
        · simp
      _ = (M : ℝ) := by simp
  rw [← hinner, ← hdiagonal]
  have hcauchy :
      ‖(fun ij => star (diagonal ij)) ⬝ᵥ z‖ ≤
        Real.sqrt (amplitudeSquaredNorm diagonal) *
          Real.sqrt (amplitudeSquaredNorm z) := by
    calc
      ‖(fun ij => star (diagonal ij)) ⬝ᵥ z‖ =
          ‖∑ ij : Fin M × Fin M, star (diagonal ij) * z ij‖ := rfl
      _ ≤ ∑ ij : Fin M × Fin M, ‖star (diagonal ij) * z ij‖ :=
        norm_sum_le Finset.univ _
      _ = ∑ ij : Fin M × Fin M, ‖diagonal ij‖ * ‖z ij‖ := by
        apply Finset.sum_congr rfl
        intro ij _
        rw [norm_mul, norm_star]
      _ ≤ Real.sqrt
            (∑ ij : Fin M × Fin M, ‖diagonal ij‖ ^ 2) *
          Real.sqrt (∑ ij : Fin M × Fin M, ‖z ij‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun ij => ‖diagonal ij‖) (fun ij => ‖z ij‖)
      _ = Real.sqrt (amplitudeSquaredNorm diagonal) *
          Real.sqrt (amplitudeSquaredNorm z) := rfl
  have hdiagonalSqrt :=
    Real.sq_sqrt (amplitudeSquaredNorm_nonneg diagonal)
  have hzSqrt := Real.sq_sqrt (amplitudeSquaredNorm_nonneg z)
  nlinarith [norm_nonneg ((fun ij => star (diagonal ij)) ⬝ᵥ z),
    Real.sqrt_nonneg (amplitudeSquaredNorm diagonal),
    Real.sqrt_nonneg (amplitudeSquaredNorm z)]

/-- At positive target rank, the squared maximally-entangled overlap is the
squared diagonal trace divided by the rank. -/
theorem maximallyEntangled_inner_norm_sq_eq
    (M : ℕ) (hM : 0 < M) (z : Fin M × Fin M → ℂ) :
    ‖(fun i => star (maximallyEntangledVector M i)) ⬝ᵥ z‖ ^ 2 =
      (1 / (M : ℝ)) * ‖∑ i : Fin M, z (i, i)‖ ^ 2 := by
  rw [maximallyEntangled_inner_eq_inv_sqrt_mul_diagonal_sum,
    norm_mul, mul_pow]
  have hsqrt : Real.sqrt (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hM))
  have hnorm :
      ‖((((Real.sqrt (M : ℝ))⁻¹ : ℝ) : ℂ))‖ ^ 2 =
        1 / (M : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    field_simp
    exact (Real.sq_sqrt (Nat.cast_nonneg M)).symm
  rw [hnorm]

/-- Fidelity of a finite sum of pure branches against a pure target is the
square root of the sum of their squared target overlaps. -/
theorem quantumFidelity_sum_rankOneMatrix
    {κ : Type u} {X : Type v}
    [Fintype κ] [Fintype X] [DecidableEq X]
    (z : κ → X → ℂ) (φ : X → ℂ) :
    quantumFidelity (∑ k, rankOneMatrix (z k)) (rankOneMatrix φ) =
      Real.sqrt
        (∑ k, ‖(fun i => star (φ i)) ⬝ᵥ z k‖ ^ 2) := by
  have hpos : (∑ k, rankOneMatrix (z k)).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ
      (fun k _ => rankOneMatrix_pos (z k))
  rw [quantumFidelity_rankOneMatrix_eq_sqrt_trace _ hpos]
  congr 1
  rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact re_trace_rankOneMatrix_mul_rankOneMatrix (z k) φ

/-- Finite complex amplitude families satisfy the Euclidean Minkowski
inequality in square-root-of-sum-of-squares form. -/
theorem sqrt_sum_norm_sq_add_le
    {κ : Type u} [Fintype κ] (a b : κ → ℂ) :
    Real.sqrt (∑ k, ‖a k + b k‖ ^ 2) ≤
      Real.sqrt (∑ k, ‖a k‖ ^ 2) +
        Real.sqrt (∑ k, ‖b k‖ ^ 2) := by
  calc
    Real.sqrt (∑ k, ‖a k + b k‖ ^ 2) ≤
        Real.sqrt (∑ k, (‖a k‖ + ‖b k‖) ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro k _
      have hab := norm_add_le (a k) (b k)
      nlinarith [norm_nonneg (a k + b k), norm_nonneg (a k),
        norm_nonneg (b k)]
    _ ≤ Real.sqrt (∑ k, ‖a k‖ ^ 2) +
          Real.sqrt (∑ k, ‖b k‖ ^ 2) := by
      simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using
        (Real.Lp_add_le_of_nonneg (Finset.univ : Finset κ)
          (p := (2 : ℝ)) (by norm_num)
          (fun k _ => norm_nonneg (a k))
          (fun k _ => norm_nonneg (b k)))

/-- Splitting an input amplitude before every branch gives the corresponding
Minkowski bound on the family of pure-target branch overlaps. -/
theorem sqrt_sum_branch_overlap_sq_add_le
    {κ : Type u} {I : Type v} {O : Type w}
    [Fintype κ] [Fintype I] [Fintype O]
    (K : κ → Matrix O I ℂ) (φ : O → ℂ)
    (zLow zHigh : I → ℂ) :
    Real.sqrt
        (∑ k, ‖(fun i => star (φ i)) ⬝ᵥ
          (K k).mulVec (zLow + zHigh)‖ ^ 2) ≤
      Real.sqrt
          (∑ k, ‖(fun i => star (φ i)) ⬝ᵥ
            (K k).mulVec zLow‖ ^ 2) +
        Real.sqrt
          (∑ k, ‖(fun i => star (φ i)) ⬝ᵥ
            (K k).mulVec zHigh‖ ^ 2) := by
  simpa only [Matrix.mulVec_add, dotProduct_add] using
    (sqrt_sum_norm_sq_add_le
      (fun k => (fun i => star (φ i)) ⬝ᵥ (K k).mulVec zLow)
      (fun k => (fun i => star (φ i)) ⬝ᵥ (K k).mulVec zHigh))

/-- Finite complex amplitudes satisfy Cauchy--Schwarz in terms of
`amplitudeSquaredNorm`. -/
theorem amplitude_innerProduct_norm_le
    {X : Type u} [Fintype X] (φ z : X → ℂ) :
    ‖(fun i => star (φ i)) ⬝ᵥ z‖ ≤
      Real.sqrt (amplitudeSquaredNorm φ) *
        Real.sqrt (amplitudeSquaredNorm z) := by
  calc
    ‖(fun i => star (φ i)) ⬝ᵥ z‖ =
        ‖∑ i : X, star (φ i) * z i‖ := rfl
    _ ≤ ∑ i : X, ‖star (φ i) * z i‖ :=
      norm_sum_le Finset.univ _
    _ = ∑ i : X, ‖φ i‖ * ‖z i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul, norm_star]
    _ ≤ Real.sqrt (∑ i : X, ‖φ i‖ ^ 2) *
          Real.sqrt (∑ i : X, ‖z i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun i => ‖φ i‖) (fun i => ‖z i‖)
    _ = Real.sqrt (amplitudeSquaredNorm φ) *
          Real.sqrt (amplitudeSquaredNorm z) := rfl

/-- Squaring finite-amplitude Cauchy--Schwarz bounds a pure-target overlap by
the product of the two squared amplitude norms. -/
theorem amplitude_innerProduct_norm_sq_le
    {X : Type u} [Fintype X] (φ z : X → ℂ) :
    ‖(fun i => star (φ i)) ⬝ᵥ z‖ ^ 2 ≤
      amplitudeSquaredNorm φ * amplitudeSquaredNorm z := by
  have h := amplitude_innerProduct_norm_le φ z
  have hφ := Real.sq_sqrt (amplitudeSquaredNorm_nonneg φ)
  have hz := Real.sq_sqrt (amplitudeSquaredNorm_nonneg z)
  have hi := norm_nonneg ((fun i => star (φ i)) ⬝ᵥ z)
  have hrφ := Real.sqrt_nonneg (amplitudeSquaredNorm φ)
  have hrz := Real.sqrt_nonneg (amplitudeSquaredNorm z)
  nlinarith

/-- A product amplitude overlaps the normalized maximally-entangled vector by
at most the inverse target dimension times its local squared norms. -/
theorem maximallyEntangled_product_overlap_sq_le
    (M : ℕ) (hM : 0 < M) (a b : Fin M → ℂ) :
    ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
        (fun ab : Fin M × Fin M => a ab.1 * b ab.2)‖ ^ 2 ≤
      (1 / (M : ℝ)) *
        amplitudeSquaredNorm a * amplitudeSquaredNorm b := by
  rw [maximallyEntangled_inner_norm_sq_eq M hM]
  have hc :=
    amplitude_innerProduct_norm_sq_le (fun i => star (a i)) b
  simp only [star_star] at hc
  have hastar :
      amplitudeSquaredNorm (fun i => star (a i)) =
        amplitudeSquaredNorm a := by
    simp [amplitudeSquaredNorm]
  rw [hastar] at hc
  calc
    (1 / (M : ℝ)) * ‖∑ i : Fin M, a i * b i‖ ^ 2 ≤
        (1 / (M : ℝ)) *
          (amplitudeSquaredNorm a * amplitudeSquaredNorm b) := by
      gcongr
      simpa only [dotProduct] using hc
    _ =
        (1 / (M : ℝ)) *
          amplitudeSquaredNorm a * amplitudeSquaredNorm b := by
      ring

/-- Trace preservation gives an exact Parseval identity for all product-Kraus
branches of a concrete LOCC protocol. -/
theorem LOCCProtocol.sum_branch_amplitudeSquaredNorm
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (P : LOCCProtocol.{u, v, w, x, 0} A B A' B')
    (z : A × B → ℂ) :
    letI := P.fintypeKrausIndex
    (∑ k : P.KrausIndex,
        amplitudeSquaredNorm ((P.productKraus k).mulVec z)) =
      amplitudeSquaredNorm z := by
  letI := P.fintypeKrausIndex
  rw [amplitudeSquaredNorm_eq_re_trace_rankOne]
  simp_rw [amplitudeSquaredNorm_eq_re_trace_rankOne]
  rw [← Complex.re_sum]
  apply congrArg Complex.re
  have htrace := P.channel.tracePreserving (rankOneMatrix z)
  change
    (MatrixMap.ofKraus P.productKraus (rankOneMatrix z)).trace =
      (rankOneMatrix z).trace at htrace
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk] at htrace
  rw [Matrix.trace_sum] at htrace
  simp_rw [mul_rankOneMatrix_mul_conjTranspose_foundation] at htrace
  exact htrace

/-- For a retained sum of product amplitudes, the total squared
maximally-entangled overlap after a concrete LOCC protocol is bounded by the
number of retained terms divided by the target rank. -/
theorem LOCCProtocol.sum_branch_maximallyEntangled_overlap_sq_sum_product_le
    {A : Type u} {B : Type v} {ι : Type y}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (M : ℕ) (hM : 0 < M)
    (P : LOCCProtocol.{u, v, 0, 0, 0}
      A B (Fin M) (Fin M))
    (S : Finset ι)
    (a : ι → A → ℂ) (b : ι → B → ℂ) :
    letI := P.fintypeKrausIndex
    (∑ k : P.KrausIndex,
      ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
        (P.productKraus k).mulVec
          (∑ i ∈ S,
            fun ab : A × B => a i ab.1 * b i ab.2)‖ ^ 2) ≤
      ((S.card : ℝ) / (M : ℝ)) *
        ∑ i ∈ S,
          amplitudeSquaredNorm
            (fun ab : A × B => a i ab.1 * b i ab.2) := by
  letI := P.fintypeKrausIndex
  let z : ι → A × B → ℂ :=
    fun i ab => a i ab.1 * b i ab.2
  let c : P.KrausIndex → ι → ℂ :=
    fun k i =>
      (fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
        (P.productKraus k).mulVec (z i)
  have hsum (k : P.KrausIndex) :
      (fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
          (P.productKraus k).mulVec (∑ i ∈ S, z i) =
        ∑ i ∈ S, c k i := by
    dsimp [c]
    rw [Matrix.mulVec_sum, dotProduct_sum]
  have hbranch (k : P.KrausIndex) (i : ι) :
      ‖c k i‖ ^ 2 ≤
        (1 / (M : ℝ)) *
          amplitudeSquaredNorm
            ((P.productKraus k).mulVec (z i)) := by
    have h :=
      maximallyEntangled_product_overlap_sq_le M hM
        ((P.leftKraus k).mulVec (a i))
        ((P.rightKraus k).mulVec (b i))
    dsimp [c, z]
    rw [LOCCProtocol.productKraus, kronecker_mulVec_product,
      amplitudeSquaredNorm_product]
    simpa [mul_assoc] using h
  calc
    (∑ k : P.KrausIndex,
      ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
        (P.productKraus k).mulVec
          (∑ i ∈ S,
            fun ab : A × B => a i ab.1 * b i ab.2)‖ ^ 2) =
        ∑ k : P.KrausIndex, ‖∑ i ∈ S, c k i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hsum]
    _ ≤
        ∑ k : P.KrausIndex,
          (S.card : ℝ) * ∑ i ∈ S, ‖c k i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact
        norm_finset_sum_sq_le_card_mul_sum_norm_sq S (c k)
    _ =
        (S.card : ℝ) *
          ∑ i ∈ S,
            ∑ k : P.KrausIndex, ‖c k i‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
    _ ≤
        (S.card : ℝ) *
          ∑ i ∈ S,
            (1 / (M : ℝ)) * amplitudeSquaredNorm (z i) := by
      gcongr with i hi
      calc
        (∑ k : P.KrausIndex, ‖c k i‖ ^ 2) ≤
            ∑ k : P.KrausIndex,
              (1 / (M : ℝ)) *
                amplitudeSquaredNorm
                  ((P.productKraus k).mulVec (z i)) := by
          apply Finset.sum_le_sum
          intro k _
          exact hbranch k i
        _ = (1 / (M : ℝ)) * amplitudeSquaredNorm (z i) := by
          rw [← Finset.mul_sum]
          have hparse :=
            LOCCProtocol.sum_branch_amplitudeSquaredNorm P (z i)
          rw [hparse]
    _ =
        ((S.card : ℝ) / (M : ℝ)) *
          ∑ i ∈ S,
            amplitudeSquaredNorm
              (fun ab : A × B => a i ab.1 * b i ab.2) := by
      dsimp [z]
      rw [← Finset.mul_sum]
      ring

/-- The retained marginal spectral truncation has total LOCC
maximally-entangled branch overlap bounded by support size over target rank
times its selected eigenvalue mass. -/
theorem LOCCProtocol.sum_branch_maximallyEntangled_overlap_sq_truncation_le
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (M : ℕ) (hM : 0 < M)
    (P : LOCCProtocol.{u, v, 0, 0, 0}
      A B (Fin M) (Fin M))
    (ψ : PureVector (A × B)) (S : Finset A) :
    letI := P.fintypeKrausIndex
    (∑ k : P.KrausIndex,
      ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
        (P.productKraus k).mulVec
          (marginalSpectralTruncation ψ S)‖ ^ 2) ≤
      ((S.card : ℝ) / (M : ℝ)) *
        ∑ i ∈ S,
          ψ.state.marginalA.pos.isHermitian.eigenvalues i := by
  letI := P.fintypeKrausIndex
  have h :=
    LOCCProtocol.sum_branch_maximallyEntangled_overlap_sq_sum_product_le
      M hM P S
      (fun i =>
        ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i)
      (fun i b =>
        ∑ a : A,
          star
              (ψ.state.marginalA.pos.isHermitian.eigenvectorBasis i a) *
            ψ.amp (a, b))
  calc
    (∑ k : P.KrausIndex,
      ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
        (P.productKraus k).mulVec
          (marginalSpectralTruncation ψ S)‖ ^ 2) ≤
        ((S.card : ℝ) / (M : ℝ)) *
          ∑ i ∈ S,
            amplitudeSquaredNorm
              (marginalEigenvectorAmplitude ψ i) := by
      simpa only [marginalSpectralTruncation,
        marginalEigenvectorAmplitude] using h
    _ =
        ((S.card : ℝ) / (M : ℝ)) *
          ∑ i ∈ S,
            ψ.state.marginalA.pos.isHermitian.eigenvalues i := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact
        marginalEigenvectorAmplitude_amplitudeSquaredNorm ψ i

/-- Discarding the selected eigenvalue mass gives the support-over-target-rank
form of the retained LOCC overlap bound. -/
theorem LOCCProtocol.sum_branch_maximallyEntangled_overlap_sq_truncation_le_ratio
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (M : ℕ) (hM : 0 < M)
    (P : LOCCProtocol.{u, v, 0, 0, 0}
      A B (Fin M) (Fin M))
    (ψ : PureVector (A × B)) (S : Finset A) :
    letI := P.fintypeKrausIndex
    (∑ k : P.KrausIndex,
      ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
        (P.productKraus k).mulVec
          (marginalSpectralTruncation ψ S)‖ ^ 2) ≤
      (S.card : ℝ) / (M : ℝ) := by
  letI := P.fintypeKrausIndex
  have hretained :=
    LOCCProtocol.sum_branch_maximallyEntangled_overlap_sq_truncation_le
      M hM P ψ S
  have hmass :
      (∑ i ∈ S,
        ψ.state.marginalA.pos.isHermitian.eigenvalues i) ≤
        1 := by
    calc
      (∑ i ∈ S,
          ψ.state.marginalA.pos.isHermitian.eigenvalues i) ≤
          ∑ i : A,
            ψ.state.marginalA.pos.isHermitian.eigenvalues i :=
        Finset.sum_le_univ_sum_of_nonneg
          (fun i => ψ.state.marginalA.pos.eigenvalues_nonneg i)
      _ = 1 := by
        have h :=
          ψ.state.marginalA.pos.isHermitian.trace_eq_sum_eigenvalues
        rw [ψ.state.marginalA.trace_eq_one] at h
        apply Complex.ofReal_injective
        simpa using h.symm
  calc
    (∑ k : P.KrausIndex,
      ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
        (P.productKraus k).mulVec
          (marginalSpectralTruncation ψ S)‖ ^ 2) ≤
        ((S.card : ℝ) / (M : ℝ)) *
          ∑ i ∈ S,
            ψ.state.marginalA.pos.isHermitian.eigenvalues i :=
      hretained
    _ ≤ ((S.card : ℝ) / (M : ℝ)) * 1 := by
      gcongr
    _ = (S.card : ℝ) / (M : ℝ) := mul_one _

/-- A normalized pure target captures at most the input squared norm after
summing its squared overlaps over all product-Kraus branches. -/
theorem LOCCProtocol.sum_branch_overlap_sq_le
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (P : LOCCProtocol.{u, v, w, x, 0} A B A' B')
    (φ : A' × B' → ℂ)
    (hφ : amplitudeSquaredNorm φ = 1)
    (z : A × B → ℂ) :
    letI := P.fintypeKrausIndex
    (∑ k : P.KrausIndex,
        ‖(fun i => star (φ i)) ⬝ᵥ
          (P.productKraus k).mulVec z‖ ^ 2) ≤
      amplitudeSquaredNorm z := by
  letI := P.fintypeKrausIndex
  calc
    (∑ k : P.KrausIndex,
        ‖(fun i => star (φ i)) ⬝ᵥ
          (P.productKraus k).mulVec z‖ ^ 2) ≤
        ∑ k : P.KrausIndex,
          amplitudeSquaredNorm ((P.productKraus k).mulVec z) := by
      apply Finset.sum_le_sum
      intro k _
      simpa [hφ] using
        amplitude_innerProduct_norm_sq_le φ
          ((P.productKraus k).mulVec z)
    _ = amplitudeSquaredNorm z :=
      _root_.QITFormalized.OneShotEntropiesAndHypothesisTesting.ConverseEntanglementConcentration.LOCCProtocol.sum_branch_amplitudeSquaredNorm
        P z

/-- The root-mean-square pure-target branch overlap is bounded by the input
amplitude norm for every normalized target. -/
theorem LOCCProtocol.sqrt_sum_branch_overlap_sq_le
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (P : LOCCProtocol.{u, v, w, x, 0} A B A' B')
    (φ : A' × B' → ℂ)
    (hφ : amplitudeSquaredNorm φ = 1)
    (z : A × B → ℂ) :
    letI := P.fintypeKrausIndex
    Real.sqrt
        (∑ k : P.KrausIndex,
          ‖(fun i => star (φ i)) ⬝ᵥ
            (P.productKraus k).mulVec z‖ ^ 2) ≤
      Real.sqrt (amplitudeSquaredNorm z) := by
  letI := P.fintypeKrausIndex
  apply Real.sqrt_le_sqrt
  exact
    _root_.QITFormalized.OneShotEntropiesAndHypothesisTesting.ConverseEntanglementConcentration.LOCCProtocol.sum_branch_overlap_sq_le
      P φ hφ z

set_option maxHeartbeats 400000 in
/-- After splitting an input, the discarded part of the pure-target branch
overlap is controlled solely by its squared amplitude norm. -/
theorem LOCCProtocol.sqrt_sum_branch_overlap_sq_add_le
    {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B']
    (P : LOCCProtocol.{u, v, w, x, 0} A B A' B')
    (φ : A' × B' → ℂ)
    (hφ : amplitudeSquaredNorm φ = 1)
    (zLow zHigh : A × B → ℂ) :
    letI := P.fintypeKrausIndex
    Real.sqrt
        (∑ k : P.KrausIndex,
          ‖(fun i => star (φ i)) ⬝ᵥ
            (P.productKraus k).mulVec (zLow + zHigh)‖ ^ 2) ≤
      Real.sqrt
          (∑ k : P.KrausIndex,
            ‖(fun i => star (φ i)) ⬝ᵥ
              (P.productKraus k).mulVec zLow‖ ^ 2) +
        Real.sqrt (amplitudeSquaredNorm zHigh) := by
  letI := P.fintypeKrausIndex
  have hHigh :
      Real.sqrt
          (∑ k : P.KrausIndex,
            ‖(fun i => star (φ i)) ⬝ᵥ
              (P.productKraus k).mulVec zHigh‖ ^ 2) ≤
        Real.sqrt (amplitudeSquaredNorm zHigh) :=
    _root_.QITFormalized.OneShotEntropiesAndHypothesisTesting.ConverseEntanglementConcentration.LOCCProtocol.sqrt_sum_branch_overlap_sq_le
      P φ hφ zHigh
  calc
    Real.sqrt
        (∑ k : P.KrausIndex,
          ‖(fun i => star (φ i)) ⬝ᵥ
            (P.productKraus k).mulVec (zLow + zHigh)‖ ^ 2) ≤
        Real.sqrt
            (∑ k : P.KrausIndex,
              ‖(fun i => star (φ i)) ⬝ᵥ
                (P.productKraus k).mulVec zLow‖ ^ 2) +
          Real.sqrt
            (∑ k : P.KrausIndex,
              ‖(fun i => star (φ i)) ⬝ᵥ
                (P.productKraus k).mulVec zHigh‖ ^ 2) :=
      _root_.QITFormalized.OneShotEntropiesAndHypothesisTesting.ConverseEntanglementConcentration.sqrt_sum_branch_overlap_sq_add_le
        P.productKraus φ zLow zHigh
    _ ≤ Real.sqrt
          (∑ k : P.KrausIndex,
            ‖(fun i => star (φ i)) ⬝ᵥ
              (P.productKraus k).mulVec zLow‖ ^ 2) +
        Real.sqrt (amplitudeSquaredNorm zHigh) :=
      by
        simpa only [add_comm] using
          add_le_add_left hHigh
            (Real.sqrt
              (∑ k : P.KrausIndex,
                ‖(fun i => star (φ i)) ⬝ᵥ
                  (P.productKraus k).mulVec zLow‖ ^ 2))

/-- Spectrally truncating a bipartite pure input gives the complete one-shot
LOCC fidelity envelope: a support-over-target-rank term plus discarded
eigenvalue mass. -/
theorem LOCCProtocol.sqrt_sum_branch_maximallyEntangled_overlap_sq_le_truncation
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (M : ℕ) (hM : 0 < M)
    (P : LOCCProtocol.{u, v, 0, 0, 0}
      A B (Fin M) (Fin M))
    (ψ : PureVector (A × B)) (S : Finset A) :
    letI := P.fintypeKrausIndex
    Real.sqrt
        (∑ k : P.KrausIndex,
          ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
            (P.productKraus k).mulVec ψ.amp‖ ^ 2) ≤
      Real.sqrt ((S.card : ℝ) / (M : ℝ)) +
        Real.sqrt
          (1 -
            ∑ i ∈ S,
              ψ.state.marginalA.pos.isHermitian.eigenvalues i) := by
  letI := P.fintypeKrausIndex
  have hsplit :=
    marginalSpectralTruncation_add_compl ψ S
  have hminkowski :=
    LOCCProtocol.sqrt_sum_branch_overlap_sq_add_le
      P (maximallyEntangledVector M)
        (amplitudeSquaredNorm_maximallyEntangledVector M hM)
        (marginalSpectralTruncation ψ S)
        (marginalSpectralTruncation ψ (Finset.univ \ S))
  have hlow :=
    LOCCProtocol.sum_branch_maximallyEntangled_overlap_sq_truncation_le_ratio
      M hM P ψ S
  have hlowSqrt :
      Real.sqrt
          (∑ k : P.KrausIndex,
            ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
              (P.productKraus k).mulVec
                (marginalSpectralTruncation ψ S)‖ ^ 2) ≤
        Real.sqrt ((S.card : ℝ) / (M : ℝ)) :=
    Real.sqrt_le_sqrt hlow
  calc
    Real.sqrt
        (∑ k : P.KrausIndex,
          ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
            (P.productKraus k).mulVec ψ.amp‖ ^ 2) =
        Real.sqrt
          (∑ k : P.KrausIndex,
            ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
              (P.productKraus k).mulVec
                (marginalSpectralTruncation ψ S +
                  marginalSpectralTruncation ψ
                    (Finset.univ \ S))‖ ^ 2) := by
      rw [hsplit]
    _ ≤
        Real.sqrt
            (∑ k : P.KrausIndex,
              ‖(fun ab => star (maximallyEntangledVector M ab)) ⬝ᵥ
                (P.productKraus k).mulVec
                  (marginalSpectralTruncation ψ S)‖ ^ 2) +
          Real.sqrt
            (amplitudeSquaredNorm
              (marginalSpectralTruncation ψ
                (Finset.univ \ S))) :=
      hminkowski
    _ ≤
        Real.sqrt ((S.card : ℝ) / (M : ℝ)) +
          Real.sqrt
            (amplitudeSquaredNorm
              (marginalSpectralTruncation ψ
                (Finset.univ \ S))) :=
      add_le_add hlowSqrt le_rfl
    _ =
        Real.sqrt ((S.card : ℝ) / (M : ℝ)) +
          Real.sqrt
            (1 -
              ∑ i ∈ S,
                ψ.state.marginalA.pos.isHermitian.eigenvalues i) := by
      rw [marginalSpectralTruncation_compl_amplitudeSquaredNorm]

end

end QITFormalized.OneShotEntropiesAndHypothesisTesting.ConverseEntanglementConcentration
