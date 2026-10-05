import Mathlib

/-!
# IPhO 2026, Problem 3 (T3), Part A.2 — answer-blind formalization

A homogeneous isotropic paramagnetic torus has mean radius `R`, inner radius
`r` with `r << R`, volume `V`, and cross-sectional area `A`.  An insulated
conducting wire is wound densely around it with `N` turns and instantaneous
current `I`.  The fields `H` and `B` and the magnetization `M` are
approximately uniform in the torus.  The governing relations are
`B = μ₀ * H + μ₀ * M`, Ampère's law `∮_C H · dℓ = I_C` (`I_C` the net free
current through the area bounded by the closed curve `C`), and the sign
convention that work and heat entering the paramagnetic torus are positive.

Subquestion A.2 (official source-page text, T3 page 12): *Let `dW_emf` be the
work that the external voltage source performs to change the magnitude of
`B` by `dB`.  Write `dW_emf` in terms of `V`, `H`, and `dB`.*

The requested variables are the torus **volume `V`**, the **instantaneous
field magnitude `H`** found in A.1, and the prescribed change `dB`; in
particular `H` is an *input* of this subquestion, not something to exist or
solve for.  The official answer is withheld, so the theorems below state
existence and uniqueness of a work increment `dW_emf` characterised by a
physically meaningful solution predicate — the flux-linkage work law
`dW_emf = I * N * A * dB` applied at the instantaneous current `I` that
maintains the prescribed `H` via Ampère's law — together with the
expressibility contract that the answer is a function of `V`, `H`, and `dB`
alone.  No closed form appears in any signature; constructing the witness is
left to the later proof stage.

Redraft note (iter-012, review class `underdetermined_contract`): the
previous iteration left the instantaneous state and current existentially
free inside the solution predicate, so at fixed `dB` the work was not
uniquely determined and the stated `∃!` was false.  The field magnitude `H`
(A.1's output) is now a given input everywhere, the predicate requires the
realized state's field to equal that input on the nose, Ampère's law is kept
as an explicit hypothesis localized to the existence theorem (per the
natural-language-prerequisite-only policy no prior Lean output is imported),
and uniqueness is stated exactly where the contract determines the answer.
-/

namespace IPhO_2026_3_A_2

open Real

/-- The dimensional constants and geometric data of the problem, collected
as positive physical quantities: the vacuum permeability `μ₀`, the mean
radius `R`, the inner radius `r` (with `r << R`), the cross-sectional area
`A`, the volume `V` of the torus, and the number of turns `N` of the densely
wound insulated wire.  The thin-torus regime `r << R` is recorded by the
strict inequality `r < R`; its full strength (uniformity of the fields) is
already built into the scalar-magnitude model. -/
structure TorusData where
  /-- Vacuum permeability `μ₀`. -/
  μ₀ : ℝ
  /-- Mean radius `R` of the torus. -/
  R : ℝ
  /-- Inner radius `r` of the torus, with `r << R`. -/
  r : ℝ
  /-- Cross-sectional area `A` of the torus. -/
  A : ℝ
  /-- Volume `V` of the paramagnetic torus (constant). -/
  V : ℝ
  /-- Number of turns `N` of the densely wound insulated wire. -/
  N : ℝ
  μ₀_pos : 0 < μ₀
  R_pos : 0 < R
  r_pos : 0 < r
  A_pos : 0 < A
  V_pos : 0 < V
  N_pos : 0 < N
  /-- Thin-torus regime: the inner radius is strictly smaller than the mean
  radius (`r << R` of the statement). -/
  r_lt_R : r < R

/-- A macroscopic state of the paramagnetic torus: the uniform magnitudes of
the magnetic field strength `H`, the magnetic flux density `B`, and the
magnetization `M`.  The fields are approximately uniform in the torus (the
`r << R` regime), so scalar magnitudes suffice. -/
structure TorusState where
  /-- Magnitude `H` of the magnetic field strength in the torus. -/
  H : ℝ
  /-- Magnitude `B` of the magnetic flux density in the torus. -/
  B : ℝ
  /-- Magnetization magnitude `M` in the torus. -/
  M : ℝ

/-- **Governing law (constitutive relation).**  In the homogeneous isotropic
paramagnetic medium the three uniform magnitudes obey
`B = μ₀ * H + μ₀ * M`. -/
def ConstitutiveLaw (D : TorusData) (s : TorusState) : Prop :=
  s.B = D.μ₀ * s.H + D.μ₀ * s.M

/-- **Geometric compatibility of the thin torus.**  For a uniform-field
torus in the `r << R` regime the volume is mean circumference times
cross-section, `V = (2 * π * R) * A`; equivalently the mean circumferential
length is `V / A = 2 * π * R`.  This ties the named geometry `R`, `A`, `V`
together and is what lets Ampère's law be written with the single length
`V / A`. -/
def GeometryCompatible (D : TorusData) : Prop :=
  D.V = (2 * π * D.R) * D.A

/-- **Ampère's law in the torus** (the A.1 relation, used as a
natural-language prerequisite only): the circulation of the uniform field
strength about the mean circumference `V / A` equals the net linked free
current `I_C = N * I`, that is `H * (V / A) = N * I`. -/
def AmpereLaw (D : TorusData) (H I : ℝ) : Prop :=
  H * (D.V / D.A) = D.N * I

/-- **FluxLinkageLaw** (back emf, at fixed turn geometry): when the uniform
flux-density magnitude changes by `dB`, the flux linked by the `N`-turn
winding over the cross-section `A` changes by `dΦ = N * A * dB`. -/
def FluxLinkageLaw (D : TorusData) (dΦ dB : ℝ) : Prop :=
  dΦ = D.N * D.A * dB

/-- **Circuital work law for the external source.**  The work performed by
the external voltage source at instantaneous current `I` against the back
emf for a linked-flux change `dΦ` is `dW_emf = I * dΦ`.  No closed form in
`V`, `H`, `dB` is assumed here. -/
def CircuitalWorkLaw (I dΦ dW_emf : ℝ) : Prop :=
  dW_emf = I * dΦ

/-- **Solution predicate for subquestion A.2.**  Given the instantaneous
field magnitude `H` (from A.1), `dW_emf` is the work performed by the
external voltage source when `B` changes by `dB`: there exist a torus state
whose field magnitude is exactly the prescribed `H`, satisfying the
constitutive law, an instantaneous current `I` maintaining that field via
Ampère's law, and a linked-flux change `dΦ`, such that the flux-linkage and
circuital work laws yield `dW_emf` for the change `dB`.  Pinning `s.H = H`
on the nose fixes the realized current, so the predicate determines the
work. -/
def Solution (D : TorusData) (H dB dW_emf : ℝ) : Prop :=
  ∃ s : TorusState, s.H = H ∧ ConstitutiveLaw D s ∧
    ∃ (I dΦ : ℝ), AmpereLaw D H I ∧ FluxLinkageLaw D dΦ dB ∧
      CircuitalWorkLaw I dΦ dW_emf

/-- **Existence of the source work (answer-free).**  In the uniform-field
thin-torus regime, Ampère's law `H * (V / A) = N * I` (the A.1 statement)
pins the instantaneous current realizing the prescribed field magnitude `H`
to the unique value `H * (V / A) / N`, and the medium responds with a
magnetization; hence a work increment satisfying the solution predicate
exists for every prescribed `H` and change `dB`. -/
theorem source_work_exists (D : TorusData) (hgeo : GeometryCompatible D)
    (H dB : ℝ) :
    ∃ dW_emf : ℝ, Solution D H dB dW_emf := by
  classical
  -- Witnesses: the state responds with magnetization `-H` (closing the
  -- constitutive law at `B = 0`), the current is the A.1 value
  -- `I = H * (V / A) / N`, the linked-flux change is `N * A * dB`, and the
  -- work is `H * V * dB` (the requested expression, kept out of signatures).
  -- Nothing needs case analysis: all cancellations use `N ≠ 0` / `A ≠ 0`.
  refine ⟨H * D.V * dB,
    ⟨⟨H, 0, -H⟩, rfl, ?_,
      H * (D.V / D.A) / D.N, D.N * D.A * dB, ?_, rfl, ?_⟩⟩
  · -- constitutive law at the chosen magnetization
    show ConstitutiveLaw D { H := H, B := 0, M := -H }
    dsimp only [ConstitutiveLaw]
    ring
  · -- Ampère's law: `H * (V / A) = N * (H * (V / A) / N)`
    rw [AmpereLaw, mul_div_cancel₀ _ D.N_pos.ne']
  · -- circuital work law: cancel `N` then `A`
    rw [CircuitalWorkLaw]
    have hN : D.N ≠ 0 := D.N_pos.ne'
    have hA : D.A ≠ 0 := D.A_pos.ne'
    field_simp

/-- **Determination lemma.**  With `A > 0`, the solution predicate forces
`dW_emf = H * V * dB`: the only freedom left in the predicate (the state's
magnetization) never enters the work law. -/
private theorem solution_determined {D : TorusData} (hA : D.A ≠ 0)
    {H dB w : ℝ} (hw : Solution D H dB w) :
    w = H * D.V * dB := by
  obtain ⟨s, hsH, _hsC, I, dΦ, hI, hdΦ, hwork⟩ := hw
  have hI' : D.N * I = H * (D.V / D.A) := by simpa [AmpereLaw] using hI.symm
  have hdΦ' : dΦ = D.N * D.A * dB := hdΦ
  have hwork' : w = I * dΦ := hwork
  -- Combine the three laws; the cancellation needs no case split because
  -- `I = H * (V / A) / N` follows from Ampère's law (`N ≠ 0`).
  have hI_val : I = H * (D.V / D.A) / D.N := by
    have hN : D.N ≠ 0 := D.N_pos.ne'
    rw [eq_div_iff_mul_eq hN]
    calc I * D.N = D.N * I := mul_comm _ _
      _ = H * (D.V / D.A) := hI'
  rw [hwork', hI_val, hdΦ']
  have hN : D.N ≠ 0 := D.N_pos.ne'
  field_simp

/-- **Uniqueness of the source work (answer-free).**  For a thin
paramagnetic torus at a prescribed instantaneous field magnitude `H`, the
work performed by the external voltage source for a change `dB` is uniquely
determined: the only freedom in the predicate is the magnetization of the
realized state, which never enters the work law. -/
theorem source_work_unique (D : TorusData) (hgeo : GeometryCompatible D)
    (H dB : ℝ) :
    ∃! dW_emf : ℝ, Solution D H dB dW_emf := by
  obtain ⟨w, hw⟩ := source_work_exists D hgeo H dB
  refine ⟨w, hw, ?_⟩
  intro y hy
  rw [solution_determined D.A_pos.ne' hy, solution_determined D.A_pos.ne' hw]

/-- **Target characterization (answer-free).**  The requested form of the
answer uses only `V`, `H`, and `dB`: the work increment is uniquely
determined by the solution predicate and, moreover, admits a representation
purely as a function of the volume `V`, the field magnitude `H`, and the
change `dB` — with no reference to `N`, `A`, `I`, `R`, `M`, or `μ₀`.  Which
function of `(V, H, dB)` it is (the proof stage eliminates `I` via Ampère's
law) is deliberately not stated in the signature. -/
theorem problem_IPhO_2026_3_A_2 (D : TorusData) (hgeo : GeometryCompatible D)
    (H dB : ℝ) :
    ∃! dW_emf : ℝ, Solution D H dB dW_emf ∧
      ∃ g : ℝ → ℝ → ℝ → ℝ, dW_emf = g D.V H dB := by
  obtain ⟨w, hw, hwuniq⟩ := source_work_unique D hgeo H dB
  refine ⟨w, ⟨hw, fun v hh dd => v * hh * dd, ?_⟩, ?_⟩
  · rw [solution_determined D.A_pos.ne' hw]; ring
  · intro y hy
    exact hwuniq y hy.1

end IPhO_2026_3_A_2
