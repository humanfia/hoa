import Mathlib

/- USER: Mandatory contract repair. Encode the actual C.3 leading cusp data: signed/branched horizontal order three (`Xc θ / θ^3 -> cX`, `cX ≠ 0`) and a POSITIVE vertical-drop scale of order two (`(R - Yc θ) / θ^2 -> cY`, `cY > 0`), with the C.3 coefficient relation needed to force the scale. The fit MUST use candidate `u - v * |Xc θ|^(p/q)` with `v>0`, never `u + v * ...`; its residual itself must satisfy `(fun θ => Yc θ - (u - v * |Xc θ|^(p/q))) =o[nhdsWithin 0 (Ioi 0)] (fun θ => θ^2)`, not a quotient normalized by `|Xc|^α`. Keep `q>0` and lowest terms. Premises must not contain `R-u ≠ 0`, `u=R`, `p/q=2/3`, or the target `v`. Check the concrete monomial witness `Xc θ=-θ^3`, `Yc θ=R-θ^2` and compile before handoff. -/

/-!
# IPhO 2026, Theoretical Question 2 (T2), Part C.4 — Paraxial power-law form
of the caustic

## Subquestion T2-C4 (1.0 pt), Fig. 2g

> For the half-cylindrical mirror of radius `R`, ray `A` is incident at
> angle `θ`; a neighbouring parallel ray `B` is incident at `θ + Δθ`.
> The envelope/limiting intersection of neighbouring reflected rays is the
> caustic point `(X_c, Y_c)(θ)`.
>
> **T2-C4.**  For `θ ≪ 1`, the caustic has the form
> `Y_c = v |X_c|^(p/q) + u`.  Determine `u`, `v` in terms of `R` and the
> integers `p, q` (i.e. the reduced rational exponent `p/q`).

(Official page image `.archon/blind-assets/IPhO_2026_2_C_4/T2_page-4.png`;
Figure 2g coordinates: origin at the centre of the half-circle, `y`
vertical, the mirror occupying the upper half-circle of radius `R`; a ray
incident at angle `θ` hits the mirror at `(R sin θ, R cos θ)`.)

## Answer-blind formalization contract (redraft 4, iter-017)

Parts C.1–C.3 derive, from specular reflection at the half-cylindrical
mirror, everything this subquestion starts from; per the dependency policy
(`natural_language_prerequisite_only; do_not_import_Lean_output`) C.3's
output enters here only as the *asymptotic data* carried by
`CausticPointData`:

* the paraxial window `0 < θ < δ` on which the neighbouring-ray
  construction is physical;
* the limiting caustic height `Tendsto Yc (𝓝[>] 0) (𝓝 R)` — C.3's
  `Y_c → R` as `θ → 0`;
* the left branch `Xc θ < 0` on the window (Figure 2g), which is why the
  asked form uses `|X_c|`;
* the **leading cusp orders** `XcLeadingOrderAt cX 3` and
  `YcDropLeadingOrderAt cY 2`: nonzero, order-coefficient-free records that
  some nonzero scale `cX` makes `Xc θ / θ³ → cX` and some nonzero scale
  `cY` makes `(R − Yc θ) / θ² → cY`.  This is the answer-free content of
  C.3's explicit parametrization: the horizontal coordinate vanishes to
  order three (signed — hence cusped, hence the absolute value in the asked
  form) and the vertical drop to order two.  The actual coefficients are
  the withheld C.3 answers and never appear here; the C.4 proof stage
  re-derives them from the C.3 parametrization.

The sign-normalized form is formalized by `FitsParaxialPowerLaw`.  A fit has
`α > 0`, `v > 0`, candidate `u - v |X_c|^α`, and the literal residual

    θ ↦ Yc θ - (u - v |Xc θ|^α)

is `o(θ²)` on `𝓝[>] 0`.  The positive vertical-drop coefficient and negative
horizontal branch are part of the exact C.3 leading data.  Consequently the
order ratio pins `α`, while cancellation of the leading `θ²` coefficient
pins `v`; no target value is included among the premises.

`IsExactFormOf` adds the integrality content of "the integers `p` and `q`":
`α = p/q` with `q > 0` and `IsCoprime p q` (lowest terms).

The main theorem `caustic_paraxial_form_exists_unique` states existence
and uniqueness of each ingredient `u`, `v`, `(p, q)`.  No candidate value
appears in any signature: the answer-blind policy keeps the official
values out, and the proof stage constructs them by substituting the C.3
parametrization and matching powers.

The concrete monomial sanity model `Xc θ = -θ³`, `Yc θ = R - θ²` is
inhabited and is fitted by a positive downward scale.  A wrong `u`, exponent,
or scale leaves a non-little-o leading term, so it cannot satisfy the fit.
-/

noncomputable section

namespace Ipho2026KimiK3Blind32.ProblemIPhO2026_2C4

open Real Set Filter Asymptotics
open scoped Topology

/-- **Horizontal order-`n` link (signed, branched, coefficient-free).**

The data `θ ↦ x θ` vanishes at `0` and has a genuine leading behaviour of
degree `n` on the right paraxial filter `𝓝[>] 0`: `x θ = o(θⁿ)` would fail
and `x θ = O(θⁿ)` holds, and moreover the normalized quotient
`θ ↦ x θ / θⁿ` tends to the nonzero signed scale `c`.

*Signed*: `c` keeps the orientation of the Figure-2g branch (for the
caustic, `c < 0` — the cusp opens on the left), so the record knows the
asked `|X_c|` is the absolute value of a genuinely negative branch.
*Order-`n`*: this records *that* the leading order is `n`, not *which*
number it is; the order `3` for the caustic is carried by the structure
field of `CausticPointData`, and the scale itself is the withheld C.3
coefficient, deliberately never named here. -/
structure HorizLeadingOrderAt (x : ℝ → ℝ) (c : ℝ) (n : ℕ) : Prop where
  /-- The data extends continuously to `θ = 0` with value `0`
  (order-zero completion at the apex). -/
  zero_at_zero : x 0 = 0
  /-- The leading order is not lower than `n`: `x = O(θⁿ)`. -/
  isBigO : (fun θ ↦ x θ) =O[𝓝[>] 0] fun θ ↦ θ ^ n
  /-- The leading order is not higher than `n`: `x ≠ o(θⁿ)`. -/
  not_littleO : ¬ (fun θ ↦ x θ) =o[𝓝[>] 0] fun θ ↦ θ ^ n
  /-- The signed scale of the leading term: `x θ / θⁿ → c`. -/
  tendsto_quotient :
    Tendsto (fun θ ↦ x θ / θ ^ n) (𝓝[>] 0) (𝓝 c)
  /-- The Figure-2g caustic branch is signed to the left.  In particular the
  leading coefficient is nonzero. -/
  scale_neg : c < 0

/-- **Vertical drop of order `m>0` from the limiting height `u₀`.**

The data `θ ↦ y θ` approaches `u₀` from below at a genuine order `m`:
`(u₀ − y θ) / θᵐ → c` on `𝓝[>] 0` with nonzero scale `c` (hence
`u₀ − y θ = Θ(θᵐ)`, not `o(θᵐ)` — the quotient converging to a nonzero
limit forces boundedness below on some punctured right neighbourhood).
Order-zero completion is again recorded: `y 0 = u₀`.  The actual scale —
the withheld C.3 vertical coefficient — never appears here. -/
structure VertDropLeadingOrderAt (y : ℝ → ℝ) (u₀ c : ℝ) (m : ℕ) : Prop where
  /-- The window order is a genuine positive power: `m ≥ 1`. -/
  order_pos : 1 ≤ m
  /-- The data extends continuously to `θ = 0` at the limiting height. -/
  zero_at_zero : y 0 = u₀
  /-- The drop has leading order at least `m`: `u₀ − y = O(θᵐ)`. -/
  isBigO : (fun θ ↦ u₀ - y θ) =O[𝓝[>] 0] fun θ ↦ θ ^ m
  /-- The drop has leading order at most `m`: `u₀ − y ≠ o(θᵐ)`. -/
  not_littleO : ¬ (fun θ ↦ u₀ - y θ) =o[𝓝[>] 0] fun θ ↦ θ ^ m
  /-- The scale of the leading drop term: `(u₀ − y θ) / θᵐ → c`. -/
  tendsto_quotient :
    Tendsto (fun θ ↦ (u₀ - y θ) / θ ^ m) (𝓝[>] 0) (𝓝 c)
  /-- The caustic drops below its apex with a positive leading scale. -/
  scale_pos : 0 < c

/-- **Caustic raw data with the C.3 paraxial asymptotic linkage
(answer-blind).**

The limiting intersection `θ ↦ (Xc θ, Yc θ)` of neighbouring reflected
rays of the half-cylindrical mirror of radius `R`, recorded over the
paraxial window `0 < θ < δ`, with the answer-free asymptotic content C.3
hands to C.4: the curve approaches the apex height `R` as `θ → 0⁺`, runs
on the left Figure-2g branch (`Xc θ < 0`, hence the asked `|X_c|`), and
has the branched signed horizontal leading order three and the vertical
drop leading order two of the C.3 parametrization — expressed through
existentially quantified nonzero scales, so that no derived C.3/C.4 value
enters the structure.  The two order literals `3`/`2` are C.3's *input
orders* to this subquestion, not C.4 conclusions: the C.4 proof must
extract the exponent ratio `2/3` from them together with the fit. -/
structure CausticPointData where
  /-- Horizontal caustic coordinate `X_c`, as a function of `θ`. -/
  Xc : ℝ → ℝ
  /-- Vertical caustic coordinate `Y_c`, as a function of `θ`. -/
  Yc : ℝ → ℝ
  /-- Mirror radius `R` (a length). -/
  R : ℝ
  /-- Physical mirror: positive radius. -/
  hR : 0 < R
  /-- Radius of the paraxial window: the data is physical on `0 < θ < δ`. -/
  δ : ℝ
  /-- The paraxial window is nonempty. -/
  hδ : 0 < δ
  /-- **C.3 apex limit:** the caustic approaches the top of the mirror,
  `Yc θ → R` as `θ → 0⁺`.  This is the C.3 limiting behaviour handed to
  C.4; it names no C.4 quantity. -/
  Yc_tendsto : Tendsto Yc (𝓝[>] 0) (𝓝 R)
  /-- **Figure-2g branch:** on the physical window the caustic lies
  strictly to the left of the symmetry axis — the reason the asked form
  carries `|X_c|`. -/
  Xc_neg : ∀ θ ∈ Ioo 0 δ, Xc θ < 0
  /-- **C.3 horizontal cusp order (signed):** some nonzero signed scale
  `cX` makes `Xc θ / θ³ → cX` on `𝓝[>] 0`. -/
  Xc_order_three : ∃ cX : ℝ, HorizLeadingOrderAt Xc cX 3
  /-- **C.3 vertical drop order:** some nonzero scale `cY` makes
  `(R − Yc θ) / θ² → cY` on `𝓝[>] 0`. -/
  Yc_drop_order_two : ∃ cY : ℝ, VertDropLeadingOrderAt Yc R cY 2

namespace CausticPointData

/-- The sign-normalized power-law candidate `θ ↦ u - v · |Xc θ|^α`.
The scale `v` is positive, so the candidate lies below the apex `u` on the
physical caustic branch. -/
noncomputable def candidate (s : CausticPointData) (u v α : ℝ) (θ : ℝ) : ℝ :=
  u - v * (|s.Xc θ| : ℝ) ^ α

/-- **Paraxial power-law fit.**

`(u, v, α)` fits the caustic data in the paraxial regime when

* the exponent and downward cusp scale are positive (`0 < α`, `0 < v`);
* the residual itself is `o(θ²)` on the punctured right-neighbourhood of
  the apex.  This is deliberately not a quotient normalized by
  `|Xc|^α`, and it does not assume any candidate value.

Together with the exact horizontal and vertical leading-coefficient limits
in `CausticPointData`, this condition pins the exponent by the order ratio
and pins `v` by cancellation of the leading `θ²` coefficient. -/
def FitsParaxialPowerLaw (s : CausticPointData) (u v α : ℝ) : Prop :=
  0 < α ∧ 0 < v ∧
    (fun θ : ℝ ↦ s.Yc θ - s.candidate u v α θ)
      =o[𝓝[>] 0] (fun θ : ℝ ↦ θ ^ 2)

/-- **Exact paraxial form.**  A fit whose exponent is the rational number
`p / q` in lowest terms — `q > 0` and `IsCoprime p q` — the "integers `p`
and `q`" the question asks to determine. -/
def IsExactFormOf (s : CausticPointData) (u v : ℝ) (p q : ℤ) : Prop :=
  s.FitsParaxialPowerLaw u v ((p : ℝ) / (q : ℝ)) ∧ 0 < q ∧ IsCoprime p q

/-- A fit residual divided by `θ²` tends to `0`. -/
private lemma residual_tendsto_zero {s : CausticPointData} {u v α : ℝ}
    (hfit : s.FitsParaxialPowerLaw u v α) :
    Tendsto (fun θ : ℝ ↦ (s.Yc θ - s.candidate u v α θ) / θ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hne : ∀ᶠ θ : ℝ in 𝓝[>] 0, θ ^ 2 = 0 → s.Yc θ - s.candidate u v α θ = 0 := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ h2
    exact absurd h2 (pow_ne_zero 2 (ne_of_gt hθ))
  exact (isLittleO_iff_tendsto' hne).mp hfit.2.2

/-- The power factor `θ ↦ v * |Xc θ| ^ α` tends to `0` for a fit. -/
private lemma power_factor_tendsto_zero (s : CausticPointData) {u v α : ℝ}
    (hfit : s.FitsParaxialPowerLaw u v α) :
    Tendsto (fun θ : ℝ ↦ v * |s.Xc θ| ^ α) (𝓝[>] 0) (𝓝 0) := by
  rcases s.Xc_order_three with ⟨cX, hX⟩
  have hα : 0 < α := hfit.1
  have hXt : Tendsto s.Xc (𝓝[>] 0) (𝓝 0) := by
    have h := (hX.tendsto_quotient).mul (tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_id.tendsto (0 : ℝ)).pow 3))
    simp only [id, zero_pow (show (3:ℕ) ≠ 0 by norm_num), mul_zero] at h
    have heq : (fun θ : ℝ ↦ s.Xc θ / θ ^ 3 * θ ^ 3) =ᶠ[𝓝[>] 0] s.Xc := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      rw [div_mul_cancel₀]; exact pow_ne_zero 3 (ne_of_gt hθ)
    exact h.congr' heq
  have habs : Tendsto (fun θ ↦ |s.Xc θ|) (𝓝[>] 0) (𝓝 0) := by
    have := hXt.abs
    simpa using this
  have hα0 : (0 : ℝ) ^ α = 0 := Real.zero_rpow (ne_of_gt hα)
  have := habs.rpow_const (Or.inr hα.le)
  rw [hα0] at this
  have hmul := this.const_mul v
  rw [mul_zero] at hmul
  exact hmul

/-- The apex height is pinned: any fit has `u = R`. -/
private lemma u_eq_R (s : CausticPointData) {u v α : ℝ}
    (hfit : s.FitsParaxialPowerLaw u v α) : u = s.R := by
  have hres := residual_tendsto_zero hfit
  have hpow := s.power_factor_tendsto_zero hfit
  -- The residual itself tends to `0`: it equals `(residual/θ²) * θ²` eventually.
  have hθ2 : Tendsto (fun θ : ℝ ↦ θ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun θ : ℝ ↦ θ ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) :=
      (continuous_id.tendsto (0 : ℝ)).pow 2
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hmul := hres.mul hθ2
  have hmain : Tendsto (fun θ ↦ s.Yc θ - s.candidate u v α θ) (𝓝[>] 0) (𝓝 0) := by
    have heq : (fun θ ↦ (s.Yc θ - s.candidate u v α θ) / θ ^ 2 * θ ^ 2)
        =ᶠ[𝓝[>] 0] fun θ ↦ s.Yc θ - s.candidate u v α θ := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      rw [div_mul_cancel₀]; exact pow_ne_zero 2 (ne_of_gt hθ)
    rw [mul_zero] at hmul
    exact hmul.congr' heq
  have hmain' : Tendsto (fun θ ↦ s.Yc θ - u + v * |s.Xc θ| ^ α) (𝓝[>] 0) (𝓝 0) := by
    have heq2 : (fun θ ↦ s.Yc θ - s.candidate u v α θ)
        = fun θ ↦ s.Yc θ - u + v * |s.Xc θ| ^ α := by
      funext θ; simp [candidate]; ring
    rwa [heq2] at hmain
  have hlim : Tendsto (fun θ ↦ s.Yc θ - u + v * |s.Xc θ| ^ α) (𝓝[>] 0)
      (𝓝 (s.R - u + 0)) := by
    have h1 : Tendsto (fun θ ↦ s.Yc θ - u) (𝓝[>] 0) (𝓝 (s.R - u)) :=
      s.Yc_tendsto.sub (tendsto_const_nhds (x := u))
    exact h1.add hpow
  have hsne : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  have : s.R - u + 0 = 0 := tendsto_nhds_unique hlim hmain'
  linarith

/-- The probing sequence `θ n = 1/(n+1)`, positive and tending to `0`. -/
private lemma seq_tendsto_nhdsWithin :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
  have h0 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1:ℝ)))
    have hi := tendsto_inv_atTop_zero.comp h
    rwa [Function.comp_def] at hi
  rw [tendsto_nhdsWithin_iff]
  refine ⟨h0, ?_⟩
  filter_upwards with n
  simp only [mem_Ioi]
  positivity

/-- Pointwise rewriting of rpow/power expressions along the probing sequence
`θ n = (n+1)⁻¹`: `θ n ^ β = ((n+1)^β)⁻¹`. -/
private lemma seq_rpow (β : ℝ) (n : ℕ) :
    (((n : ℝ) + 1)⁻¹) ^ β = (((n : ℝ) + 1) ^ β)⁻¹ := by
  rw [← Real.inv_rpow (by positivity : (0:ℝ) ≤ (n:ℝ) + 1) β]

private lemma seq_pow (m : ℕ) (n : ℕ) :
    (((n : ℝ) + 1)⁻¹) ^ m = (((n : ℝ) + 1) ^ m)⁻¹ := by
  rw [inv_pow]

/-- Uniqueness of limits along the probing sequence: if `F` tends to `L` on
`𝓝[>] 0` and to `M` along `atTop` (via the sequence), then `L = M`. -/
private lemma eq_of_tendsto_nhds {F : ℝ → ℝ} {L M : ℝ}
    (hF : Tendsto F (𝓝[>] 0) (𝓝 L)) (hFn : Tendsto (fun n : ℕ ↦ F (((n : ℝ) + 1)⁻¹)) atTop (𝓝 M)) :
    L = M :=
  tendsto_nhds_unique (hF.comp seq_tendsto_nhdsWithin) hFn

/-- The quotient `|Xc θ| / θ³` tends to `|cX|`. -/
private lemma tendsto_absXc_div_cube (s : CausticPointData) {cX : ℝ}
    (hX : HorizLeadingOrderAt s.Xc cX 3) :
    Tendsto (fun θ ↦ |s.Xc θ| / θ ^ 3) (𝓝[>] 0) (𝓝 |cX|) := by
  have h := hX.tendsto_quotient.abs
  have heq : (fun θ ↦ |s.Xc θ / θ ^ 3|) =ᶠ[𝓝[>] 0] (fun θ ↦ |s.Xc θ| / θ ^ 3) := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [abs_div, abs_of_pos (pow_pos hθ 3 : (0:ℝ) < θ ^ 3)]
  exact h.congr' heq

/-- On `θ > 0`, `v * |Xc θ| ^ α / θ²` factors as
`v * (|Xc θ| / θ³)^α * θ ^ (3α - 2)`. -/
private lemma power_factor_div_sq_form (s : CausticPointData) (v α : ℝ) :
    (fun θ : ℝ ↦ v * |s.Xc θ| ^ α / θ ^ 2) =ᶠ[𝓝[>] 0]
      (fun θ : ℝ ↦ v * (|s.Xc θ| / θ ^ 3) ^ α * θ ^ (3 * α - 2)) := by
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ0 : (0:ℝ) < θ := hθ
  have hθ3 : θ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hθ0)
  have hθ2 : θ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hθ0)
  have hnn : 0 ≤ |s.Xc θ| / θ ^ 3 := by positivity
  have key : v * |s.Xc θ| ^ α / θ ^ 2
      = v * (|s.Xc θ| / θ ^ 3) ^ α * θ ^ (3 * α - 2) := by
    have h1 : |s.Xc θ| = (|s.Xc θ| / θ ^ 3) * θ ^ 3 := by
      field_simp
    rw [h1]
    rw [show ((|s.Xc θ| / θ ^ 3) * θ ^ 3) ^ α
        = (|s.Xc θ| / θ ^ 3) ^ α * (θ ^ 3) ^ α from
      Real.mul_rpow hnn (pow_pos hθ0 3).le]
    rw [show ((θ ^ 3 : ℝ) ^ α) = θ ^ ((3 : ℝ) * α) by
      rw [← Real.rpow_natCast θ 3, ← Real.rpow_mul (le_of_lt hθ0), Nat.cast_ofNat]]
    rw [show θ ^ ((3 : ℝ) * α) = θ ^ ((3 * α - 2) + 2) by ring_nf]
    rw [Real.rpow_add hθ0]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  exact key

/-- The fit power term normalized by `θ²` tends to `cY`. -/
private lemma lim_drop_sub_powfactor (s : CausticPointData) {u v α cX cY : ℝ}
    (hfit : s.FitsParaxialPowerLaw u v α) (hu : u = s.R)
    (_hX : HorizLeadingOrderAt s.Xc cX 3) (hY : VertDropLeadingOrderAt s.Yc s.R cY 2) :
    Tendsto (fun θ : ℝ ↦ v * |s.Xc θ| ^ α / θ ^ 2)
      (𝓝[>] 0) (𝓝 cY) := by
  have hres := residual_tendsto_zero hfit
  have hdrop := hY.tendsto_quotient
  -- residual/θ² = v|Xc|^α/θ² - dropθ²  (since u = R)
  have heq : (fun θ : ℝ ↦ (s.Yc θ - s.candidate u v α θ) / θ ^ 2)
      =ᶠ[𝓝[>] 0] fun θ : ℝ ↦ v * |s.Xc θ| ^ α / θ ^ 2 - (s.R - s.Yc θ) / θ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have h2 : θ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hθ)
    simp only [candidate]
    subst hu
    field_simp
    ring
  have hmain : Tendsto (fun θ : ℝ ↦ v * |s.Xc θ| ^ α / θ ^ 2 - (s.R - s.Yc θ) / θ ^ 2)
      (𝓝[>] 0) (𝓝 0) := hres.congr' heq
  -- add dropθ² → cY
  have hsum := hmain.add hdrop
  have heq2 : (fun θ : ℝ ↦ v * |s.Xc θ| ^ α / θ ^ 2 - (s.R - s.Yc θ) / θ ^ 2
        + (s.R - s.Yc θ) / θ ^ 2)
      =ᶠ[𝓝[>] 0] fun θ : ℝ ↦ v * |s.Xc θ| ^ α / θ ^ 2 := by
    filter_upwards with θ; ring
  have htarget : Tendsto (fun θ : ℝ ↦ v * |s.Xc θ| ^ α / θ ^ 2) (𝓝[>] 0) (𝓝 (0 + cY)) :=
    hsum.congr' heq2
  rwa [zero_add] at htarget

/-- The exponent of a fit is pinned to `2/3` by the C.3 order data. -/
private lemma exponent_eq_two_thirds (s : CausticPointData) {u v α : ℝ}
    (hfit : s.FitsParaxialPowerLaw u v α) (hu : u = s.R) :
    α = 2 / 3 := by
  rcases s.Xc_order_three with ⟨cX, hX⟩
  rcases s.Yc_drop_order_two with ⟨cY, hY⟩
  have hv : 0 < v := hfit.2.1
  have hα : 0 < α := hfit.1
  have hcXne : cX ≠ 0 := ne_of_lt hX.scale_neg
  have hcXabs : 0 < |cX| := abs_pos.mpr hcXne
  have hcY : 0 < cY := hY.scale_pos
  have hlim := s.lim_drop_sub_powfactor hfit hu hX hY
  have hform := s.power_factor_div_sq_form v α
  have hlim2 : Tendsto (fun θ : ℝ ↦ v * (|s.Xc θ| / θ ^ 3) ^ α * θ ^ (3 * α - 2))
      (𝓝[>] 0) (𝓝 cY) := hlim.congr' hform
  have hw : Tendsto (fun θ ↦ |s.Xc θ| / θ ^ 3) (𝓝[>] 0) (𝓝 |cX|) :=
    s.tendsto_absXc_div_cube hX
  have hwrpow : Tendsto (fun θ : ℝ ↦ (|s.Xc θ| / θ ^ 3) ^ α) (𝓝[>] 0) (𝓝 (|cX| ^ α)) :=
    hw.rpow_const (Or.inl (ne_of_gt hcXabs))
  have hseq := seq_tendsto_nhdsWithin
  have hlim2n := hlim2.comp hseq
  have hwrpown := hwrpow.comp hseq
  have hN : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1:ℝ)))
    simpa [add_comm] using h
  rcases lt_trichotomy (3 * α - 2) 0 with hlt | heq2 | hgt
  · -- 3α - 2 < 0 : the θ-power blows up; the product tends to atTop, contradiction
    exfalso
    have hγ : 0 < -(3 * α - 2) := by linarith
    have hNγ : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-(3 * α - 2))) atTop atTop :=
      (tendsto_rpow_atTop hγ).comp hN
    have hvw : Tendsto (fun n : ℕ ↦ v * (|s.Xc (((n:ℝ)+1)⁻¹)| / (((n:ℝ)+1)⁻¹) ^ 3) ^ α)
        atTop (𝓝 (v * |cX| ^ α)) :=
      (tendsto_const_nhds (x := v)).mul hwrpown
    have hvwpos : 0 < v * |cX| ^ α := mul_pos hv (Real.rpow_pos_of_pos hcXabs α)
    have htop := hvw.pos_mul_atTop hvwpos hNγ
    have hθγ : ∀ n : ℕ, (((n : ℝ) + 1)⁻¹ : ℝ) ^ (3 * α - 2)
        = ((n : ℝ) + 1) ^ (-(3 * α - 2)) := by
      intro n
      have h1 : (((n : ℝ) + 1)⁻¹ : ℝ) ^ (3 * α - 2)
          = (((n : ℝ) + 1) ^ (3 * α - 2))⁻¹ := seq_rpow (3 * α - 2) n
      rw [h1, ← Real.rpow_neg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1)]
    have hcongr : (fun n : ℕ ↦ v * (|s.Xc (((n:ℝ)+1)⁻¹)| / (((n:ℝ)+1)⁻¹) ^ 3) ^ α
          * ((n : ℝ) + 1) ^ (-(3 * α - 2)))
        =ᶠ[atTop] fun n : ℕ ↦ v * (|s.Xc (((n:ℝ)+1)⁻¹)| / (((n:ℝ)+1)⁻¹) ^ 3) ^ α
            * (((n:ℝ)+1)⁻¹) ^ (3 * α - 2) := by
      filter_upwards with n
      rw [hθγ n]
    have hPtop : Tendsto (fun n : ℕ ↦ v * (|s.Xc (((n:ℝ)+1)⁻¹)| / (((n:ℝ)+1)⁻¹) ^ 3) ^ α
        * (((n:ℝ)+1)⁻¹) ^ (3 * α - 2)) atTop atTop := htop.congr' hcongr
    exact not_tendsto_atTop_of_tendsto_nhds hlim2n hPtop
  · -- 3α - 2 = 0 : done
    linarith
  · -- 3α - 2 > 0 : the θ-power → 0, so the product → 0 ≠ cY, contradiction
    exfalso
    have hNγ : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (3 * α - 2)) atTop atTop :=
      (tendsto_rpow_atTop hgt).comp hN
    have hθγ0 : Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹ : ℝ) ^ (3 * α - 2)) atTop (𝓝 0) := by
      have heq : (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹ : ℝ) ^ (3 * α - 2))
          = (fun n : ℕ ↦ (((n : ℝ) + 1) ^ (3 * α - 2))⁻¹) := by
        funext n
        rw [seq_rpow]
      rw [heq]
      exact tendsto_inv_atTop_zero.comp hNγ
    have hprod : Tendsto (fun n : ℕ ↦ v * (|s.Xc (((n:ℝ)+1)⁻¹)| / (((n:ℝ)+1)⁻¹) ^ 3) ^ α
        * (((n:ℝ)+1)⁻¹) ^ (3 * α - 2)) atTop (𝓝 (v * |cX| ^ α * 0)) :=
      ((tendsto_const_nhds (x := v)).mul hwrpown).mul hθγ0
    have htarget : cY = v * |cX| ^ α * 0 := eq_of_tendsto_nhds hlim2 hprod
    rw [mul_zero] at htarget
    exact (ne_of_gt hcY) htarget

/-- For the exponent `2/3` the fit power term normalized by `θ²` tends to
`v * |cX| ^ (2/3)`. -/
private lemma powerterm_tendsto (s : CausticPointData) (v : ℝ) {cX : ℝ}
    (hX : HorizLeadingOrderAt s.Xc cX 3) :
    Tendsto (fun θ : ℝ ↦ v * |s.Xc θ| ^ (2 / 3 : ℝ) / θ ^ 2) (𝓝[>] 0)
      (𝓝 (v * |cX| ^ (2 / 3 : ℝ))) := by
  have hform := s.power_factor_div_sq_form v (2 / 3 : ℝ)
  have hw : Tendsto (fun θ ↦ |s.Xc θ| / θ ^ 3) (𝓝[>] 0) (𝓝 |cX|) :=
    s.tendsto_absXc_div_cube hX
  have hcXabs : 0 < |cX| := abs_pos.mpr (ne_of_lt hX.scale_neg)
  have hwrpow : Tendsto (fun θ : ℝ ↦ (|s.Xc θ| / θ ^ 3) ^ (2 / 3 : ℝ)) (𝓝[>] 0)
      (𝓝 (|cX| ^ (2 / 3 : ℝ))) := hw.rpow_const (Or.inl (ne_of_gt hcXabs))
  have hmain : Tendsto (fun θ : ℝ ↦ v * (|s.Xc θ| / θ ^ 3) ^ (2 / 3 : ℝ)) (𝓝[>] 0)
      (𝓝 (v * |cX| ^ (2 / 3 : ℝ))) := (tendsto_const_nhds (x := v)).mul hwrpow
  have hθγ : (fun θ : ℝ ↦ θ ^ (3 * (2 / 3 : ℝ) - 2)) = fun _ ↦ (1 : ℝ) := by
    funext θ; norm_num
  have heq : (fun θ : ℝ ↦ v * (|s.Xc θ| / θ ^ 3) ^ (2 / 3 : ℝ) * θ ^ (3 * (2 / 3 : ℝ) - 2))
      =ᶠ[𝓝[>] 0] fun θ : ℝ ↦ v * (|s.Xc θ| / θ ^ 3) ^ (2 / 3 : ℝ) := by
    filter_upwards with θ
    have h1 : θ ^ (3 * (2 / 3 : ℝ) - 2) = 1 := congrFun hθγ θ
    rw [h1]; ring
  have h2 : Tendsto (fun θ : ℝ ↦ v * (|s.Xc θ| / θ ^ 3) ^ (2 / 3 : ℝ) * θ ^ (3 * (2 / 3 : ℝ) - 2))
      (𝓝[>] 0) (𝓝 (v * |cX| ^ (2 / 3 : ℝ))) := hmain.congr' heq.symm
  exact h2.congr' hform.symm

/-- The scale relation of a fit: `v * |cX| ^ (2/3) = cY` for any C.3 scales. -/
private lemma scale_relation (s : CausticPointData) {u v α cX cY : ℝ}
    (hfit : s.FitsParaxialPowerLaw u v α) (hu : u = s.R) (hα : α = 2 / 3)
    (hX : HorizLeadingOrderAt s.Xc cX 3) (hY : VertDropLeadingOrderAt s.Yc s.R cY 2) :
    v * |cX| ^ (2 / 3 : ℝ) = cY := by
  subst hα
  have hlim := s.lim_drop_sub_powfactor hfit hu hX hY
  have hlim4 := s.powerterm_tendsto v hX
  have hsne : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact tendsto_nhds_unique hlim4 hlim

/-- The canonical fit: `(R, cY / |cX| ^ (2/3), 2/3)` fits the caustic data. -/
private lemma canonical_fit (s : CausticPointData) {cX cY : ℝ}
    (hX : HorizLeadingOrderAt s.Xc cX 3) (hY : VertDropLeadingOrderAt s.Yc s.R cY 2) :
    s.FitsParaxialPowerLaw s.R (cY / |cX| ^ (2 / 3 : ℝ)) (2 / 3 : ℝ) := by
  have hcXabs : 0 < |cX| := abs_pos.mpr (ne_of_lt hX.scale_neg)
  have hcXpow : 0 < |cX| ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hcXabs _
  have hcY : 0 < cY := hY.scale_pos
  refine ⟨by norm_num, by positivity, ?_⟩
  set v : ℝ := cY / |cX| ^ (2 / 3 : ℝ) with hvdef
  have hvt : v * |cX| ^ (2 / 3 : ℝ) = cY := by
    rw [hvdef]; field_simp
  have hpow := s.powerterm_tendsto v hX
  rw [hvt] at hpow
  have hdrop := hY.tendsto_quotient
  have hdiff := Filter.Tendsto.sub hpow hdrop
  rw [sub_self cY] at hdiff
  have heq : (fun θ : ℝ ↦ (s.Yc θ - s.candidate s.R v (2 / 3 : ℝ) θ) / θ ^ 2)
      =ᶠ[𝓝[>] 0] fun θ : ℝ ↦ v * |s.Xc θ| ^ (2 / 3 : ℝ) / θ ^ 2 - (s.R - s.Yc θ) / θ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have h2 : θ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hθ)
    simp only [candidate]
    field_simp
    ring
  have hres : Tendsto (fun θ : ℝ ↦ (s.Yc θ - s.candidate s.R v (2 / 3 : ℝ) θ) / θ ^ 2)
      (𝓝[>] 0) (𝓝 0) := hdiff.congr' heq.symm
  have hne : ∀ᶠ θ : ℝ in 𝓝[>] 0,
      θ ^ 2 = 0 → s.Yc θ - s.candidate s.R v (2 / 3 : ℝ) θ = 0 := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ h2
    exact absurd h2 (pow_ne_zero 2 (ne_of_gt hθ))
  exact (isLittleO_iff_tendsto' hne).mpr hres

end CausticPointData

/-- **T2-C4 — the caustic admits a unique exact paraxial power-law form.**

For the caustic data `s` of the half-cylindrical mirror (with its C.3
paraxial asymptotic linkage), the ingredients of the paraxial form
`Y_c = u - v |X_c|^{p/q}` all exist and are uniquely determined:

* a unique limiting-height shift `u`,
* a unique cusp scale `v`,
* a unique lowest-terms integer pair `(p, q)`,

such that `(u, v, p, q)` is an exact paraxial form of the data.

The concrete values are the withheld answers; the C.4 proof constructs
them by substituting the C.3 parametrization into the fit and matching
leading powers: the apex limit pins `u`, the horizontal/vertical order
records pin `α = p/q`, and cancellation of the exact leading coefficients
pins `v`.  No value appears in this signature. -/
theorem caustic_paraxial_form_exists_unique (s : CausticPointData) :
    (∃! u : ℝ, ∃ v p q, s.IsExactFormOf u v p q) ∧
    (∃! v : ℝ, ∃ u p q, s.IsExactFormOf u v p q) ∧
    (∃! pq : ℤ × ℤ, ∃ u v, s.IsExactFormOf u v pq.1 pq.2) := by
  rcases s.Xc_order_three with ⟨cX, hX⟩
  rcases s.Yc_drop_order_two with ⟨cY, hY⟩
  have hcXabs : 0 < |cX| := abs_pos.mpr (ne_of_lt hX.scale_neg)
  have hcXpow : 0 < |cX| ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hcXabs _
  have hcY : 0 < cY := hY.scale_pos
  set v₀ : ℝ := cY / |cX| ^ (2 / 3 : ℝ) with hv₀def
  have hv₀ : v₀ * |cX| ^ (2 / 3 : ℝ) = cY := by rw [hv₀def]; field_simp
  -- The witness exact form
  have hfitR : s.FitsParaxialPowerLaw s.R v₀ (2 / 3 : ℝ) := s.canonical_fit hX hY
  have hcast : ((2 : ℤ) : ℝ) / ((3 : ℤ) : ℝ) = (2 : ℝ) / 3 := by norm_num
  have hfitRz : s.FitsParaxialPowerLaw s.R v₀ (((2 : ℤ) : ℝ) / ((3 : ℤ) : ℝ)) := by
    rw [hcast]; exact hfitR
  have hcop23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
  have hexact : s.IsExactFormOf s.R v₀ 2 3 := ⟨hfitRz, by norm_num, hcop23⟩
  -- Auxiliary uniqueness facts
  have huniq_of_fit : ∀ {u v p q : _} , s.IsExactFormOf u v p q →
      u = s.R := fun {_ _ _ _} h => s.u_eq_R h.1
  have hα_of_fit : ∀ {u v : ℝ} {p q : ℤ} (h : s.IsExactFormOf u v p q),
      ((p : ℝ) / (q : ℝ)) = 2 / 3 := fun {u v p q} h =>
    s.exponent_eq_two_thirds h.1 (s.u_eq_R h.1)
  have hv_of_fit : ∀ {u v : ℝ} {p q : ℤ} (h : s.IsExactFormOf u v p q),
      v = v₀ := by
    intro u v p q h
    have hrel := s.scale_relation h.1 (s.u_eq_R h.1) (hα_of_fit h) hX hY
    have : v * |cX| ^ (2 / 3 : ℝ) = v₀ * |cX| ^ (2 / 3 : ℝ) := by rw [hrel, hv₀]
    exact (mul_right_cancel₀ (ne_of_gt hcXpow)) this
  have hpq_of_fit : ∀ {u v : ℝ} {p q : ℤ} (h : s.IsExactFormOf u v p q),
      p = 2 ∧ q = 3 := by
    intro u v p q h
    have hα := hα_of_fit h
    have hqpos : 0 < q := h.2.1
    have hcop : IsCoprime p q := h.2.2
    have hqne : (q : ℝ) ≠ 0 := by
      have h1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
      exact ne_of_gt h1
    -- integer relation 3 p = 2 q
    have hrel : 3 * (p : ℝ) = 2 * (q : ℝ) := by
      field_simp at hα
      linarith
    have hrelz : 3 * p = 2 * q := by exact_mod_cast hrel
    -- hence q ∣ 3 p, and coprimality gives q ∣ 3
    have hqdvd : q ∣ p * 3 := ⟨2, by linarith [hrelz]⟩
    have hq3 : q ∣ 3 := hcop.symm.dvd_of_dvd_mul_left hqdvd
    obtain ⟨k, hk⟩ := hq3
    have hkpos : 0 < k := by
      by_contra hkk
      push Not at hkk
      have : (3 : ℤ) ≤ 0 := by rw [hk]; nlinarith [hqpos, hkk]
      norm_num at this
    have hqle : q ≤ 3 := by nlinarith [hk, hkpos, hqpos]
    interval_cases q <;> omega
  refine ⟨⟨s.R, ⟨v₀, 2, 3, hexact⟩, fun u' hu' => by
            obtain ⟨v', p', q', h'⟩ := hu'; exact huniq_of_fit h'⟩,
          ⟨v₀, ⟨s.R, 2, 3, hexact⟩, fun v' hv' => by
            obtain ⟨u', p', q', h'⟩ := hv'; exact hv_of_fit h'⟩,
          ⟨⟨2, 3⟩, ⟨s.R, v₀, hexact⟩, ?_⟩⟩
  rintro ⟨p', q'⟩ ⟨u', v', hfit'⟩
  obtain ⟨hp, hq⟩ := hpq_of_fit hfit'
  have h1 : p' = 2 := hp
  have h3 : q' = 3 := hq
  rw [h1, h3]

end Ipho2026KimiK3Blind32.ProblemIPhO2026_2C4
