import IChO2026Chem

/-!
# IChO 2026, problem T8-A10

This file formalizes the concentration dependence of the emission lifetimes of
the singlet and triplet excited states of the photosensitizer.  Concentrations
are represented in molar (`M`), rate constants in `M⁻¹ s⁻¹`, decay rates in
`s⁻¹`, and lifetimes in seconds.

The source gives a bimolecular reductive-quenching channel for each excited
state.  At fixed reductant concentration `c`, mass action makes its
pseudo-first-order decay contribution `kq * c`.  The unquenched lifetime
aggregates the other Jablonski-diagram pathways, so the total decay rate is
`1 / τ₀ + kq * c` and the emission lifetime is its reciprocal.
-/

namespace IChO2026Problems
namespace T8A10

noncomputable section

/-- The two photosensitizer excited states named in T8-A10. -/
inductive ExcitedState where
  | singletS1
  | tripletT1
  deriving DecidableEq, Repr

/-- Species needed to record the two reductive-quenching reactions printed in
the source. -/
inductive PhotochemicalSpecies where
  | excitedPhotosensitizer (state : ExcitedState)
  | reductant
  | photosensitizerRadicalAnion
  | reductantRadicalCation
  deriving DecidableEq, Repr

/-- A source-stated bimolecular reductive-quenching reaction.  Repetition in a
list would record a stoichiometric coefficient; all four printed coefficients
are one here. -/
structure ReductiveQuenchingChannel where
  state : ExcitedState
  reactants : List PhotochemicalSpecies
  products : List PhotochemicalSpecies
  rateConstant_M_inv_s_inv : ℝ

/-- The printed reaction
`PS(S₁) + Red ⟶ PS•⁻ + Red•⁺`, with `kS = 2.7 × 10⁹ M⁻¹ s⁻¹`. -/
def singletQuenchingChannel : ReductiveQuenchingChannel where
  state := .singletS1
  reactants := [.excitedPhotosensitizer .singletS1, .reductant]
  products := [.photosensitizerRadicalAnion, .reductantRadicalCation]
  rateConstant_M_inv_s_inv := (2.7 : ℝ) * 10 ^ 9

/-- The printed reaction
`PS(T₁) + Red ⟶ PS•⁻ + Red•⁺`, with `kT = 1.5 × 10⁸ M⁻¹ s⁻¹`. -/
def tripletQuenchingChannel : ReductiveQuenchingChannel where
  state := .tripletT1
  reactants := [.excitedPhotosensitizer .tripletT1, .reductant]
  products := [.photosensitizerRadicalAnion, .reductantRadicalCation]
  rateConstant_M_inv_s_inv := (1.5 : ℝ) * 10 ^ 8

/-- Formal charges displayed in the two reaction schemes. -/
def formalCharge : PhotochemicalSpecies → ℤ
  | .excitedPhotosensitizer _ => 0
  | .reductant => 0
  | .photosensitizerRadicalAnion => -1
  | .reductantRadicalCation => 1

/-- Total formal charge of one side of a recorded reaction. -/
def totalFormalCharge (species : List PhotochemicalSpecies) : ℤ :=
  (species.map formalCharge).sum

/-- Both printed one-to-one electron-transfer channels conserve formal charge. -/
theorem sourceQuenchingChannelsConserveCharge :
    totalFormalCharge singletQuenchingChannel.reactants =
        totalFormalCharge singletQuenchingChannel.products ∧
      totalFormalCharge tripletQuenchingChannel.reactants =
        totalFormalCharge tripletQuenchingChannel.products := by
  norm_num [totalFormalCharge, singletQuenchingChannel,
    tripletQuenchingChannel, formalCharge]

/-- Kinetic data for one excited state.  The zero-quencher lifetime absorbs all
of the concentration-independent pathways shown in the Jablonski diagram. -/
structure ExcitedStateKinetics where
  state : ExcitedState
  zeroQuencherLifetime_s : ℝ
  quenchingChannel : ReductiveQuenchingChannel

/-- Source data for S₁: `τ₀(S₁) = 2.9 ns`. -/
def singletKinetics : ExcitedStateKinetics where
  state := .singletS1
  zeroQuencherLifetime_s := (2.9 : ℝ) / 10 ^ 9
  quenchingChannel := singletQuenchingChannel

/-- Source data for T₁: `τ₀(T₁) = 84 μs`. -/
def tripletKinetics : ExcitedStateKinetics where
  state := .tripletT1
  zeroQuencherLifetime_s := (84 : ℝ) / 10 ^ 6
  quenchingChannel := tripletQuenchingChannel

/-- The concentration-independent decay rate inferred from the zero-quencher
lifetime, in `s⁻¹`. -/
def intrinsicDecayRate_per_s (data : ExcitedStateKinetics) : ℝ :=
  data.zeroQuencherLifetime_s⁻¹

/-- At reductant concentration `c` in `M`, a bimolecular rate constant in
`M⁻¹ s⁻¹` contributes the pseudo-first-order decay rate `kq * c`. -/
def quenchingDecayRate_per_s (data : ExcitedStateKinetics)
    (redConcentration_M : ℝ) : ℝ :=
  data.quenchingChannel.rateConstant_M_inv_s_inv * redConcentration_M

/-- The additive decay-rate law represented by the Jablonski diagram.  It is
equivalent to the dynamic-quenching relation `τ₀ / τ = 1 + kq * τ₀ * [Q]`
given by IUPAC Gold Book entry S06004, “Stern–Volmer kinetic relationships”,
DOI `10.1351/goldbook.S06004`, for a single bimolecular quenching reaction. -/
def totalDecayRate_per_s (data : ExcitedStateKinetics)
    (redConcentration_M : ℝ) : ℝ :=
  intrinsicDecayRate_per_s data +
    quenchingDecayRate_per_s data redConcentration_M

/-- Emission lifetime under reductive quenching, in seconds. -/
def emissionLifetime_s (data : ExcitedStateKinetics)
    (redConcentration_M : ℝ) : ℝ :=
  (totalDecayRate_per_s data redConcentration_M)⁻¹

/-- Quenching percentage used to rederive the prerequisite T8-A9 directly from
the problem-side kinetic data. -/
def quenchingPercentage (data : ExcitedStateKinetics)
    (redConcentration_M : ℝ) : ℝ :=
  100 * quenchingDecayRate_per_s data redConcentration_M /
    totalDecayRate_per_s data redConcentration_M

/-- The concentration printed in T8-A9, in `M`. -/
def previousPartRedConcentration_M : ℝ := 0.1

/-- The source's qualitative note `kF ≫ kISC` entails at least positivity of
`kF`, nonnegativity of `kISC`, and the strict ordering shown here.  No numerical
separation factor is supplied by the problem. -/
def FluorescenceDominatesISC (kF_per_s kISC_per_s : ℝ) : Prop :=
  0 ≤ kISC_per_s ∧ kISC_per_s < kF_per_s

/-- Both printed zero-quencher lifetimes and both printed bimolecular
quenching constants are strictly positive. -/
theorem sourceParametersPositive :
    0 < singletKinetics.zeroQuencherLifetime_s ∧
      0 < singletKinetics.quenchingChannel.rateConstant_M_inv_s_inv ∧
      0 < tripletKinetics.zeroQuencherLifetime_s ∧
      0 < tripletKinetics.quenchingChannel.rateConstant_M_inv_s_inv := by
  norm_num [singletKinetics, tripletKinetics, singletQuenchingChannel,
    tripletQuenchingChannel]

/-- Rootless answer-blind derivation of the numerical prerequisite T8-A9.
The values are exact percentages, before any display rounding.  The dominance
condition is retained from the source; because `τ₀` already aggregates all
intrinsic pathways, the displayed Stern--Volmer calculation does not require
unknown individual values of `kF` or `kISC`. -/
theorem previousPartA9BlindDerivation
    : quenchingPercentage singletKinetics previousPartRedConcentration_M =
        (78300 : ℝ) / 1783 ∧
      quenchingPercentage tripletKinetics previousPartRedConcentration_M =
        (126000 : ℝ) / 1261 := by
  norm_num [quenchingPercentage, quenchingDecayRate_per_s,
    totalDecayRate_per_s, intrinsicDecayRate_per_s,
    previousPartRedConcentration_M, singletKinetics, tripletKinetics,
    singletQuenchingChannel, tripletQuenchingChannel]

/-- General source-to-mathematics bridge: a positive bimolecular quenching
constant makes the reciprocal total decay rate strictly decrease as a
nonnegative reductant concentration increases. -/
theorem emissionLifetime_strictAntiOn
    (data : ExcitedStateKinetics)
    (hLifetime : 0 < data.zeroQuencherLifetime_s)
    (hQuenching : 0 < data.quenchingChannel.rateConstant_M_inv_s_inv) :
    StrictAntiOn (emissionLifetime_s data) (Set.Ici 0) := by
  intro c₁ hc₁ c₂ hc₂ hc₁₂
  apply inv_strictAntiOn
  · exact add_pos_of_pos_of_nonneg (inv_pos.mpr hLifetime)
      (mul_nonneg hQuenching.le hc₁)
  · exact add_pos_of_pos_of_nonneg (inv_pos.mpr hLifetime)
      (mul_nonneg hQuenching.le hc₂)
  · exact add_lt_add_right (mul_lt_mul_of_pos_left hc₁₂ hQuenching) _

/-- Countermodel-sufficiency check: if the extra quenching rate constant were
zero, changing reductant concentration would not change the lifetime.  Thus
the source's strict positivity is outcome-decisive, rather than an answer
hidden in the definition of `emissionLifetime_s`. -/
theorem emissionLifetime_constant_of_zeroQuenching
    (data : ExcitedStateKinetics)
    (hRate : data.quenchingChannel.rateConstant_M_inv_s_inv = 0) :
    ∀ c₁ c₂ : ℝ, emissionLifetime_s data c₁ = emissionLifetime_s data c₂ := by
  intro c₁ c₂
  simp [emissionLifetime_s, totalDecayRate_per_s,
    quenchingDecayRate_per_s, hRate]

/-- The three answer-box classifications offered by T8-A10. -/
inductive LifetimeTrend where
  | increases
  | decreases
  | unchanged
  deriving DecidableEq, Repr

/-- A non-answer-shaped specification assigning mathematical content to each
of the three printed answer choices on the physical domain `[Red] ≥ 0`. -/
def ClassifiesLifetimeTrend (lifetime : ℝ → ℝ) : LifetimeTrend → Prop
  | .increases => StrictMonoOn lifetime (Set.Ici 0)
  | .decreases => StrictAntiOn lifetime (Set.Ici 0)
  | .unchanged =>
      ∀ ⦃c₁ : ℝ⦄, c₁ ∈ Set.Ici 0 →
        ∀ ⦃c₂ : ℝ⦄, c₂ ∈ Set.Ici 0 → lifetime c₁ = lifetime c₂

/-- Requested output carrier `lifetime_s1`: the S₁ emission lifetime takes
choice (b) when reductant concentration increases. -/
theorem lifetime_s1 :
    ClassifiesLifetimeTrend (emissionLifetime_s singletKinetics)
      .decreases := by
  rcases sourceParametersPositive with ⟨hLifetime, hQuenching, -, -⟩
  exact emissionLifetime_strictAntiOn singletKinetics hLifetime hQuenching

/-- Requested output carrier `lifetime_t1`: the T₁ emission lifetime takes
choice (b) when reductant concentration increases. -/
theorem lifetime_t1 :
    ClassifiesLifetimeTrend (emissionLifetime_s tripletKinetics)
      .decreases := by
  rcases sourceParametersPositive with ⟨-, -, hLifetime, hQuenching⟩
  exact emissionLifetime_strictAntiOn tripletKinetics hLifetime hQuenching

/-- Raw symbolic solve-phase contract: both exact lifetime functions are
strictly antitone on physically admissible reductant concentrations. -/
theorem rawLifetimeTrendResult :
    StrictAntiOn (emissionLifetime_s singletKinetics) (Set.Ici 0) ∧
      StrictAntiOn (emissionLifetime_s tripletKinetics) (Set.Ici 0) := by
  exact ⟨lifetime_s1, lifetime_t1⟩

/-- Reported exact-symbolic solve-phase contract, preserving requested-output
order (S₁, then T₁). -/
theorem reportedLifetimeTrendResult :
    ClassifiesLifetimeTrend (emissionLifetime_s singletKinetics) .decreases ∧
      ClassifiesLifetimeTrend (emissionLifetime_s tripletKinetics) .decreases := by
  exact ⟨lifetime_s1, lifetime_t1⟩

end
end T8A10
end IChO2026Problems
