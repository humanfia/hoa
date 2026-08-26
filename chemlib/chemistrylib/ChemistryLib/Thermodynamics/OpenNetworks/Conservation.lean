import ChemistryLib.Thermodynamics.OpenNetworks.RateEquation

/-!
# Conservation laws in open reaction networks

A closed-network conservation covector annihilates every stoichiometric
reaction vector.  Opening the network classifies such a law as broken when
it has a nonzero component on a chemostatted species, and unbroken when all
of those components vanish.  Consequently an unbroken law has zero rate
under reservoir currents supported on the chemostats.

This follows Rao and Esposito (2016), Sections II.B–II.C, equations (7)–(16),
especially the conservation-law classification accompanying the open-network
rate equations.
-/

namespace ChemistryLib.Thermodynamics.OpenNetworks

/-- A conservation law is broken by the selected chemostats when its
covector has a nonzero component on at least one chemostatted species. -/
def IsBrokenConservationLaw : ∀ {Species : Type} [DecidableEq Species],
    Finset Species → (Species → ℝ) → Prop :=
  fun chemostats law ↦
    ∃ species ∈ chemostats, law species ≠ 0

/-- A closed-network conservation law is a covector in the left kernel of
the stoichiometric matrix. -/
def IsClosedConservationLaw : ∀ {Species Reaction : Type} [Fintype Species],
    (Reaction → Species → ℝ) → (Species → ℝ) → Prop :=
  fun stoichiometry law ↦
    ∀ reaction, ∑ species, law species * stoichiometry reaction species = 0

/-- A conservation law is unbroken by the selected chemostats when its
covector vanishes on every chemostatted species. -/
def IsUnbrokenConservationLaw : ∀ {Species : Type} [DecidableEq Species],
    Finset Species → (Species → ℝ) → Prop :=
  fun chemostats law ↦
    ∀ species ∈ chemostats, law species = 0

/-- A closed conservation law that vanishes on all chemostats has zero
instantaneous rate in the corresponding open network. -/
theorem unbroken_conservation_rate :
    ∀ {Species Reaction : Type} [Fintype Species] [DecidableEq Species]
      [Fintype Reaction] (Y : Finset Species) (ν : Reaction → Species → ℝ)
      (j : Reaction → ℝ) (I ℓ : Species → ℝ),
      IsClosedConservationLaw ν ℓ →
      IsUnbrokenConservationLaw Y ℓ →
      IsChemostatCurrent Y I →
      ∑ s, ℓ s * openSpeciesRate ν j I s = 0 := by
  intro Species Reaction _ _ _ Y ν j I ℓ hclosed hunbroken hcurrent
  have hreservoir : ∀ species, ℓ species * I species = 0 := by
    intro species
    by_cases hs : species ∈ Y
    · rw [hunbroken species hs, zero_mul]
    · rw [hcurrent species hs, mul_zero]
  simp only [openSpeciesRate, reactionSpeciesRate, mul_add, hreservoir, add_zero]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro reaction _
  rw [hclosed reaction, zero_mul]

end ChemistryLib.Thermodynamics.OpenNetworks
