import Mathlib

/-!
# IChO 2026 T4-A2: neutron-producing nuclear reactions

The problem supplies three neutron-producing channels: boron-11 with an
alpha particle, a gamma ray with deuterium, and beryllium-9 with an alpha
particle.  A species is represented by its mass number and atomic number.
The `Balanced` predicate is conservation of those two numbers.

For each requested equation below, Lean proves both that the displayed
reaction is balanced and that its residual nucleus is the unique one that can
balance the source-specified one-residual-plus-one-neutron channel.
-/

namespace IChO2026Problems.ProblemIChO2026T4A2

/-- The two integer labels that identify a nuclear species: mass number `A`
and atomic number `Z`.  This representation also covers a neutron `(1, 0)`
and a gamma ray `(0, 0)` for conservation bookkeeping. -/
structure Species where
  massNumber : ℕ
  atomicNumber : ℕ
  deriving DecidableEq, Repr

/-- A nuclear equation has an ordered list of reactants and products. -/
structure NuclearReaction where
  reactants : List Species
  products : List Species
  deriving DecidableEq, Repr

/-- Total mass number on one side of a nuclear equation. -/
def totalMassNumber : List Species → ℕ
  | [] => 0
  | species :: rest => species.massNumber + totalMassNumber rest

/-- Total atomic number (and hence nuclear charge number) on one side. -/
def totalAtomicNumber : List Species → ℕ
  | [] => 0
  | species :: rest => species.atomicNumber + totalAtomicNumber rest

/-- Conservation criterion used to check a proposed nuclear equation. -/
def Balanced (reaction : NuclearReaction) : Prop :=
  totalMassNumber reaction.reactants = totalMassNumber reaction.products ∧
  totalAtomicNumber reaction.reactants = totalAtomicNumber reaction.products

/-! ## Source-model data

The prompt supplies the three initial isotope/radiation combinations and says
that each is a neutron source.  The numerical pairs below are the isotope
labels printed in the prompt together with the standard `(A, Z)` bookkeeping
for alpha, gamma, and neutron radiation. -/

def boron11 : Species := ⟨11, 5⟩
def beryllium9 : Species := ⟨9, 4⟩
def deuterium : Species := ⟨2, 1⟩
def alphaParticle : Species := ⟨4, 2⟩
def gammaRay : Species := ⟨0, 0⟩
def neutron : Species := ⟨1, 0⟩

/-- The channel shape in part (a), with its residual nucleus left open. -/
def boronAlphaChannel (residual : Species) : NuclearReaction :=
  ⟨[boron11, alphaParticle], [residual, neutron]⟩

/-- The channel shape in part (b), with its residual nucleus left open. -/
def deuteriumGammaChannel (residual : Species) : NuclearReaction :=
  ⟨[gammaRay, deuterium], [residual, neutron]⟩

/-- The channel shape in part (c), with its residual nucleus left open. -/
def berylliumAlphaChannel (residual : Species) : NuclearReaction :=
  ⟨[beryllium9, alphaParticle], [residual, neutron]⟩

/-! ## Derived answer data and proofs

These are the three residual isotope labels obtained by conserving `A` and
`Z`.  The theorems below verify the proposed equations and prove uniqueness,
rather than taking those products as unchecked premises. -/

def nitrogen14 : Species := ⟨14, 7⟩
def hydrogen1 : Species := ⟨1, 1⟩
def carbon12 : Species := ⟨12, 6⟩

/-- Requested equation (a): `¹¹₅B + ⁴₂He → ¹⁴₇N + ¹₀n`. -/
def reactionA : NuclearReaction := boronAlphaChannel nitrogen14

/-- Requested equation (b): `γ + ²₁H → ¹₁H + ¹₀n`. -/
def reactionB : NuclearReaction := deuteriumGammaChannel hydrogen1

/-- Requested equation (c): `⁹₄Be + ⁴₂He → ¹²₆C + ¹₀n`. -/
def reactionC : NuclearReaction := berylliumAlphaChannel carbon12

theorem reactionA_balanced : Balanced reactionA := by
  norm_num [Balanced, reactionA, boronAlphaChannel, totalMassNumber,
    boron11, alphaParticle, nitrogen14, neutron, totalAtomicNumber]

theorem reactionB_balanced : Balanced reactionB := by
  norm_num [Balanced, reactionB, deuteriumGammaChannel, totalMassNumber,
    gammaRay, deuterium, hydrogen1, neutron, totalAtomicNumber]

theorem reactionC_balanced : Balanced reactionC := by
  norm_num [Balanced, reactionC, berylliumAlphaChannel, totalMassNumber,
    beryllium9, alphaParticle, carbon12, neutron, totalAtomicNumber]

/-- In channel (a), conservation determines nitrogen-14 uniquely. -/
theorem nuclear_a (residual : Species) :
    Balanced (boronAlphaChannel residual) ↔ residual = nitrogen14 := by
  constructor
  · intro h
    rcases residual with ⟨mass, atomic⟩
    simp [Balanced, boronAlphaChannel, totalMassNumber, totalAtomicNumber,
      boron11, alphaParticle, neutron, nitrogen14] at h ⊢
    omega
  · rintro rfl
    exact reactionA_balanced

/-- In channel (b), conservation determines hydrogen-1 uniquely. -/
theorem nuclear_b (residual : Species) :
    Balanced (deuteriumGammaChannel residual) ↔ residual = hydrogen1 := by
  constructor
  · intro h
    rcases residual with ⟨mass, atomic⟩
    simp [Balanced, deuteriumGammaChannel, totalMassNumber, totalAtomicNumber,
      gammaRay, deuterium, neutron, hydrogen1] at h ⊢
    omega
  · rintro rfl
    exact reactionB_balanced

/-- In channel (c), conservation determines carbon-12 uniquely. -/
theorem nuclear_c (residual : Species) :
    Balanced (berylliumAlphaChannel residual) ↔ residual = carbon12 := by
  constructor
  · intro h
    rcases residual with ⟨mass, atomic⟩
    simp [Balanced, berylliumAlphaChannel, totalMassNumber, totalAtomicNumber,
      beryllium9, alphaParticle, neutron, carbon12] at h ⊢
    omega
  · rintro rfl
    exact reactionC_balanced

#print axioms reactionA_balanced
#print axioms reactionB_balanced
#print axioms reactionC_balanced
#print axioms nuclear_a
#print axioms nuclear_b
#print axioms nuclear_c

end IChO2026Problems.ProblemIChO2026T4A2
