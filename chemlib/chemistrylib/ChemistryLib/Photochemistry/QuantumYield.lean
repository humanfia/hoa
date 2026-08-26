import ChemistryLib.Photochemistry.AbsorbedPhoton

/-!
# Quantum yield

Integral quantum yield is the number of specified events divided by the number
of absorbed photons.  Differential quantum yield is the corresponding event
rate divided by absorbed photon flux.  Both ratios expose their denominator
conditions as explicit domains.

Source: *IUPAC Gold Book 5.0.0*, term Q04991, definition 1 and the displayed
integral and differential identities.  The source record is
`research:iupac_goldbook_2025:quantum_yield` (public JSON SHA-256
`62bc4bf9360c58c3cecc453383be3b0352f55fd4feca0d850d0b0605b7835075`).
-/

namespace ChemistryLib.Photochemistry

/-- Empirical inputs for differential quantum yield. -/
structure DifferentialQuantumYieldInput : Type where
  /-- Rate of occurrence of the specified photochemical event. -/
  eventRate : ℝ
  /-- Observation from which the absorbed photon flux is determined. -/
  photonObservation : AbsorbedPhotonObservation

/-- The absorbed photon flux must be positive for the differential ratio. -/
def DifferentialQuantumYieldDomain (input : DifferentialQuantumYieldInput) : Prop :=
  0 < absorbedPhotonFlux input.photonObservation

/-- Differential quantum yield: event rate per absorbed photon flux. -/
noncomputable def differentialQuantumYield (input : DifferentialQuantumYieldInput)
    (_ : DifferentialQuantumYieldDomain input) : ℝ :=
  input.eventRate / absorbedPhotonFlux input.photonObservation

/-- The differential quantum-yield domain is positivity of absorbed photon flux. -/
theorem differentialQuantumYieldDomain_iff : (input : DifferentialQuantumYieldInput) →
    DifferentialQuantumYieldDomain input ↔
      0 < absorbedPhotonFlux input.photonObservation :=
  fun _ ↦ Iff.rfl

/-- The IUPAC differential quantum-yield identity. -/
theorem differentialQuantumYield_eq : (input : DifferentialQuantumYieldInput) →
    (h : DifferentialQuantumYieldDomain input) →
      differentialQuantumYield input h =
        input.eventRate / absorbedPhotonFlux input.photonObservation :=
  fun _ _ ↦ rfl

/-- Empirical inputs for integral quantum yield. -/
structure IntegralQuantumYieldInput : Type where
  /-- Number of occurrences of the specified photochemical event. -/
  eventCount : ℝ
  /-- Number of photons absorbed by the sample. -/
  absorbedPhotonCount : ℝ

/-- The absorbed-photon count must be nonzero for the integral ratio. -/
def IntegralQuantumYieldDomain (input : IntegralQuantumYieldInput) : Prop :=
  input.absorbedPhotonCount ≠ 0

/-- Integral quantum yield: event count per absorbed-photon count. -/
noncomputable def integralQuantumYield (input : IntegralQuantumYieldInput)
    (_ : IntegralQuantumYieldDomain input) : ℝ :=
  input.eventCount / input.absorbedPhotonCount

/-- The integral quantum-yield domain is a nonzero absorbed-photon count. -/
theorem integralQuantumYieldDomain_iff : (input : IntegralQuantumYieldInput) →
    IntegralQuantumYieldDomain input ↔ input.absorbedPhotonCount ≠ 0 :=
  fun _ ↦ Iff.rfl

/-- The IUPAC integral quantum-yield identity. -/
theorem integralQuantumYield_eq : (input : IntegralQuantumYieldInput) →
    (h : IntegralQuantumYieldDomain input) →
      integralQuantumYield input h = input.eventCount / input.absorbedPhotonCount :=
  fun _ _ ↦ rfl

end ChemistryLib.Photochemistry
