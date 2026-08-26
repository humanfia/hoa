import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorbed photon flux

An observation records the empirical inputs at one excitation wavelength.  The
absorbed photon flux is the incident photon flux multiplied by the absorbed
fraction `1 - 10 ^ (-A)`, where `A` is the absorbance at that wavelength.

Source: *IUPAC Gold Book 5.0.0*, term Q04991, definition 1 and the displayed
absorbed-photon identity.  The source record is
`research:iupac_goldbook_2025:quantum_yield` (public JSON SHA-256
`62bc4bf9360c58c3cecc453383be3b0352f55fd4feca0d850d0b0605b7835075`).
-/

namespace ChemistryLib.Photochemistry

/-- Empirical inputs for absorbed photon flux at one excitation wavelength. -/
structure AbsorbedPhotonObservation : Type where
  /-- Excitation wavelength of the observation. -/
  excitationWavelength : ℝ
  /-- Incident photon flux at the excitation wavelength. -/
  incidentPhotonFlux : ℝ
  /-- Absorbance at the excitation wavelength. -/
  absorbance : ℝ

/-- The explicit domain condition that the absorbed photon flux is positive. -/
def PositiveAbsorbedPhotonFlux (input : AbsorbedPhotonObservation) : Prop :=
  0 < input.incidentPhotonFlux * (1 - Real.rpow 10 (-input.absorbance))

/-- Photon flux absorbed by the observed sample. -/
noncomputable def absorbedPhotonFlux (input : AbsorbedPhotonObservation) : ℝ :=
  input.incidentPhotonFlux * (1 - Real.rpow 10 (-input.absorbance))

/-- The IUPAC absorbed-photon-flux identity. -/
theorem absorbedPhotonFlux_eq : (input : AbsorbedPhotonObservation) →
    absorbedPhotonFlux input =
      input.incidentPhotonFlux * (1 - Real.rpow 10 (-input.absorbance)) :=
  fun _ ↦ rfl

/-- The named domain condition is exactly positivity of absorbed photon flux. -/
theorem positiveAbsorbedPhotonFlux_iff : (input : AbsorbedPhotonObservation) →
    PositiveAbsorbedPhotonFlux input ↔ 0 < absorbedPhotonFlux input :=
  fun _ ↦ Iff.rfl

end ChemistryLib.Photochemistry
