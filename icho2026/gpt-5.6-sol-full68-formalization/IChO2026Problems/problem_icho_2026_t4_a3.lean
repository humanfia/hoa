import Mathlib
import CRNT.Basic.Reaction
import IChO2026Chem

/-!
# IChO 2026 T4-A3: most common uranium-235 fission equation

This file formalizes the source-derived candidate, not a uniqueness claim over
all physically imaginable nuclides.  The two modal mass numbers are an explicit
readout of the supplied graph.  Nucleon number, atomic number, stoichiometric
support, and the stated same-periodic-group condition are all retained as
separate checks.
-/

namespace IChO2026Problems.IChO2026T4A3

/-- Permitted provenance classes for source facts and local derived facts. -/
inductive FactProvenance where
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- A value paired with the class of evidence from which it was read. -/
structure Sourced (α : Type) where
  value : α
  provenance : FactProvenance
  deriving Repr

/-- Nuclear species are identified by atomic number `Z` and mass number `A`.
The free neutron is represented by `(Z,A) = (0,1)`. -/
structure NuclearSpecies where
  atomicNumber : ℕ
  massNumber : ℕ
  deriving DecidableEq, Repr

/-- A binary neutron-induced fission equation with one light fragment, one
heavy fragment, and explicit incident/emitted neutron coefficients. -/
structure BinaryFissionEquation where
  parent : NuclearSpecies
  incidentNeutronCount : ℕ
  lightFragment : NuclearSpecies
  heavyFragment : NuclearSpecies
  emittedNeutronCount : ℕ
  deriving DecidableEq, Repr

def uranium235 : NuclearSpecies :=
  { atomicNumber := 92, massNumber := 235 }

def freeNeutron : NuclearSpecies :=
  { atomicNumber := 0, massNumber := 1 }

/-- The element with `Z = 37` is rubidium. -/
def rubidium93 : NuclearSpecies :=
  { atomicNumber := 37, massNumber := 93 }

/-- The element with `Z = 55` is caesium (cesium). -/
def cesium140 : NuclearSpecies :=
  { atomicNumber := 55, massNumber := 140 }

/-- Source-text datum: uranium-235 is the parent nuclide. -/
def sourceParent : Sourced NuclearSpecies :=
  { value := uranium235, provenance := .problemText }

/-- Source-text datum: the parent absorbs one neutron. -/
def sourceIncidentNeutronCount : Sourced ℕ :=
  { value := 1, provenance := .problemText }

/-- Source-text datum: the fission event produces three additional neutrons. -/
def sourceEmittedNeutronCount : Sourced ℕ :=
  { value := 3, provenance := .problemText }

/-- A source-first readout of the mass-number axis and the two maxima of the
supplied fission-yield graph. -/
structure FissionYieldPeakReadout where
  displayedMassMinimum : ℕ
  displayedMassMaximum : ℕ
  lightPeakMass : ℕ
  heavyPeakMass : ℕ
  provenance : FactProvenance
  deriving DecidableEq, Repr

/-- On `T4_page-1.png`, the plotted domain is `70 ≤ A ≤ 170`; the two curve
apices align with `A = 93` and `A = 140`. -/
def sourceYieldPeakReadout : FissionYieldPeakReadout :=
  { displayedMassMinimum := 70
    displayedMassMaximum := 170
    lightPeakMass := 93
    heavyPeakMass := 140
    provenance := .problemImage }

/-- Atomic numbers in each IUPAC periodic-table group.  Lanthanum/lutetium and
actinium/lawrencium are both retained in group 3; that convention is irrelevant
to the group-1 witness used below. -/
def periodicGroupMembers : ℕ → Finset ℕ
  | 1 => [1, 3, 11, 19, 37, 55, 87].toFinset
  | 2 => [4, 12, 20, 38, 56, 88].toFinset
  | 3 => [21, 39, 57, 71, 89, 103].toFinset
  | 4 => [22, 40, 72, 104].toFinset
  | 5 => [23, 41, 73, 105].toFinset
  | 6 => [24, 42, 74, 106].toFinset
  | 7 => [25, 43, 75, 107].toFinset
  | 8 => [26, 44, 76, 108].toFinset
  | 9 => [27, 45, 77, 109].toFinset
  | 10 => [28, 46, 78, 110].toFinset
  | 11 => [29, 47, 79, 111].toFinset
  | 12 => [30, 48, 80, 112].toFinset
  | 13 => [5, 13, 31, 49, 81, 113].toFinset
  | 14 => [6, 14, 32, 50, 82, 114].toFinset
  | 15 => [7, 15, 33, 51, 83, 115].toFinset
  | 16 => [8, 16, 34, 52, 84, 116].toFinset
  | 17 => [9, 17, 35, 53, 85, 117].toFinset
  | 18 => [2, 10, 18, 36, 54, 86, 118].toFinset
  | _ => ∅

/-- Provenance carrier for the periodic-group classification. -/
def periodicGroupTableProvenance : FactProvenance :=
  .trustedGeneralLaw

def AtomicNumberInPeriodicGroup (z group : ℕ) : Prop :=
  z ∈ periodicGroupMembers group

/-- Two elements are in the same numbered group of the periodic table. -/
def SamePeriodicGroup (x y : NuclearSpecies) : Prop :=
  ∃ group : ℕ,
    1 ≤ group ∧ group ≤ 18 ∧
      AtomicNumberInPeriodicGroup x.atomicNumber group ∧
      AtomicNumberInPeriodicGroup y.atomicNumber group

/-- Minimal well-formedness conditions for a fragment nuclide used here. -/
def IsElementNuclide (x : NuclearSpecies) : Prop :=
  1 ≤ x.atomicNumber ∧ x.atomicNumber ≤ 118 ∧ x.atomicNumber ≤ x.massNumber

/-- Whole-number nucleon conservation, including every incident and emitted
free neutron. -/
def ConservesNucleonNumber (r : BinaryFissionEquation) : Prop :=
  r.parent.massNumber + r.incidentNeutronCount =
    r.lightFragment.massNumber + r.heavyFragment.massNumber + r.emittedNeutronCount

/-- Atomic-number (nuclear charge) conservation.  Free neutrons contribute
zero to both sides. -/
def ConservesAtomicNumber (r : BinaryFissionEquation) : Prop :=
  r.parent.atomicNumber =
    r.lightFragment.atomicNumber + r.heavyFragment.atomicNumber

/-- A singleton stoichiometric complex over the generic nuclear-species type. -/
def singletonComplex (species : NuclearSpecies) (coefficient : ℕ) :
    CRNT.Complex NuclearSpecies :=
  fun candidate => if candidate = species then coefficient else 0

/-- Re-express the binary equation using CRNT's verified directed-reaction API. -/
def toStoichiometricReaction (r : BinaryFissionEquation) :
    CRNT.Reaction NuclearSpecies where
  source := CRNT.Complex.add
    (singletonComplex r.parent 1)
    (singletonComplex freeNeutron r.incidentNeutronCount)
  target := CRNT.Complex.add
    (singletonComplex r.lightFragment 1)
    (CRNT.Complex.add
      (singletonComplex r.heavyFragment 1)
      (singletonComplex freeNeutron r.emittedNeutronCount))

/-- No reactant or product stream occurs outside the species explicitly shown
in the nuclear equation. -/
def HasClosedStoichiometricSupport (r : BinaryFissionEquation) : Prop :=
  (∀ species : NuclearSpecies,
      (toStoichiometricReaction r).source species ≠ 0 →
        species = r.parent ∨ species = freeNeutron) ∧
  (∀ species : NuclearSpecies,
      (toStoichiometricReaction r).target species ≠ 0 →
        species = r.lightFragment ∨
          species = r.heavyFragment ∨ species = freeNeutron)

/-- The outcome-decisive ledgers for this quantitative reaction stage. -/
def QuantitativeMaterialStageAudit (r : BinaryFissionEquation) : Prop :=
  ConservesNucleonNumber r ∧
    ConservesAtomicNumber r ∧
    HasClosedStoichiometricSupport r

/-- All constraints explicitly used from T4-A3 and its shared problem context. -/
def SatisfiesT4A3Source (r : BinaryFissionEquation) : Prop :=
  r.parent = sourceParent.value ∧
    r.incidentNeutronCount = sourceIncidentNeutronCount.value ∧
    r.emittedNeutronCount = sourceEmittedNeutronCount.value ∧
    r.lightFragment.massNumber = sourceYieldPeakReadout.lightPeakMass ∧
    r.heavyFragment.massNumber = sourceYieldPeakReadout.heavyPeakMass ∧
    r.lightFragment.massNumber < r.heavyFragment.massNumber ∧
    r.lightFragment.atomicNumber ≠ r.heavyFragment.atomicNumber ∧
    IsElementNuclide r.lightFragment ∧
    IsElementNuclide r.heavyFragment ∧
    SamePeriodicGroup r.lightFragment r.heavyFragment ∧
    QuantitativeMaterialStageAudit r

/-- Source-derived concrete candidate:
`²³⁵₉₂U + ¹₀n → ⁹³₃₇Rb + ¹⁴⁰₅₅Cs + 3 ¹₀n`. -/
def mostCommonFissionEquation : BinaryFissionEquation :=
  { parent := uranium235
    incidentNeutronCount := 1
    lightFragment := rubidium93
    heavyFragment := cesium140
    emittedNeutronCount := 3 }

/-- Raw exact-symbolic answer proposition.  It both identifies the two product
nuclides and requires the candidate to discharge the full source specification. -/
def FissionEquationRawResult : Prop :=
  mostCommonFissionEquation.lightFragment = rubidium93 ∧
    mostCommonFissionEquation.heavyFragment = cesium140 ∧
    SatisfiesT4A3Source mostCommonFissionEquation

/-- A symbolic submission keeps an exact structural raw equation and displayed
equation; the source reporting policy permits no rounding or alteration. -/
structure SymbolicEquationSubmission where
  rawEquation : BinaryFissionEquation
  displayedEquation : BinaryFissionEquation
  deriving DecidableEq, Repr

def fissionEquationSubmission : SymbolicEquationSubmission :=
  { rawEquation := mostCommonFissionEquation
    displayedEquation := mostCommonFissionEquation }

def ExactSymbolicReport (submission : SymbolicEquationSubmission) : Prop :=
  submission.displayedEquation = submission.rawEquation

/-- Reported exact-symbolic answer proposition. -/
def FissionEquationReportedResult : Prop :=
  FissionEquationRawResult ∧
    fissionEquationSubmission.rawEquation = mostCommonFissionEquation ∧
    fissionEquationSubmission.displayedEquation = mostCommonFissionEquation ∧
    ExactSymbolicReport fissionEquationSubmission

/-- The two image-read modal masses and the three-neutron coefficient satisfy
the source-side nucleon-number ledger. -/
theorem graphPeakMasses_nucleonLedger :
    uranium235.massNumber + sourceIncidentNeutronCount.value =
      sourceYieldPeakReadout.lightPeakMass +
        sourceYieldPeakReadout.heavyPeakMass + sourceEmittedNeutronCount.value := by
  norm_num [uranium235, sourceIncidentNeutronCount, sourceYieldPeakReadout,
    sourceEmittedNeutronCount]

/-- The proposed product atomic numbers satisfy charge conservation. -/
theorem rubidiumCesium_atomicNumberLedger :
    uranium235.atomicNumber =
      rubidium93.atomicNumber + cesium140.atomicNumber := by
  norm_num [uranium235, rubidium93, cesium140]

/-- Both proposed product elements are in periodic-table group 1. -/
theorem rubidiumCesium_samePeriodicGroup :
    SamePeriodicGroup rubidium93 cesium140 := by
  refine ⟨1, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num [AtomicNumberInPeriodicGroup, periodicGroupMembers, rubidium93]
  · norm_num [AtomicNumberInPeriodicGroup, periodicGroupMembers, cesium140]

/-- Named carrier for the complete quantitative-stage audit. -/
theorem mostCommonFissionEquation_quantitativeMaterialStageAudit :
    QuantitativeMaterialStageAudit mostCommonFissionEquation := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [ConservesNucleonNumber, mostCommonFissionEquation, uranium235,
      rubidium93, cesium140]
  · norm_num [ConservesAtomicNumber, mostCommonFissionEquation, uranium235,
      rubidium93, cesium140]
  · constructor
    · intro species h
      by_cases hp : species = uranium235
      · exact Or.inl hp
      by_cases hn : species = freeNeutron
      · exact Or.inr hn
      exfalso
      apply h
      simp [toStoichiometricReaction, mostCommonFissionEquation, singletonComplex,
        CRNT.Complex.add, hp, hn]
    · intro species h
      by_cases hl : species = rubidium93
      · exact Or.inl hl
      by_cases hh : species = cesium140
      · exact Or.inr (Or.inl hh)
      by_cases hn : species = freeNeutron
      · exact Or.inr (Or.inr hn)
      exfalso
      apply h
      simp [toStoichiometricReaction, mostCommonFissionEquation, singletonComplex,
        CRNT.Complex.add, hl, hh, hn]

/-- The concrete equation meets every encoded problem-side constraint. -/
theorem mostCommonFissionEquation_satisfiesSource :
    SatisfiesT4A3Source mostCommonFissionEquation := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_,
    rubidiumCesium_samePeriodicGroup,
    mostCommonFissionEquation_quantitativeMaterialStageAudit⟩
  · norm_num [mostCommonFissionEquation, rubidium93, cesium140]
  · norm_num [mostCommonFissionEquation, rubidium93, cesium140]
  · norm_num [IsElementNuclide, mostCommonFissionEquation, rubidium93]
  · norm_num [IsElementNuclide, mostCommonFissionEquation, cesium140]

/-- Raw result contract for the requested fission equation. -/
theorem fissionEquation_raw_result : FissionEquationRawResult := by
  exact ⟨rfl, rfl, mostCommonFissionEquation_satisfiesSource⟩

/-- Reported result contract under exact-symbolic reporting. -/
theorem fissionEquation_reported_result : FissionEquationReportedResult := by
  exact ⟨fissionEquation_raw_result, rfl, rfl, rfl⟩

end IChO2026Problems.IChO2026T4A3
