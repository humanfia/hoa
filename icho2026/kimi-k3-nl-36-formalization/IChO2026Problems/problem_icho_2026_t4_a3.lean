import Mathlib

/-!
# IChO 2026, problem T4-A3

The problem asks for the modal neutron-induced binary-fission equation of
uranium-235.  The graph supplies the two modal fragment mass numbers, while the
surrounding text supplies absorption of one neutron, emission of three neutrons,
and the requirement that the two product elements lie in the same periodic-table
group.

CRNT's `Reaction` records molecular complexes, but it has no carrier for isotope
mass number or nuclear charge.  The small local interface below retains exactly
the nuclear data used by this question.
-/

namespace IChO2026Problems.T4A3

/-- Chemical elements represented by their zero-based position in the complete
atomic-number domain `1, ..., 118`. -/
abbrev Element := Fin 118

/-- The usual one-based atomic number of an element. -/
def atomicNumber (e : Element) : ℕ := e.val + 1

/-- Uranium, atomic number 92. -/
def uranium : Element := ⟨91, by decide⟩

/-- Rubidium, atomic number 37.  Verified with the pinned CIAAW-2024 offline
record `df9863f473ad885a2dff7e5479fdeea63dcd44f0cfdaf64d499bda1000532428`
in dataset `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`. -/
def rubidium : Element := ⟨36, by decide⟩

/-- Caesium, atomic number 55.  Verified with the pinned CIAAW-2024 offline
record `189e0e7fa5e78bab53f78f06d09442aacdfc9d67cb2d75b9f2349a9c28e49454`
in dataset `11a02c1d207b810d28bc105970081324cb892592539f6d9a9e1d340a475983d5`. -/
def caesium : Element := ⟨54, by decide⟩

/-- Conventional IUPAC group number for the atomic numbers assigned to groups
1--18, following the IUPAC Periodic Table of the Elements (4 May 2022).
Lanthanides and actinides not conventionally placed in a single group are
returned as `none`. -/
def periodicGroupOfAtomicNumber (z : ℕ) : Option ℕ :=
  if z ∈ [1, 3, 11, 19, 37, 55, 87] then some 1
  else if z ∈ [4, 12, 20, 38, 56, 88] then some 2
  else if z ∈ [21, 39] then some 3
  else if z ∈ [22, 40, 72, 104] then some 4
  else if z ∈ [23, 41, 73, 105] then some 5
  else if z ∈ [24, 42, 74, 106] then some 6
  else if z ∈ [25, 43, 75, 107] then some 7
  else if z ∈ [26, 44, 76, 108] then some 8
  else if z ∈ [27, 45, 77, 109] then some 9
  else if z ∈ [28, 46, 78, 110] then some 10
  else if z ∈ [29, 47, 79, 111] then some 11
  else if z ∈ [30, 48, 80, 112] then some 12
  else if z ∈ [5, 13, 31, 49, 81, 113] then some 13
  else if z ∈ [6, 14, 32, 50, 82, 114] then some 14
  else if z ∈ [7, 15, 33, 51, 83, 115] then some 15
  else if z ∈ [8, 16, 34, 52, 84, 116] then some 16
  else if z ∈ [9, 17, 35, 53, 85, 117] then some 17
  else if z ∈ [2, 10, 18, 36, 54, 86, 118] then some 18
  else none

/-- Two elements are in the same periodic-table group when their independently
tabulated atomic numbers map to the same group. -/
def SamePeriodicGroup (x y : Element) : Prop :=
  ∃ g : ℕ,
    periodicGroupOfAtomicNumber (atomicNumber x) = some g ∧
      periodicGroupOfAtomicNumber (atomicNumber y) = some g

/-- A nuclide retains its element and integer mass number.  The side condition
rules out more protons than total nucleons. -/
structure Nuclide where
  element : Element
  massNumber : ℕ
  atomicNumber_le_massNumber : atomicNumber element ≤ massNumber

/-- Uranium-235, the parent nuclide printed in the problem. -/
def uranium235 : Nuclide where
  element := uranium
  massNumber := 235
  atomicNumber_le_massNumber := by decide

/-- Rubidium-93, the light candidate fragment. -/
def rubidium93 : Nuclide where
  element := rubidium
  massNumber := 93
  atomicNumber_le_massNumber := by decide

/-- Caesium-140, the heavy candidate fragment. -/
def caesium140 : Nuclide where
  element := caesium
  massNumber := 140
  atomicNumber_le_massNumber := by decide

/-- Source-first readout of the two maxima in the fission-product yield graph on
`T4_page-1.png`.  The first field is the lighter maximum. -/
structure YieldCurvePeakReadout where
  lightMassNumber : ℕ
  heavyMassNumber : ℕ
  light_lt_heavy : lightMassNumber < heavyMassNumber

/-- The graph's two integer modal mass-number readouts. -/
def sourceYieldCurvePeaks : YieldCurvePeakReadout where
  lightMassNumber := 93
  heavyMassNumber := 140
  light_lt_heavy := by decide

/-- A binary fission equation with free neutrons represented by their
multiplicities.  Free neutrons have mass number one and atomic number zero. -/
structure BinaryFissionEquation where
  parent : Nuclide
  absorbedNeutrons : ℕ
  fragment₁ : Nuclide
  fragment₂ : Nuclide
  emittedNeutrons : ℕ

/-- Nucleon-number ledger for a binary fission equation. -/
def ConservesMassNumber (r : BinaryFissionEquation) : Prop :=
  r.parent.massNumber + r.absorbedNeutrons =
    r.fragment₁.massNumber + r.fragment₂.massNumber + r.emittedNeutrons

/-- Nuclear-charge ledger for a binary fission equation.  The absorbed and
emitted free neutrons contribute zero charge. -/
def ConservesAtomicNumber (r : BinaryFissionEquation) : Prop :=
  atomicNumber r.parent.element =
    atomicNumber r.fragment₁.element + atomicNumber r.fragment₂.element

/-- The two fragments occur at the two graph maxima.  The disjunction preserves
the physically irrelevant order in which the fragments are written. -/
def UsesModalFragmentMasses (r : BinaryFissionEquation) : Prop :=
  (r.fragment₁.massNumber = sourceYieldCurvePeaks.lightMassNumber ∧
      r.fragment₂.massNumber = sourceYieldCurvePeaks.heavyMassNumber) ∨
    (r.fragment₂.massNumber = sourceYieldCurvePeaks.lightMassNumber ∧
      r.fragment₁.massNumber = sourceYieldCurvePeaks.heavyMassNumber)

/-- Exact source-side specification of an equation answering T4-A3. -/
def SatisfiesSourceSpecification (r : BinaryFissionEquation) : Prop :=
  r.parent = uranium235 ∧
    r.absorbedNeutrons = 1 ∧
    r.emittedNeutrons = 3 ∧
    UsesModalFragmentMasses r ∧
    r.fragment₁.element ≠ r.fragment₂.element ∧
    SamePeriodicGroup r.fragment₁.element r.fragment₂.element ∧
    ConservesMassNumber r ∧
    ConservesAtomicNumber r

/-- Candidate equation
`²³⁵₉₂U + ¹₀n ⟶ ⁹³₃₇Rb + ¹⁴⁰₅₅Cs + 3 ¹₀n`. -/
def rubidiumCaesiumFission : BinaryFissionEquation where
  parent := uranium235
  absorbedNeutrons := 1
  fragment₁ := rubidium93
  fragment₂ := caesium140
  emittedNeutrons := 3

/-- Named carrier for the raw symbolic result. -/
def RawFissionEquationResult : Prop :=
  SatisfiesSourceSpecification rubidiumCaesiumFission

/-- Exact-symbolic reporting makes no rounding or other change to the raw
formula. -/
def ReportedFissionEquationResult : Prop :=
  SatisfiesSourceSpecification rubidiumCaesiumFission

/-- The candidate uses the two mass numbers read from the yield-curve maxima. -/
theorem candidate_usesModalFragmentMasses :
    UsesModalFragmentMasses rubidiumCaesiumFission := by
  left
  constructor <;> rfl

/-- Explicit nucleon ledger: `235 + 1 = 93 + 140 + 3 = 236`. -/
theorem candidate_massNumberLedger :
    rubidiumCaesiumFission.parent.massNumber +
        rubidiumCaesiumFission.absorbedNeutrons = 236 ∧
      rubidiumCaesiumFission.fragment₁.massNumber +
          rubidiumCaesiumFission.fragment₂.massNumber +
        rubidiumCaesiumFission.emittedNeutrons = 236 := by
  norm_num [rubidiumCaesiumFission, uranium235, rubidium93, caesium140]

/-- Explicit charge ledger: `92 = 37 + 55`. -/
theorem candidate_atomicNumberLedger :
    atomicNumber rubidiumCaesiumFission.parent.element = 92 ∧
      atomicNumber rubidiumCaesiumFission.fragment₁.element = 37 ∧
      atomicNumber rubidiumCaesiumFission.fragment₂.element = 55 ∧
      ConservesAtomicNumber rubidiumCaesiumFission := by
  norm_num [ConservesAtomicNumber, rubidiumCaesiumFission, uranium235,
    rubidium93, caesium140, atomicNumber, uranium, rubidium, caesium]

/-- Rubidium and caesium are both in conventional periodic-table group 1. -/
theorem candidate_samePeriodicGroup :
    SamePeriodicGroup rubidiumCaesiumFission.fragment₁.element
      rubidiumCaesiumFission.fragment₂.element := by
  refine ⟨1, ?_, ?_⟩ <;>
    decide

/-- Raw result contract: the candidate is derived against every source-side
constraint rather than being supplied as a theorem premise. -/
theorem rawFissionEquationResult : RawFissionEquationResult := by
  refine ⟨rfl, rfl, rfl, candidate_usesModalFragmentMasses, ?_,
    candidate_samePeriodicGroup, ?_, candidate_atomicNumberLedger.2.2.2⟩
  · decide
  · unfold ConservesMassNumber
    exact candidate_massNumberLedger.1.trans candidate_massNumberLedger.2.symm

/-- Requested exact symbolic output for T4-A3. -/
theorem fissionEquation : ReportedFissionEquationResult := by
  exact rawFissionEquationResult

end IChO2026Problems.T4A3
