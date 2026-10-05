import Mathlib

/-!
# IChO 2026, theory problem 4.3

The problem page supplies the uranium and neutron nuclides, says that three
neutrons are emitted, and gives a mass-yield graph.  Reading the integer mass
numbers at the two maxima of that graph gives 93 and 140.  Those observations
are recorded in `sourceData` and kept separate from the ordinary
periodic-table data in `Element.atomicNumber` and `Element.periodicGroup`.

The requested equation is represented by `mostCommonFission`.  The theorem
`requested_fission_equation` proves that it uses the two peak masses, has the
stated neutron multiplicity, conserves mass number and atomic number, and has
both fission-product elements in the same periodic-table group.
-/

namespace IChO2026Problems.T4A3

/-- The element identities needed to state the proposed nuclear equation.
`neutron` is included as a distinguished non-element particle. -/
inductive Element where
  | neutron
  | rubidium
  | caesium
  | uranium
  deriving DecidableEq, Repr

namespace Element

/-- Standard atomic numbers for the elements occurring in the equation. -/
def atomicNumber : Element → ℕ
  | neutron => 0
  | rubidium => 37
  | caesium => 55
  | uranium => 92

/-- Standard IUPAC group numbers where applicable here.
Rubidium and caesium are both alkali metals in group 1. -/
def periodicGroup : Element → Option ℕ
  | neutron => none
  | rubidium => some 1
  | caesium => some 1
  | uranium => none

end Element

/-- A nuclide is specified by its element and integer mass number. -/
structure Nuclide where
  element : Element
  massNumber : ℕ
  deriving DecidableEq, Repr

namespace Nuclide

/-- Nuclear charge, identified with the atomic number of the element. -/
def atomicNumber (n : Nuclide) : ℕ := n.element.atomicNumber

end Nuclide

/-- Source data read directly from Q4-1/Q4-2 of the problem PDF.

The graph has its light and heavy yield maxima at mass numbers 93 and 140;
the surrounding text gives uranium-235, one absorbed neutron, and three
emitted neutrons.  The Boolean group condition records only that a common
group is required; it does not encode which group or which products. -/
structure SourceData where
  targetMassNumber : ℕ
  targetAtomicNumber : ℕ
  incidentNeutronMassNumber : ℕ
  incidentNeutronAtomicNumber : ℕ
  emittedNeutronCount : ℕ
  lightPeakMassNumber : ℕ
  heavyPeakMassNumber : ℕ
  sameGroupRequired : Bool
  deriving DecidableEq, Repr

/-- The numerical and qualitative facts printed or graphed in the problem. -/
def sourceData : SourceData where
  targetMassNumber := 235
  targetAtomicNumber := 92
  incidentNeutronMassNumber := 1
  incidentNeutronAtomicNumber := 0
  emittedNeutronCount := 3
  lightPeakMassNumber := 93
  heavyPeakMassNumber := 140
  sameGroupRequired := true

def uranium235 : Nuclide := ⟨.uranium, 235⟩
def neutron : Nuclide := ⟨.neutron, 1⟩
def rubidium93 : Nuclide := ⟨.rubidium, 93⟩
def caesium140 : Nuclide := ⟨.caesium, 140⟩

/-- A binary fission equation with one incident particle and a repeated
emitted particle. -/
structure FissionEquation where
  target : Nuclide
  incident : Nuclide
  lightProduct : Nuclide
  heavyProduct : Nuclide
  emittedParticle : Nuclide
  emittedMultiplicity : ℕ
  deriving DecidableEq, Repr

/-- Total mass number on the reactant side. -/
def reactantMassNumber (r : FissionEquation) : ℕ :=
  r.target.massNumber + r.incident.massNumber

/-- Total mass number on the product side. -/
def productMassNumber (r : FissionEquation) : ℕ :=
  r.lightProduct.massNumber + r.heavyProduct.massNumber +
    r.emittedMultiplicity * r.emittedParticle.massNumber

/-- Total atomic number on the reactant side. -/
def reactantAtomicNumber (r : FissionEquation) : ℕ :=
  r.target.atomicNumber + r.incident.atomicNumber

/-- Total atomic number on the product side. -/
def productAtomicNumber (r : FissionEquation) : ℕ :=
  r.lightProduct.atomicNumber + r.heavyProduct.atomicNumber +
    r.emittedMultiplicity * r.emittedParticle.atomicNumber

def ConservesMassNumber (r : FissionEquation) : Prop :=
  reactantMassNumber r = productMassNumber r

def ConservesAtomicNumber (r : FissionEquation) : Prop :=
  reactantAtomicNumber r = productAtomicNumber r

/-- Both nuclear products are chemical elements assigned to one and the same
periodic-table group. -/
def ProductsInSamePeriodicGroup (r : FissionEquation) : Prop :=
  ∃ group : ℕ,
    r.lightProduct.element.periodicGroup = some group ∧
    r.heavyProduct.element.periodicGroup = some group

/-- The two product masses coincide with the two yield maxima on the graph. -/
def UsesYieldPeaks (data : SourceData) (r : FissionEquation) : Prop :=
  r.lightProduct.massNumber = data.lightPeakMassNumber ∧
  r.heavyProduct.massNumber = data.heavyPeakMassNumber

/-- The equation to be written in the answer box:

`²³⁵₉₂U + ¹₀n → ⁹³₃₇Rb + ¹⁴⁰₅₅Cs + 3 ¹₀n`. -/
def mostCommonFission : FissionEquation where
  target := uranium235
  incident := neutron
  lightProduct := rubidium93
  heavyProduct := caesium140
  emittedParticle := neutron
  emittedMultiplicity := 3

/-- The two graph-peak mass numbers and the stated three neutrons exactly
balance uranium-235 plus the absorbed neutron. -/
theorem source_mass_number_balance :
    sourceData.targetMassNumber + sourceData.incidentNeutronMassNumber =
      sourceData.lightPeakMassNumber + sourceData.heavyPeakMassNumber +
        sourceData.emittedNeutronCount * sourceData.incidentNeutronMassNumber := by
  norm_num [sourceData]

/-- Conversely, once the two peak masses are used, mass-number conservation
forces the emitted-neutron multiplicity to be three. -/
theorem emitted_neutron_count_forced (k : ℕ)
    (h : 235 + 1 = 93 + 140 + k) : k = 3 := by
  omega

/-- Rubidium and caesium have the same standard periodic-table group. -/
theorem rubidium_caesium_same_group :
    ∃ group : ℕ,
      Element.periodicGroup .rubidium = some group ∧
      Element.periodicGroup .caesium = some group := by
  exact ⟨1, rfl, rfl⟩

/-- Once rubidium supplies atomic number 37, charge conservation fixes the
other product's atomic number as 55, the atomic number of caesium. -/
theorem partner_atomic_number_forced (z : ℕ)
    (h : sourceData.targetAtomicNumber + sourceData.incidentNeutronAtomicNumber =
      Element.atomicNumber .rubidium + z) :
    z = Element.atomicNumber .caesium := by
  norm_num [sourceData, Element.atomicNumber] at h ⊢
  omega

theorem mostCommonFission_uses_yield_peaks :
    UsesYieldPeaks sourceData mostCommonFission := by
  constructor <;> rfl

theorem mostCommonFission_conserves_mass_number :
    ConservesMassNumber mostCommonFission := by
  norm_num [ConservesMassNumber, reactantMassNumber, productMassNumber,
    mostCommonFission, uranium235, neutron, rubidium93, caesium140]

theorem mostCommonFission_conserves_atomic_number :
    ConservesAtomicNumber mostCommonFission := by
  norm_num [ConservesAtomicNumber, reactantAtomicNumber, productAtomicNumber,
    mostCommonFission, uranium235, neutron, rubidium93, caesium140,
    Nuclide.atomicNumber, Element.atomicNumber]

theorem mostCommonFission_products_same_group :
    ProductsInSamePeriodicGroup mostCommonFission := by
  simpa [ProductsInSamePeriodicGroup, mostCommonFission, rubidium93, caesium140]
    using rubidium_caesium_same_group

/-- Complete formal specification of the requested output.  In particular,
the equation is not merely printed: each source-dependent and nuclear-
conservation condition needed by Q4.3 is proved. -/
theorem requested_fission_equation :
    mostCommonFission.target = uranium235 ∧
    mostCommonFission.incident = neutron ∧
    mostCommonFission.lightProduct = rubidium93 ∧
    mostCommonFission.heavyProduct = caesium140 ∧
    mostCommonFission.emittedParticle = neutron ∧
    mostCommonFission.emittedMultiplicity = sourceData.emittedNeutronCount ∧
    sourceData.sameGroupRequired = true ∧
    UsesYieldPeaks sourceData mostCommonFission ∧
    ConservesMassNumber mostCommonFission ∧
    ConservesAtomicNumber mostCommonFission ∧
    ProductsInSamePeriodicGroup mostCommonFission := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact mostCommonFission_uses_yield_peaks
  · exact mostCommonFission_conserves_mass_number
  · exact mostCommonFission_conserves_atomic_number
  · exact mostCommonFission_products_same_group

end IChO2026Problems.T4A3

#print axioms IChO2026Problems.T4A3.source_mass_number_balance
#print axioms IChO2026Problems.T4A3.emitted_neutron_count_forced
#print axioms IChO2026Problems.T4A3.partner_atomic_number_forced
#print axioms IChO2026Problems.T4A3.requested_fission_equation
