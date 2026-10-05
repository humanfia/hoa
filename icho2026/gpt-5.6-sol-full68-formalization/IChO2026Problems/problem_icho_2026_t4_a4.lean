import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T4-A4

This file formalizes the binding-energy calculation for the most common
fission channel of uranium-235.  The preceding A3 channel is derived locally
from the problem image and text: the yield-curve peaks have mass numbers 93
and 140, the fragments are required to be in one periodic-table group, and
three free neutrons are emitted.

All energy-valued definitions below are numerical values in MeV.  The two
binding-energy data are numerical values in MeV per nucleon.
-/

namespace IChO2026Problems.Icho2026T4A4

/-- The element data needed for this source-bounded nuclear channel.

This is a vocabulary for named elements, not an exhaustive candidate domain.
`periodicGroup = none` means that no group datum is used for that element in
this target. -/
structure Element where
  symbol : String
  atomicNumber : ℕ
  periodicGroup : Option ℕ
  deriving DecidableEq, Repr

/-- A nuclide, represented by its element and integer mass number. -/
structure Nuclide where
  element : Element
  massNumber : ℕ
  deriving DecidableEq, Repr

/-- Problem-text datum: uranium in the displayed reaction has atomic number 92. -/
def uranium : Element :=
  { symbol := "U", atomicNumber := 92, periodicGroup := none }

/-- Standard periodic-table data used to check the A3 same-group clue.
Provenance: IUPAC Periodic Table of the Elements (4 May 2022), the Rb cell in
the column headed group 1. -/
def rubidium : Element :=
  { symbol := "Rb", atomicNumber := 37, periodicGroup := some 1 }

/-- Standard periodic-table data used to check the A3 same-group clue.
Provenance: IUPAC Periodic Table of the Elements (4 May 2022), the Cs cell in
the column headed group 1. -/
def caesium : Element :=
  { symbol := "Cs", atomicNumber := 55, periodicGroup := some 1 }

/-- The uranium-235 reactant named in the problem. -/
def uranium235 : Nuclide :=
  { element := uranium, massNumber := 235 }

/-- Source-first readout of the two maxima of the fission-yield graph on page 1. -/
structure YieldGraphPeakReadout where
  lightMassNumber : ℕ
  heavyMassNumber : ℕ
  deriving DecidableEq, Repr

/-- The graph maxima occur at mass numbers 93 and 140. -/
def sourceYieldGraphPeaks : YieldGraphPeakReadout :=
  { lightMassNumber := 93, heavyMassNumber := 140 }

/-- The light fragment candidate selected by the graph and same-group clue. -/
def rubidium93 : Nuclide :=
  { element := rubidium
    massNumber := sourceYieldGraphPeaks.lightMassNumber }

/-- The heavy fragment candidate selected by the graph and same-group clue. -/
def caesium140 : Nuclide :=
  { element := caesium
    massNumber := sourceYieldGraphPeaks.heavyMassNumber }

/-- A two-fragment fission channel with explicit free-neutron coefficients. -/
structure FissionChannel where
  parent : Nuclide
  incomingFreeNeutrons : ℕ
  lightFragment : Nuclide
  heavyFragment : Nuclide
  emittedFreeNeutrons : ℕ
  deriving DecidableEq, Repr

/-- Conservation of nucleon (mass) number for a two-fragment channel. -/
def MassNumberConserved (channel : FissionChannel) : Prop :=
  channel.parent.massNumber + channel.incomingFreeNeutrons =
    channel.lightFragment.massNumber + channel.heavyFragment.massNumber +
      channel.emittedFreeNeutrons

/-- Conservation of proton (atomic) number; free neutrons carry atomic number zero. -/
def AtomicNumberConserved (channel : FissionChannel) : Prop :=
  channel.parent.element.atomicNumber =
    channel.lightFragment.element.atomicNumber +
      channel.heavyFragment.element.atomicNumber

/-- Two elements lie in the same numbered periodic-table group. -/
def SamePeriodicGroup (first second : Element) : Prop :=
  ∃ group : ℕ,
    first.periodicGroup = some group ∧ second.periodicGroup = some group

/-- The locally derived A3 candidate
`²³⁵₉₂U + ¹₀n → ⁹³₃₇Rb + ¹⁴⁰₅₅Cs + 3 ¹₀n`. -/
def mostCommonFissionChannel : FissionChannel :=
  { parent := uranium235
    incomingFreeNeutrons := 1
    lightFragment := rubidium93
    heavyFragment := caesium140
    emittedFreeNeutrons := 3 }

/-- Source-grounded specification of the A3 fission equation.  It checks both
graph peaks, the stated neutron coefficients, the same-group clue, and both
nuclear conservation laws. -/
def MostCommonFissionChannelSpec (channel : FissionChannel) : Prop :=
  channel.parent = uranium235 ∧
  channel.incomingFreeNeutrons = 1 ∧
  channel.lightFragment.massNumber = sourceYieldGraphPeaks.lightMassNumber ∧
  channel.heavyFragment.massNumber = sourceYieldGraphPeaks.heavyMassNumber ∧
  channel.lightFragment.massNumber ≤ channel.heavyFragment.massNumber ∧
  channel.emittedFreeNeutrons = 3 ∧
  SamePeriodicGroup channel.lightFragment.element channel.heavyFragment.element ∧
  MassNumberConserved channel ∧
  AtomicNumberConserved channel

/-- Inline derivation of the prerequisite A3 reaction from the bound problem
statement and yield graph. -/
theorem mostCommonFissionChannel_spec :
    MostCommonFissionChannelSpec mostCommonFissionChannel := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · norm_num [mostCommonFissionChannel, rubidium93, caesium140,
      sourceYieldGraphPeaks]
  · exact ⟨1, rfl, rfl⟩
  · norm_num [MassNumberConserved, mostCommonFissionChannel, uranium235,
      rubidium93, caesium140, sourceYieldGraphPeaks]
  · norm_num [AtomicNumberConserved, mostCommonFissionChannel, uranium235,
      uranium, rubidium93, rubidium, caesium140, caesium]

/-- The number of nucleons bound into the two fission fragments. -/
def fragmentBoundNucleonCount (channel : FissionChannel) : ℕ :=
  channel.lightFragment.massNumber + channel.heavyFragment.massNumber

/-- Any mass-balanced channel with the source-stated coefficients has 233
bound fragment nucleons.  Consequently, the A4 energy does not depend on a
further choice between fragment identities once A3's neutron count is fixed. -/
theorem fragmentBoundNucleonCount_eq_of_source_balance
    (channel : FissionChannel)
    (hParent : channel.parent.massNumber = 235)
    (hIncoming : channel.incomingFreeNeutrons = 1)
    (hEmitted : channel.emittedFreeNeutrons = 3)
    (hMass : MassNumberConserved channel) :
    fragmentBoundNucleonCount channel = 233 := by
  unfold fragmentBoundNucleonCount
  unfold MassNumberConserved at hMass
  omega

/-- The A3 balance leaves 233 nucleons bound in the fragments and three as free
neutrons.  This is the previous-part fact needed by A4. -/
theorem mostCommonFissionChannel_boundNucleons :
    fragmentBoundNucleonCount mostCommonFissionChannel = 233 := by
  norm_num [fragmentBoundNucleonCount, mostCommonFissionChannel, rubidium93,
    caesium140, sourceYieldGraphPeaks]

/-- Numerical values measured in MeV. -/
abbrev MeV := ℝ

/-- Numerical binding-energy values measured in MeV per nucleon. -/
abbrev MeVPerNucleon := ℝ

/-- Problem-stipulated average binding energy of uranium-235, in MeV/nucleon. -/
noncomputable def uranium235BindingEnergyPerNucleon : MeVPerNucleon :=
  (759 : ℝ) / 100

/-- Problem-stipulated average binding energy of the fission fragments, in
MeV/nucleon. -/
noncomputable def fissionProductBindingEnergyPerNucleon : MeVPerNucleon :=
  (845 : ℝ) / 100

/-- The instruction to neglect free-neutron binding energy is modeled as zero
MeV per free neutron. -/
def freeNeutronBindingEnergy : MeV := 0

/-- Total binding energy of a collection of bound nucleons, in MeV. -/
def totalBindingEnergy
    (nucleonCount : ℕ) (averageBindingEnergy : MeVPerNucleon) : MeV :=
  (nucleonCount : ℝ) * averageBindingEnergy

/-- Exact, unrounded released energy: total final binding energy minus total
initial binding energy, retaining the zero free-neutron terms explicitly. -/
noncomputable def fissionEnergyRaw : MeV :=
  totalBindingEnergy
      (fragmentBoundNucleonCount mostCommonFissionChannel)
      fissionProductBindingEnergyPerNucleon +
    (mostCommonFissionChannel.emittedFreeNeutrons : ℝ) *
      freeNeutronBindingEnergy -
    (totalBindingEnergy mostCommonFissionChannel.parent.massNumber
        uranium235BindingEnergyPerNucleon +
      (mostCommonFissionChannel.incomingFreeNeutrons : ℝ) *
        freeNeutronBindingEnergy)

/-- Problem-specific derivation contract for a proposed released energy.
Besides checking the A3 channel, it exposes the fragment nucleon count, the
zero-neutron convention, the governing final-minus-initial relation, and the
positive sign convention for released energy. -/
def FissionEnergyDerivationSpec (energy : MeV) : Prop :=
  MostCommonFissionChannelSpec mostCommonFissionChannel ∧
  fragmentBoundNucleonCount mostCommonFissionChannel = 233 ∧
  freeNeutronBindingEnergy = 0 ∧
  energy =
    totalBindingEnergy
        (fragmentBoundNucleonCount mostCommonFissionChannel)
        fissionProductBindingEnergyPerNucleon +
      (mostCommonFissionChannel.emittedFreeNeutrons : ℝ) *
        freeNeutronBindingEnergy -
      (totalBindingEnergy mostCommonFissionChannel.parent.massNumber
          uranium235BindingEnergyPerNucleon +
        (mostCommonFissionChannel.incomingFreeNeutrons : ℝ) *
          freeNeutronBindingEnergy) ∧
  0 ≤ energy

/-- The zero-argument derivation proposition certified by the raw answer-blind
result theorem.  Naming this proposition separately makes the generated result
contract bind to the complete source derivation, rather than to a bare number. -/
def FissionEnergyRawDerivationSpec : Prop :=
  FissionEnergyDerivationSpec fissionEnergyRaw

/-- Exact evaluation of the unrounded source expression. -/
theorem fissionEnergyRaw_eq :
    fissionEnergyRaw = (926 : ℝ) / 5 := by
  norm_num [fissionEnergyRaw, totalBindingEnergy,
    fragmentBoundNucleonCount, mostCommonFissionChannel, uranium235,
    rubidium93, caesium140, sourceYieldGraphPeaks,
    fissionProductBindingEnergyPerNucleon,
    uranium235BindingEnergyPerNucleon, freeNeutronBindingEnergy]

/-- Raw answer-blind result contract.  The interval is the closed enclosure
supporting the later three-significant-figure reporting cell (quantum 1 MeV),
not a measurement tolerance. -/
theorem fissionEnergy_raw_result :
    FissionEnergyRawDerivationSpec ∧
      (369 : ℝ) / 2 ≤ fissionEnergyRaw ∧
      fissionEnergyRaw ≤ (371 : ℝ) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨mostCommonFissionChannel_spec,
      mostCommonFissionChannel_boundNucleons, rfl, rfl, ?_⟩
    rw [fissionEnergyRaw_eq]
    norm_num
  · rw [fissionEnergyRaw_eq]
    norm_num
  · rw [fissionEnergyRaw_eq]
    norm_num

/-- Final reporting contract.  At this magnitude, three significant figures
have quantum 1 MeV; ties are interpreted by `ReportsAtQuantum` as required by
the project-wide half-away-from-zero policy. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"fission_energy","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"185","reporting_quantum":"1","raw_declaration":"IChO2026Problems.Icho2026T4A4.fissionEnergyRaw","reporting_declaration":"IChO2026Problems.Icho2026T4A4.fissionEnergy_reported_result"}
theorem fissionEnergy_reported_result :
    IChO2026Chem.Reporting.ReportsAtQuantum
      fissionEnergyRaw (185 : ℝ) 1 := by
  rw [fissionEnergyRaw_eq]
  refine ⟨by norm_num, ?_, ?_⟩
  · exact ⟨185, by norm_num⟩
  · norm_num

end IChO2026Problems.Icho2026T4A4
