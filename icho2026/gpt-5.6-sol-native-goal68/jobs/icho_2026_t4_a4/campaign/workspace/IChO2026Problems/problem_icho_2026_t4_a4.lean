import IChO2026Chem.Reporting

/-!
# IChO 2026 T4-A4: energy released by the stated uranium-235 fission

The problem's preceding part supplies the fission channel.  Reading the two
maxima of the supplied yield graph gives mass numbers 93 and 140.  Together
with the same-periodic-group clue and charge conservation, these are
`Rb-93` (`Z = 37`) and `Cs-140` (`Z = 55`).  Thus the channel used here is

`U-235 + n -> Rb-93 + Cs-140 + 3 n`.

The namespaces below deliberately distinguish printed/graph-read input data
from quantities proved by arithmetic.  All decimal literals in this file are
exact rationals in `Real`; no intermediate rounding is performed.
-/

namespace IChO2026Problems.T4A4

open IChO2026Chem.Reporting

/-- Minimal nuclide data needed to check mass-number and charge conservation. -/
structure Nuclide where
  massNumber : ℕ
  atomicNumber : ℕ
deriving DecidableEq

/-- A binary fission channel with one incident neutron and some emitted neutrons. -/
structure BinaryFissionChannel where
  target : Nuclide
  incident : Nuclide
  lightFragment : Nuclide
  heavyFragment : Nuclide
  emittedNeutrons : ℕ

/-- Conservation of nucleon number for the channel. -/
def MassNumberBalanced (r : BinaryFissionChannel) : Prop :=
  r.target.massNumber + r.incident.massNumber =
    r.lightFragment.massNumber + r.heavyFragment.massNumber + r.emittedNeutrons

/-- Conservation of nuclear charge for the channel; neutrons have charge zero. -/
def AtomicNumberBalanced (r : BinaryFissionChannel) : Prop :=
  r.target.atomicNumber + r.incident.atomicNumber =
    r.lightFragment.atomicNumber + r.heavyFragment.atomicNumber

namespace ProblemInput

/-! Values printed on Q4-1/Q4-2 or read directly from the supplied graph. -/

def uranium235 : Nuclide := ⟨235, 92⟩
def neutron : Nuclide := ⟨1, 0⟩

/-- The light-fragment maximum read from the problem's yield graph. -/
def lightPeakMass : ℕ := 93

/-- The heavy-fragment maximum read from the problem's yield graph. -/
def heavyPeakMass : ℕ := 140

def emittedNeutronCount : ℕ := 3

/-- Printed average binding energy of uranium-235, in MeV per nucleon. -/
def uraniumBindingPerNucleon : ℝ := 7.59

/-- Printed average binding energy of the bound fission fragments, in MeV per nucleon. -/
def fragmentBindingPerNucleon : ℝ := 8.45

/-- The question instructs us to neglect binding energy of free neutrons. -/
def freeNeutronBindingEnergy : ℝ := 0

end ProblemInput

namespace DerivedChannel

open ProblemInput

/-- Rubidium-93: the `A = 93`, `Z = 37` light fragment. -/
def rubidium93 : Nuclide := ⟨lightPeakMass, 37⟩

/-- Caesium-140: the `A = 140`, `Z = 55` heavy fragment. -/
def caesium140 : Nuclide := ⟨heavyPeakMass, 55⟩

/-- Both Rb and Cs are in periodic-table group 1. -/
def rubidiumGroup : ℕ := 1
def caesiumGroup : ℕ := 1

theorem fragments_same_group : rubidiumGroup = caesiumGroup := by
  rfl

/-- The T4-A3 channel derived from the graph, group clue, and conservation laws. -/
def commonFission : BinaryFissionChannel where
  target := uranium235
  incident := neutron
  lightFragment := rubidium93
  heavyFragment := caesium140
  emittedNeutrons := emittedNeutronCount

theorem commonFission_massNumberBalanced : MassNumberBalanced commonFission := by
  norm_num [MassNumberBalanced, commonFission, uranium235, neutron,
    rubidium93, caesium140, lightPeakMass, heavyPeakMass, emittedNeutronCount]

theorem commonFission_atomicNumberBalanced : AtomicNumberBalanced commonFission := by
  norm_num [AtomicNumberBalanced, commonFission, uranium235, neutron,
    rubidium93, caesium140]

/-- The two bound fragments contain 233 nucleons; the other three product
nucleons are the explicitly free neutrons. -/
theorem boundFragmentNucleons :
    commonFission.lightFragment.massNumber + commonFission.heavyFragment.massNumber = 233 := by
  norm_num [commonFission, rubidium93, caesium140, lightPeakMass, heavyPeakMass]

end DerivedChannel

/-- Total binding energy in MeV from a mass number and a per-nucleon value. -/
def totalBindingEnergy (massNumber : ℕ) (perNucleon : ℝ) : ℝ :=
  (massNumber : ℝ) * perNucleon

/-- Energy release is final total binding energy minus initial total binding
energy.  Free-neutron terms are retained explicitly so that the source's
instruction to neglect them is represented rather than silently omitted. -/
def energyReleased
    (r : BinaryFissionChannel)
    (targetBindingPerNucleon fragmentBindingPerNucleon freeNeutronBinding : ℝ) : ℝ :=
  (totalBindingEnergy r.lightFragment.massNumber fragmentBindingPerNucleon +
      totalBindingEnergy r.heavyFragment.massNumber fragmentBindingPerNucleon +
      (r.emittedNeutrons : ℝ) * freeNeutronBinding) -
    (totalBindingEnergy r.target.massNumber targetBindingPerNucleon +
      totalBindingEnergy r.incident.massNumber freeNeutronBinding)

open ProblemInput DerivedChannel

/-- The exact, unrounded energy-release expression requested in T4-A4. -/
def fissionEnergy : ℝ :=
  energyReleased commonFission uraniumBindingPerNucleon
    fragmentBindingPerNucleon freeNeutronBindingEnergy

theorem initialTotalBindingEnergy :
    totalBindingEnergy uranium235.massNumber uraniumBindingPerNucleon = 1783.65 := by
  norm_num [totalBindingEnergy, uranium235, uraniumBindingPerNucleon]

theorem finalTotalBindingEnergy :
    totalBindingEnergy rubidium93.massNumber fragmentBindingPerNucleon +
        totalBindingEnergy caesium140.massNumber fragmentBindingPerNucleon = 1968.85 := by
  norm_num [totalBindingEnergy, rubidium93, caesium140, lightPeakMass, heavyPeakMass,
    fragmentBindingPerNucleon]

/-- Raw result: `233 * 8.45 - 235 * 7.59 = 185.20 MeV`. -/
theorem fissionEnergy_exact : fissionEnergy = 185.20 := by
  norm_num [fissionEnergy, energyReleased, totalBindingEnergy, commonFission,
    uranium235, neutron, rubidium93, caesium140, lightPeakMass, heavyPeakMass,
    emittedNeutronCount, uraniumBindingPerNucleon, fragmentBindingPerNucleon,
    freeNeutronBindingEnergy]

/-- The same exact result as a reduced rational, showing that `185.20` has not
been treated as a floating-point approximation. -/
theorem fissionEnergy_exactFraction : fissionEnergy = (926 : ℝ) / 5 := by
  rw [fissionEnergy_exact]
  norm_num

/-- Three significant figures at 185 MeV have a one-MeV reporting quantum. -/
def fissionEnergySubmission : NumericSubmission where
  rawValue := fissionEnergy
  reportedValue := 185
  reportingQuantum := 1

theorem fissionEnergy_reported :
    ValidNumericSubmission fissionEnergy fissionEnergySubmission := by
  constructor
  · rfl
  change ReportsAtQuantum fissionEnergy 185 1
  rw [fissionEnergy_exact]
  constructor
  · norm_num
  constructor
  · exact ⟨(185 : ℤ), by norm_num⟩
  · norm_num

/-- Final requested output: exact raw value and valid three-significant-figure display. -/
theorem answer_fission_energy :
    fissionEnergy = 185.20 ∧
      fissionEnergySubmission.reportedValue = 185 ∧
      ValidNumericSubmission fissionEnergy fissionEnergySubmission := by
  exact ⟨fissionEnergy_exact, rfl, fissionEnergy_reported⟩

#print axioms commonFission_massNumberBalanced
#print axioms commonFission_atomicNumberBalanced
#print axioms answer_fission_energy

end IChO2026Problems.T4A4
