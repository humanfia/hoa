import IChO2026Chem.Reporting

/-!
# IChO 2026 T4, part 4.9

The problem asks for the number of fissions responsible for a 30 kiloton TNT
equivalent explosion and the initial mass of 90%-enriched uranium when 33% of
its uranium-235 fissions.  The energy per fission is derived here from part 4.4
rather than replaced by the printed 200 MeV fallback.

Problem data and standard conversion laws are kept in separate namespaces.
Every decimal below is represented by an exact rational number.  Rounding is
performed only by the two final `NumericSubmission` values.
-/

namespace IChO2026Problems.Icho2026T4A9

open IChO2026Chem.Reporting

noncomputable section

/-- The minimal nuclide data needed to check the reaction from parts 4.3--4.4. -/
structure Nuclide where
  massNumber : ℕ
  atomicNumber : ℕ
deriving DecidableEq

namespace ProblemInput

def uranium235 : Nuclide := ⟨235, 92⟩
def absorbedNeutrons : ℕ := 1
def emittedNeutrons : ℕ := 3

/-- Light-product mass number read from the first maximum of the supplied
fission-yield graph. -/
def lightProductPeakMassNumber : ℕ := 93

/-- Heavy-product mass number read from the second maximum of the supplied
fission-yield graph. -/
def heavyProductPeakMassNumber : ℕ := 140

/-- Binding energy per nucleon of uranium-235, in MeV/nucleon. -/
def uraniumBindingMeVPerNucleon : ℝ := 759 / 100

/-- Average binding energy per nucleon of the two fission products, in
MeV/nucleon. -/
def productBindingMeVPerNucleon : ℝ := 845 / 100

/-- Stated explosive yield in kilotons of TNT equivalent. -/
def explosionYieldKiloton : ℝ := 30

/-- The problem states that one ton of TNT equivalent is 4.184 GJ. -/
def joulePerTonTNT : ℝ := 4184 * 10 ^ 6

/-- Mass fraction of uranium-235 in the enriched uranium. -/
def uranium235MassFraction : ℝ := 90 / 100

/-- Fraction of the uranium-235 inventory that underwent fission. -/
def fissionedFraction : ℝ := 33 / 100

/-- Numerical molar mass in g/mol, using the uranium-235 atomic mass printed
in part 4.1. -/
def uranium235MolarMassGPerMol : ℝ := 23504 / 100

end ProblemInput

namespace TrustedLaw

/-- Periodic-table atomic number of rubidium. -/
def rubidiumAtomicNumber : ℕ := 37

/-- Periodic-table atomic number of caesium. -/
def caesiumAtomicNumber : ℕ := 55

/-- Rubidium is in periodic-table group 1. -/
def rubidiumPeriodicGroup : ℕ := 1

/-- Caesium is in periodic-table group 1. -/
def caesiumPeriodicGroup : ℕ := 1

/-- `1 MeV = 1.602176634e-13 J`, from the exact SI elementary charge and the
definition of the electronvolt. -/
def joulePerMeV : ℝ := 1602176634 / 10 ^ 22

/-- Exact SI Avogadro constant, in mol^-1. -/
def avogadroPerMol : ℝ := 602214076 * 10 ^ 15

/-- The standard prefix conversion from kilotons to tons. -/
def tonPerKiloton : ℝ := 1000

/-- The standard prefix conversion from kilograms to grams. -/
def gramPerKilogram : ℝ := 1000

end TrustedLaw

namespace Derived

/-- The light graph maximum, interpreted using the same-group condition. -/
def rubidium93 : Nuclide :=
  ⟨ProblemInput.lightProductPeakMassNumber, TrustedLaw.rubidiumAtomicNumber⟩

/-- The heavy graph maximum, interpreted using the same-group condition. -/
def caesium140 : Nuclide :=
  ⟨ProblemInput.heavyProductPeakMassNumber, TrustedLaw.caesiumAtomicNumber⟩

/-- Both selected fission products are alkali metals in periodic-table group
1, as required by part 4.3. -/
theorem fission_products_same_periodic_group :
    TrustedLaw.rubidiumPeriodicGroup = TrustedLaw.caesiumPeriodicGroup := by
  norm_num [TrustedLaw.rubidiumPeriodicGroup, TrustedLaw.caesiumPeriodicGroup]

/-- The displayed fission channel conserves nucleon number:
`235 U + n -> 93 Rb + 140 Cs + 3 n`. -/
theorem fission_mass_number_conserved :
    ProblemInput.uranium235.massNumber + ProblemInput.absorbedNeutrons =
      rubidium93.massNumber + caesium140.massNumber +
        ProblemInput.emittedNeutrons := by
  norm_num [ProblemInput.uranium235, rubidium93, caesium140,
    ProblemInput.lightProductPeakMassNumber,
    ProblemInput.heavyProductPeakMassNumber, ProblemInput.absorbedNeutrons,
    ProblemInput.emittedNeutrons, TrustedLaw.rubidiumAtomicNumber,
    TrustedLaw.caesiumAtomicNumber]

/-- The same fission channel conserves atomic number. -/
theorem fission_atomic_number_conserved :
    ProblemInput.uranium235.atomicNumber =
      rubidium93.atomicNumber + caesium140.atomicNumber := by
  norm_num [ProblemInput.uranium235, rubidium93, caesium140,
    ProblemInput.lightProductPeakMassNumber,
    ProblemInput.heavyProductPeakMassNumber, TrustedLaw.rubidiumAtomicNumber,
    TrustedLaw.caesiumAtomicNumber]

/-- Total number of bound nucleons in the two products.  The three emitted
neutrons are free, exactly as stipulated in part 4.4. -/
def productBoundNucleons : ℕ :=
  rubidium93.massNumber + caesium140.massNumber

theorem product_bound_nucleons : productBoundNucleons = 233 := by
  norm_num [productBoundNucleons, rubidium93, caesium140,
    ProblemInput.lightProductPeakMassNumber,
    ProblemInput.heavyProductPeakMassNumber, TrustedLaw.rubidiumAtomicNumber,
    TrustedLaw.caesiumAtomicNumber]

/-- Energy released per fission in MeV, derived from the binding-energy
difference requested in part 4.4. -/
def fissionEnergyMeV : ℝ :=
  productBoundNucleons * ProblemInput.productBindingMeVPerNucleon -
    ProblemInput.uranium235.massNumber *
      ProblemInput.uraniumBindingMeVPerNucleon

/-- Part 4.4 gives 185.20 MeV, so the 200 MeV fallback is not used. -/
theorem part_4_4_fission_energy : fissionEnergyMeV = 926 / 5 := by
  norm_num [fissionEnergyMeV, productBoundNucleons,
    rubidium93, caesium140, ProblemInput.lightProductPeakMassNumber,
    ProblemInput.heavyProductPeakMassNumber, TrustedLaw.rubidiumAtomicNumber,
    TrustedLaw.caesiumAtomicNumber, ProblemInput.uranium235,
    ProblemInput.productBindingMeVPerNucleon,
    ProblemInput.uraniumBindingMeVPerNucleon]

/-- Macroscopic energy of the stated 30 kiloton explosion, in joules. -/
def explosionEnergyJ : ℝ :=
  ProblemInput.explosionYieldKiloton * TrustedLaw.tonPerKiloton *
    ProblemInput.joulePerTonTNT

theorem explosion_energy_joule : explosionEnergyJ = 125520000000000 := by
  norm_num [explosionEnergyJ, ProblemInput.explosionYieldKiloton,
    TrustedLaw.tonPerKiloton, ProblemInput.joulePerTonTNT]

/-- Energy carried by one fission according to part 4.4, in joules. -/
def energyPerFissionJ : ℝ := fissionEnergyMeV * TrustedLaw.joulePerMeV

theorem energy_per_fission_joule :
    energyPerFissionJ = 370903890771 / 12500000000000000000000 := by
  norm_num [energyPerFissionJ, part_4_4_fission_energy,
    TrustedLaw.joulePerMeV]

/-- Exact unrounded real-valued fission-count estimate obtained from the
macroscopic energy balance. -/
def totalFissionsRaw : ℝ := explosionEnergyJ / energyPerFissionJ

theorem total_fissions_raw_exact :
    totalFissionsRaw =
      523000000000000000000000000000000000 / 123634630257 := by
  rw [totalFissionsRaw, explosion_energy_joule, energy_per_fission_joule]
  norm_num

/-- The raw fission count satisfies the physical energy balance. -/
theorem total_fissions_energy_balance :
    totalFissionsRaw * energyPerFissionJ = explosionEnergyJ := by
  rw [totalFissionsRaw, explosion_energy_joule, energy_per_fission_joule]
  norm_num

/-- The positive per-fission energy makes the energy-balance solution unique. -/
theorem total_fissions_unique {n : ℝ}
    (h : n * energyPerFissionJ = explosionEnergyJ) :
    n = totalFissionsRaw := by
  have hne : energyPerFissionJ ≠ 0 := by
    rw [energy_per_fission_joule]
    norm_num
  exact (eq_div_iff hne).2 h

/-- Fissions produced per kilogram of the stated enriched uranium. -/
def fissionsPerKgEnriched : ℝ :=
  TrustedLaw.gramPerKilogram * ProblemInput.uranium235MassFraction /
      ProblemInput.uranium235MolarMassGPerMol * TrustedLaw.avogadroPerMol *
    ProblemInput.fissionedFraction

/-- Exact unrounded enriched-uranium mass, in kilograms. -/
def enrichedUraniumMassKgRaw : ℝ := totalFissionsRaw / fissionsPerKgEnriched

theorem enriched_uranium_mass_raw_exact :
    enrichedUraniumMassKgRaw =
      30731480000000000000000 / 5528247710670201641751 := by
  rw [enrichedUraniumMassKgRaw, total_fissions_raw_exact]
  norm_num [fissionsPerKgEnriched, TrustedLaw.gramPerKilogram,
    ProblemInput.uranium235MassFraction,
    ProblemInput.uranium235MolarMassGPerMol, TrustedLaw.avogadroPerMol,
    ProblemInput.fissionedFraction]

/-- The mass result reproduces the required number of fissions after the 90%
enrichment and 33% fissioned-fraction factors are applied. -/
theorem enriched_uranium_inventory_balance :
    enrichedUraniumMassKgRaw * fissionsPerKgEnriched = totalFissionsRaw := by
  rw [enrichedUraniumMassKgRaw, total_fissions_raw_exact]
  norm_num [fissionsPerKgEnriched, TrustedLaw.gramPerKilogram,
    ProblemInput.uranium235MassFraction,
    ProblemInput.uranium235MolarMassGPerMol, TrustedLaw.avogadroPerMol,
    ProblemInput.fissionedFraction]

/-- The positive inventory coefficient makes the uranium-mass solution unique. -/
theorem enriched_uranium_mass_unique {m : ℝ}
    (h : m * fissionsPerKgEnriched = totalFissionsRaw) :
    m = enrichedUraniumMassKgRaw := by
  have hne : fissionsPerKgEnriched ≠ 0 := by
    norm_num [fissionsPerKgEnriched, TrustedLaw.gramPerKilogram,
      ProblemInput.uranium235MassFraction,
      ProblemInput.uranium235MolarMassGPerMol, TrustedLaw.avogadroPerMol,
      ProblemInput.fissionedFraction]
  exact (eq_div_iff hne).2 h

/-- Three-significant-figure fission-count submission: `4.23e24`. -/
def totalFissionsSubmission : NumericSubmission where
  rawValue := totalFissionsRaw
  reportedValue := 423 * 10 ^ 22
  reportingQuantum := 10 ^ 22

/-- Three-significant-figure mass submission: `5.56 kg`. -/
def enrichedUraniumMassSubmission : NumericSubmission where
  rawValue := enrichedUraniumMassKgRaw
  reportedValue := 556 / 100
  reportingQuantum := 1 / 100

/-- First requested output, including its exact raw expression and proof that
`4.23e24` is the nearest value at the three-significant-figure quantum. -/
theorem total_fissions_output :
    ValidNumericSubmission totalFissionsRaw totalFissionsSubmission := by
  constructor
  · rfl
  · rw [ReportsAtQuantum]
    refine ⟨by norm_num [totalFissionsSubmission], ?_, ?_⟩
    · refine ⟨423, ?_⟩
      norm_num [totalFissionsSubmission]
    · simp only [totalFissionsSubmission]
      rw [if_pos]
      · rw [total_fissions_raw_exact]
        norm_num
      · rw [total_fissions_raw_exact]
        norm_num

/-- Second requested output, including its exact raw expression and proof that
`5.56 kg` is the nearest value at the three-significant-figure quantum. -/
theorem enriched_uranium_mass_output :
    ValidNumericSubmission enrichedUraniumMassKgRaw
      enrichedUraniumMassSubmission := by
  constructor
  · rfl
  · rw [ReportsAtQuantum]
    refine ⟨by norm_num [enrichedUraniumMassSubmission], ?_, ?_⟩
    · refine ⟨556, ?_⟩
      norm_num [enrichedUraniumMassSubmission]
    · simp only [enrichedUraniumMassSubmission]
      rw [if_pos]
      · rw [enriched_uranium_mass_raw_exact]
        norm_num
      · rw [enriched_uranium_mass_raw_exact]
        norm_num

/-- Both numerical outputs requested by the blank answer sheet. -/
theorem requested_outputs :
    ValidNumericSubmission totalFissionsRaw totalFissionsSubmission ∧
      ValidNumericSubmission enrichedUraniumMassKgRaw
        enrichedUraniumMassSubmission :=
  ⟨total_fissions_output, enriched_uranium_mass_output⟩

end Derived

end

end IChO2026Problems.Icho2026T4A9

#print axioms IChO2026Problems.Icho2026T4A9.Derived.total_fissions_output
#print axioms IChO2026Problems.Icho2026T4A9.Derived.enriched_uranium_mass_output
#print axioms IChO2026Problems.Icho2026T4A9.Derived.requested_outputs
