import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T3-A6

The source supplies pairwise pi-stacking energies in kJ mol⁻¹ for directly
registered and slightly shifted aromatic rings.  The COF-8 drawing supplies
the aromatic inventory of an `E1 + D2` repeat unit and the contacts made in
the AA and AB stacking diagrams.  This file keeps those source observations
separate from the three requested, derived energy sums.
-/

namespace IChO2026Problems
namespace T3A6

noncomputable section

/-- Scalar molar energies in this problem are measured in kJ mol⁻¹. -/
abbrev KilojoulesPerMole := ℝ

/-- Allowed provenance tags for the finite image and table observations used here. -/
inductive FactProvenance where
  | problemText
  | problemImage
  | derivedTheorem
  deriving DecidableEq, Repr

/-- The two aromatic ring types distinguished by the interaction table. -/
inductive AromaticUnit where
  | benzene
  | triazine
  deriving DecidableEq, Repr

/-- Aromatic rings belonging to a molecular building block or repeat unit. -/
structure AromaticInventory where
  benzene : ℕ
  triazine : ℕ
  deriving DecidableEq, Repr

/-- D2 has three phenylene rings attached to one central triazine ring. -/
def d2AromaticInventory : AromaticInventory :=
  { benzene := 3, triazine := 1 }

/-- E1 contributes its central benzene ring. -/
def e1AromaticInventory : AromaticInventory :=
  { benzene := 1, triazine := 0 }

/-- Multiplicities of the two depicted building blocks in one COF-8 repeat unit. -/
structure RepeatAssembly where
  e1Copies : ℕ
  d2Copies : ℕ
  deriving DecidableEq, Repr

/-- The dashed COF-8 repeat-unit construction is one E1 plus one D2. -/
def cof8RepeatAssembly : RepeatAssembly :=
  { e1Copies := 1, d2Copies := 1 }

/-- Recombine the aromatic components of an E1/D2 assembly. -/
def aromaticInventoryOfAssembly (assembly : RepeatAssembly) : AromaticInventory :=
  { benzene :=
      assembly.e1Copies * e1AromaticInventory.benzene +
        assembly.d2Copies * d2AromaticInventory.benzene
    triazine :=
      assembly.e1Copies * e1AromaticInventory.triazine +
        assembly.d2Copies * d2AromaticInventory.triazine }

/-- Image-derived aromatic inventory of one complete COF-8 repeat unit. -/
def cof8RepeatInventory : AromaticInventory :=
  aromaticInventoryOfAssembly cof8RepeatAssembly

/-- Provenance of the repeat-unit component recount. -/
def cof8RepeatInventoryProvenance : FactProvenance := .problemImage

/-- Direct registration versus the second-column, slightly shifted geometry. -/
inductive InteractionGeometry where
  | directlyRegistered
  | slightlyShifted
  deriving DecidableEq, Repr

/-- Pair energies for benzene-benzene, benzene-triazine, and triazine-triazine. -/
structure PairEnergyTable where
  benzeneBenzene : KilojoulesPerMole
  benzeneTriazine : KilojoulesPerMole
  triazineTriazine : KilojoulesPerMole

/-- First column of the printed interaction-energy table. -/
def directlyRegisteredEnergies : PairEnergyTable :=
  { benzeneBenzene := -(79 : ℝ) / 10
    benzeneTriazine := -(249 : ℝ) / 5
    triazineTriazine := -(67 : ℝ) / 10 }

/-- Second column of the printed interaction-energy table. -/
def slightlyShiftedEnergies : PairEnergyTable :=
  { benzeneBenzene := -(63 : ℝ) / 5
    benzeneTriazine := -(278 : ℝ) / 5
    triazineTriazine := -(167 : ℝ) / 10 }

/-- Source-table provenance of both pair-energy records. -/
def pairEnergyTableProvenance : FactProvenance := .problemImage

/-- Multiplicities of the three possible aromatic contact types. -/
structure ContactLedger where
  benzeneBenzene : ℕ
  benzeneTriazine : ℕ
  triazineTriazine : ℕ
  deriving DecidableEq, Repr

/-- A contact ledger together with its exact source kind and image locator. -/
structure ContactObservation where
  contacts : ContactLedger
  provenance : FactProvenance
  sourceLocator : String

/-- In AA (and AA'), all four benzene sites and the triazine site register. -/
def aaContactObservation : ContactObservation :=
  { contacts :=
      { benzeneBenzene := 4
        benzeneTriazine := 0
        triazineTriazine := 1 }
    provenance := .problemImage
    sourceLocator := "T3_page-6.png: COF-8 repeat unit and panels (a)-(b)" }

/-- In AB (and AB'), one opposite-node benzene-triazine contact registers. -/
def abContactObservation : ContactObservation :=
  { contacts :=
      { benzeneBenzene := 0
        benzeneTriazine := 1
        triazineTriazine := 0 }
    provenance := .problemImage
    sourceLocator := "T3_page-6.png: stacking panel (c)" }

/-- The four arrangements needed for the supplied cross-check and requested outputs. -/
inductive StackingArrangement where
  | aa
  | aaPrime
  | ab
  | abPrime
  deriving DecidableEq, Repr

/-- Primed arrangements use the slightly shifted column of the table. -/
def geometryOfArrangement : StackingArrangement → InteractionGeometry
  | .aa => .directlyRegistered
  | .aaPrime => .slightlyShifted
  | .ab => .directlyRegistered
  | .abPrime => .slightlyShifted

/-- AA variants share one contact ledger; AB variants share the other. -/
def contactsOfArrangement : StackingArrangement → ContactLedger
  | .aa => aaContactObservation.contacts
  | .aaPrime => aaContactObservation.contacts
  | .ab => abContactObservation.contacts
  | .abPrime => abContactObservation.contacts

/-- Select the source table column associated with an interaction geometry. -/
def energiesOfGeometry : InteractionGeometry → PairEnergyTable
  | .directlyRegistered => directlyRegisteredEnergies
  | .slightlyShifted => slightlyShiftedEnergies

/-- Add only the aromatic contacts in a ledger, as required by the question. -/
def energyOfContacts (table : PairEnergyTable)
    (contacts : ContactLedger) : KilojoulesPerMole :=
  (contacts.benzeneBenzene : ℝ) * table.benzeneBenzene +
    (contacts.benzeneTriazine : ℝ) * table.benzeneTriazine +
    (contacts.triazineTriazine : ℝ) * table.triazineTriazine

/-- Source-derived raw stacking energy for any of the four arrangements. -/
def stackingEnergy (arrangement : StackingArrangement) : KilojoulesPerMole :=
  energyOfContacts (energiesOfGeometry (geometryOfArrangement arrangement))
    (contactsOfArrangement arrangement)

/-- Requested raw AA energy, before reporting. -/
def stackingEnergyAA : KilojoulesPerMole := stackingEnergy .aa

/-- Supplied AA' energy reconstructed as a consistency check. -/
def stackingEnergyAAPrime : KilojoulesPerMole := stackingEnergy .aaPrime

/-- Requested raw AB energy, before reporting. -/
def stackingEnergyAB : KilojoulesPerMole := stackingEnergy .ab

/-- Requested raw AB' energy, before reporting. -/
def stackingEnergyABPrime : KilojoulesPerMole := stackingEnergy .abPrime

/-- The image component recount gives four benzene and one triazine per repeat unit. -/
theorem cof8_repeat_inventory_value :
    cof8RepeatInventory.benzene = 4 ∧ cof8RepeatInventory.triazine = 1 := by
  norm_num [cof8RepeatInventory, aromaticInventoryOfAssembly,
    cof8RepeatAssembly, e1AromaticInventory, d2AromaticInventory]

/-- The AA contact ledger accounts for every aromatic unit in the repeat cell. -/
theorem aa_contact_ledger_complete :
    aaContactObservation.contacts.benzeneBenzene +
          aaContactObservation.contacts.benzeneTriazine +
          aaContactObservation.contacts.triazineTriazine =
        cof8RepeatInventory.benzene + cof8RepeatInventory.triazine := by
  norm_num [aaContactObservation, cof8RepeatInventory, aromaticInventoryOfAssembly,
    cof8RepeatAssembly, e1AromaticInventory, d2AromaticInventory]

/-- The same image/table calculation reproduces the problem's printed AA' check. -/
theorem aaPrime_supplied_energy_crosscheck :
    stackingEnergyAAPrime = -(671 : ℝ) / 10 := by
  norm_num [stackingEnergyAAPrime, stackingEnergy, energyOfContacts,
    energiesOfGeometry, geometryOfArrangement, contactsOfArrangement,
    aaContactObservation, slightlyShiftedEnergies]

/-- Exact end-to-end AA calculation from its contact ledger and table column. -/
theorem stackingEnergyAA_raw :
    stackingEnergyAA =
        (4 : ℝ) * (-(79 : ℝ) / 10) + (-(67 : ℝ) / 10) ∧
      stackingEnergyAA = -(383 : ℝ) / 10 := by
  norm_num [stackingEnergyAA, stackingEnergy, energyOfContacts,
    energiesOfGeometry, geometryOfArrangement, contactsOfArrangement,
    aaContactObservation, directlyRegisteredEnergies]

/-- Exact end-to-end AB calculation from its sole registered aromatic pair. -/
theorem stackingEnergyAB_raw :
    stackingEnergyAB = (1 : ℝ) * (-(249 : ℝ) / 5) ∧
      stackingEnergyAB = -(249 : ℝ) / 5 := by
  norm_num [stackingEnergyAB, stackingEnergy, energyOfContacts,
    energiesOfGeometry, geometryOfArrangement, contactsOfArrangement,
    abContactObservation, directlyRegisteredEnergies]

/-- Exact end-to-end AB' calculation using the shifted benzene-triazine entry. -/
theorem stackingEnergyABPrime_raw :
    stackingEnergyABPrime = (1 : ℝ) * (-(278 : ℝ) / 5) ∧
      stackingEnergyABPrime = -(278 : ℝ) / 5 := by
  norm_num [stackingEnergyABPrime, stackingEnergy, energyOfContacts,
    energiesOfGeometry, geometryOfArrangement, contactsOfArrangement,
    abContactObservation, slightlyShiftedEnergies]

/-- Combined semantic proposition for all three exact requested outputs. -/
def RawResultSpec : Prop :=
  (stackingEnergyAA =
      (aaContactObservation.contacts.benzeneBenzene : ℝ) *
          directlyRegisteredEnergies.benzeneBenzene +
        (aaContactObservation.contacts.benzeneTriazine : ℝ) *
          directlyRegisteredEnergies.benzeneTriazine +
        (aaContactObservation.contacts.triazineTriazine : ℝ) *
          directlyRegisteredEnergies.triazineTriazine) ∧
  stackingEnergyAA = -(383 : ℝ) / 10 ∧
  (stackingEnergyAB =
      (abContactObservation.contacts.benzeneBenzene : ℝ) *
          directlyRegisteredEnergies.benzeneBenzene +
        (abContactObservation.contacts.benzeneTriazine : ℝ) *
          directlyRegisteredEnergies.benzeneTriazine +
        (abContactObservation.contacts.triazineTriazine : ℝ) *
          directlyRegisteredEnergies.triazineTriazine) ∧
  stackingEnergyAB = -(249 : ℝ) / 5 ∧
  (stackingEnergyABPrime =
      (abContactObservation.contacts.benzeneBenzene : ℝ) *
          slightlyShiftedEnergies.benzeneBenzene +
        (abContactObservation.contacts.benzeneTriazine : ℝ) *
          slightlyShiftedEnergies.benzeneTriazine +
        (abContactObservation.contacts.triazineTriazine : ℝ) *
          slightlyShiftedEnergies.triazineTriazine) ∧
  stackingEnergyABPrime = -(278 : ℝ) / 5

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"stacking_energy_aa","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"-38.3","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T3A6.stackingEnergyAA","reporting_declaration":"IChO2026Problems.T3A6.stackingEnergyAA_reported"}
theorem stackingEnergyAA_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyAA (-(383 : ℝ) / 10) ((1 : ℝ) / 10) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨(-383 : ℤ), by norm_num⟩, ?_⟩
  norm_num [stackingEnergyAA, stackingEnergy, energyOfContacts,
    energiesOfGeometry, geometryOfArrangement, contactsOfArrangement,
    aaContactObservation, directlyRegisteredEnergies]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"stacking_energy_ab","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"-49.8","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T3A6.stackingEnergyAB","reporting_declaration":"IChO2026Problems.T3A6.stackingEnergyAB_reported"}
theorem stackingEnergyAB_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyAB (-(249 : ℝ) / 5) ((1 : ℝ) / 10) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨(-498 : ℤ), by norm_num⟩, ?_⟩
  norm_num [stackingEnergyAB, stackingEnergy, energyOfContacts,
    energiesOfGeometry, geometryOfArrangement, contactsOfArrangement,
    abContactObservation, directlyRegisteredEnergies]

-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"stacking_energy_ab_prime","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"-55.6","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T3A6.stackingEnergyABPrime","reporting_declaration":"IChO2026Problems.T3A6.stackingEnergyABPrime_reported"}
theorem stackingEnergyABPrime_reported :
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyABPrime (-(278 : ℝ) / 5) ((1 : ℝ) / 10) := by
  unfold IChO2026Chem.Reporting.ReportsAtQuantum
  refine ⟨by norm_num, ⟨(-556 : ℤ), by norm_num⟩, ?_⟩
  norm_num [stackingEnergyABPrime, stackingEnergy, energyOfContacts,
    energiesOfGeometry, geometryOfArrangement, contactsOfArrangement,
    abContactObservation, slightlyShiftedEnergies]

/-- Combined semantic proposition for the three independently rounded outputs. -/
def ReportedResultSpec : Prop :=
  IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyAA (-(383 : ℝ) / 10) ((1 : ℝ) / 10) ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyAB (-(249 : ℝ) / 5) ((1 : ℝ) / 10) ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyABPrime (-(278 : ℝ) / 5) ((1 : ℝ) / 10)

/-- Payload-bound exact-result contract for the answer-blind raw record. -/
theorem raw_result_contract :
    ("7a81ec2db667f918f2e38141d40169a61eca33b7ab7fe10cff1416163ea17f95" : String) =
        "7a81ec2db667f918f2e38141d40169a61eca33b7ab7fe10cff1416163ea17f95" ∧
      RawResultSpec := by
  refine ⟨rfl, ?_⟩
  norm_num [RawResultSpec, stackingEnergyAA, stackingEnergyAB,
    stackingEnergyABPrime, stackingEnergy, energyOfContacts,
    energiesOfGeometry, geometryOfArrangement, contactsOfArrangement,
    aaContactObservation, abContactObservation, directlyRegisteredEnergies,
    slightlyShiftedEnergies]

/-- Payload-bound exact-result contract for the answer-blind reported record. -/
theorem reported_result_contract :
    ("3a7bb0ba20aa0dadd4bef52a4533535bf50adbaddd8687eeacf5d9e9c6b380d8" : String) =
        "3a7bb0ba20aa0dadd4bef52a4533535bf50adbaddd8687eeacf5d9e9c6b380d8" ∧
      ReportedResultSpec := by
  exact ⟨rfl, stackingEnergyAA_reported, stackingEnergyAB_reported,
    stackingEnergyABPrime_reported⟩

end
end T3A6
end IChO2026Problems
