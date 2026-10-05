import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026, problem T3-A6: aromatic stacking in COF-8

The source reports all interaction energies as numerical readouts in
`kJ mol⁻¹`, so they are represented by exact real numbers in that fixed unit.
The molecular drawing is represented by a finite aromatic-site inventory for
one repeat cell.  A stacking energy is then the sum over the contacts selected
by the stacking diagram; no non-aromatic site can occur in a contact.
-/

namespace IChO2026Problems.T3A6

noncomputable section

/-- The two aromatic ring classes distinguished by the supplied interaction
energy table. -/
inductive AromaticKind where
  | benzene
  | triazine
  deriving DecidableEq, Repr

/-- Aromatic sites in one smallest translation repeat of the depicted COF-8.
The E1 monomer contributes its benzene core.  D2 contributes its central
triazine and its three phenylene arms. -/
inductive COF8AromaticSite where
  | e1CoreBenzene
  | d2PhenyleneOne
  | d2PhenyleneTwo
  | d2PhenyleneThree
  | d2CoreTriazine
  deriving DecidableEq, Fintype, Repr

/-- Ring identity at each aromatic site in the depicted repeat cell. -/
def siteKind : COF8AromaticSite → AromaticKind
  | .e1CoreBenzene => .benzene
  | .d2PhenyleneOne => .benzene
  | .d2PhenyleneTwo => .benzene
  | .d2PhenyleneThree => .benzene
  | .d2CoreTriazine => .triazine

/-- The closed finite site domain comes directly from the molecular drawing. -/
def repeatAromaticSites : Finset COF8AromaticSite := Finset.univ

/-- Benzene sites in the depicted repeat cell. -/
def repeatBenzeneSites : Finset COF8AromaticSite :=
  repeatAromaticSites.filter fun site => siteKind site = .benzene

/-- Triazine sites in the depicted repeat cell. -/
def repeatTriazineSites : Finset COF8AromaticSite :=
  repeatAromaticSites.filter fun site => siteKind site = .triazine

/-- Nontrivial carrier for the aromatic-component count read from the COF-8
drawing on page 6. -/
def COF8RepeatCellSpec : Prop :=
  repeatAromaticSites.card = 5 ∧
    repeatBenzeneSites.card = 4 ∧
    repeatTriazineSites.card = 1

theorem cof8RepeatCell_from_problem_image : COF8RepeatCellSpec := by
  unfold COF8RepeatCellSpec repeatAromaticSites repeatBenzeneSites
    repeatTriazineSites siteKind
  native_decide

/-- The two relative ring geometries pictured in the columns of the supplied
interaction table. -/
inductive ContactGeometry where
  | eclipsed
  | slightlyShifted
  deriving DecidableEq, Repr

/-- The three unordered aromatic pair classes in the supplied table. -/
inductive AromaticPairClass where
  | benzeneBenzene
  | benzeneTriazine
  | triazineTriazine
  deriving DecidableEq, Repr

/-- Convert an ordered pair of ring identities into the corresponding
unordered table row. -/
def aromaticPairClass : AromaticKind → AromaticKind → AromaticPairClass
  | .benzene, .benzene => .benzeneBenzene
  | .benzene, .triazine => .benzeneTriazine
  | .triazine, .benzene => .benzeneTriazine
  | .triazine, .triazine => .triazineTriazine

/-- The six problem-stipulated pair energies, exactly as printed, in
`kJ mol⁻¹`. -/
def pairInteractionEnergy : ContactGeometry → AromaticPairClass → ℝ
  | .eclipsed, .benzeneBenzene => (-79 : ℝ) / 10
  | .eclipsed, .benzeneTriazine => (-498 : ℝ) / 10
  | .eclipsed, .triazineTriazine => (-67 : ℝ) / 10
  | .slightlyShifted, .benzeneBenzene => (-126 : ℝ) / 10
  | .slightlyShifted, .benzeneTriazine => (-556 : ℝ) / 10
  | .slightlyShifted, .triazineTriazine => (-167 : ℝ) / 10

/-- Source-to-Lean bridge for every numerical cell in the pair-energy table. -/
def PrintedPairEnergyTableSpec : Prop :=
  pairInteractionEnergy .eclipsed .benzeneBenzene = (-79 : ℝ) / 10 ∧
    pairInteractionEnergy .eclipsed .benzeneTriazine = (-498 : ℝ) / 10 ∧
    pairInteractionEnergy .eclipsed .triazineTriazine = (-67 : ℝ) / 10 ∧
    pairInteractionEnergy .slightlyShifted .benzeneBenzene = (-126 : ℝ) / 10 ∧
    pairInteractionEnergy .slightlyShifted .benzeneTriazine = (-556 : ℝ) / 10 ∧
    pairInteractionEnergy .slightlyShifted .triazineTriazine = (-167 : ℝ) / 10

theorem printedPairEnergyTable_from_problem_image : PrintedPairEnergyTableSpec := by
  norm_num [PrintedPairEnergyTableSpec, pairInteractionEnergy]

/-- One π-π contact between an aromatic site in the lower repeat and an
aromatic site in the upper repeat. -/
structure AromaticContact where
  lowerSite : COF8AromaticSite
  upperSite : COF8AromaticSite
  deriving DecidableEq, Repr

/-- Like-for-like contacts in the eclipsed AA diagram. -/
def aaContacts : List AromaticContact :=
  [ ⟨.e1CoreBenzene, .e1CoreBenzene⟩,
    ⟨.d2PhenyleneOne, .d2PhenyleneOne⟩,
    ⟨.d2PhenyleneTwo, .d2PhenyleneTwo⟩,
    ⟨.d2PhenyleneThree, .d2PhenyleneThree⟩,
    ⟨.d2CoreTriazine, .d2CoreTriazine⟩ ]

/-- The single occupied aromatic overlap per primitive cell in the depicted
AB translation: an E1 benzene in one layer lies over a D2 triazine in the
other, while the other aromatic sites lie over pores or non-aromatic parts. -/
def abContacts : List AromaticContact :=
  [⟨.e1CoreBenzene, .d2CoreTriazine⟩]

/-- The four modes needed to use the supplied AA′ calibration and answer the
three requested cases.  A prime preserves the contact identity and selects the
slightly shifted column of the table. -/
inductive StackingMode where
  | aa
  | aaPrime
  | ab
  | abPrime
  deriving DecidableEq, Repr

/-- Aromatic contacts selected by each stacking-mode diagram. -/
def modeContacts : StackingMode → List AromaticContact
  | .aa => aaContacts
  | .aaPrime => aaContacts
  | .ab => abContacts
  | .abPrime => abContacts

/-- Pair geometry selected by the presence or absence of a prime. -/
def modeGeometry : StackingMode → ContactGeometry
  | .aa => .eclipsed
  | .aaPrime => .slightlyShifted
  | .ab => .eclipsed
  | .abPrime => .slightlyShifted

/-- Table row selected by a contact. -/
def contactPairClass (contact : AromaticContact) : AromaticPairClass :=
  aromaticPairClass (siteKind contact.lowerSite) (siteKind contact.upperSite)

/-- Number of contacts of a given pair class in one bilayer repeat. -/
def contactCount (mode : StackingMode) (pairClass : AromaticPairClass) : ℕ :=
  ((modeContacts mode).filter fun contact => contactPairClass contact = pairClass).length

/-- Explicit contact-count ledger read from the AA/AA′/AB diagrams and the
meaning of the prime marker. -/
def ContactInventorySpec : Prop :=
  contactCount .aa .benzeneBenzene = 4 ∧
    contactCount .aa .benzeneTriazine = 0 ∧
    contactCount .aa .triazineTriazine = 1 ∧
    contactCount .aaPrime .benzeneBenzene = 4 ∧
    contactCount .aaPrime .benzeneTriazine = 0 ∧
    contactCount .aaPrime .triazineTriazine = 1 ∧
    contactCount .ab .benzeneBenzene = 0 ∧
    contactCount .ab .benzeneTriazine = 1 ∧
    contactCount .ab .triazineTriazine = 0 ∧
    contactCount .abPrime .benzeneBenzene = 0 ∧
    contactCount .abPrime .benzeneTriazine = 1 ∧
    contactCount .abPrime .triazineTriazine = 0

/-- The source assumption that π-π stacking occurs only between aromatic units
is enforced by the typed contact domain; this proposition also records that no
contact points outside the depicted repeat-cell site inventory are admitted. -/
def OnlyAromaticContactsSpec : Prop :=
  ∀ mode contact,
    contact ∈ modeContacts mode →
      contact.lowerSite ∈ repeatAromaticSites ∧
      contact.upperSite ∈ repeatAromaticSites

theorem contactInventory_from_problem_images :
    ContactInventorySpec ∧ OnlyAromaticContactsSpec := by
  constructor
  · unfold ContactInventorySpec contactCount modeContacts aaContacts abContacts
      contactPairClass aromaticPairClass siteKind
    native_decide
  · intro mode contact _
    exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩

/-- Add the pairwise π-π energies for exactly the aromatic contacts selected by
a stacking mode.  The result is in `kJ mol⁻¹` per bilayer repeat. -/
def stackingEnergy (mode : StackingMode) : ℝ :=
  ((modeContacts mode).map fun contact =>
    pairInteractionEnergy (modeGeometry mode) (contactPairClass contact)).sum

/-- Raw requested AA energy, kept as the complete contact sum. -/
def stackingEnergyAA : ℝ := stackingEnergy .aa

/-- Raw requested AB energy, kept as the complete contact sum. -/
def stackingEnergyAB : ℝ := stackingEnergy .ab

/-- Raw requested AB′ energy, kept as the complete contact sum. -/
def stackingEnergyABPrime : ℝ := stackingEnergy .abPrime

/-- The independently printed AA′ aggregate is a calibration check on the
repeat-cell count and the shifted-column interpretation. -/
def AAPrimeCalibrationSpec : Prop :=
  stackingEnergy .aaPrime = (-671 : ℝ) / 10

theorem aaPrimeCalibration_from_problem_text : AAPrimeCalibrationSpec := by
  norm_num [AAPrimeCalibrationSpec, stackingEnergy, modeContacts, aaContacts,
    modeGeometry, contactPairClass, aromaticPairClass, siteKind,
    pairInteractionEnergy]

/-- End-to-end raw specification for all three requested outputs.  Each result
is first tied to the contact ledger and the appropriate source table cells,
then evaluated exactly without intermediate rounding. -/
def RawResultSpec : Prop :=
  COF8RepeatCellSpec ∧
    PrintedPairEnergyTableSpec ∧
    ContactInventorySpec ∧
    OnlyAromaticContactsSpec ∧
    AAPrimeCalibrationSpec ∧
    stackingEnergyAA =
      4 * pairInteractionEnergy .eclipsed .benzeneBenzene +
        pairInteractionEnergy .eclipsed .triazineTriazine ∧
    stackingEnergyAB = pairInteractionEnergy .eclipsed .benzeneTriazine ∧
    stackingEnergyABPrime =
      pairInteractionEnergy .slightlyShifted .benzeneTriazine ∧
    stackingEnergyAA = (-383 : ℝ) / 10 ∧
    stackingEnergyAB = (-249 : ℝ) / 5 ∧
    stackingEnergyABPrime = (-278 : ℝ) / 5

theorem rawStackingEnergies : RawResultSpec := by
  refine ⟨cof8RepeatCell_from_problem_image,
    printedPairEnergyTable_from_problem_image,
    contactInventory_from_problem_images.1,
    contactInventory_from_problem_images.2,
    aaPrimeCalibration_from_problem_text, ?_⟩
  norm_num [stackingEnergyAA, stackingEnergyAB, stackingEnergyABPrime,
    stackingEnergy, modeContacts, aaContacts, abContacts, modeGeometry,
    contactPairClass, aromaticPairClass, siteKind, pairInteractionEnergy]

/-- At magnitudes from 10 (inclusive) to 100 (exclusive), reporting to three
significant figures has quantum `0.1`. -/
def ThreeSignificantFiguresAtTensScale (raw quantum : ℝ) : Prop :=
  10 ≤ |raw| ∧ |raw| < 100 ∧ quantum = (1 : ℝ) / 10

/-- Final reporting specification.  The three significant-figure policy is
stated for each raw value, and each displayed value is checked with the shared
nearest-quantum, ties-away-from-zero relation. -/
def ReportedResultSpec : Prop :=
  stackingEnergyAA = (-383 : ℝ) / 10 ∧
    ThreeSignificantFiguresAtTensScale stackingEnergyAA ((1 : ℝ) / 10) ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyAA ((-383 : ℝ) / 10) ((1 : ℝ) / 10) ∧
    stackingEnergyAB = (-249 : ℝ) / 5 ∧
    ThreeSignificantFiguresAtTensScale stackingEnergyAB ((1 : ℝ) / 10) ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyAB ((-498 : ℝ) / 10) ((1 : ℝ) / 10) ∧
    stackingEnergyABPrime = (-278 : ℝ) / 5 ∧
    ThreeSignificantFiguresAtTensScale stackingEnergyABPrime ((1 : ℝ) / 10) ∧
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyABPrime ((-556 : ℝ) / 10) ((1 : ℝ) / 10)

/-- Machine-checked three-significant-figure report for the requested AA
energy. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"stacking_energy_aa","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"-38.3","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T3A6.stackingEnergyAA","reporting_declaration":"IChO2026Problems.T3A6.stackingEnergyAA_reportsAtThreeSignificantFigures"}
theorem stackingEnergyAA_reportsAtThreeSignificantFigures :
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyAA ((-383 : ℝ) / 10) ((1 : ℝ) / 10) := by
  norm_num [IChO2026Chem.Reporting.ReportsAtQuantum, stackingEnergyAA,
    stackingEnergy, modeContacts, aaContacts, modeGeometry, contactPairClass,
    aromaticPairClass, siteKind, pairInteractionEnergy]
  exact ⟨-383, by norm_num⟩

/-- Machine-checked three-significant-figure report for the requested AB
energy. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"stacking_energy_ab","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"-49.8","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T3A6.stackingEnergyAB","reporting_declaration":"IChO2026Problems.T3A6.stackingEnergyAB_reportsAtThreeSignificantFigures"}
theorem stackingEnergyAB_reportsAtThreeSignificantFigures :
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyAB ((-249 : ℝ) / 5) ((1 : ℝ) / 10) := by
  norm_num [IChO2026Chem.Reporting.ReportsAtQuantum, stackingEnergyAB,
    stackingEnergy, modeContacts, abContacts, modeGeometry, contactPairClass,
    aromaticPairClass, siteKind, pairInteractionEnergy]
  exact ⟨-498, by norm_num⟩

/-- Machine-checked three-significant-figure report for the requested AB′
energy. -/
-- archon:numeric-reporting-certificate {"schema_version":1,"output_id":"stacking_energy_ab_prime","reporting_policy_kind":"significant_figures","reporting_policy_digits":3,"reported_value":"-55.6","reporting_quantum":"0.1","raw_declaration":"IChO2026Problems.T3A6.stackingEnergyABPrime","reporting_declaration":"IChO2026Problems.T3A6.stackingEnergyABPrime_reportsAtThreeSignificantFigures"}
theorem stackingEnergyABPrime_reportsAtThreeSignificantFigures :
    IChO2026Chem.Reporting.ReportsAtQuantum
      stackingEnergyABPrime ((-278 : ℝ) / 5) ((1 : ℝ) / 10) := by
  norm_num [IChO2026Chem.Reporting.ReportsAtQuantum, stackingEnergyABPrime,
    stackingEnergy, modeContacts, abContacts, modeGeometry, contactPairClass,
    aromaticPairClass, siteKind, pairInteractionEnergy]
  exact ⟨-556, by norm_num⟩

theorem reportedStackingEnergies : ReportedResultSpec := by
  norm_num [ReportedResultSpec, ThreeSignificantFiguresAtTensScale,
    IChO2026Chem.Reporting.ReportsAtQuantum, stackingEnergyAA,
    stackingEnergyAB, stackingEnergyABPrime, stackingEnergy, modeContacts,
    aaContacts, abContacts, modeGeometry, contactPairClass,
    aromaticPairClass, siteKind, pairInteractionEnergy]
  exact ⟨⟨-383, by norm_num⟩,
    ⟨⟨-498, by norm_num⟩, ⟨-556, by norm_num⟩⟩⟩

/-- Payload-bound raw solve-phase result contract. -/
theorem rawResultContract :
    ("990f4d632701be862b511231741bf2a47f9ee4062f4979ccf86c20417d0f1c31" : String) =
        "990f4d632701be862b511231741bf2a47f9ee4062f4979ccf86c20417d0f1c31" ∧
      IChO2026Problems.T3A6.RawResultSpec := by
  exact ⟨rfl, rawStackingEnergies⟩

/-- Payload-bound reported solve-phase result contract. -/
theorem reportedResultContract :
    ("2206063e8e0c08b7304693e1c0dddc8c37d29540bad0232218230e2612273c92" : String) =
        "2206063e8e0c08b7304693e1c0dddc8c37d29540bad0232218230e2612273c92" ∧
      IChO2026Problems.T3A6.ReportedResultSpec := by
  exact ⟨rfl, reportedStackingEnergies⟩

end

end IChO2026Problems.T3A6
