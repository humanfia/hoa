import Mathlib
import IChO2026Chem.Reporting

/-!
# IChO 2026 T7-A5: a dinitrogen-bridged dimolybdenum complex

The problem permits the PNP pincer ligand to be drawn by its simplified symbol.
Accordingly, the molecular graph below makes the three donor atoms of each PNP
ligand explicit and records the source-specified ligand template separately.  It
also makes every atom and bond of all five dinitrogen ligands explicit.

The chemistry used to select the graph is kept separate from the graph itself:

* three-electron reduction of neutral `MoCl₃(PNP)` gives neutral Mo(0) after
  loss of three chlorides as NaCl;
* neutral PNP donates six electrons and each end-on N₂ contact donates two,
  so an 18-electron Mo(0) center has three N₂ contacts;
* the gas datum gives the smallest whole-molecule stoichiometry 2 precursor :
  5 N₂.  Two centers with three contacts each and five intact N₂ units can
  therefore have only one shared N₂, leaving two terminal N₂ units at each
  metal.
-/

namespace IChO2026Problems.T7A5

open IChO2026Chem.Reporting

noncomputable section

/-! ## Source-grounded numerical clue -/

/-- Molar mass of precursor 4, in g mol⁻¹, as printed in the scheme. -/
def molarMass4 : ℝ := 597824 / 1000

/-- The printed mass of precursor 4, in grams. -/
def precursorMass : ℝ := 1

/-- A conventional ideal-gas constant in L bar mol⁻¹ K⁻¹. -/
def gasConstant : ℝ := 8314 / 100000

/-- Temperature and pressure printed beside the gas-uptake datum. -/
def sourceTemperature : ℝ := 27315 / 100
def sourcePressure : ℝ := 1

/-- Volume predicted if two molecules of 4 bind five molecules of N₂. -/
def predictedVolumeCm3 : ℝ :=
  (5 / 2) * (precursorMass / molarMass4) * gasConstant *
    sourceTemperature / sourcePressure * 1000

/-- N₂ molecules per precursor molecule inferred from the printed central
values using `PV = nRT`. -/
def sourceMoleRatio : ℝ :=
  ((sourcePressure * ((9497 / 100) / 1000)) /
      (gasConstant * sourceTemperature)) /
    (precursorMass / molarMass4)

/-- The unrounded central-value ratio is 2.500049..., within 0.0001 of 5/2. -/
theorem source_mole_ratio_near_five_halves :
    |sourceMoleRatio - 5 / 2| < 1 / 10000 := by
  norm_num [sourceMoleRatio, precursorMass, molarMass4, gasConstant,
    sourceTemperature, sourcePressure, abs_of_nonneg]

/-- The 5 : 2 stoichiometry predicts 94.968... cm³.  With no intermediate
rounding it reports as the source value 94.97 cm³ at the source's 0.01 cm³
display quantum. -/
theorem five_n2_for_two_precursors_matches_gas_datum :
    ReportsAtQuantum predictedVolumeCm3 (9497 / 100) (1 / 100) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · refine ⟨9497, by norm_num⟩
  · norm_num [predictedVolumeCm3, precursorMass, molarMass4, gasConstant,
      sourceTemperature, sourcePressure]

/-- The same calculation explicitly satisfies the closed half-quantum
measurement interval around 94.97 cm³. -/
theorem five_n2_for_two_precursors_in_measurement_interval :
    ConsistentMeasurement predictedVolumeCm3 (9497 / 100) (1 / 100) := by
  norm_num [ConsistentMeasurement, predictedVolumeCm3, precursorMass,
    molarMass4, gasConstant, sourceTemperature, sourcePressure, abs_of_nonpos]

/-- The whole-number coefficients selected by the clue are already reduced. -/
theorem two_to_five_is_primitive : Nat.Coprime 2 5 := by decide

/-! ## Ligand template permitted by the problem's simplified notation -/

inductive Element where
  | molybdenum
  | nitrogen
  | phosphorus
deriving DecidableEq, Repr

inductive Linker where
  | methylene
deriving DecidableEq, Repr

inductive Substituent where
  | tertButyl
deriving DecidableEq, Repr

/-- Source figure's expansion of the simplified PNP symbol:
2,6-bis[(di-tert-butylphosphino)methyl]pyridine. -/
structure PNPTemplate where
  centralDonor : Element
  phosphorusDonors : Nat
  linker : Linker
  pyridineAttachmentPositions : Nat × Nat
  substituent : Substituent
  substituentsPerPhosphorus : Nat
  netCharge : ℤ
  radicalElectrons : Nat
  stereocentres : Nat
deriving DecidableEq, Repr

def sourcePNPTemplate : PNPTemplate where
  centralDonor := .nitrogen
  phosphorusDonors := 2
  linker := .methylene
  pyridineAttachmentPositions := (2, 6)
  substituent := .tertButyl
  substituentsPerPhosphorus := 2
  netCharge := 0
  radicalElectrons := 0
  stereocentres := 0

theorem source_pnp_template_fields :
    sourcePNPTemplate.centralDonor = .nitrogen ∧
    sourcePNPTemplate.phosphorusDonors = 2 ∧
    sourcePNPTemplate.linker = .methylene ∧
    sourcePNPTemplate.pyridineAttachmentPositions = (2, 6) ∧
    sourcePNPTemplate.substituent = .tertButyl ∧
    sourcePNPTemplate.substituentsPerPhosphorus = 2 ∧
    sourcePNPTemplate.netCharge = 0 ∧
    sourcePNPTemplate.radicalElectrons = 0 ∧
    sourcePNPTemplate.stereocentres = 0 := by
  decide

/-! ## Deriving the terminal/bridging topology -/

/-- Charge/electron bookkeeping read from neutral `MoCl₃(PNP)` and the
source's three equivalents of sodium amalgam per precursor unit. -/
def precursorMoOxidationState : ℤ := 3
def reducingElectronsPerMo : ℤ := 3

theorem three_electron_reduction_gives_mo_zero :
    precursorMoOxidationState - reducingElectronsPerMo = 0 := by
  norm_num [precursorMoOxidationState, reducingElectronsPerMo]

/-- Neutral-atom electron count at reduced Mo(0): six metal electrons plus
six from neutral tridentate PNP plus two for each end-on N₂ contact. -/
def moElectronCount (n2Contacts : ℕ) : ℕ := 6 + 6 + 2 * n2Contacts

theorem three_n2_contacts_of_eighteen_electron_mo
    (n2Contacts : ℕ) (h18 : moElectronCount n2Contacts = 18) :
    n2Contacts = 3 := by
  simp [moElectronCount] at h18
  omega

/-- For two Mo centers and five intact N₂ units, the 18-electron contact
counts force exactly one bridging N₂ and two terminal N₂ ligands per Mo. -/
theorem binding_topology_unique
    (terminalLeft terminalRight bridging : ℕ)
    (hLeft18 : moElectronCount (terminalLeft + bridging) = 18)
    (hRight18 : moElectronCount (terminalRight + bridging) = 18)
    (hFive : terminalLeft + terminalRight + bridging = 5) :
    terminalLeft = 2 ∧ terminalRight = 2 ∧ bridging = 1 := by
  have hLeft : terminalLeft + bridging = 3 :=
    three_n2_contacts_of_eighteen_electron_mo _ hLeft18
  have hRight : terminalRight + bridging = 3 :=
    three_n2_contacts_of_eighteen_electron_mo _ hRight18
  omega

/-! ## Explicit molecular graph of 5 -/

inductive Side where
  | left
  | right
deriving DecidableEq, Fintype, Repr

def Side.other : Side → Side
  | .left => .right
  | .right => .left

inductive AxialSlot where
  | upper
  | lower
deriving DecidableEq, Fintype, Repr

/-- Atom identifiers in the simplified structure.  `pnpP` and `pnpN` are the
three donor atoms of one ligand symbol; `terminalNear`/`terminalFar` are the
two atoms of each terminal N₂; the two `bridgeN` atoms form μ-N₂. -/
inductive Atom where
  | mo (side : Side)
  | pnpP (side : Side) (slot : AxialSlot)
  | pnpN (side : Side)
  | terminalNear (side : Side) (slot : AxialSlot)
  | terminalFar (side : Side) (slot : AxialSlot)
  | bridgeN (side : Side)
deriving DecidableEq, Fintype, Repr

inductive BondOrder where
  | coordinate
  | triple
deriving DecidableEq, Repr

inductive DinitrogenUnit where
  | terminal (side : Side) (slot : AxialSlot)
  | bridge
deriving DecidableEq, Fintype, Repr

def atomElement : Atom → Element
  | .mo _ => .molybdenum
  | .pnpP _ _ => .phosphorus
  | .pnpN _ => .nitrogen
  | .terminalNear _ _ => .nitrogen
  | .terminalFar _ _ => .nitrogen
  | .bridgeN _ => .nitrogen

def elementCount (e : Element) : ℕ :=
  (Finset.univ.filter fun a : Atom => atomElement a = e).card

private def coordinateIfSameSide (s t : Side) : Option BondOrder :=
  if s = t then some .coordinate else none

private def tripleIfSameUnit
    (s t : Side) (i j : AxialSlot) : Option BondOrder :=
  if s = t ∧ i = j then some .triple else none

/-- Complete bond table for the simplified graph.  All metal-ligand bonds are
coordinate bonds and every intact N₂ unit retains an N≡N triple bond. -/
def bondOrder : Atom → Atom → Option BondOrder
  | .mo s, .pnpP t _ => coordinateIfSameSide s t
  | .pnpP t _, .mo s => coordinateIfSameSide s t
  | .mo s, .pnpN t => coordinateIfSameSide s t
  | .pnpN t, .mo s => coordinateIfSameSide s t
  | .mo s, .terminalNear t _ => coordinateIfSameSide s t
  | .terminalNear t _, .mo s => coordinateIfSameSide s t
  | .mo s, .bridgeN t => coordinateIfSameSide s t
  | .bridgeN t, .mo s => coordinateIfSameSide s t
  | .terminalNear s i, .terminalFar t j => tripleIfSameUnit s t i j
  | .terminalFar t j, .terminalNear s i => tripleIfSameUnit s t i j
  | .bridgeN .left, .bridgeN .right => some .triple
  | .bridgeN .right, .bridgeN .left => some .triple
  | _, _ => none

/-- Each displayed P, N, P donor is grouped into the corresponding single PNP
ligand symbol. -/
def pnpLigandMembership : Atom → Option Side
  | .pnpP s _ => some s
  | .pnpN s => some s
  | _ => none

def n2Atoms : DinitrogenUnit → Atom × Atom
  | .terminal s i => (.terminalNear s i, .terminalFar s i)
  | .bridge => (.bridgeN .left, .bridgeN .right)

/-- Which atom of an N₂ unit, if any, contacts a selected metal center. -/
def contactAtom : DinitrogenUnit → Side → Option Atom
  | .terminal t i, s => if t = s then some (.terminalNear t i) else none
  | .bridge, s => some (.bridgeN s)

def boundTo (u : DinitrogenUnit) (s : Side) : Bool :=
  match contactAtom u s with
  | none => false
  | some a => bondOrder (.mo s) a = some .coordinate

def n2ContactCount (s : Side) : ℕ :=
  (Finset.univ.filter fun u : DinitrogenUnit => boundTo u s).card

def bridgingN2Count : ℕ :=
  (Finset.univ.filter fun u : DinitrogenUnit =>
    boundTo u .left ∧ boundTo u .right).card

def terminalN2Count (s : Side) : ℕ :=
  (Finset.univ.filter fun u : DinitrogenUnit =>
    boundTo u s ∧ ¬ boundTo u s.other).card

/-- Octahedral trans pairs: P trans P, pyridine-N trans bridging-N₂, and the
two terminal N₂ donors mutually trans.  This records the coordination
geometry that accompanies the connectivity. -/
def transAt : Atom → Atom → Atom → Prop
  | .mo s, .pnpP t .upper, .pnpP u .lower => s = t ∧ s = u
  | .mo s, .pnpP t .lower, .pnpP u .upper => s = t ∧ s = u
  | .mo s, .pnpN t, .bridgeN u => s = t ∧ s = u
  | .mo s, .bridgeN u, .pnpN t => s = t ∧ s = u
  | .mo s, .terminalNear t .upper, .terminalNear u .lower => s = t ∧ s = u
  | .mo s, .terminalNear t .lower, .terminalNear u .upper => s = t ∧ s = u
  | _, _, _ => False

structure MolecularStructure where
  element : Atom → Element
  bond : Atom → Atom → Option BondOrder
  formalCharge : Atom → ℤ
  radicalElectrons : Atom → ℕ
  stereocentre : Atom → Bool
  oxidationState : Side → ℤ
  trans : Atom → Atom → Atom → Prop

/-- Structure 5: `[(PNP)Mo(N₂)₂]₂(μ-N₂)`. -/
def structure5 : MolecularStructure where
  element := atomElement
  bond := bondOrder
  formalCharge := fun _ => 0
  radicalElectrons := fun _ => 0
  stereocentre := fun _ => false
  oxidationState := fun _ => 0
  trans := transAt

theorem bond_order_symmetric (a b : Atom) :
    structure5.bond a b = structure5.bond b a := by
  cases a <;> cases b <;>
    simp [structure5, bondOrder, coordinateIfSameSide, tripleIfSameUnit,
      and_comm, eq_comm] <;>
    rename_i s t <;> cases s <;> cases t <;> rfl

theorem no_atom_bonded_to_itself (a : Atom) :
    structure5.bond a a = none := by
  cases a <;> simp [structure5, bondOrder]

theorem every_n2_has_triple_bond (u : DinitrogenUnit) :
    structure5.bond (n2Atoms u).1 (n2Atoms u).2 = some .triple := by
  cases u with
  | terminal s i => cases s <;> cases i <;> rfl
  | bridge => rfl

theorem graph_has_five_intact_n2_units :
    Fintype.card DinitrogenUnit = 5 := by decide

theorem graph_has_two_molybdenum_centres : Fintype.card Side = 2 := by decide

theorem simplified_graph_element_counts :
    elementCount .molybdenum = 2 ∧
    elementCount .phosphorus = 4 ∧
    elementCount .nitrogen = 12 := by
  decide

theorem graph_n2_binding_counts :
    n2ContactCount .left = 3 ∧
    n2ContactCount .right = 3 ∧
    terminalN2Count .left = 2 ∧
    terminalN2Count .right = 2 ∧
    bridgingN2Count = 1 := by
  decide

theorem each_molybdenum_is_eighteen_electron (s : Side) :
    moElectronCount (n2ContactCount s) = 18 := by
  cases s <;> decide

theorem product_is_neutral_closed_shell_mo_zero :
    (∀ a, structure5.formalCharge a = 0) ∧
    (∀ a, structure5.radicalElectrons a = 0) ∧
    (∀ a, structure5.stereocentre a = false) ∧
    (∀ s, structure5.oxidationState s = 0) := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem pnp_is_tridentate (s : Side) :
    pnpLigandMembership (.pnpP s .upper) = some s ∧
    pnpLigandMembership (.pnpN s) = some s ∧
    pnpLigandMembership (.pnpP s .lower) = some s ∧
    structure5.bond (.mo s) (.pnpP s .upper) = some .coordinate ∧
    structure5.bond (.mo s) (.pnpN s) = some .coordinate ∧
    structure5.bond (.mo s) (.pnpP s .lower) = some .coordinate := by
  cases s <;> decide

theorem coordination_geometry (s : Side) :
    structure5.trans (.mo s) (.pnpP s .upper) (.pnpP s .lower) ∧
    structure5.trans (.mo s) (.pnpN s) (.bridgeN s) ∧
    structure5.trans (.mo s) (.terminalNear s .upper)
      (.terminalNear s .lower) := by
  cases s <;> exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Final requested output: the explicit graph realizes the topology uniquely
derived from two 18-electron Mo centers and five N₂ units. -/
theorem structure_5_is_dinitrogen_bridged_dimolybdenum :
    terminalN2Count .left = 2 ∧
    terminalN2Count .right = 2 ∧
    bridgingN2Count = 1 ∧
    Fintype.card DinitrogenUnit = 5 ∧
    (∀ u, structure5.bond (n2Atoms u).1 (n2Atoms u).2 = some .triple) ∧
    (∀ a, structure5.formalCharge a = 0) ∧
    (∀ a, structure5.radicalElectrons a = 0) ∧
    (∀ a, structure5.stereocentre a = false) := by
  rcases graph_n2_binding_counts with ⟨_, _, htl, htr, hb⟩
  exact ⟨htl, htr, hb, graph_has_five_intact_n2_units,
    every_n2_has_triple_bond, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

#print axioms five_n2_for_two_precursors_matches_gas_datum
#print axioms binding_topology_unique
#print axioms structure_5_is_dinitrogen_bridged_dimolybdenum

end

end IChO2026Problems.T7A5
