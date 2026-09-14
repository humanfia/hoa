import Mathlib

/-!
# IChO 2026, theory problem 8.4

This file reconstructs complexes 9--15 from the reaction arrows on Q8-2 and
the five fields printed on the blank answer sheets A8-3/A8-4.  Ligand 8 is
kept as the tetradentate N4 cartoon requested by the question.  Every other
atom and covalent bond is represented by a small molecular graph, while
`BoundFragment.donorSites` records every Fe--donor bond.

The electron count is the standard ionic count: Fe contributes `8 - OS`
electrons and every donor atom contributes one two-electron pair.
-/

namespace IChO2026Problems.T8A4

/-! ## Explicit graphs for the non-cartoon fragments -/

inductive Element where
  | H | C | N | O | Cl | Fe
  deriving DecidableEq, Repr

inductive BondOrder where
  | single | double | triple
  deriving DecidableEq, Repr

/-- `formalCharge` and `radicalElectrons` make the Lewis information explicit.
The atom indices used by bonds are positions in a fragment's atom list. -/
structure Atom where
  element : Element
  formalCharge : Int
  radicalElectrons : Nat
  deriving DecidableEq, Repr

structure CovalentBond where
  left : Nat
  right : Nat
  order : BondOrder
  deriving DecidableEq, Repr

structure FragmentGraph where
  atoms : List Atom
  bonds : List CovalentBond
  /-- Atom indices that bind Fe, in the same order as the occupied sites. -/
  metalDonors : List Nat
  /-- Ionic ligand charge used for assigning the Fe oxidation state. -/
  ionicCharge : Int
  /-- No stereocentre is hidden: all indices would be listed here. -/
  stereocentres : List Nat
  deriving DecidableEq, Repr

def atom (e : Element) (q : Int := 0) (radicals : Nat := 0) : Atom :=
  { element := e, formalCharge := q, radicalElectrons := radicals }

def bond (a b : Nat) (o : BondOrder) : CovalentBond :=
  { left := a, right := b, order := o }

inductive Fragment where
  | chloride
  | aqua
  /-- κ²-C,O-CO₂²⁻, with Fe bound to C and to the singly bonded O. -/
  | activatedCO2
  /-- C-bound hydroxycarbonyl, Fe-C(=O)-OH⁻. -/
  | hydroxycarbonyl
  /-- C-bound carbon monoxide. -/
  | carbonyl
  deriving DecidableEq, Repr

/-- The atom order in each graph is documented by the adjacent comments.
Formal charges are an ionic Lewis bookkeeping form; their sum equals the
fragment's ionic charge. -/
def fragmentGraph : Fragment → FragmentGraph
  | .chloride =>
      { atoms := [atom .Cl (-1)]                         -- Cl
        bonds := []
        metalDonors := [0]
        ionicCharge := -1
        stereocentres := [] }
  | .aqua =>
      { atoms := [atom .O, atom .H, atom .H]             -- O, H, H
        bonds := [bond 0 1 .single, bond 0 2 .single]    -- H-O-H
        metalDonors := [0]
        ionicCharge := 0
        stereocentres := [] }
  | .activatedCO2 =>
      { atoms := [atom .C (-1), atom .O, atom .O (-1)]  -- C, O(=), O(-)
        bonds := [bond 0 1 .double, bond 0 2 .single]    -- O=C-O
        metalDonors := [0, 2]                            -- Fe-C and Fe-O
        ionicCharge := -2
        stereocentres := [] }
  | .hydroxycarbonyl =>
      { atoms := [atom .C (-1), atom .O, atom .O, atom .H]
        bonds := [bond 0 1 .double, bond 0 2 .single,
          bond 2 3 .single]                              -- Fe-C(=O)-O-H
        metalDonors := [0]
        ionicCharge := -1
        stereocentres := [] }
  | .carbonyl =>
      { atoms := [atom .C (-1), atom .O 1]               -- C⁻≡O⁺
        bonds := [bond 0 1 .triple]
        metalDonors := [0]                               -- Fe-C≡O
        ionicCharge := 0
        stereocentres := [] }

def graphFormalCharge (g : FragmentGraph) : Int :=
  (g.atoms.map (·.formalCharge)).sum

def FragmentGraph.wellFormed (g : FragmentGraph) : Bool :=
  (g.bonds.all fun b =>
      decide (b.left < g.atoms.length ∧ b.right < g.atoms.length)) &&
  (g.metalDonors.all fun i => decide (i < g.atoms.length)) &&
  (g.stereocentres.all fun i => decide (i < g.atoms.length)) &&
  decide g.metalDonors.Nodup && decide g.stereocentres.Nodup &&
  decide (graphFormalCharge g = g.ionicCharge)

/-- All five fragment drawings have valid atom indices, explicit charges, no
omitted stereocentres, and the stated ionic charge. -/
theorem all_fragment_graphs_wellFormed (f : Fragment) :
    (fragmentGraph f).wellFormed = true := by
  cases f <;> decide

/-! ## The N4 cartoon and the cis pair of labile sites -/

inductive CoordinationSite where
  | xPlus | xMinus | yPlus | yMinus | zPlus | zMinus
  deriving DecidableEq, Repr

def opposite : CoordinationSite → CoordinationSite
  | .xPlus => .xMinus
  | .xMinus => .xPlus
  | .yPlus => .yMinus
  | .yMinus => .yPlus
  | .zPlus => .zMinus
  | .zMinus => .zPlus

def areCis (a b : CoordinationSite) : Bool :=
  a != b && opposite a != b

structure CartoonLigand where
  donorAtoms : List Atom
  donorSites : List CoordinationSite
  ionicCharge : Int
  radicalElectrons : Nat
  stereocentres : List Nat
  deriving DecidableEq, Repr

/-- Ligand 8 exactly at the resolution mandated by the question: a neutral
tetradentate N4 cartoon.  Absolute octahedral axis names are arbitrary; they
record that the two sites not occupied by 8 are cis. -/
def ligand8 : CartoonLigand :=
  { donorAtoms := [atom .N, atom .N, atom .N, atom .N]
    donorSites := [.xPlus, .xMinus, .yMinus, .zMinus]
    ionicCharge := 0
    radicalElectrons := 0
    stereocentres := [] }

def labileA : CoordinationSite := .yPlus
def labileB : CoordinationSite := .zPlus

theorem ligand8_has_four_nitrogen_donors :
    ligand8.donorAtoms = [atom .N, atom .N, atom .N, atom .N] ∧
    ligand8.donorSites.length = 4 ∧ ligand8.ionicCharge = 0 ∧
    ligand8.radicalElectrons = 0 ∧ ligand8.stereocentres = [] := by
  decide

theorem labile_sites_are_cis : areCis labileA labileB = true := by
  decide

/-! ## Source-arrow data and deterministic reconstruction -/

structure BoundFragment where
  kind : Fragment
  /-- Each entry is paired with the corresponding entry of `metalDonors`. -/
  donorSites : List CoordinationSite
  deriving DecidableEq, Repr

def mono (f : Fragment) (s : CoordinationSite) : BoundFragment :=
  { kind := f, donorSites := [s] }

def activatedCO2AtCisSites : BoundFragment :=
  { kind := .activatedCO2, donorSites := [labileA, labileB] }

structure Complex where
  metal : Element
  coligands : List BoundFragment
  totalCharge : Int
  deriving DecidableEq, Repr

/-- Positive entries are consumed by the arrow; negative entries are
produced.  These are literal transcriptions of the labels in Q8-2. -/
structure Stoich where
  electron : Int := 0
  proton : Int := 0
  water : Int := 0
  chloride : Int := 0
  carbonDioxide : Int := 0
  carbonMonoxide : Int := 0
  deriving DecidableEq, Repr

instance : Add Stoich where
  add a b :=
    { electron := a.electron + b.electron
      proton := a.proton + b.proton
      water := a.water + b.water
      chloride := a.chloride + b.chloride
      carbonDioxide := a.carbonDioxide + b.carbonDioxide
      carbonMonoxide := a.carbonMonoxide + b.carbonMonoxide }

instance : Zero Stoich := ⟨{}⟩

inductive Step where
  | aquatePrecursor
  | photoReduceLoseWater
  | captureCO2LoseWater
  | photoReduceProtonate
  | bindWater
  | protonateDehydrate
  | releaseCO
  | bindWaterToClose
  deriving DecidableEq, Repr

def sourceStoich : Step → Stoich
  | .aquatePrecursor =>
      { water := 2, chloride := -2 }
  | .photoReduceLoseWater =>
      { electron := 1, water := -1 }
  | .captureCO2LoseWater =>
      { water := -1, carbonDioxide := 1 }
  | .photoReduceProtonate =>
      { electron := 1, proton := 1 }
  | .bindWater =>
      { water := 1 }
  | .protonateDehydrate =>
      { proton := 1, water := -1 }
  | .releaseCO =>
      { carbonMonoxide := -1 }
  | .bindWaterToClose =>
      { water := 1 }

/-- Charge delivered to the complex by the external species on an arrow.
Only e⁻, H⁺, and Cl⁻ are charged. -/
def Stoich.chargeDelivered (a : Stoich) : Int :=
  -a.electron + a.proton - a.chloride

def removeSite (site : CoordinationSite)
    (xs : List BoundFragment) : List BoundFragment :=
  xs.filter fun b => !b.donorSites.contains site

def replaceKind (old new : Fragment)
    (xs : List BoundFragment) : List BoundFragment :=
  xs.map fun b => if b.kind = old then { b with kind := new } else b

/-- General-chemistry interpretation of each drawn arrow.  Its charge update
is not an answer literal: it is computed from the source stoichiometry above.
The structural operations are ligand substitution, κ² CO₂ oxidative binding,
proton/electron conversion to Fe-C(=O)-OH, hydration, dehydration to Fe-CO,
and CO dissociation. -/
def applyStep (step : Step) (s : Complex) : Complex :=
  let newColigands := match step with
    | .aquatePrecursor => replaceKind .chloride .aqua s.coligands
    | .photoReduceLoseWater => removeSite labileA s.coligands
    | .captureCO2LoseWater =>
        removeSite labileB s.coligands ++ [activatedCO2AtCisSites]
    | .photoReduceProtonate =>
        (s.coligands.map fun b =>
          if b.kind = .activatedCO2 then mono .hydroxycarbonyl labileA else b)
    | .bindWater => s.coligands ++ [mono .aqua labileB]
    | .protonateDehydrate =>
        replaceKind .hydroxycarbonyl .carbonyl s.coligands
    | .releaseCO => s.coligands.filter fun b => b.kind != .carbonyl
    | .bindWaterToClose => mono .aqua labileA :: s.coligands
  { coligands := newColigands
    metal := s.metal
    totalCharge := s.totalCharge + (sourceStoich step).chargeDelivered }

/-- The FeCl₂ + neutral N4-ligand structure drawn immediately before Q8.3. -/
def precursor1 : Complex :=
  { metal := .Fe
    coligands := [mono .chloride labileA, mono .chloride labileB]
    totalCharge := 0 }

def species9 : Complex := applyStep .aquatePrecursor precursor1
def species10 : Complex := applyStep .photoReduceLoseWater species9
def species11 : Complex := applyStep .captureCO2LoseWater species10
def species12 : Complex := applyStep .photoReduceProtonate species11
def species13 : Complex := applyStep .bindWater species12
def species14 : Complex := applyStep .protonateDehydrate species13
def species15 : Complex := applyStep .releaseCO species14
def regenerated9 : Complex := applyStep .bindWaterToClose species15

def occupiedSites (s : Complex) : List CoordinationSite :=
  ligand8.donorSites ++ s.coligands.flatMap (·.donorSites)

def Complex.wellFormed (s : Complex) : Bool :=
  decide (s.metal = .Fe) &&
  (s.coligands.all fun b =>
      decide (b.donorSites.length =
        (fragmentGraph b.kind).metalDonors.length) &&
      (fragmentGraph b.kind).wellFormed) &&
  decide (occupiedSites s).Nodup

theorem reconstructed_structures_wellFormed :
    species9.wellFormed = true ∧ species10.wellFormed = true ∧
    species11.wellFormed = true ∧ species12.wellFormed = true ∧
    species13.wellFormed = true ∧ species14.wellFormed = true ∧
    species15.wellFormed = true := by
  decide

/-! ## Exact requested structures -/

theorem structure_9 :
    species9.coligands =
      [mono .aqua labileA, mono .aqua labileB] := by
  decide

theorem structure_10 :
    species10.coligands = [mono .aqua labileB] := by
  decide

theorem structure_11 :
    species11.coligands = [activatedCO2AtCisSites] := by
  decide

theorem structure_12 :
    species12.coligands = [mono .hydroxycarbonyl labileA] := by
  decide

theorem structure_13 :
    species13.coligands =
      [mono .hydroxycarbonyl labileA, mono .aqua labileB] := by
  decide

theorem structure_14 :
    species14.coligands =
      [mono .carbonyl labileA, mono .aqua labileB] := by
  decide

theorem structure_15 :
    species15.coligands = [mono .aqua labileB] := by
  decide

/-! ## Oxidation state, coordination number, and ionic electron count -/

def coligandCharge (s : Complex) : Int :=
  (s.coligands.map fun b => (fragmentGraph b.kind).ionicCharge).sum

def oxidationState (s : Complex) : Int :=
  s.totalCharge - ligand8.ionicCharge - coligandCharge s

def coordinationNumber (s : Complex) : Nat :=
  (occupiedSites s).length

def valenceElectrons (s : Complex) : Int :=
  (8 - oxidationState s) + 2 * (coordinationNumber s : Int)

def oddElectron (s : Complex) : Bool :=
  valenceElectrons s % 2 != 0

theorem complex_9_outputs :
    oxidationState species9 = 2 ∧ coordinationNumber species9 = 6 ∧
    valenceElectrons species9 = 18 ∧ species9.totalCharge = 2 := by
  decide

theorem complex_10_outputs :
    oxidationState species10 = 1 ∧ coordinationNumber species10 = 5 ∧
    valenceElectrons species10 = 17 ∧ species10.totalCharge = 1 := by
  decide

theorem complex_11_outputs :
    oxidationState species11 = 3 ∧ coordinationNumber species11 = 6 ∧
    valenceElectrons species11 = 17 ∧ species11.totalCharge = 1 := by
  decide

theorem complex_12_outputs :
    oxidationState species12 = 2 ∧ coordinationNumber species12 = 5 ∧
    valenceElectrons species12 = 16 ∧ species12.totalCharge = 1 := by
  decide

theorem complex_13_outputs :
    oxidationState species13 = 2 ∧ coordinationNumber species13 = 6 ∧
    valenceElectrons species13 = 18 ∧ species13.totalCharge = 1 := by
  decide

theorem complex_14_outputs :
    oxidationState species14 = 2 ∧ coordinationNumber species14 = 6 ∧
    valenceElectrons species14 = 18 ∧ species14.totalCharge = 2 := by
  decide

theorem complex_15_outputs :
    oxidationState species15 = 2 ∧ coordinationNumber species15 = 5 ∧
    valenceElectrons species15 = 16 ∧ species15.totalCharge = 2 := by
  decide

/-- The odd-electron information is not smuggled into a fragment graph: it is
derived from the requested VE counts.  Only 10 and 11 are odd-electron
complexes in this reconstruction. -/
theorem radical_parities :
    oddElectron species9 = false ∧ oddElectron species10 = true ∧
    oddElectron species11 = true ∧ oddElectron species12 = false ∧
    oddElectron species13 = false ∧ oddElectron species14 = false ∧
    oddElectron species15 = false := by
  decide

/-- Independent check against all five pre-filled answer-sheet facts. -/
theorem supplied_answer_sheet_fields_match :
    oxidationState species11 = 3 ∧ coordinationNumber species11 = 6 ∧
    coordinationNumber species12 = 5 ∧ oxidationState species13 = 2 ∧
    valenceElectrons species15 = 16 := by
  decide

/-- The complete coordination structure, charge, and site placement return to
9 after water binds to 15. -/
theorem catalytic_cycle_closes : regenerated9 = species9 := by
  decide

def catalyticCycleNet : Stoich :=
  sourceStoich .photoReduceLoseWater +
  sourceStoich .captureCO2LoseWater +
  sourceStoich .photoReduceProtonate +
  sourceStoich .bindWater +
  sourceStoich .protonateDehydrate +
  sourceStoich .releaseCO +
  sourceStoich .bindWaterToClose

/-- Summing the printed arrows gives CO₂ + 2 H⁺ + 2 e⁻ → CO + H₂O. -/
theorem catalytic_cycle_net_reaction :
    catalyticCycleNet =
      { electron := 2, proton := 2, water := -1,
        chloride := 0, carbonDioxide := 1, carbonMonoxide := -1 } := by
  decide

end IChO2026Problems.T8A4

-- Kernel-dependency audit for every theorem carrying a requested structure or
-- numerical output, plus the source/consistency checks used to justify them.
#print axioms IChO2026Problems.T8A4.all_fragment_graphs_wellFormed
#print axioms IChO2026Problems.T8A4.ligand8_has_four_nitrogen_donors
#print axioms IChO2026Problems.T8A4.labile_sites_are_cis
#print axioms IChO2026Problems.T8A4.reconstructed_structures_wellFormed
#print axioms IChO2026Problems.T8A4.structure_9
#print axioms IChO2026Problems.T8A4.structure_10
#print axioms IChO2026Problems.T8A4.structure_11
#print axioms IChO2026Problems.T8A4.structure_12
#print axioms IChO2026Problems.T8A4.structure_13
#print axioms IChO2026Problems.T8A4.structure_14
#print axioms IChO2026Problems.T8A4.structure_15
#print axioms IChO2026Problems.T8A4.complex_9_outputs
#print axioms IChO2026Problems.T8A4.complex_10_outputs
#print axioms IChO2026Problems.T8A4.complex_11_outputs
#print axioms IChO2026Problems.T8A4.complex_12_outputs
#print axioms IChO2026Problems.T8A4.complex_13_outputs
#print axioms IChO2026Problems.T8A4.complex_14_outputs
#print axioms IChO2026Problems.T8A4.complex_15_outputs
#print axioms IChO2026Problems.T8A4.radical_parities
#print axioms IChO2026Problems.T8A4.supplied_answer_sheet_fields_match
#print axioms IChO2026Problems.T8A4.catalytic_cycle_closes
#print axioms IChO2026Problems.T8A4.catalytic_cycle_net_reaction
