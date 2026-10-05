import Mathlib

/-!
# IChO 2026 T6-A2: structures in the surface synthesis of cyclo[14]carbon

The problem figure supplies a perchlorinated anthracene, a fully drawn
intermediate `A`, the numbers of chlorine radicals lost on each arrow, and
bond-resolved AFM images.  We number the fourteen carbon atoms around the
*outer* anthracene perimeter.  The two additional anthracene fusion bonds are
`c2-c11` and `c4-c9`.

This file keeps the transcription of the problem figure in `ProblemInput` and
the general graph/electron operations in `Chemistry`.  The requested B, C, and
D structures are independent explicit records.  The final theorems prove that
the structures obtained by the allowed operations are those records and also
check atom counts, carbon valence, charge, radical count, connectivity, and the
absence of stereocentres.
-/

namespace IChO2026Problems.T6A2

/-- Carbon sites, clockwise around the fourteen-membered outer perimeter. -/
inductive Site where
  | c0 | c1 | c2 | c3 | c4 | c5 | c6
  | c7 | c8 | c9 | c10 | c11 | c12 | c13
  deriving DecidableEq, Repr, Fintype

open Site

/-- The next carbon on the clockwise outer perimeter. -/
def next : Site → Site
  | c0 => c1 | c1 => c2 | c2 => c3 | c3 => c4
  | c4 => c5 | c5 => c6 | c6 => c7 | c7 => c8
  | c8 => c9 | c9 => c10 | c10 => c11 | c11 => c12
  | c12 => c13 | c13 => c0

/-- The preceding carbon on the clockwise outer perimeter. -/
def prev : Site → Site
  | c0 => c13 | c1 => c0 | c2 => c1 | c3 => c2
  | c4 => c3 | c5 => c4 | c6 => c5 | c7 => c6
  | c8 => c7 | c9 => c8 | c10 => c9 | c11 => c10
  | c12 => c11 | c13 => c12

inductive BondOrder where
  | none | single | double | triple
  deriving DecidableEq, Repr

namespace BondOrder

def valence : BondOrder → Nat
  | none => 0
  | single => 1
  | double => 2
  | triple => 3

end BondOrder

/-- A Lewis structure on the fixed fourteen-carbon scaffold.

`ringBond i` is the bond from `i` to `next i`.  Chlorine at site `i`, when
present, is a separate atom joined to carbon `i` by one single bond (see
`bond`).  All formal charges and every possible stereocentre are recorded,
even though they are zero/absent in the requested structures. -/
structure Structure where
  ringBond : Site → BondOrder
  leftFusion : BondOrder
  rightFusion : BondOrder
  chlorinated : Site → Bool
  radical : Site → Bool
  carbonCharge : Site → Int
  chlorineCharge : Site → Int
  stereocentre : Site → Bool
  deriving DecidableEq

namespace Structure

/-- Extensional equality for the fully explicit molecular record. -/
@[ext] theorem ext {s t : Structure}
    (hRing : s.ringBond = t.ringBond)
    (hLeft : s.leftFusion = t.leftFusion)
    (hRight : s.rightFusion = t.rightFusion)
    (hCl : s.chlorinated = t.chlorinated)
    (hRad : s.radical = t.radical)
    (hCCharge : s.carbonCharge = t.carbonCharge)
    (hClCharge : s.chlorineCharge = t.chlorineCharge)
    (hStereo : s.stereocentre = t.stereocentre) : s = t := by
  cases s
  cases t
  simp_all

end Structure

inductive Atom where
  | carbon (i : Site)
  | chlorine (i : Site)
  deriving DecidableEq, Repr

def atomPresent (s : Structure) : Atom → Bool
  | .carbon _ => true
  | .chlorine i => s.chlorinated i

/-- Unordered bond lookup, including explicit C-Cl bonds. -/
def bond (s : Structure) : Atom → Atom → BondOrder
  | .carbon i, .carbon j =>
      if next i = j then s.ringBond i
      else if next j = i then s.ringBond j
      else if (i = c2 ∧ j = c11) ∨ (i = c11 ∧ j = c2) then s.leftFusion
      else if (i = c4 ∧ j = c9) ∨ (i = c9 ∧ j = c4) then s.rightFusion
      else .none
  | .carbon i, .chlorine j =>
      if i = j ∧ s.chlorinated j = true then .single else .none
  | .chlorine i, .carbon j =>
      if i = j ∧ s.chlorinated i = true then .single else .none
  | .chlorine _, .chlorine _ => .none

def chlorineCount (s : Structure) : Nat :=
  (Finset.univ.filter fun i => s.chlorinated i = true).card

def radicalCount (s : Structure) : Nat :=
  (Finset.univ.filter fun i => s.radical i = true).card

def fusionContribution (s : Structure) (i : Site) : Nat :=
  (if i = c2 ∨ i = c11 then s.leftFusion.valence else 0) +
  (if i = c4 ∨ i = c9 then s.rightFusion.valence else 0)

/-- Lewis valence bookkeeping.  The final two summands respectively count the
C-Cl sigma bond and one unpaired carbon electron. -/
def carbonValence (s : Structure) (i : Site) : Nat :=
  (s.ringBond (prev i)).valence + (s.ringBond i).valence +
  fusionContribution s i +
  (if s.chlorinated i then 1 else 0) +
  (if s.radical i then 1 else 0)

def CarbonValenceFour (s : Structure) : Prop :=
  ∀ i, carbonValence s i = 4

def Neutral (s : Structure) : Prop :=
  (∀ i, s.carbonCharge i = 0) ∧
  (∀ i, s.chlorinated i = true → s.chlorineCharge i = 0)

def NoStereocentres (s : Structure) : Prop :=
  ∀ i, s.stereocentre i = false

def MacrocyclicC14Connectivity (s : Structure) : Prop :=
  s.leftFusion = .none ∧ s.rightFusion = .none ∧
  ∀ i, s.ringBond i ≠ .none

def NoCarbonChlorineRadicalOverlap (s : Structure) : Prop :=
  ∀ i, ¬(s.chlorinated i = true ∧ s.radical i = true)

def WellFormedOutput (s : Structure) : Prop :=
  CarbonValenceFour s ∧ Neutral s ∧ NoStereocentres s ∧
  MacrocyclicC14Connectivity s ∧ NoCarbonChlorineRadicalOverlap s

namespace ProblemInput

/-! ## Direct transcription of the problem figure

The numbering convention used here is documented in `answer.md`.  In the
given drawing of A, the absent chlorine substituents (black radical dots) are
sites 5 and 10.  Comparison of the calibrated bright chlorine features gives
the loss batches below: sites 1, 8, 12 on the A→D branch; additionally 6, 7 on
the A→B branch; then 13, 0 and finally 3.  These are observations from the
provided figure, not desired-product assumptions.
-/

def aRing : Site → BondOrder
  | c0 => .single | c1 => .double | c2 => .single | c3 => .double
  | c4 => .single | c5 => .double | c6 => .single | c7 => .double
  | c8 => .single | c9 => .double | c10 => .single | c11 => .double
  | c12 => .single | c13 => .double

def aChlorinated : Site → Bool
  | c0 | c1 | c3 | c6 | c7 | c8 | c12 | c13 => true
  | c2 | c4 | c5 | c9 | c10 | c11 => false

def aRadical : Site → Bool
  | c5 | c10 => true
  | _ => false

/-- The fully drawn structure A from the blank student answer sheet. -/
def A : Structure where
  ringBond := aRing
  leftFusion := .single
  rightFusion := .single
  chlorinated := aChlorinated
  radical := aRadical
  carbonCharge := fun _ => 0
  chlorineCharge := fun _ => 0
  stereocentre := fun _ => false

def lossAtoD : List Site := [c1, c8, c12]
def extraLossDtoB : List Site := [c6, c7]
def lossBtoC : List Site := [c13, c0]
def lossCtoC14 : List Site := [c3]

end ProblemInput

namespace Chemistry

/-- Homolysis of a C-Cl bond leaves one electron, hence a carbon radical, at
the formerly chlorinated carbon. -/
def removeChlorine (s : Structure) (i : Site) : Structure :=
  { s with
    chlorinated := Function.update s.chlorinated i false
    radical := Function.update s.radical i true }

def removeMany : Structure → List Site → Structure
  | s, [] => s
  | s, i :: is => removeMany (removeChlorine s i) is

/-- Every requested homolysis in a loss list must act on a chlorine atom that
is actually still present. -/
def ValidRemovalSequence : Structure → List Site → Prop
  | _, [] => True
  | s, i :: is =>
      s.chlorinated i = true ∧
      ValidRemovalSequence (removeChlorine s i) is

instance validRemovalSequenceDecidable (s : Structure) (is : List Site) :
    Decidable (ValidRemovalSequence s is) := by
  induction is generalizing s with
  | nil =>
      simp only [ValidRemovalSequence]
      infer_instance
  | cons i is ih =>
      simp only [ValidRemovalSequence]
      letI : Decidable (ValidRemovalSequence (removeChlorine s i) is) :=
        ih (removeChlorine s i)
      infer_instance

def LeftRetroBergmanApplicable (s : Structure) : Prop :=
  s.radical c1 = true ∧ s.radical c12 = true ∧
  s.leftFusion = .single ∧
  s.ringBond c1 = .double ∧ s.ringBond c11 = .double

instance (s : Structure) : Decidable (LeftRetroBergmanApplicable s) := by
  unfold LeftRetroBergmanApplicable
  infer_instance

def RightRetroBergmanApplicable (s : Structure) : Prop :=
  s.radical c5 = true ∧ s.radical c8 = true ∧
  s.rightFusion = .single ∧
  s.ringBond c4 = .single ∧ s.ringBond c8 = .single

instance (s : Structure) : Decidable (RightRetroBergmanApplicable s) := by
  unfold RightRetroBergmanApplicable
  infer_instance

def AdjacentPairingApplicable
    (s : Structure) (i : Site) (oldOrder : BondOrder) : Prop :=
  s.radical i = true ∧ s.radical (next i) = true ∧
  s.ringBond i = oldOrder

instance (s : Structure) (i : Site) (oldOrder : BondOrder) :
    Decidable (AdjacentPairingApplicable s i oldOrder) := by
  unfold AdjacentPairingApplicable
  infer_instance

def OppositeClosureApplicable (s : Structure) : Prop :=
  s.radical c3 = true ∧ s.radical c10 = true ∧
  s.ringBond c3 = .double ∧ s.ringBond c4 = .double ∧
  s.ringBond c5 = .double ∧ s.ringBond c6 = .double ∧
  s.ringBond c7 = .double ∧ s.ringBond c8 = .double ∧
  s.ringBond c9 = .double

instance (s : Structure) : Decidable (OppositeClosureApplicable s) := by
  unfold OppositeClosureApplicable
  infer_instance

/-- Left terminal retro-Bergman opening.  The radicals at 1 and 12 combine
with the electrons released by breaking fusion bond 2-11.  Bonds 1-2 and
11-12 consequently change from double to triple. -/
def retroBergmanLeft (s : Structure) : Structure :=
  { s with
    ringBond := Function.update (Function.update s.ringBond c1 .triple) c11 .triple
    leftFusion := .none
    radical := Function.update (Function.update s.radical c1 false) c12 false }

/-- Right terminal retro-Bergman opening.  Breaking fusion bond 4-9 and using
the radicals at 5 and 8 changes bonds 4-5 and 8-9 from single to double. -/
def retroBergmanRight (s : Structure) : Structure :=
  { s with
    ringBond := Function.update (Function.update s.ringBond c4 .double) c8 .double
    rightFusion := .none
    radical := Function.update (Function.update s.radical c5 false) c8 false }

/-- Pair two adjacent radical electrons into the specified bond. -/
def pairAdjacent (s : Structure) (i : Site) (newOrder : BondOrder) : Structure :=
  { s with
    ringBond := Function.update s.ringBond i newOrder
    radical := Function.update (Function.update s.radical i false) (next i) false }

/-- Pair the radicals at opposite sites 3 and 10 through the seven-bond
cumulenic arc, producing the alternating polyyne arc of cyclo[14]carbon. -/
def closeC14Polyyne (s : Structure) : Structure :=
  { s with
    ringBond := fun i =>
      match i with
      | c3 | c5 | c7 | c9 => .triple
      | c4 | c6 | c8 => .single
      | _ => s.ringBond i
    radical := Function.update (Function.update s.radical c3 false) c10 false }

end Chemistry

open Chemistry

/-! ## Independently explicit requested structures -/

def dRing : Site → BondOrder
  | c0 => .single | c1 => .triple | c2 => .single | c3 => .double
  | c4 => .double | c5 => .double | c6 => .single | c7 => .double
  | c8 => .double | c9 => .double | c10 => .single | c11 => .triple
  | c12 => .single | c13 => .double

def bRing : Site → BondOrder
  | c0 => .single | c1 => .triple | c2 => .single | c3 => .double
  | c4 => .double | c5 => .double | c6 => .double | c7 => .double
  | c8 => .double | c9 => .double | c10 => .single | c11 => .triple
  | c12 => .single | c13 => .double

def cRing : Site → BondOrder
  | c0 => .single | c1 => .triple | c2 => .single | c3 => .double
  | c4 => .double | c5 => .double | c6 => .double | c7 => .double
  | c8 => .double | c9 => .double | c10 => .single | c11 => .triple
  | c12 => .single | c13 => .triple

def dChlorinated : Site → Bool
  | c0 | c3 | c6 | c7 | c13 => true
  | _ => false

def bChlorinated : Site → Bool
  | c0 | c3 | c13 => true
  | _ => false

def cChlorinated : Site → Bool
  | c3 => true
  | _ => false

def radicalAt10 : Site → Bool
  | c10 => true
  | _ => false

def makeOutput (rb : Site → BondOrder) (cl : Site → Bool) : Structure where
  ringBond := rb
  leftFusion := .none
  rightFusion := .none
  chlorinated := cl
  radical := radicalAt10
  carbonCharge := fun _ => 0
  chlorineCharge := fun _ => 0
  stereocentre := fun _ => false

/-- Requested structure D: C14Cl5 with one radical. -/
def structureD : Structure := makeOutput dRing dChlorinated

/-- Requested structure B: C14Cl3 with one radical. -/
def structureB : Structure := makeOutput bRing bChlorinated

/-- Requested structure C: C14Cl with one radical. -/
def structureC : Structure := makeOutput cRing cChlorinated

/-! ## Derivation from A and the observed chlorine-loss batches -/

def derivedD : Structure :=
  retroBergmanRight
    (retroBergmanLeft
      (removeMany ProblemInput.A ProblemInput.lossAtoD))

def derivedB : Structure :=
  pairAdjacent
    (retroBergmanRight
      (retroBergmanLeft
        (removeMany ProblemInput.A
          (ProblemInput.lossAtoD ++ ProblemInput.extraLossDtoB))))
    c6 .double

def derivedC : Structure :=
  pairAdjacent
    (removeMany derivedB ProblemInput.lossBtoC)
    c13 .triple

def derivedC14 : Structure :=
  closeC14Polyyne
    (removeMany derivedC ProblemInput.lossCtoC14)

def polyyneRing : Site → BondOrder
  | c0 => .single | c1 => .triple | c2 => .single | c3 => .triple
  | c4 => .single | c5 => .triple | c6 => .single | c7 => .triple
  | c8 => .single | c9 => .triple | c10 => .single | c11 => .triple
  | c12 => .single | c13 => .triple

def cyclo14 : Structure where
  ringBond := polyyneRing
  leftFusion := .none
  rightFusion := .none
  chlorinated := fun _ => false
  radical := fun _ => false
  carbonCharge := fun _ => 0
  chlorineCharge := fun _ => 0
  stereocentre := fun _ => false

def preD : Structure :=
  removeMany ProblemInput.A ProblemInput.lossAtoD

def preB : Structure :=
  retroBergmanRight
    (retroBergmanLeft
      (removeMany ProblemInput.A
        (ProblemInput.lossAtoD ++ ProblemInput.extraLossDtoB)))

def preC : Structure :=
  removeMany derivedB ProblemInput.lossBtoC

def preC14 : Structure :=
  removeMany derivedC ProblemInput.lossCtoC14

/-! ## Verified chemical and structural consequences -/

theorem input_A_has_eight_chlorines : chlorineCount ProblemInput.A = 8 := by
  decide

theorem input_A_has_two_radicals : radicalCount ProblemInput.A = 2 := by
  decide

theorem input_A_valence : CarbonValenceFour ProblemInput.A := by
  intro i
  fin_cases i <;> rfl

theorem loss_counts_match_figure :
    ProblemInput.lossAtoD.length = 3 ∧
    (ProblemInput.lossAtoD ++ ProblemInput.extraLossDtoB).length = 5 ∧
    ProblemInput.lossBtoC.length = 2 ∧
    ProblemInput.lossCtoC14.length = 1 := by
  decide

/-- The site assignment read from the AFM panels never removes an absent
chlorine and supplies exactly the radical/bond pattern required by each
general chemistry operation. -/
theorem every_transformation_is_applicable :
    ValidRemovalSequence ProblemInput.A ProblemInput.lossAtoD ∧
    LeftRetroBergmanApplicable preD ∧
    RightRetroBergmanApplicable (retroBergmanLeft preD) ∧
    ValidRemovalSequence ProblemInput.A
      (ProblemInput.lossAtoD ++ ProblemInput.extraLossDtoB) ∧
    LeftRetroBergmanApplicable
      (removeMany ProblemInput.A
        (ProblemInput.lossAtoD ++ ProblemInput.extraLossDtoB)) ∧
    RightRetroBergmanApplicable
      (retroBergmanLeft
        (removeMany ProblemInput.A
          (ProblemInput.lossAtoD ++ ProblemInput.extraLossDtoB))) ∧
    AdjacentPairingApplicable preB c6 .single ∧
    ValidRemovalSequence derivedB ProblemInput.lossBtoC ∧
    AdjacentPairingApplicable preC c13 .double ∧
    ValidRemovalSequence derivedC ProblemInput.lossCtoC14 ∧
    OppositeClosureApplicable preC14 := by
  decide

theorem structure_d_derived : derivedD = structureD := by
  apply Structure.ext
  · funext i
    fin_cases i <;> rfl
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl
  · rfl
  · rfl

theorem structure_b_derived : derivedB = structureB := by
  apply Structure.ext
  · funext i
    fin_cases i <;> rfl
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl
  · rfl
  · rfl

theorem structure_c_derived : derivedC = structureC := by
  apply Structure.ext
  · funext i
    fin_cases i <;> rfl
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl
  · rfl
  · rfl

private theorem structureD_wellFormed : WellFormedOutput structureD := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> rfl
  · constructor
    · intro i
      fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp [structureD, makeOutput]
  · intro i
    fin_cases i <;> rfl
  · refine ⟨rfl, rfl, ?_⟩
    intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide

private theorem structureB_wellFormed : WellFormedOutput structureB := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> rfl
  · constructor
    · intro i
      fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp [structureB, makeOutput]
  · intro i
    fin_cases i <;> rfl
  · refine ⟨rfl, rfl, ?_⟩
    intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide

private theorem structureC_wellFormed : WellFormedOutput structureC := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> rfl
  · constructor
    · intro i
      fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp [structureC, makeOutput]
  · intro i
    fin_cases i <;> rfl
  · refine ⟨rfl, rfl, ?_⟩
    intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide

theorem structure_d_complete :
    WellFormedOutput structureD ∧
    chlorineCount structureD = 5 ∧ radicalCount structureD = 1 := by
  exact ⟨structureD_wellFormed, by decide, by decide⟩

theorem structure_b_complete :
    WellFormedOutput structureB ∧
    chlorineCount structureB = 3 ∧ radicalCount structureB = 1 := by
  exact ⟨structureB_wellFormed, by decide, by decide⟩

theorem structure_c_complete :
    WellFormedOutput structureC ∧
    chlorineCount structureC = 1 ∧ radicalCount structureC = 1 := by
  exact ⟨structureC_wellFormed, by decide, by decide⟩

/-- Final answer theorem for requested output D.  It derives D from the given A
and the three AFM-assigned losses, and verifies all of its structural fields. -/
theorem structure_d_answer :
    derivedD = structureD ∧
    WellFormedOutput structureD ∧
    chlorineCount structureD = 5 ∧ radicalCount structureD = 1 := by
  exact ⟨structure_d_derived, structure_d_complete⟩

/-- Final answer theorem for requested output B. -/
theorem structure_b_answer :
    derivedB = structureB ∧
    WellFormedOutput structureB ∧
    chlorineCount structureB = 3 ∧ radicalCount structureB = 1 := by
  exact ⟨structure_b_derived, structure_b_complete⟩

/-- Final answer theorem for requested output C. -/
theorem structure_c_answer :
    derivedC = structureC ∧
    WellFormedOutput structureC ∧
    chlorineCount structureC = 1 ∧ radicalCount structureC = 1 := by
  exact ⟨structure_c_derived, structure_c_complete⟩

/-- The last printed `-Cl·` step converts C into neutral, closed-shell,
alternating-polyyne cyclo[14]carbon.  This is an independent consistency check
on the radical and bond-order placement in C. -/
theorem c_to_cyclo14_consistency :
    derivedC14 = cyclo14 ∧
    WellFormedOutput cyclo14 ∧
    chlorineCount cyclo14 = 0 ∧ radicalCount cyclo14 = 0 := by
  have hDerived : derivedC14 = cyclo14 := by
    apply Structure.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
    · rfl
    · rfl
  have hWellFormed : WellFormedOutput cyclo14 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> rfl
    · constructor
      · intro i
        fin_cases i <;> rfl
      · intro i
        fin_cases i <;> simp [cyclo14]
    · intro i
      fin_cases i <;> rfl
    · refine ⟨rfl, rfl, ?_⟩
      intro i
      fin_cases i <;> decide
    · intro i
      fin_cases i <;> decide
  exact ⟨hDerived, hWellFormed, by decide, by decide⟩

/-- Explicit C-Cl connectivity: a chlorine atom is present exactly at a site
marked by the structure's `chlorinated` field, and its bond is single. -/
theorem c_cl_bond_iff (s : Structure) (i : Site) :
    bond s (.carbon i) (.chlorine i) = .single ↔ s.chlorinated i = true := by
  simp [bond]

/-- The graph lookup is symmetric, so the bond tables describe unordered
chemical bonds rather than directed arcs. -/
theorem bond_symmetric (s : Structure) (a b : Atom) :
    bond s a b = bond s b a := by
  cases a with
  | carbon i =>
      cases b with
      | carbon j => fin_cases i <;> fin_cases j <;> rfl
      | chlorine j =>
          by_cases h : i = j
          · subst j
            rfl
          · have h' : j ≠ i := Ne.symm h
            simp [bond, h, h']
  | chlorine i =>
      cases b with
      | carbon j =>
          by_cases h : i = j
          · subst j
            rfl
          · have h' : j ≠ i := Ne.symm h
            simp [bond, h, h']
      | chlorine j => rfl

#print axioms structure_d_answer
#print axioms structure_b_answer
#print axioms structure_c_answer
#print axioms every_transformation_is_applicable
#print axioms c_to_cyclo14_consistency

end IChO2026Problems.T6A2
