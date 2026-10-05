import Mathlib

/-!
# IChO 2026, theory problem 5.5

The problem states that dianionic PL1 forms a lamellar phase and asks for the
phase after both acidic groups are protonated.  This file separates that
problem input (`hPhysiological`) from the qualitative packing law used to make
the inference.

`ElectrostaticPackingModel` is an intentionally qualitative model.  Its
strictly positive `chargeExpansion` records the standard packing-law fact that
like charges enlarge the effective polar-head cross-section.  No numerical
area, PL1 structure, or desired phase is assumed.  The proof first recovers
head/tail balance from the stated lamellar phase, proves that removing both
charges makes the head smaller than the hydrophobic region, and then identifies
the only listed phase with negative curvature.
-/

namespace IChO2026Problems.T5A5

/-- The four phases displayed in the question, in chemical rather than answer
order. -/
inductive LipidPhase where
  | micellar
  | lamellar
  | hexagonal
  | inverseHexagonal
  deriving DecidableEq, Repr

/-- The three protonation states of a diprotic lipid acid. -/
inductive ProtonationState where
  | fullyProtonated
  | monoanion
  | dianion
  deriving DecidableEq, Repr

/-- Number of deprotonated acidic groups (and hence magnitude of the negative
charge in this qualitative model). -/
def deprotonatedGroups : ProtonationState → ℝ
  | .fullyProtonated => 0
  | .monoanion => 1
  | .dianion => 2

/-- A qualitative electrostatic packing model.  `chargeExpansion > 0` is the
trusted general physical law: deprotonated, mutually repelling head groups have
a larger effective cross-section than the neutral head group. -/
structure ElectrostaticPackingModel where
  neutralHeadArea : ℝ
  hydrophobicArea : ℝ
  chargeExpansion : ℝ
  neutralHeadArea_pos : 0 < neutralHeadArea
  hydrophobicArea_pos : 0 < hydrophobicArea
  chargeExpansion_pos : 0 < chargeExpansion

/-- Effective polar-head area in the qualitative packing model.  The linear
formula merely records the ordering of the three charge states; no measured
area is assigned. -/
def effectiveHeadArea (m : ElectrostaticPackingModel)
    (state : ProtonationState) : ℝ :=
  m.neutralHeadArea + deprotonatedGroups state * m.chargeExpansion

/-- Sign of the preferred interfacial curvature inferred from head and
hydrophobic cross-sections. -/
inductive CurvatureSign where
  | positive
  | zero
  | negative
  deriving DecidableEq, Repr

/-- A smaller head than hydrophobic region is an inverted cone (negative
curvature); equal areas give a cylindrical, zero-curvature packing. -/
noncomputable def packingCurvature (headArea hydrophobicArea : ℝ) : CurvatureSign :=
  if headArea < hydrophobicArea then .negative
  else if hydrophobicArea < headArea then .positive
  else .zero

/-- Curvature sign represented by each of the four diagrams in the question.
The two ordinary (non-inverse) curved aggregates are both positive here; their
different curvature magnitudes are irrelevant once negative curvature has been
derived. -/
def LipidPhase.curvature : LipidPhase → CurvatureSign
  | .micellar => .positive
  | .lamellar => .zero
  | .hexagonal => .positive
  | .inverseHexagonal => .negative

/-- A phase fits a protonation state when the phase diagram and packing model
have the same curvature sign. -/
def PhaseFits (m : ElectrostaticPackingModel) (state : ProtonationState)
    (phase : LipidPhase) : Prop :=
  phase.curvature = packingCurvature (effectiveHeadArea m state) m.hydrophobicArea

theorem packingCurvature_eq_zero_iff {headArea hydrophobicArea : ℝ} :
    packingCurvature headArea hydrophobicArea = .zero ↔
      headArea = hydrophobicArea := by
  constructor
  · intro hzero
    by_cases hHead : headArea < hydrophobicArea
    · simp [packingCurvature, hHead] at hzero
    · by_cases hHydrophobic : hydrophobicArea < headArea
      · simp [packingCurvature, hHead, hHydrophobic] at hzero
      · exact le_antisymm (le_of_not_gt hHydrophobic) (le_of_not_gt hHead)
  · rintro rfl
    simp [packingCurvature]

/-- Removing both negative charges strictly contracts the effective head area.
This is derived from positivity of electrostatic expansion, rather than assumed
as the requested phase. -/
theorem fullyProtonated_headArea_lt_dianion
    (m : ElectrostaticPackingModel) :
    effectiveHeadArea m .fullyProtonated < effectiveHeadArea m .dianion := by
  simp only [effectiveHeadArea, deprotonatedGroups]
  linarith [m.chargeExpansion_pos]

/-- The stated lamellar phase of the dianion fixes head/tail balance in the
qualitative model. -/
theorem dianion_lamellar_implies_area_balance
    (m : ElectrostaticPackingModel)
    (hPhysiological : PhaseFits m .dianion .lamellar) :
    effectiveHeadArea m .dianion = m.hydrophobicArea := by
  apply packingCurvature_eq_zero_iff.mp
  simpa [PhaseFits, LipidPhase.curvature] using hPhysiological.symm

/-- Main chemical result: from the problem-stated lamellar dianion and the
general electrostatic packing law, the fully protonated lipid fits the inverse
hexagonal phase, and no other displayed phase fits. -/
theorem protonatedPL1_phase_is_inverseHexagonal
    (m : ElectrostaticPackingModel)
    (hPhysiological : PhaseFits m .dianion .lamellar) :
    ∀ phase, PhaseFits m .fullyProtonated phase ↔
      phase = .inverseHexagonal := by
  have hBalance : effectiveHeadArea m .dianion = m.hydrophobicArea :=
    dianion_lamellar_implies_area_balance m hPhysiological
  have hContract :
      effectiveHeadArea m .fullyProtonated < effectiveHeadArea m .dianion :=
    fullyProtonated_headArea_lt_dianion m
  have hNegative :
      packingCurvature (effectiveHeadArea m .fullyProtonated) m.hydrophobicArea =
        .negative := by
    simp [packingCurvature, hContract.trans_eq hBalance]
  intro phase
  constructor
  · intro hFits
    have hPhaseNegative : phase.curvature = .negative := by
      simpa [PhaseFits, hNegative] using hFits
    cases phase <;> simp_all [LipidPhase.curvature]
  · rintro rfl
    simp [PhaseFits, LipidPhase.curvature, hNegative]

/-- The answer-letter ordering printed in the question and on blank answer
sheet A5-3. -/
inductive AnswerChoice where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

def AnswerChoice.phase : AnswerChoice → LipidPhase
  | .a => .micellar
  | .b => .lamellar
  | .c => .hexagonal
  | .d => .inverseHexagonal

/-- Requested classification output: among the printed alternatives, exactly
choice (d) fits fully protonated PL1. -/
theorem icho_2026_t5_a5
    (m : ElectrostaticPackingModel)
    (hPhysiological : PhaseFits m .dianion .lamellar) :
    ∀ choice : AnswerChoice,
      PhaseFits m .fullyProtonated choice.phase ↔ choice = .d := by
  intro choice
  calc
    PhaseFits m .fullyProtonated choice.phase ↔
        choice.phase = .inverseHexagonal :=
      protonatedPL1_phase_is_inverseHexagonal m hPhysiological choice.phase
    _ ↔ choice = .d := by
      cases choice <;> simp [AnswerChoice.phase]

#print axioms protonatedPL1_phase_is_inverseHexagonal
#print axioms icho_2026_t5_a5

end IChO2026Problems.T5A5
