import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T5-A5: protonation-dependent phase of PL1

The source supplies a closed domain of four phase choices and observes that
the physiological PL1 dianion is lamellar.  The requested state has both acid
residues protonated.

The decisive chemistry is represented below by two general, independently
sourced packing principles rather than by a premise naming the requested
phase:

1. Reducing the negative charge of a cardiolipin headgroup reduces its
   effective area because electrostatic repulsion is reduced.  See G. Olofsson
   and E. Sparr, “Ionization constants pKa of cardiolipin”, *PLoS ONE* 8
   (2013), e73040, DOI `10.1371/journal.pone.0073040`, Introduction, second
   paragraph.
2. Relative hydrophilic-head and hydrophobic-tail cross sections determine
   normal, lamellar, and reversed packing.  See Y. Huang and S. Gui, “Factors
   affecting the structure of lyotropic liquid crystals and the correlation
   between structure and drug diffusion”, *RSC Advances* 8 (2018), 6978–6987,
   DOI `10.1039/C7RA12008G`, section 3, first paragraph.

`ChargeExpansionLaw` is uniform over all three protonation states, while
`PackingGeometryLaw` is uniform over every state and every source-listed
phase.  The target constructor is obtained only after deriving a strict area
inequality and checking all four constructors.
-/

namespace IChO2026Problems.ProblemIChO2026T5A5

/-- The four and only four phase choices printed in T5-A5. -/
inductive LipidPhase where
  | micellar
  | lamellar
  | hexagonal
  | inverseHexagonal
  deriving DecidableEq, Fintype, Repr

/-- Exact human-readable labels used by the problem's choice table. -/
def LipidPhase.label : LipidPhase → String
  | .micellar => "micellar"
  | .lamellar => "lamellar"
  | .hexagonal => "hexagonal"
  | .inverseHexagonal => "inverse hexagonal"

/-- Coarse head-versus-tail geometry used by the critical-packing model.
Normal micelles and normal hexagonal cylinders are both head-dominant;
lamellae are balanced; inverse cylinders are tail-dominant. -/
inductive PackingBias where
  | headDominant
  | balanced
  | tailDominant
  deriving DecidableEq, Fintype, Repr

/-- Source-option/figure ledger.  This map is applied uniformly to the full
four-choice domain; it does not select a target phase. -/
def LipidPhase.packingBias : LipidPhase → PackingBias
  | .micellar => .headDominant
  | .lamellar => .balanced
  | .hexagonal => .headDominant
  | .inverseHexagonal => .tailDominant

/-- Compare the effective polar-head cross section with the hydrophobic-tail
cross section.  Equality is the idealized zero-curvature (lamellar) case used
by the qualitative critical-packing model. -/
noncomputable def areaPackingBias (headArea tailArea : ℝ) : PackingBias :=
  if headArea < tailArea then .tailDominant
  else if tailArea < headArea then .headDominant
  else .balanced

theorem areaPackingBias_eq_balanced_iff (headArea tailArea : ℝ) :
    areaPackingBias headArea tailArea = .balanced ↔ headArea = tailArea := by
  constructor
  · intro h
    by_cases hHead : headArea < tailArea
    · simp [areaPackingBias, hHead] at h
    by_cases hTail : tailArea < headArea
    · simp [areaPackingBias, hHead, hTail] at h
    exact le_antisymm (le_of_not_gt hTail) (le_of_not_gt hHead)
  · rintro rfl
    simp [areaPackingBias]

theorem areaPackingBias_eq_tailDominant_iff (headArea tailArea : ℝ) :
    areaPackingBias headArea tailArea = .tailDominant ↔ headArea < tailArea := by
  by_cases hHead : headArea < tailArea
  · simp [areaPackingBias, hHead]
  · by_cases hTail : tailArea < headArea
    · simp [areaPackingBias, hHead, hTail]
    · simp [areaPackingBias, hHead, hTail]

/-- Inside the exact source option domain, tail-dominant/reversed packing
identifies precisely the inverse-hexagonal panel. -/
theorem phasePackingBias_eq_tailDominant_iff (phase : LipidPhase) :
    phase.packingBias = .tailDominant ↔ phase = .inverseHexagonal := by
  cases phase <;> simp [LipidPhase.packingBias]

/-- The three protonation states of a molecule with two acidic residues. -/
inductive AcidProtonationState where
  | bothAcidResiduesProtonated
  | monoanion
  | dianion
  deriving DecidableEq, Fintype, Repr

/-- Number of deprotonated acidic residues in each state. -/
def deprotonatedAcidResidueCount : AcidProtonationState → ℕ
  | .bothAcidResiduesProtonated => 0
  | .monoanion => 1
  | .dianion => 2

/-- Formal charge supplied by the corresponding number of deprotonations. -/
def formalCharge (state : AcidProtonationState) : ℤ :=
  -((deprotonatedAcidResidueCount state : ℕ) : ℤ)

/-- The source states that PL1 is diprotic. -/
def pl1AcidResidueCount : ℕ := 2

/-- A qualitative packing model for the source-named cardiolipin PL1.  The
hydrophobic cross section is shared by protonation states because protonation
changes the acid headgroup, not the hydrocarbon residues. -/
structure CardiolipinPackingModel where
  phaseAt : AcidProtonationState → LipidPhase
  effectiveHeadArea : AcidProtonationState → ℝ
  hydrophobicCrossSection : ℝ

/-- Exact problem-side facts: PL1 is diprotic, the named endpoint charges are
zero and minus two, its phase is pH-dependent, and the physiological dianion
is observed to be lamellar. -/
structure ProblemSourceFacts (model : CardiolipinPackingModel) : Prop where
  diprotic : pl1AcidResidueCount = 2
  fullyProtonatedCharge : formalCharge .bothAcidResiduesProtonated = 0
  dianionCharge : formalCharge .dianion = -2
  pHDependentPhase : ∃ s t, model.phaseAt s ≠ model.phaseAt t
  physiologicalDianionPhase : model.phaseAt .dianion = .lamellar

/-- General electrostatic headgroup law.  Within a fixed cardiolipin, a state
with more deprotonated (negatively charged) acid residues has a strictly larger
effective polar-head area because like-charge repulsion is greater. -/
def ChargeExpansionLaw (model : CardiolipinPackingModel) : Prop :=
  ∀ s t,
    deprotonatedAcidResidueCount s < deprotonatedAcidResidueCount t →
      model.effectiveHeadArea s < model.effectiveHeadArea t

/-- General critical-packing compatibility law, applied to every protonation
state.  It relates a phase to head/tail geometry but contains no selected
target state or selected answer constructor. -/
def PackingGeometryLaw (model : CardiolipinPackingModel) : Prop :=
  ∀ state,
    (model.phaseAt state).packingBias =
      areaPackingBias (model.effectiveHeadArea state)
        model.hydrophobicCrossSection

/-- Source facts plus the two general packing laws imply the requested phase.
The proof first calibrates balanced head/tail packing from the observed
lamellar dianion, then derives strict tail dominance after protonation. -/
theorem fullyProtonatedPL1Phase
    (model : CardiolipinPackingModel)
    (hSource : ProblemSourceFacts model)
    (hChargeExpansion : ChargeExpansionLaw model)
    (hPacking : PackingGeometryLaw model) :
    model.phaseAt .bothAcidResiduesProtonated = .inverseHexagonal := by
  have hDianionPacking :
      areaPackingBias (model.effectiveHeadArea .dianion)
          model.hydrophobicCrossSection = .balanced := by
    calc
      areaPackingBias (model.effectiveHeadArea .dianion)
          model.hydrophobicCrossSection =
          (model.phaseAt .dianion).packingBias := (hPacking .dianion).symm
      _ = .balanced := by
        rw [hSource.physiologicalDianionPhase]
        rfl
  have hDianionArea :
      model.effectiveHeadArea .dianion = model.hydrophobicCrossSection :=
    (areaPackingBias_eq_balanced_iff _ _).mp hDianionPacking
  have hChargeCount :
      deprotonatedAcidResidueCount .bothAcidResiduesProtonated <
        deprotonatedAcidResidueCount .dianion := by
    norm_num [deprotonatedAcidResidueCount]
  have hHeadArea :
      model.effectiveHeadArea .bothAcidResiduesProtonated <
        model.effectiveHeadArea .dianion :=
    hChargeExpansion _ _ hChargeCount
  have hTailDominates :
      model.effectiveHeadArea .bothAcidResiduesProtonated <
        model.hydrophobicCrossSection := by
    simpa [hDianionArea] using hHeadArea
  apply (phasePackingBias_eq_tailDominant_iff _).mp
  calc
    (model.phaseAt .bothAcidResiduesProtonated).packingBias =
        areaPackingBias
          (model.effectiveHeadArea .bothAcidResiduesProtonated)
          model.hydrophobicCrossSection :=
      hPacking .bothAcidResiduesProtonated
    _ = .tailDominant :=
      (areaPackingBias_eq_tailDominant_iff _ _).mpr hTailDominates

/-- Closed raw semantic proposition used by the answer-blind result contract.
Every source-compatible model is filtered by the same charge and packing
principles; no candidate phase occurs in a premise. -/
def LipidPhaseRawSpec : Prop :=
  ∀ model : CardiolipinPackingModel,
    ProblemSourceFacts model →
    ChargeExpansionLaw model →
    PackingGeometryLaw model →
    model.phaseAt .bothAcidResiduesProtonated = .inverseHexagonal

/-- Exact-symbolic display specification for the requested classification. -/
def LipidPhaseReportedSpec : Prop :=
  LipidPhaseRawSpec ∧
    LipidPhase.label .inverseHexagonal = "inverse hexagonal"

/- The payload markers are replaced with hashes mechanically generated from
the synchronized answer-blind candidate record. -/
theorem lipidPhaseRawResult :
    ("dfa1a37bc30d45efc7dba7829419686409f4dee013ea4aac4851452b36491a54" : String) =
        "dfa1a37bc30d45efc7dba7829419686409f4dee013ea4aac4851452b36491a54" ∧
      LipidPhaseRawSpec := by
  constructor
  · rfl
  · intro model hSource hChargeExpansion hPacking
    exact fullyProtonatedPL1Phase model hSource hChargeExpansion hPacking

theorem lipidPhaseReportedResult :
    ("8257da63180260dccd11a788216d1f2d0e4c8d8a94102295558ab32777930cdd" : String) =
        "8257da63180260dccd11a788216d1f2d0e4c8d8a94102295558ab32777930cdd" ∧
      LipidPhaseReportedSpec := by
  constructor
  · rfl
  · exact ⟨lipidPhaseRawResult.2, rfl⟩

end IChO2026Problems.ProblemIChO2026T5A5
