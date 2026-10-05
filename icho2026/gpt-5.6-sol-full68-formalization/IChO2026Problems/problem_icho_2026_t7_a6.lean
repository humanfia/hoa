import Mathlib
import IChO2026Chem

/-!
# IChO 2026, problem 7, part 6

The page-3 source first gives four measured calibration experiments and then
asks for a decreasing-yield order of four new reductant/additive combinations.
The calibration rows contain two controlled comparisons relevant to the
target table:

* rows 1 and 4 have the same additive, counterion, and pKₐ; the more negative
  reductant potential in row 4 accompanies the higher ammonia yield;
* rows 3 and 4 have the same reductant potential and triflate counterion; the
  higher additive pKₐ in row 4 accompanies the higher ammonia yield.

The source-indicated ordinal rule therefore ranks a more negative reductant
potential first and, at fixed reductant/potential/counterion, ranks the higher
pKₐ first. It is applied uniformly to the source-selected A--D domain. No
numerical target yield, interpolation, fitted coefficient, or target-specific
response value is introduced.
-/

namespace IChO2026Problems
namespace T7A6

/-! ## Source carriers and image transcription -/

/-- Provenance tags admitted by the answer-blind source contract. -/
inductive Provenance where
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- This question compares empirical conditions; it is not a staged material
transformation and consumes no material ledger. -/
inductive StagedTransformationUse where
  | notStagedTransformation
  deriving DecidableEq, Repr

def stagedTransformationUse : StagedTransformationUse :=
  .notStagedTransformation

/-- Metal labels drawn between two cyclopentadienyl rings on page 3. -/
inductive MetalloceneMetal where
  | chromium
  | cobalt
  | nickel
  | vanadium
  deriving DecidableEq, Repr

/-- Source-first carrier for one depicted metallocene reductant. -/
structure MetalloceneSketch where
  metal : MetalloceneMetal
  cyclopentadienylRingCount : ℕ
  provenance : Provenance
  deriving DecidableEq, Repr

/-- The five distinct additive cations drawn in the two page-3 tables. -/
inductive AdditiveCation where
  | twoSixDimethylpyridinium
  | twoMethylpyridinium
  | monoprotonatedOneTenPhenanthroline
  | twoFourSixTrimethylpyridinium
  | anilinium
  deriving DecidableEq, Repr

/-- Structural counts read directly from an additive drawing. -/
structure AdditiveSketch where
  aromaticSixMemberedRingCount : ℕ
  ringNitrogenCount : ℕ
  protonatedRingNitrogenCount : ℕ
  methylSubstituentCount : ℕ
  exocyclicAmmoniumNitrogenCount : ℕ
  exocyclicAmmoniumHydrogenCount : ℕ
  provenance : Provenance
  deriving DecidableEq, Repr

/-- Separate component recount for every distinct additive drawing. -/
def additiveSketch : AdditiveCation → AdditiveSketch
  | .twoSixDimethylpyridinium => ⟨1, 1, 1, 2, 0, 0, .problemImage⟩
  | .twoMethylpyridinium => ⟨1, 1, 1, 1, 0, 0, .problemImage⟩
  | .monoprotonatedOneTenPhenanthroline => ⟨3, 2, 1, 0, 0, 0, .problemImage⟩
  | .twoFourSixTrimethylpyridinium => ⟨1, 1, 1, 3, 0, 0, .problemImage⟩
  | .anilinium => ⟨1, 0, 0, 0, 1, 3, .problemImage⟩

/-- Counterions printed as separate components below the additive cations. -/
inductive Counterion where
  | chloride
  | triflate
  deriving DecidableEq, Repr

/-- The chemical species named by the measured response row. -/
inductive Species where
  | ammonia
  deriving DecidableEq, Repr

/-- One reductant/additive condition. Potential is stored in hundredths of a
volt and pKₐ in tenths, exactly matching the displayed quanta. -/
structure RedAdCombination where
  reductant : MetalloceneSketch
  standardPotentialHundredthsV : ℤ
  additive : AdditiveCation
  counterion : Counterion
  additivePKaTenths : ℤ
  provenance : Provenance
  deriving DecidableEq, Repr

/-- Exact standard potential in volts recovered from the source-scaled value. -/
def RedAdCombination.standardPotentialV
    (combination : RedAdCombination) : ℚ :=
  combination.standardPotentialHundredthsV / 100

/-- Exact dimensionless pKₐ recovered from the source-scaled value. -/
def RedAdCombination.additivePKa
    (combination : RedAdCombination) : ℚ :=
  combination.additivePKaTenths / 10

/-- One measured calibration experiment. Yield is in tenths of a mole. -/
structure CalibrationTrial where
  combination : RedAdCombination
  product : Species
  ammoniaYieldTenthsMol : ℕ
  provenance : Provenance
  deriving DecidableEq, Repr

/-- Exact ammonia amount in moles recovered from a calibration cell. -/
def CalibrationTrial.ammoniaYieldMol (trial : CalibrationTrial) : ℚ :=
  trial.ammoniaYieldTenthsMol / 10

/-! ## Exact calibration table -/

def calibrationTrial1 : CalibrationTrial where
  combination :=
    { reductant := ⟨.chromium, 2, .problemImage⟩
      standardPotentialHundredthsV := -88
      additive := .twoSixDimethylpyridinium
      counterion := .triflate
      additivePKaTenths := 144
      provenance := .problemImage }
  product := .ammonia
  ammoniaYieldTenthsMol := 0
  provenance := .problemImage

def calibrationTrial2 : CalibrationTrial where
  combination :=
    { reductant := ⟨.cobalt, 2, .problemImage⟩
      standardPotentialHundredthsV := -115
      additive := .twoSixDimethylpyridinium
      counterion := .chloride
      additivePKaTenths := 144
      provenance := .problemImage }
  product := .ammonia
  ammoniaYieldTenthsMol := 7
  provenance := .problemImage

def calibrationTrial3 : CalibrationTrial where
  combination :=
    { reductant := ⟨.cobalt, 2, .problemImage⟩
      standardPotentialHundredthsV := -115
      additive := .twoMethylpyridinium
      counterion := .triflate
      additivePKaTenths := 139
      provenance := .problemImage }
  product := .ammonia
  ammoniaYieldTenthsMol := 91
  provenance := .problemImage

def calibrationTrial4 : CalibrationTrial where
  combination :=
    { reductant := ⟨.cobalt, 2, .problemImage⟩
      standardPotentialHundredthsV := -115
      additive := .twoSixDimethylpyridinium
      counterion := .triflate
      additivePKaTenths := 144
      provenance := .problemImage }
  product := .ammonia
  ammoniaYieldTenthsMol := 118
  provenance := .problemImage

def calibrationTrials : List CalibrationTrial :=
  [calibrationTrial1, calibrationTrial2, calibrationTrial3, calibrationTrial4]

/-- Exact transcription of every printed calibration field. -/
def CalibrationTableEvidence : Prop :=
  calibrationTrials =
    [calibrationTrial1, calibrationTrial2, calibrationTrial3, calibrationTrial4] ∧
  calibrationTrial1.combination.reductant =
      ⟨.chromium, 2, .problemImage⟩ ∧
  calibrationTrial1.combination.standardPotentialHundredthsV = -88 ∧
  calibrationTrial1.combination.additive = .twoSixDimethylpyridinium ∧
  calibrationTrial1.combination.counterion = .triflate ∧
  calibrationTrial1.combination.additivePKaTenths = 144 ∧
  calibrationTrial1.product = .ammonia ∧
  calibrationTrial1.ammoniaYieldTenthsMol = 0 ∧
  calibrationTrial2.combination.reductant =
      ⟨.cobalt, 2, .problemImage⟩ ∧
  calibrationTrial2.combination.standardPotentialHundredthsV = -115 ∧
  calibrationTrial2.combination.additive = .twoSixDimethylpyridinium ∧
  calibrationTrial2.combination.counterion = .chloride ∧
  calibrationTrial2.combination.additivePKaTenths = 144 ∧
  calibrationTrial2.product = .ammonia ∧
  calibrationTrial2.ammoniaYieldTenthsMol = 7 ∧
  calibrationTrial3.combination.reductant =
      ⟨.cobalt, 2, .problemImage⟩ ∧
  calibrationTrial3.combination.standardPotentialHundredthsV = -115 ∧
  calibrationTrial3.combination.additive = .twoMethylpyridinium ∧
  calibrationTrial3.combination.counterion = .triflate ∧
  calibrationTrial3.combination.additivePKaTenths = 139 ∧
  calibrationTrial3.product = .ammonia ∧
  calibrationTrial3.ammoniaYieldTenthsMol = 91 ∧
  calibrationTrial4.combination.reductant =
      ⟨.cobalt, 2, .problemImage⟩ ∧
  calibrationTrial4.combination.standardPotentialHundredthsV = -115 ∧
  calibrationTrial4.combination.additive = .twoSixDimethylpyridinium ∧
  calibrationTrial4.combination.counterion = .triflate ∧
  calibrationTrial4.combination.additivePKaTenths = 144 ∧
  calibrationTrial4.product = .ammonia ∧
  calibrationTrial4.ammoniaYieldTenthsMol = 118

/-! ## Exact target table and finite domain -/

/-- The complete candidate domain explicitly printed by the source. -/
inductive Candidate where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr, Fintype

def candidateA : RedAdCombination where
  reductant := ⟨.nickel, 2, .problemImage⟩
  standardPotentialHundredthsV := -9
  additive := .monoprotonatedOneTenPhenanthroline
  counterion := .triflate
  additivePKaTenths := 137
  provenance := .problemImage

def candidateB : RedAdCombination where
  reductant := ⟨.vanadium, 2, .problemImage⟩
  standardPotentialHundredthsV := -110
  additive := .twoFourSixTrimethylpyridinium
  counterion := .triflate
  additivePKaTenths := 150
  provenance := .problemImage

def candidateC : RedAdCombination where
  reductant := ⟨.vanadium, 2, .problemImage⟩
  standardPotentialHundredthsV := -110
  additive := .monoprotonatedOneTenPhenanthroline
  counterion := .triflate
  additivePKaTenths := 137
  provenance := .problemImage

def candidateD : RedAdCombination where
  reductant := ⟨.vanadium, 2, .problemImage⟩
  standardPotentialHundredthsV := -110
  additive := .anilinium
  counterion := .triflate
  additivePKaTenths := 106
  provenance := .problemImage

def candidateCombination : Candidate → RedAdCombination
  | .A => candidateA
  | .B => candidateB
  | .C => candidateC
  | .D => candidateD

/-- A source-selected domain fixed before applying either trend. -/
structure CandidateDomain where
  members : List Candidate
  provenance : Provenance

def sourceCandidateDomain : CandidateDomain where
  members := [.A, .B, .C, .D]
  provenance := .problemImage

/-- Exact transcription of every identity and numerical field in A--D. -/
def TargetTableEvidence : Prop :=
  sourceCandidateDomain.members = [.A, .B, .C, .D] ∧
  sourceCandidateDomain.provenance = .problemImage ∧
  candidateA.reductant = ⟨.nickel, 2, .problemImage⟩ ∧
  candidateA.standardPotentialHundredthsV = -9 ∧
  candidateA.additive = .monoprotonatedOneTenPhenanthroline ∧
  candidateA.counterion = .triflate ∧
  candidateA.additivePKaTenths = 137 ∧
  candidateB.reductant = ⟨.vanadium, 2, .problemImage⟩ ∧
  candidateB.standardPotentialHundredthsV = -110 ∧
  candidateB.additive = .twoFourSixTrimethylpyridinium ∧
  candidateB.counterion = .triflate ∧
  candidateB.additivePKaTenths = 150 ∧
  candidateC.reductant = ⟨.vanadium, 2, .problemImage⟩ ∧
  candidateC.standardPotentialHundredthsV = -110 ∧
  candidateC.additive = .monoprotonatedOneTenPhenanthroline ∧
  candidateC.counterion = .triflate ∧
  candidateC.additivePKaTenths = 137 ∧
  candidateD.reductant = ⟨.vanadium, 2, .problemImage⟩ ∧
  candidateD.standardPotentialHundredthsV = -110 ∧
  candidateD.additive = .anilinium ∧
  candidateD.counterion = .triflate ∧
  candidateD.additivePKaTenths = 106

/-- All target rows use triflate, so the chloride/triflate calibration
contrast introduces no further distinction among A--D. -/
def UniformTargetCounterionEvidence : Prop :=
  ∀ candidate, (candidateCombination candidate).counterion = .triflate

/-! ## Controlled calibration contrasts -/

/-- Rows 1 and 4 isolate the displayed reductant change: their additive,
counterion, and pKₐ agree, while row 4 has both the more negative potential
and the greater ammonia yield. -/
def CalibrationPotentialContrast : Prop :=
  calibrationTrial4.combination.additive =
      calibrationTrial1.combination.additive ∧
  calibrationTrial4.combination.counterion =
      calibrationTrial1.combination.counterion ∧
  calibrationTrial4.combination.additivePKaTenths =
      calibrationTrial1.combination.additivePKaTenths ∧
  calibrationTrial4.combination.standardPotentialHundredthsV <
      calibrationTrial1.combination.standardPotentialHundredthsV ∧
  calibrationTrial4.ammoniaYieldTenthsMol >
      calibrationTrial1.ammoniaYieldTenthsMol

/-- Rows 3 and 4 isolate the displayed additive-acidity direction at fixed
reductant, potential, and triflate: the higher pKₐ accompanies the greater
ammonia yield. -/
def CalibrationPKaContrast : Prop :=
  calibrationTrial4.combination.reductant =
      calibrationTrial3.combination.reductant ∧
  calibrationTrial4.combination.standardPotentialHundredthsV =
      calibrationTrial3.combination.standardPotentialHundredthsV ∧
  calibrationTrial4.combination.counterion =
      calibrationTrial3.combination.counterion ∧
  calibrationTrial4.combination.additivePKaTenths >
      calibrationTrial3.combination.additivePKaTenths ∧
  calibrationTrial4.ammoniaYieldTenthsMol >
      calibrationTrial3.ammoniaYieldTenthsMol

/-- Rows 2 and 4 also isolate counterion identity. It is retained as source
evidence, although every target row has the same triflate counterion. -/
def CalibrationCounterionContrast : Prop :=
  calibrationTrial4.combination.reductant =
      calibrationTrial2.combination.reductant ∧
  calibrationTrial4.combination.standardPotentialHundredthsV =
      calibrationTrial2.combination.standardPotentialHundredthsV ∧
  calibrationTrial4.combination.additive =
      calibrationTrial2.combination.additive ∧
  calibrationTrial4.combination.additivePKaTenths =
      calibrationTrial2.combination.additivePKaTenths ∧
  calibrationTrial4.combination.counterion = .triflate ∧
  calibrationTrial2.combination.counterion = .chloride ∧
  calibrationTrial4.ammoniaYieldTenthsMol >
      calibrationTrial2.ammoniaYieldTenthsMol

/-- Exact target inequalities read before constructing the ranking: B--D all
have a more negative potential than A. -/
def TargetPotentialOrderingEvidence : Prop :=
  ∀ candidate ∈ ([.B, .C, .D] : List Candidate),
    (candidateCombination candidate).standardPotentialHundredthsV <
      candidateA.standardPotentialHundredthsV

/-- At the common vanadocene potential and triflate counterion, the target
pKₐ values decrease B, C, D. -/
def TargetPKaOrderingEvidence : Prop :=
  candidateB.reductant = candidateC.reductant ∧
  candidateC.reductant = candidateD.reductant ∧
  candidateB.standardPotentialHundredthsV =
      candidateC.standardPotentialHundredthsV ∧
  candidateC.standardPotentialHundredthsV =
      candidateD.standardPotentialHundredthsV ∧
  candidateB.counterion = candidateC.counterion ∧
  candidateC.counterion = candidateD.counterion ∧
  candidateB.additivePKaTenths > candidateC.additivePKaTenths ∧
  candidateC.additivePKaTenths > candidateD.additivePKaTenths

/-! ## Source-indicated ordinal response relation -/

/-- Transfer of the controlled E° direction to two members of the printed
target domain. The calibration evidence is part of the relation, rather than
an unconstrained response flag. -/
def MoreNegativePotentialPredictsHigherYield
    (higher lower : Candidate) : Prop :=
  CalibrationPotentialContrast ∧
  (candidateCombination higher).standardPotentialHundredthsV <
    (candidateCombination lower).standardPotentialHundredthsV

/-- Transfer of the controlled pKₐ direction at fixed reductant, potential,
and counterion. -/
def HigherPKaAtFixedReductantPredictsHigherYield
    (higher lower : Candidate) : Prop :=
  CalibrationPKaContrast ∧
  (candidateCombination higher).reductant =
      (candidateCombination lower).reductant ∧
  (candidateCombination higher).standardPotentialHundredthsV =
      (candidateCombination lower).standardPotentialHundredthsV ∧
  (candidateCombination higher).counterion =
      (candidateCombination lower).counterion ∧
  (candidateCombination higher).additivePKaTenths >
      (candidateCombination lower).additivePKaTenths

/-- The qualitative higher-yield relation requested by the source table:
first apply the calibrated reductant-potential direction, and at a fixed
reductant condition apply the calibrated pKₐ direction. -/
def SourceIndicatedHigherAmmoniaYield
    (higher lower : Candidate) : Prop :=
  MoreNegativePotentialPredictsHigherYield higher lower ∨
  HigherPKaAtFixedReductantPredictsHigherYield higher lower

/-- Explicit E°-to-yield bridge over the entire source-selected target domain. -/
def PotentialTrendTransfer : Prop :=
  ∀ higher lower : Candidate,
    (candidateCombination higher).standardPotentialHundredthsV <
        (candidateCombination lower).standardPotentialHundredthsV →
      SourceIndicatedHigherAmmoniaYield higher lower

/-- Explicit pKₐ-to-yield bridge at fixed target reductant and counterion. -/
def PKaTrendTransfer : Prop :=
  ∀ higher lower : Candidate,
    (candidateCombination higher).reductant =
        (candidateCombination lower).reductant →
    (candidateCombination higher).standardPotentialHundredthsV =
        (candidateCombination lower).standardPotentialHundredthsV →
    (candidateCombination higher).counterion =
        (candidateCombination lower).counterion →
    (candidateCombination higher).additivePKaTenths >
        (candidateCombination lower).additivePKaTenths →
      SourceIndicatedHigherAmmoniaYield higher lower

/-! ## Complete ranking carrier and derivation -/

/-- A complete decreasing order of the four printed target labels. -/
structure YieldRanking where
  first : Candidate
  second : Candidate
  third : Candidate
  fourth : Candidate
  deriving DecidableEq, Repr, Fintype

def YieldRanking.asList (ranking : YieldRanking) : List Candidate :=
  [ranking.first, ranking.second, ranking.third, ranking.fourth]

/-- A valid result contains every source candidate exactly once and every
earlier entry has source-indicated higher ammonia yield than every later one. -/
def YieldRankingSpecification (ranking : YieldRanking) : Prop :=
  ranking.asList.Perm sourceCandidateDomain.members ∧
  ranking.asList.Pairwise SourceIndicatedHigherAmmoniaYield

/-- Candidate result computed from the two calibrated trend directions. -/
def derivedYieldRanking : YieldRanking :=
  ⟨.B, .C, .D, .A⟩

/-- Requested classification carrier: the derived order is valid and is the
unique complete A--D order admitted by the source-indicated comparator. -/
def YieldRankingOutput : Prop :=
  YieldRankingSpecification derivedYieldRanking ∧
  (∀ ranking, YieldRankingSpecification ranking →
    ranking = derivedYieldRanking) ∧
  derivedYieldRanking.asList = [.B, .C, .D, .A]

theorem calibrationTableEvidence : CalibrationTableEvidence := by
  unfold CalibrationTableEvidence
  native_decide

theorem targetTableEvidence : TargetTableEvidence := by
  unfold TargetTableEvidence
  native_decide

theorem uniformTargetCounterionEvidence :
    UniformTargetCounterionEvidence := by
  unfold UniformTargetCounterionEvidence
  native_decide

theorem calibrationPotentialContrast : CalibrationPotentialContrast := by
  unfold CalibrationPotentialContrast
  native_decide

theorem calibrationPKaContrast : CalibrationPKaContrast := by
  unfold CalibrationPKaContrast
  native_decide

theorem calibrationCounterionContrast : CalibrationCounterionContrast := by
  unfold CalibrationCounterionContrast
  native_decide

theorem targetPotentialOrderingEvidence :
    TargetPotentialOrderingEvidence := by
  unfold TargetPotentialOrderingEvidence
  native_decide

theorem targetPKaOrderingEvidence : TargetPKaOrderingEvidence := by
  unfold TargetPKaOrderingEvidence
  native_decide

theorem potentialTrendTransfer : PotentialTrendTransfer := by
  intro higher lower hPotential
  exact Or.inl ⟨calibrationPotentialContrast, hPotential⟩

theorem pKaTrendTransfer : PKaTrendTransfer := by
  intro higher lower hReductant hPotential hCounterion hPKa
  exact Or.inr
    ⟨calibrationPKaContrast, hReductant, hPotential, hCounterion, hPKa⟩

theorem derivedYieldRanking_specification :
    YieldRankingSpecification derivedYieldRanking := by
  unfold YieldRankingSpecification YieldRanking.asList derivedYieldRanking
    SourceIndicatedHigherAmmoniaYield
    MoreNegativePotentialPredictsHigherYield
    HigherPKaAtFixedReductantPredictsHigherYield
    CalibrationPotentialContrast CalibrationPKaContrast
  native_decide

theorem derivedYieldRanking_unique :
    ∀ ranking, YieldRankingSpecification ranking →
      ranking = derivedYieldRanking := by
  unfold YieldRankingSpecification YieldRanking.asList derivedYieldRanking
    SourceIndicatedHigherAmmoniaYield
    MoreNegativePotentialPredictsHigherYield
    HigherPKaAtFixedReductantPredictsHigherYield
    CalibrationPotentialContrast CalibrationPKaContrast
  native_decide

theorem yieldRankingOutput : YieldRankingOutput := by
  exact ⟨derivedYieldRanking_specification,
    derivedYieldRanking_unique, rfl⟩

/-! ## Raw and reported answer-blind result binding -/

/-- Raw result: every printed datum, both controlled contrasts, both uniform
trend transfers, and the unique requested A--D classification. -/
def YieldRankingRawResult : Prop :=
  CalibrationTableEvidence ∧
  TargetTableEvidence ∧
  UniformTargetCounterionEvidence ∧
  CalibrationPotentialContrast ∧
  CalibrationPKaContrast ∧
  CalibrationCounterionContrast ∧
  TargetPotentialOrderingEvidence ∧
  TargetPKaOrderingEvidence ∧
  PotentialTrendTransfer ∧
  PKaTrendTransfer ∧
  YieldRankingOutput

theorem yieldRankingRawResult : YieldRankingRawResult := by
  exact ⟨calibrationTableEvidence,
    targetTableEvidence,
    uniformTargetCounterionEvidence,
    calibrationPotentialContrast,
    calibrationPKaContrast,
    calibrationCounterionContrast,
    targetPotentialOrderingEvidence,
    targetPKaOrderingEvidence,
    potentialTrendTransfer,
    pKaTrendTransfer,
    yieldRankingOutput⟩

/-- Exact-symbolic display required for the classification output. -/
def yieldRankingReportText : String := "B > C > D > A"

/-- Reported result linked to the complete raw derivation. -/
def YieldRankingReportedResult : Prop :=
  YieldRankingRawResult ∧
  yieldRankingReportText = "B > C > D > A"

theorem yieldRankingReportedResult : YieldRankingReportedResult := by
  exact ⟨yieldRankingRawResult, rfl⟩

/-- Raw answer-blind result contract. Its digest is regenerated from the
target-local blind candidate on every semantic redraft. -/
theorem yieldRankingRaw :
    ("3656cd1d71887303b249a2e92cc69f9e9eb452590c71a6041907419fe612f088" : String) =
      "3656cd1d71887303b249a2e92cc69f9e9eb452590c71a6041907419fe612f088" ∧
      YieldRankingRawResult := by
  exact ⟨rfl, yieldRankingRawResult⟩

/-- Reported exact-symbolic answer-blind result contract. -/
theorem yieldRankingReported :
    ("732c337c2c8cd0f523c54d2344d41fb3e13e5dae1ec0dcbf0d811726f77c9210" : String) =
      "732c337c2c8cd0f523c54d2344d41fb3e13e5dae1ec0dcbf0d811726f77c9210" ∧
      YieldRankingReportedResult := by
  exact ⟨rfl, yieldRankingReportedResult⟩

end T7A6
end IChO2026Problems
