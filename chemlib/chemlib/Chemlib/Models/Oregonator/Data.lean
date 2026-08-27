import Chemlib.Models.SBML.Compile

/-!
# Curated Oregonator model data

This module encodes the five species and five irreversible reactions of the
Field--Körös--Noyes Oregonator model as finite SBML data.  The reaction
endpoints, stoichiometric coefficients, and boundary flags are grounded in
BioModels model `BIOMD0000000040`, specifically its `listOfSpecies`,
`listOfReactions`, and `Reaction1`--`Reaction5`.  The cited raw SBML artifact
has SHA-256
`0bf2abb25229f3fe7979315139396f9c0bcdb06370ae9c835f7d3fc0e0c79c6a`.

The three internal species are `Br`, `Ce`, and `HBrO2`; `BrO3` and `HOBr` are
boundary species.  All reaction sources use natural stoichiometric
coefficients.  The parameter `f` occurs only as the real `Br` coefficient of
the fifth reaction's product complex.  Species records are supplied by the
caller and are preserved without changing their constant flags or initial
concentrations.
-/

namespace Chemlib.Models.Oregonator

/-- The five species listed by the curated Oregonator SBML model. -/
inductive Species : Type
  | Br
  | Ce
  | HBrO2
  | BrO3
  | HOBr
  deriving DecidableEq

instance : Fintype Species where
  elems := {.Br, .Ce, .HBrO2, .BrO3, .HOBr}
  complete := by
    intro s
    cases s <;> simp

/-- The non-boundary species used as coordinates of the dynamical state. -/
inductive InternalSpecies : Type
  | Br
  | Ce
  | HBrO2
  deriving DecidableEq

instance : Fintype InternalSpecies where
  elems := {.Br, .Ce, .HBrO2}
  complete := by
    intro s
    cases s <;> simp

/-- Include an internal-state coordinate in the complete species index. -/
def includeInternal : InternalSpecies → Species
  | .Br => .Br
  | .Ce => .Ce
  | .HBrO2 => .HBrO2

/-- Identifiers for the ten source and target complexes of the five curated
Oregonator reactions. -/
inductive ComplexId : Type
  | Br_BrO3
  | HBrO2_HOBr
  | Br_HBrO2
  | twoHOBr
  | BrO3_HBrO2
  | twoHBrO2_Ce
  | twoHBrO2
  | BrO3_HOBr
  | Ce
  | fBr
  deriving DecidableEq

instance : Fintype ComplexId where
  elems := {
    .Br_BrO3, .HBrO2_HOBr, .Br_HBrO2, .twoHOBr, .BrO3_HBrO2,
    .twoHBrO2_Ce, .twoHBrO2, .BrO3_HOBr, .Ce, .fBr
  }
  complete := by
    intro c
    cases c <;> simp

/-- Identifiers for `Reaction1`--`Reaction5` in the source SBML model. -/
inductive Reaction : Type
  | R1
  | R2
  | R3
  | R4
  | R5
  deriving DecidableEq

instance : Fintype Reaction where
  elems := {.R1, .R2, .R3, .R4, .R5}
  complete := by
    intro r
    cases r <;> simp

/-- Caller-curated species metadata, constrained only by the boundary flags
authenticated by the source SBML model. -/
structure OregonatorSourceData : Type where
  private records : Species → Chemlib.Models.SBML.SpeciesRecord
  private internal_boundary :
    ∀ i : InternalSpecies, (records (includeInternal i)).boundaryCondition = false
  private bro3_boundary : (records .BrO3).boundaryCondition = true
  private hobr_boundary : (records .HOBr).boundaryCondition = true

/-- Return every caller-supplied species record unchanged. -/
def OregonatorSourceData.speciesRecords :
    OregonatorSourceData → Species → Chemlib.Models.SBML.SpeciesRecord :=
  fun data ↦ data.records

/-- The source-authenticated partition into three internal and two boundary
species. -/
theorem OregonatorSourceData.boundary_spec : ∀ data : OregonatorSourceData,
    (∀ i : InternalSpecies,
      (data.speciesRecords (includeInternal i)).boundaryCondition = false) ∧
    (data.speciesRecords Species.BrO3).boundaryCondition = true ∧
    (data.speciesRecords Species.HOBr).boundaryCondition = true := by
  intro data
  exact ⟨data.internal_boundary, data.bro3_boundary, data.hobr_boundary⟩

/-- Compile caller-curated species metadata with the authenticated Oregonator
reaction skeleton and its symbolic fifth-product coefficient. -/
noncomputable def oregonatorModel (data : OregonatorSourceData) :
    Chemlib.Models.SBML.ParametricModel ℝ Species ComplexId Reaction := by
  let network : Chemlib.ReactionNetwork Species ComplexId Reaction := {
    complex := fun
      | .Br_BrO3 => Finsupp.single .Br 1 + Finsupp.single .BrO3 1
      | .HBrO2_HOBr => Finsupp.single .HBrO2 1 + Finsupp.single .HOBr 1
      | .Br_HBrO2 => Finsupp.single .Br 1 + Finsupp.single .HBrO2 1
      | .twoHOBr => Finsupp.single .HOBr 2
      | .BrO3_HBrO2 => Finsupp.single .BrO3 1 + Finsupp.single .HBrO2 1
      | .twoHBrO2_Ce => Finsupp.single .HBrO2 2 + Finsupp.single .Ce 1
      | .twoHBrO2 => Finsupp.single .HBrO2 2
      | .BrO3_HOBr => Finsupp.single .BrO3 1 + Finsupp.single .HOBr 1
      | .Ce => Finsupp.single .Ce 1
      | .fBr => Finsupp.single .Br 1
    source := fun
      | .R1 => .Br_BrO3
      | .R2 => .Br_HBrO2
      | .R3 => .BrO3_HBrO2
      | .R4 => .twoHBrO2
      | .R5 => .Ce
    target := fun
      | .R1 => .HBrO2_HOBr
      | .R2 => .twoHOBr
      | .R3 => .twoHBrO2_Ce
      | .R4 => .BrO3_HOBr
      | .R5 => .fBr
  }
  refine {
    composition := fun f s c ↦ match c with
      | .fBr => if s = .Br then f else 0
      | _ => network.compositionMatrix s c
    reversible := fun _ ↦ false
    skeleton := network
    source_eq := ?_
    species := data.speciesRecords
  }
  intro f r s
  cases r <;> cases s <;>
    simp [network, Chemlib.ReactionNetwork.compositionMatrix,
      Chemlib.ReactionNetwork.reactant]

/-- The complete source-backed finite model specification, including exact
endpoints, boundary partition, symbolic stoichiometry, and incidence
factorization. -/
theorem oregonatorModel_spec : ∀ (data : OregonatorSourceData) (f : ℝ),
    Fintype.card Species = 5 ∧
    Fintype.card InternalSpecies = 3 ∧
    Fintype.card Reaction = 5 ∧
    Fintype.card ComplexId = 10 ∧
    includeInternal InternalSpecies.Br = Species.Br ∧
    includeInternal InternalSpecies.Ce = Species.Ce ∧
    includeInternal InternalSpecies.HBrO2 = Species.HBrO2 ∧
    Function.Injective includeInternal ∧
    (∀ s : Species,
      (∃ i : InternalSpecies, includeInternal i = s) ↔
        ((oregonatorModel data).species s).boundaryCondition = false) ∧
    (∀ s : Species, (oregonatorModel data).species s = data.speciesRecords s) ∧
    (∀ r : Reaction, (oregonatorModel data).reversible r = false) ∧
    (oregonatorModel data).skeleton.source Reaction.R1 = ComplexId.Br_BrO3 ∧
    (oregonatorModel data).skeleton.target Reaction.R1 = ComplexId.HBrO2_HOBr ∧
    (oregonatorModel data).skeleton.source Reaction.R2 = ComplexId.Br_HBrO2 ∧
    (oregonatorModel data).skeleton.target Reaction.R2 = ComplexId.twoHOBr ∧
    (oregonatorModel data).skeleton.source Reaction.R3 = ComplexId.BrO3_HBrO2 ∧
    (oregonatorModel data).skeleton.target Reaction.R3 = ComplexId.twoHBrO2_Ce ∧
    (oregonatorModel data).skeleton.source Reaction.R4 = ComplexId.twoHBrO2 ∧
    (oregonatorModel data).skeleton.target Reaction.R4 = ComplexId.BrO3_HOBr ∧
    (oregonatorModel data).skeleton.source Reaction.R5 = ComplexId.Ce ∧
    (oregonatorModel data).skeleton.target Reaction.R5 = ComplexId.fBr ∧
    (oregonatorModel data).composition f Species.Br
      ((oregonatorModel data).skeleton.target Reaction.R5) = f ∧
    Chemlib.Models.SBML.stoichiometricMatrix (oregonatorModel data) f =
      (fun s r ↦ match s, r with
        | .Br, .R1 => -1
        | .Br, .R2 => -1
        | .Br, .R3 => 0
        | .Br, .R4 => 0
        | .Br, .R5 => f
        | .Ce, .R1 => 0
        | .Ce, .R2 => 0
        | .Ce, .R3 => 1
        | .Ce, .R4 => 0
        | .Ce, .R5 => -1
        | .HBrO2, .R1 => 1
        | .HBrO2, .R2 => -1
        | .HBrO2, .R3 => 1
        | .HBrO2, .R4 => -2
        | .HBrO2, .R5 => 0
        | .BrO3, .R1 => -1
        | .BrO3, .R2 => 0
        | .BrO3, .R3 => -1
        | .BrO3, .R4 => 1
        | .BrO3, .R5 => 0
        | .HOBr, .R1 => 1
        | .HOBr, .R2 => 2
        | .HOBr, .R3 => 0
        | .HOBr, .R4 => 1
        | .HOBr, .R5 => 0) ∧
    Chemlib.Models.SBML.stoichiometricMatrix (oregonatorModel data) f =
      ((oregonatorModel data).composition f) *
        (oregonatorModel data).skeleton.incidenceMatrix := by
  intro data f
  refine ⟨by decide, by decide, by decide, by decide,
    rfl, rfl, rfl, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro a b h
    cases a <;> cases b <;> simp [includeInternal] at h ⊢
  · intro s
    cases s with
    | Br =>
        refine ⟨fun _ ↦ ?_, fun _ ↦ ⟨.Br, rfl⟩⟩
        simpa [includeInternal, oregonatorModel] using
          (OregonatorSourceData.boundary_spec data).1 .Br
    | Ce =>
        refine ⟨fun _ ↦ ?_, fun _ ↦ ⟨.Ce, rfl⟩⟩
        simpa [includeInternal, oregonatorModel] using
          (OregonatorSourceData.boundary_spec data).1 .Ce
    | HBrO2 =>
        refine ⟨fun _ ↦ ?_, fun _ ↦ ⟨.HBrO2, rfl⟩⟩
        simpa [includeInternal, oregonatorModel] using
          (OregonatorSourceData.boundary_spec data).1 .HBrO2
    | BrO3 =>
        constructor
        · rintro ⟨i, hi⟩
          cases i <;> simp [includeInternal] at hi
        · intro hf
          have ht := (OregonatorSourceData.boundary_spec data).2.1
          change (data.speciesRecords .BrO3).boundaryCondition = false at hf
          rw [ht] at hf
          contradiction
    | HOBr =>
        constructor
        · rintro ⟨i, hi⟩
          cases i <;> simp [includeInternal] at hi
        · intro hf
          have ht := (OregonatorSourceData.boundary_spec data).2.2
          change (data.speciesRecords .HOBr).boundaryCondition = false at hf
          rw [ht] at hf
          contradiction
  · intro s
    rfl
  · intro r
    rfl
  · simp [oregonatorModel]
  · ext s r
    rw [Chemlib.Models.SBML.stoichiometricMatrix_apply]
    cases s <;> cases r <;>
      simp [Chemlib.Models.SBML.productMatrix,
        Chemlib.Models.SBML.reactantMatrix,
        oregonatorModel,
        Chemlib.ReactionNetwork.compositionMatrix,
        Chemlib.ReactionNetwork.reactant] <;> norm_num
  · exact Chemlib.Models.SBML.stoichiometricMatrix_eq_mul_incidence
      (oregonatorModel data) f

/-- The explicit source-data layer has a source-authenticated inhabitant. -/
theorem oregonatorSourceData_nonempty : Nonempty OregonatorSourceData := by
  let records : Species → Chemlib.Models.SBML.SpeciesRecord :=
    fun s ↦ {
      boundaryCondition := match s with
        | .BrO3 | .HOBr => true
        | _ => false
      constant := false
      initialConcentration := none
    }
  refine ⟨{
    records := records
    internal_boundary := ?_
    bro3_boundary := rfl
    hobr_boundary := rfl
  }⟩
  intro i
  cases i <;> rfl

end Chemlib.Models.Oregonator
