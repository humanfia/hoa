import Mathlib
import Ipho2026Gpt56solBlind.Shared.Figure17Apparatus
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, Problem 4, Part A.1

This answer-blind adapter packages the Figure 17 apparatus and air-material
inputs, then characterizes the requested confined-air inventory by the shared
density--volume, molar-mass, and amount-to-molecule governing equations.
-/

namespace Ipho2026Gpt56solBlind.ProblemIPhO2026_4_A_1

open Ipho2026Gpt56solBlind.Shared.Figure17Apparatus

/-- The Figure 17 apparatus and air-material inputs used in Part A.1. -/
structure SourceData where
  apparatus : ApparatusData
  material : AirMaterialData

/-- The apparatus preparation and air data required by the statement. -/
def MatchesStatement (source : SourceData) : Prop :=
  PreparedPartAApparatus source.apparatus ∧
    PositiveAirMaterialData source.material ∧
    SatisfiesStatedAirData source.material

/--
A candidate answer is precisely an inventory satisfying the shared typed
density--volume, molar-mass, and amount-to-molecule equations.
-/
def IsRequestedAirInventory (source : SourceData) (inventory : AirInventory) : Prop :=
  AirInventorySolution source.apparatus source.material inventory

/-- The Part A.1 adapter preserves the shared governing predicate verbatim. -/
lemma requestedAirInventory_iff_shared (source : SourceData) (inventory : AirInventory) :
    IsRequestedAirInventory source inventory ↔
      AirInventorySolution source.apparatus source.material inventory := by
  rfl

/-- Matching source data determine exactly one typed confined-air inventory. -/
theorem requestedAirInventory_existsUnique (source : SourceData)
    (hMatches : MatchesStatement source) :
    ∃! inventory : AirInventory, IsRequestedAirInventory source inventory := by
  rcases hMatches with ⟨hPrepared, hMaterial, _⟩
  change ∃! inventory : AirInventory,
    AirInventorySolution source.apparatus source.material inventory
  exact
    existsUnique_airInventorySolution source.apparatus source.material hPrepared hMaterial

end Ipho2026Gpt56solBlind.ProblemIPhO2026_4_A_1
