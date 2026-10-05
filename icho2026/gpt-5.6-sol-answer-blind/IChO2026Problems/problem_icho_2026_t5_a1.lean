import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T5.1: parity of the number of type-a fragments

The source image gives four fragment kinds.  Their numbers of open attachment
sites are respectively `1`, `2`, `3`, and `1`, while their multiplicities in
PL1 are `n`, `2`, `3`, and `4`.  Thus a complete molecular assembly has
`n + 17` attachment sites.  Since every bond pairs two sites, completeness of
the assembly forces this number to be even.

The structures below keep the source's non-ionised and peroxide-free
conditions explicit, although the parity conclusion uses only the complete
attachment-site ledger.
-/

namespace IChO2026Problems
namespace CardiolipinsT5A1

/-- The four building-block kinds shown for PL1 in the problem image. -/
inductive FragmentKind where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype, Repr

/-- Number of wavy-bond attachment sites on one depicted fragment. -/
def attachmentSites : FragmentKind → ℕ
  | .a => 1
  | .b => 2
  | .c => 3
  | .d => 1

/-- Multiplicity of each fragment kind in the stated PL1 inventory. -/
def fragmentMultiplicity (n : ℕ) : FragmentKind → ℕ
  | .a => n
  | .b => 2
  | .c => 3
  | .d => 4

/-- Total number of open sites contributed by the entire fragment inventory. -/
def totalAttachmentSites (n : ℕ) : ℕ :=
  ∑ kind : FragmentKind, fragmentMultiplicity n kind * attachmentSites kind

/-- Image-derived component ledger: `n·1 + 2·2 + 3·3 + 4·1 = n + 17`. -/
theorem totalAttachmentSites_eq (n : ℕ) :
    totalAttachmentSites n = n + 17 := by
  unfold totalAttachmentSites
  rw [show (Finset.univ : Finset FragmentKind) =
      {.a, .b, .c, .d} by decide]
  simp [fragmentMultiplicity, attachmentSites]

/-- Elements exposed at open fragment sites and hence joined by assembly bonds. -/
inductive EndpointElement where
  | hydrogen
  | oxygen
  | phosphorus
  | carbon
  deriving DecidableEq, Repr

/-- An assembled bond, recorded by the elements at its two endpoints. -/
structure Bond where
  left : EndpointElement
  right : EndpointElement

/-- A peroxide bond is precisely an oxygen--oxygen bond. -/
def Bond.IsPeroxide (bond : Bond) : Prop :=
  bond.left = .oxygen ∧ bond.right = .oxygen

/-- The source only specifies that every fatty-acid `R` is a hydrocarbon
substituent; the two atom counts record exactly that restricted composition. -/
structure HydrocarbonSubstituent where
  carbonAtoms : ℕ
  hydrogenAtoms : ℕ
  carbonAtoms_pos : 0 < carbonAtoms

/-- The outcome-decisive attachment-site ledger.  `completePairing` states that
every open site from the source inventory is consumed by exactly one endpoint
of an assembled bond. -/
structure AttachmentSiteLedger (n : ℕ) where
  bondCount : ℕ
  completePairing : totalAttachmentSites n = 2 * bondCount

/-- A source-faithful carrier for an assembly of the non-ionised form of PL1.
It retains the four hydrocarbon substituents and the stipulated absence of
peroxide bonds separately from the connector-count ledger. -/
structure NonIonisedPL1Assembly (n : ℕ) where
  ledger : AttachmentSiteLedger n
  bonds : Fin ledger.bondCount → Bond
  fattyAcidSubstituent : Fin 4 → HydrocarbonSubstituent
  formalCharge : ℤ
  nonIonised : formalCharge = 0
  peroxideFree : ∀ i, ¬(bonds i).IsPeroxide

/-- Raw source-to-mathematics specification: whenever the depicted attachment
sites can all be paired, the unknown fragment count is odd. -/
def FragmentParityRaw : Prop :=
  ∀ (n bondCount : ℕ),
    totalAttachmentSites n = 2 * bondCount → Odd n

/-- Reported classification, phrased directly for every source-faithful PL1
assembly rather than as an answer-shaped equality. -/
def FragmentParityReported : Prop :=
  ∀ n : ℕ, NonIonisedPL1Assembly n → Odd n

/-- Arithmetic derivation of the raw parity classification from the complete
pairing equation. -/
theorem fragmentParityRaw_derivation : FragmentParityRaw := by
  intro n bondCount h
  rw [totalAttachmentSites_eq] at h
  rw [Nat.odd_iff]
  omega

/-- Requested output carrier: option (b), i.e. `n` is odd, follows for every
non-ionised peroxide-free PL1 assembly using the stated inventory. -/
theorem fragmentParityStatement : FragmentParityReported := by
  intro n assembly
  exact fragmentParityRaw_derivation n assembly.ledger.bondCount
    assembly.ledger.completePairing

/-- Answer-blind raw-result contract.  The digest is filled from the exact
solver-owned candidate payload. -/
theorem fragmentParityRawResultContract :
    ("90f3eeed0060cca71328f4a6b78abe179d18ebdf382552fd5c7d7e28491c6a6c" : String) =
        "90f3eeed0060cca71328f4a6b78abe179d18ebdf382552fd5c7d7e28491c6a6c" ∧
      FragmentParityRaw := by
  exact ⟨rfl, fragmentParityRaw_derivation⟩

/-- Answer-blind reported-result contract.  The digest is filled from the exact
solver-owned candidate payload. -/
theorem fragmentParityReportedResultContract :
    ("22cec907691ea8c815b3a63d06cd53903515bacb07cf77ed6ec81b3f334a3323" : String) =
        "22cec907691ea8c815b3a63d06cd53903515bacb07cf77ed6ec81b3f334a3323" ∧
      FragmentParityReported := by
  exact ⟨rfl, fragmentParityStatement⟩

end CardiolipinsT5A1
end IChO2026Problems
