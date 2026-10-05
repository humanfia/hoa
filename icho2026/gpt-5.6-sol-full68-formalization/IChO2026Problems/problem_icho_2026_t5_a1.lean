import Mathlib

/-!
# IChO 2026, problem T5-A1: parity of the number of type-a fragments

The problem image describes an acyclic, connected, non-ionised PL1 molecule
assembled from four explicitly pictured fragment kinds.  This file models the
fragments as the vertices of the molecular assembly graph and every joined
wavy attachment as an edge.  Thus vertex degree is the number of pictured
attachment sites.  The raw source ledger has

* `n` one-site type-a (hydrogen) fragments,
* two two-site type-b (phosphate) fragments,
* three three-site type-c (glycerol) fragments, and
* four one-site type-d (fatty-acyl) fragments.

The definitions retain all three answer choices.  In particular, “either” is
not represented by the tautology that each fixed natural number is even or
odd; it means that source-feasible assemblies of both parities exist.
-/

namespace IChO2026Problems.IChO2026T5A1

/-- Permitted provenance tags for finite domains and source-derived counts. -/
inductive SourceProvenance where
  | problemText
  | problemImage
  | problemStatedFallback
  | trustedGeneralLaw
  | derivedTheorem
  deriving DecidableEq, Repr

/-- The four fragment kinds displayed for the assembly of PL1. -/
inductive FragmentKind where
  | typeA
  | typeB
  | typeC
  | typeD
  deriving DecidableEq, Fintype, Repr

/-- The atom at a fragment-side endpoint of a newly assembled bond. -/
inductive AttachmentAtom where
  | hydrogen
  | phosphorus
  | oxygen
  | carbon
  deriving DecidableEq, Repr

/-- Multiplicities read from the PL1 fragment panel on `T5_page-1.png`.
Type A is the unknown `n`; types B, C, and D occur 2, 3, and 4 times. -/
def sourceFragmentMultiplicity (n : ℕ) : FragmentKind → ℕ
  | .typeA => n
  | .typeB => 2
  | .typeC => 3
  | .typeD => 4

/-- Number of wavy attachment bonds on each fragment, read independently from
the PL1 fragment panel: A has 1, B has 2, C has 3, and D has 1. -/
def sourceAttachmentSiteCount : FragmentKind → ℕ
  | .typeA => 1
  | .typeB => 2
  | .typeC => 3
  | .typeD => 1

/-- The fragment inventory and its attachment-site counts come from the
problem image rather than from a candidate answer. -/
def fragmentKindProvenance (_ : FragmentKind) : SourceProvenance :=
  .problemImage

/-- Atom type shown at each fragment's outward attachment: H for A, P for B,
O for C, and the carbonyl carbon for D.  The internal `R` in D is the
source-stated hydrocarbon substituent and adds no outward wavy attachment. -/
def endpointAtomAllowed : FragmentKind → AttachmentAtom → Prop
  | .typeA, atom => atom = .hydrogen
  | .typeB, atom => atom = .phosphorus
  | .typeC, atom => atom = .oxygen
  | .typeD, atom => atom = .carbon

/-- Total number of attachment sites supplied by the image inventory before
the sites are paired into bonds. -/
def sourceTotalAttachmentSites (n : ℕ) : ℕ :=
  ∑ kind : FragmentKind,
    sourceFragmentMultiplicity n kind * sourceAttachmentSiteCount kind

/-- Source-first component ledger: `n·1 + 2·2 + 3·3 + 4·1 = n + 17`. -/
theorem sourceTotalAttachmentSites_eq (n : ℕ) :
    sourceTotalAttachmentSites n = n + 17 := by
  classical
  unfold sourceTotalAttachmentSites
  rw [show (Finset.univ : Finset FragmentKind) =
      {.typeA, .typeB, .typeC, .typeD} by decide]
  simp [sourceFragmentMultiplicity, sourceAttachmentSiteCount]

/-- A source-faithful assembly of the complete PL1 molecule.

Vertices are whole pictured fragments, and graph edges are exactly the bonds
formed by joining pairs of wavy attachment sites.  `allAttachmentSitesJoined`
rules out unused or anonymous attachment streams.  `isAcyclicMolecule` encodes
both connectedness (one molecule) and acyclicity.  Formal charges are retained
so that the source's “non-ionised form” is expressed as a zero-charge ledger.
-/
structure PL1Assembly (n : ℕ) where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  graph : SimpleGraph Vertex
  [adjDecidable : DecidableRel graph.Adj]
  fragmentKind : Vertex → FragmentKind
  inventory : ∀ kind,
    (Finset.univ.filter fun v => fragmentKind v = kind).card =
      sourceFragmentMultiplicity n kind
  allAttachmentSitesJoined : ∀ v,
    graph.degree v = sourceAttachmentSiteCount (fragmentKind v)
  isAcyclicMolecule : graph.IsTree
  endpointAtom : Vertex → Vertex → AttachmentAtom
  endpointAtom_matches_fragment : ∀ {v w}, graph.Adj v w →
    endpointAtomAllowed (fragmentKind v) (endpointAtom v w)
  noPeroxideBond : ∀ {v w}, graph.Adj v w →
    ¬ (endpointAtom v w = .oxygen ∧ endpointAtom w v = .oxygen)
  formalCharge : Vertex → ℤ
  nonIonised : (∑ v, formalCharge v) = 0

/-- Number of fragment vertices in an assembly. -/
noncomputable def fragmentCount {n : ℕ} (assembly : PL1Assembly n) : ℕ :=
  letI := assembly.vertexFintype
  Fintype.card assembly.Vertex

/-- Number of inter-fragment bonds in an assembly. -/
noncomputable def bondCount {n : ℕ} (assembly : PL1Assembly n) : ℕ :=
  letI := assembly.vertexFintype
  letI := assembly.vertexDecidableEq
  letI := assembly.adjDecidable
  assembly.graph.edgeFinset.card

/-- Sum of all used attachment sites, computed from the degrees prescribed by
the pictured fragment kinds. -/
noncomputable def usedAttachmentSiteCount {n : ℕ}
    (assembly : PL1Assembly n) : ℕ :=
  letI := assembly.vertexFintype
  ∑ v, sourceAttachmentSiteCount (assembly.fragmentKind v)

/-- The exact source inventory contains `n + 9` whole fragments. -/
theorem fragment_inventory_ledger {n : ℕ} (assembly : PL1Assembly n) :
    fragmentCount assembly = n + 9 := by
  letI := assembly.vertexFintype
  letI := assembly.vertexDecidableEq
  calc
    fragmentCount assembly =
        ∑ kind : FragmentKind,
          (Finset.univ.filter fun v => assembly.fragmentKind v = kind).card := by
      rw [fragmentCount, Fintype.card,
        Finset.card_eq_sum_card_fiberwise (f := assembly.fragmentKind)
          (s := Finset.univ) (t := Finset.univ) (by simp)]
    _ = ∑ kind : FragmentKind, sourceFragmentMultiplicity n kind := by
      apply Finset.sum_congr rfl
      intro kind _
      exact assembly.inventory kind
    _ = n + 9 := by
      rw [show (Finset.univ : Finset FragmentKind) =
          {.typeA, .typeB, .typeC, .typeD} by decide]
      simp [sourceFragmentMultiplicity]

/-- Re-indexing the degree sum by the four source fragment kinds gives the
source-first attachment ledger. -/
theorem used_attachment_sites_ledger {n : ℕ} (assembly : PL1Assembly n) :
    usedAttachmentSiteCount assembly = sourceTotalAttachmentSites n := by
  letI := assembly.vertexFintype
  letI := assembly.vertexDecidableEq
  calc
    usedAttachmentSiteCount assembly =
        ∑ kind : FragmentKind,
          (Finset.univ.filter fun v => assembly.fragmentKind v = kind).card *
            sourceAttachmentSiteCount kind := by
      rw [usedAttachmentSiteCount,
        ← Finset.sum_fiberwise' Finset.univ assembly.fragmentKind
          sourceAttachmentSiteCount]
      apply Finset.sum_congr rfl
      intro kind _
      rw [Finset.sum_const_nat]
      intro _ _
      rfl
    _ = ∑ kind : FragmentKind,
          sourceFragmentMultiplicity n kind * sourceAttachmentSiteCount kind := by
      apply Finset.sum_congr rfl
      intro kind _
      rw [assembly.inventory kind]
    _ = sourceTotalAttachmentSites n := rfl

/-- Every attachment site is paired with exactly one other site, so the used
site count is twice the number of assembled bonds (the handshaking ledger). -/
theorem attachment_pairing_ledger {n : ℕ} (assembly : PL1Assembly n) :
    usedAttachmentSiteCount assembly = 2 * bondCount assembly := by
  letI := assembly.vertexFintype
  letI := assembly.vertexDecidableEq
  letI := assembly.adjDecidable
  calc
    usedAttachmentSiteCount assembly = ∑ v, assembly.graph.degree v := by
      apply Finset.sum_congr rfl
      intro v _
      exact (assembly.allAttachmentSitesJoined v).symm
    _ = 2 * assembly.graph.edgeFinset.card :=
      assembly.graph.sum_degrees_eq_twice_card_edges
    _ = 2 * bondCount assembly := rfl

/-- A connected acyclic assembly is a tree: its edge count plus one is its
fragment count. -/
theorem acyclic_fragment_bond_ledger {n : ℕ} (assembly : PL1Assembly n) :
    bondCount assembly + 1 = fragmentCount assembly := by
  letI := assembly.vertexFintype
  letI := assembly.vertexDecidableEq
  letI := assembly.adjDecidable
  simpa [bondCount, fragmentCount] using
    assembly.isAcyclicMolecule.card_edgeFinset

/-- The source ledgers in fact determine that exactly one type-a fragment is
present.  This stronger intermediate result is derived, never assumed. -/
theorem typeA_count_eq_one {n : ℕ} (assembly : PL1Assembly n) : n = 1 := by
  have hSource := sourceTotalAttachmentSites_eq n
  have hUsed := used_attachment_sites_ledger assembly
  have hPaired := attachment_pairing_ledger assembly
  have hFragments := fragment_inventory_ledger assembly
  have hTree := acyclic_fragment_bond_ledger assembly
  omega

/-- The requested parity consequence of the source assembly constraints. -/
theorem typeA_count_is_odd {n : ℕ} (assembly : PL1Assembly n) : Odd n := by
  rw [typeA_count_eq_one assembly]
  exact odd_one

/-- A value of `n` is source-feasible precisely when a complete assembly with
the problem's inventory and structural constraints exists. -/
def SourceFeasibleFragmentCount (n : ℕ) : Prop :=
  Nonempty (PL1Assembly n)

/-- Assumption side of the problem contract.  The problem text states that
PL1 can be assembled from the displayed inventory, without supplying the
unknown value of `n`; this field records exactly that existential fact. -/
structure PL1ProblemAssumptions : Prop where
  assemblyExists : ∃ n, SourceFeasibleFragmentCount n

/-- The three classifications printed in T5-A1. -/
inductive FragmentParityChoice where
  | even
  | odd
  | either
  deriving DecidableEq, Repr

/-- Meaning of each printed answer choice over the source-feasible domain.
The `either` case requires witnesses of both parities. -/
def FragmentParityChoice.claim : FragmentParityChoice → Prop
  | .even => ∀ n, SourceFeasibleFragmentCount n → Even n
  | .odd => ∀ n, SourceFeasibleFragmentCount n → Odd n
  | .either =>
      (∃ n, SourceFeasibleFragmentCount n ∧ Even n) ∧
      (∃ n, SourceFeasibleFragmentCount n ∧ Odd n)

/-- Ledger-level certificate for one source-feasible value of `n`. -/
structure FragmentParityDerivation (n : ℕ) (assembly : PL1Assembly n) : Prop where
  sourceSiteLedger : sourceTotalAttachmentSites n = n + 17
  usedSiteLedger :
    usedAttachmentSiteCount assembly = sourceTotalAttachmentSites n
  pairedSiteLedger :
    usedAttachmentSiteCount assembly = 2 * bondCount assembly
  fragmentLedger : fragmentCount assembly = n + 9
  acyclicBondLedger : bondCount assembly + 1 = fragmentCount assembly
  exactTypeACount : n = 1
  parityConclusion : Odd n

/-- Raw solve-phase proposition.  It exposes every decisive ledger for every
source-feasible assembly and uses the source's existence statement to provide
a non-vacuous derived instance, without assuming a value or parity for `n`. -/
def FragmentParityRawSpec : Prop :=
  ∀ _source : PL1ProblemAssumptions,
    (∀ n (assembly : PL1Assembly n), FragmentParityDerivation n assembly) ∧
    (∃ n, ∃ assembly : PL1Assembly n, FragmentParityDerivation n assembly)

/-- A printed choice is correct when the source-feasible domain is nonempty,
its claim holds, and no distinct printed choice has a true claim. -/
def IsCorrectFragmentParityChoice (choice : FragmentParityChoice) : Prop :=
  (∃ n, SourceFeasibleFragmentCount n) ∧
  choice.claim ∧
  ∀ other, other.claim → other = choice

/-- Exact-symbolic reported proposition corresponding to the printed choice
whose claim is forced by the raw source derivation. -/
def FragmentParityReportedSpec : Prop :=
  ∀ _source : PL1ProblemAssumptions,
    IsCorrectFragmentParityChoice .odd

/-- Raw result carrier for `fragment_parity_statement`. -/
theorem fragmentParityRawResult : FragmentParityRawSpec := by
  intro source
  have derive : ∀ n (assembly : PL1Assembly n),
      FragmentParityDerivation n assembly := by
    intro n assembly
    exact
      { sourceSiteLedger := sourceTotalAttachmentSites_eq n
        usedSiteLedger := used_attachment_sites_ledger assembly
        pairedSiteLedger := attachment_pairing_ledger assembly
        fragmentLedger := fragment_inventory_ledger assembly
        acyclicBondLedger := acyclic_fragment_bond_ledger assembly
        exactTypeACount := typeA_count_eq_one assembly
        parityConclusion := typeA_count_is_odd assembly }
  refine ⟨derive, ?_⟩
  obtain ⟨n, ⟨assembly⟩⟩ := source.assemblyExists
  exact ⟨n, assembly, derive n assembly⟩

/-- Reported exact-symbolic result carrier for `fragment_parity_statement`. -/
theorem fragmentParityReportedResult : FragmentParityReportedSpec := by
  intro source
  refine ⟨source.assemblyExists, ?_, ?_⟩
  · intro n feasible
    obtain ⟨assembly⟩ := feasible
    exact typeA_count_is_odd assembly
  · intro other hOther
    cases other with
    | odd => rfl
    | even =>
        obtain ⟨n, ⟨assembly⟩⟩ := source.assemblyExists
        have hEven : Even n := hOther n ⟨assembly⟩
        have hOne : n = 1 := typeA_count_eq_one assembly
        obtain ⟨k, hk⟩ := hEven
        omega
    | either =>
        obtain ⟨⟨n, ⟨assembly⟩, hEven⟩, _⟩ := hOther
        have hOne : n = 1 := typeA_count_eq_one assembly
        obtain ⟨k, hk⟩ := hEven
        omega

end IChO2026Problems.IChO2026T5A1
