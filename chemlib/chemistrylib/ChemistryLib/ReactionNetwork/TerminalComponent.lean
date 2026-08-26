import ChemistryLib.ReactionNetwork.Basic
import ChemistryLib.ReactionNetwork.Graph

/-!
# Terminal strong components

A terminal strong component is a nonempty strong linkage class from which no
reaction leaves.  These components index the terminal classes used in the
kernel decomposition of a reaction graph.

The definition follows the graph-theoretic setup in GUNAWARDENA-2003,
Sections 3–4 and Theorem 4.2 (source corpus SHA-256
`f191f4cdfe12d2a6bf5f91ce1e3358a12780f12a4b6f296b0b095f0fa42fd530`).
-/

namespace ChemistryLib.ReactionNetwork

/-- A nonempty strong linkage class with no reaction edge leaving it. -/
def IsTerminalStrongComponent
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (C : Finset ComplexId) : Prop :=
  C.Nonempty ∧
    (∀ a, a ∈ C → ∀ b, b ∈ C ↔ N.SameStrongLinkageClass a b) ∧
    ∀ r, N.source r ∈ C → N.target r ∈ C

/-- The type of terminal strong components of a finite reaction graph. -/
abbrev TerminalStrongComponent
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) : Type :=
  {C : Finset ComplexId // IsTerminalStrongComponent N C}

/-- A finite reaction graph has finitely many terminal strong components. -/
noncomputable instance terminalStrongComponentFintype
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    Fintype (TerminalStrongComponent N) :=
  Fintype.ofFinite _

/-- Membership of a complex in a terminal strong component. -/
def terminalStrongComponentMem
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId)
    (C : TerminalStrongComponent N) (c : ComplexId) : Prop :=
  c ∈ C.1

/-- Distinct terminal strong components have no complex in common. -/
theorem terminalStrongComponents_disjoint
    {Species ComplexId ReactionId : Type}
    [Fintype ComplexId] [DecidableEq ComplexId]
    (N : ChemistryLib.ReactionNetwork Species ComplexId ReactionId) :
    ∀ C D : TerminalStrongComponent N, C ≠ D →
      Disjoint (C.1 : Set ComplexId) (D.1 : Set ComplexId) := by
  intro C D hCD
  rw [Set.disjoint_left]
  intro c hcC hcD
  apply hCD
  apply Subtype.ext
  apply Finset.ext
  intro x
  exact (C.2.2.1 c hcC x).trans (D.2.2.1 c hcD x).symm

end ChemistryLib.ReactionNetwork
