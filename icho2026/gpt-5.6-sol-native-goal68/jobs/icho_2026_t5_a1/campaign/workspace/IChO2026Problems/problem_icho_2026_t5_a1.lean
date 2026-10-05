import Mathlib

/-!
# IChO 2026, theory problem 5.1

The problem page depicts fragments with respectively one, two, three, and one
open (wavy) attachment bonds.  Their prescribed multiplicities are `n`, `2`,
`3`, and `4`.  The source also says that these pieces assemble the non-ionised
form of the single, acyclic molecule PL1.

The definitions in `ProblemInput` record only those diagram data and the
ordinary meaning of completing an assembly: every open attachment end belongs
to one newly formed bond, hence the ends occur in pairs.  The answer is then a
derived parity result; it is not stored as an input assumption.
-/

namespace IChO2026Problems.IChO2026T5A1

namespace ProblemInput

/-- Number of open attachment ends on one fragment of each depicted type. -/
def attachmentEndsA : ℕ := 1
def attachmentEndsB : ℕ := 2
def attachmentEndsC : ℕ := 3
def attachmentEndsD : ℕ := 1

/-- Fixed multiplicities printed for fragment types `b`, `c`, and `d`. -/
def copiesB : ℕ := 2
def copiesC : ℕ := 3
def copiesD : ℕ := 4

/-- Total number of wavy attachment ends in the printed inventory. -/
def totalAttachmentEnds (n : ℕ) : ℕ :=
  n * attachmentEndsA + copiesB * attachmentEndsB +
    copiesC * attachmentEndsC + copiesD * attachmentEndsD

/-- Number of separately supplied fragments in the printed inventory. -/
def totalFragments (n : ℕ) : ℕ := n + copiesB + copiesC + copiesD

/-- A completed assembly pairs every attachment end into a newly made bond. -/
def CompleteAssembly (n : ℕ) : Prop :=
  ∃ joinedBonds : ℕ, totalAttachmentEnds n = 2 * joinedBonds

/-- The extra bond-count property of a connected acyclic assembly: joining
`v` initially separate connected pieces into one tree uses `v - 1` joins.
This records the source descriptions "PL1" (one molecule) and "acyclic". -/
structure ConnectedAcyclicAssembly (n : ℕ) where
  joinedBonds : ℕ
  allEndsPaired : totalAttachmentEnds n = 2 * joinedBonds
  treeJoinCount : joinedBonds + 1 = totalFragments n

end ProblemInput

/-- The three statements offered by question 5.1. -/
inductive ParityStatement where
  | even
  | odd
  | either
  deriving DecidableEq, Repr

/-- Meaning of each multiple-choice statement over all fragment counts that
satisfy the necessary complete-assembly condition.  In particular, `either`
means that an even count and an odd count are both compatible, rather than the
pointwise tautology that each natural number has some parity. -/
def ParityStatement.IsCorrect (statement : ParityStatement) : Prop :=
  match statement with
  | .even => ∀ n, ProblemInput.CompleteAssembly n → Even n
  | .odd => ∀ n, ProblemInput.CompleteAssembly n → Odd n
  | .either =>
      (∃ n, ProblemInput.CompleteAssembly n ∧ Even n) ∧
        (∃ n, ProblemInput.CompleteAssembly n ∧ Odd n)

/-- The answer selected for the requested classification output. -/
def selectedStatement : ParityStatement := .odd

namespace Derived

open ProblemInput

theorem totalAttachmentEnds_eq (n : ℕ) :
    totalAttachmentEnds n = n + 17 := by
  simp [totalAttachmentEnds, attachmentEndsA, attachmentEndsB,
    attachmentEndsC, attachmentEndsD, copiesB, copiesC, copiesD]

theorem totalFragments_eq (n : ℕ) : totalFragments n = n + 9 := by
  simp [totalFragments, copiesB, copiesC, copiesD]

/-- Pairing all `n + 17` ends already determines the requested parity; the
specific chemical connectivity and the no-peroxide restriction are not needed
for this necessary condition. -/
theorem completeAssembly_forces_odd {n : ℕ} (h : CompleteAssembly n) : Odd n := by
  rcases h with ⟨joinedBonds, hEnds⟩
  rw [totalAttachmentEnds_eq] at hEnds
  refine ⟨joinedBonds - 9, ?_⟩
  omega

theorem completeAssembly_excludes_even {n : ℕ} (h : CompleteAssembly n) :
    ¬ Even n := by
  rcases completeAssembly_forces_odd h with ⟨oddWitness, hOdd⟩
  rintro ⟨evenWitness, hEven⟩
  omega

theorem one_satisfies_completeAssembly : CompleteAssembly 1 := by
  refine ⟨9, ?_⟩
  norm_num [totalAttachmentEnds, attachmentEndsA, attachmentEndsB,
    attachmentEndsC, attachmentEndsD, copiesB, copiesC, copiesD]

/-- Among the three answer choices, `odd` is uniquely supported by the
complete-assembly invariant. -/
theorem parityStatement_correct_iff (statement : ParityStatement) :
    statement.IsCorrect ↔ statement = .odd := by
  constructor
  · intro hCorrect
    cases statement with
    | even =>
        exfalso
        have hEvenOne : Even 1 := hCorrect 1 one_satisfies_completeAssembly
        rcases hEvenOne with ⟨witness, hWitness⟩
        omega
    | odd => rfl
    | either =>
        exfalso
        rcases hCorrect.1 with ⟨n, hAssembly, hEven⟩
        exact completeAssembly_excludes_even hAssembly hEven
  · rintro rfl
    intro n hAssembly
    exact completeAssembly_forces_odd hAssembly

/-- The connected-acyclic information on the page yields the stronger value
`n = 1`, consistently with (and more than is required for) the parity choice. -/
theorem connectedAcyclicAssembly_forces_n_eq_one {n : ℕ}
    (h : ConnectedAcyclicAssembly n) : n = 1 := by
  have hEnds := h.allEndsPaired
  have hTree := h.treeJoinCount
  rw [totalAttachmentEnds_eq] at hEnds
  rw [totalFragments_eq] at hTree
  omega

theorem connectedAcyclicAssembly_forces_odd {n : ℕ}
    (h : ConnectedAcyclicAssembly n) : Odd n := by
  rw [connectedAcyclicAssembly_forces_n_eq_one h]
  exact ⟨0, rfl⟩

/-- Requested output `fragment_parity_statement`: option (b), "`n` is odd",
is the unique statement supported by completed PL1 assemblies. -/
theorem fragment_parity_statement :
    selectedStatement = .odd ∧ selectedStatement.IsCorrect := by
  refine ⟨rfl, ?_⟩
  intro n hAssembly
  exact completeAssembly_forces_odd hAssembly

end Derived

end IChO2026Problems.IChO2026T5A1

#print axioms IChO2026Problems.IChO2026T5A1.Derived.completeAssembly_forces_odd
#print axioms IChO2026Problems.IChO2026T5A1.Derived.parityStatement_correct_iff
#print axioms IChO2026Problems.IChO2026T5A1.Derived.connectedAcyclicAssembly_forces_n_eq_one
#print axioms IChO2026Problems.IChO2026T5A1.Derived.fragment_parity_statement
