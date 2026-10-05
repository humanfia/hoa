import Ipho2026Gpt56solBlind.Shared.GeometricOptics
import Mathlib.Tactic
import Physlib.Units.SIUnitChoices
import Physlib.Units.WithDim.Basic

/-!
# Exact half-disk ray traces

This module specializes the common geometric-optics kernel to an
aperture-owned half-disk cavity, with ordered mirror contacts and a final
aperture exit.
-/

noncomputable section

namespace Ipho2026Gpt56solBlind.Shared.GeometricOptics

/-! ## Aperture-owned half-disk cavities and ordered traces -/

/-- A half-disk cavity whose two rims belong to the aperture. -/
structure HalfDiskCavity where
  circle : Circle
  orientation : VerticalOrientation

/-- The aperture-owned semicircle associated to a half-disk cavity. -/
def HalfDiskCavity.toSemicircle (H : HalfDiskCavity) : Semicircle :=
  { circle := H.circle, orientation := H.orientation, rims := .aperture }

/-- ISQ-typed half-disk cavity data. -/
structure PhysicalHalfDiskCavity (u : SIUnitChoices) where
  circle : PhysicalCircle u
  orientation : VerticalOrientation

/-- Scalar coherent-SI representation of a physical half-disk cavity. -/
def physicalHalfDiskCavityCoordinateInSI (u : SIUnitChoices)
    (H : PhysicalHalfDiskCavity u) : HalfDiskCavity :=
  { circle := physicalCircleCoordinateInSI u H.circle
    orientation := H.orientation }

/-- Ordered first contact with the optical boundary of a half-disk cavity. -/
def IsFirstCavityContact (H : HalfDiskCavity) (r : ForwardRay)
    (s : Length) (Q : Point2) : Prop :=
  IsFirstForwardBoundaryContact
    (InSemicircleInterior H.toSemicircle)
    (OnSemicircleBoundary H.toSemicircle) r s Q

/-- Every cavity first contact is exactly one of an aperture exit or mirror hit. -/
theorem firstCavityContact_partition (H : HalfDiskCavity) (r : ForwardRay)
    {s : Length} {Q : Point2} (h : IsFirstCavityContact H r s Q) :
    (OnAperture H.toSemicircle Q ∨ OnReflectingArc H.toSemicircle Q) ∧
      ¬(OnAperture H.toSemicircle Q ∧ OnReflectingArc H.toSemicircle Q) := by
  have hBoundary : OnSemicircleBoundary H.toSemicircle Q := h.2.2.1
  constructor
  · rcases hBoundary with hMirror | hAperture
    · exact Or.inr hMirror
    · exact Or.inl hAperture
  · rintro ⟨hAperture, hMirror⟩
    exact (boundary_partition H.toSemicircle Q).1 ⟨hMirror, hAperture⟩

/-- The two kinds of events in a finite exact cavity trace. -/
inductive CavityTraceEvent
  | mirrorHit (point : Point2)
  | exit (point : Point2)
deriving DecidableEq

/-- Recursive finite trace: ordered mirror contacts followed by one aperture exit. -/
inductive ExactCavityTrace (H : HalfDiskCavity) :
    ForwardRay → ℕ → List CavityTraceEvent → Prop
  | exit {r : ForwardRay} {s : Length} {Q : Point2}
      (contact : IsFirstCavityContact H r s Q)
      (atAperture : OnAperture H.toSemicircle Q) :
      ExactCavityTrace H r 0 [CavityTraceEvent.exit Q]
  | reflection {r : ForwardRay} {s : Length} {Q : Point2}
      {n : ℕ} {events : List CavityTraceEvent}
      (contact : IsFirstCavityContact H r s Q)
      (atMirror : OnReflectingArc H.toSemicircle Q)
      (tail : ExactCavityTrace H
        (rayAfterReflection H.circle r Q atMirror.1) n events) :
      ExactCavityTrace H r (n + 1) (CavityTraceEvent.mirrorHit Q :: events)

namespace ExactCavityTrace

/-- An exact trace has `n` mirror events followed by exactly one exit event. -/
theorem invariants {H : HalfDiskCavity} {r : ForwardRay} {n : ℕ}
    {events : List CavityTraceEvent} (h : ExactCavityTrace H r n events) :
    ∃ (hits : List Point2) (exitPoint : Point2),
      hits.length = n ∧
        events = hits.map CavityTraceEvent.mirrorHit ++ [CavityTraceEvent.exit exitPoint] := by
  induction h with
  | @exit r s Q contact atAperture =>
      exact ⟨[], Q, by simp⟩
  | @reflection r s Q n events contact atMirror tail ih =>
      rcases ih with ⟨hits, exitPoint, hLength, hEvents⟩
      refine ⟨Q :: hits, exitPoint, ?_, ?_⟩
      · simp [hLength]
      · simp [hEvents]

end ExactCavityTrace

/-- A fixed cavity and initial ray determine every finite exact trace. -/
theorem exactCavityTrace_unique (H : HalfDiskCavity) (r : ForwardRay)
    {n₁ n₂ : ℕ} {events₁ events₂ : List CavityTraceEvent}
    (h₁ : ExactCavityTrace H r n₁ events₁)
    (h₂ : ExactCavityTrace H r n₂ events₂) :
    n₁ = n₂ ∧ events₁ = events₂ := by
  have contact_unique :
      ∀ {ray : ForwardRay} {s₁ s₂ : Length} {Q₁ Q₂ : Point2},
        IsFirstCavityContact H ray s₁ Q₁ →
        IsFirstCavityContact H ray s₂ Q₂ →
        s₁ = s₂ ∧ Q₁ = Q₂ := by
    intro ray s₁ s₂ Q₁ Q₂ contact₁ contact₂
    exact firstForwardBoundaryContact_unique
      (InSemicircleInterior H.toSemicircle)
      (OnSemicircleBoundary H.toSemicircle)
      (fun P hInterior hBoundary =>
        interior_disjoint_boundary H.toSemicircle P ⟨hInterior, hBoundary⟩)
      ray contact₁ contact₂
  induction h₁ generalizing n₂ events₂ with
  | @exit r₁ s₁ Q₁ contact₁ atAperture₁ =>
      cases h₂ with
      | @exit r₂ s₂ Q₂ contact₂ atAperture₂ =>
          rcases contact_unique contact₁ contact₂ with ⟨_, hQ⟩
          subst Q₂
          exact ⟨rfl, rfl⟩
      | @reflection r₂ s₂ Q₂ n events contact₂ atMirror₂ tail₂ =>
          rcases contact_unique contact₁ contact₂ with ⟨_, hQ⟩
          subst Q₂
          exact False.elim
            ((boundary_partition H.toSemicircle Q₁).1
              ⟨atMirror₂, atAperture₁⟩)
  | @reflection r₁ s₁ Q₁ n₁ events₁ contact₁ atMirror₁ tail₁ ih =>
      cases h₂ with
      | @exit r₂ s₂ Q₂ contact₂ atAperture₂ =>
          rcases contact_unique contact₁ contact₂ with ⟨_, hQ⟩
          subst Q₂
          exact False.elim
            ((boundary_partition H.toSemicircle Q₁).1
              ⟨atMirror₁, atAperture₂⟩)
      | @reflection r₂ s₂ Q₂ n₂ events₂ contact₂ atMirror₂ tail₂ =>
          rcases contact_unique contact₁ contact₂ with ⟨_, hQ⟩
          subst Q₂
          rcases ih tail₂ with ⟨hn, hEvents⟩
          exact ⟨congrArg (fun n => n + 1) hn,
            congrArg (List.cons (CavityTraceEvent.mirrorHit Q₁)) hEvents⟩

/-- A ray has an exact finite trace with the specified reflection count. -/
def ExitsAfter (H : HalfDiskCavity) (r : ForwardRay) (n : ℕ) : Prop :=
  ∃ events, ExactCavityTrace H r n events

/-- Axial incident ray launched from the aperture coordinate `x`. -/
def incidentCavityRay (H : HalfDiskCavity) (x : Length) : ForwardRay :=
  { origin := { x := H.circle.center.x + x, y := H.circle.center.y }
    direction := axisDirection H.orientation }

/-- Strict non-rim domain of an aperture coordinate. -/
def IsIncidentCoordinate (H : HalfDiskCavity) (x : Length) : Prop :=
  |x| < H.circle.radius

/-- Exact reflection-count predicate for an axial cavity ray. -/
def HasReflectionCount (H : HalfDiskCavity) (x : Length) (n : ℕ) : Prop :=
  IsIncidentCoordinate H x ∧ ExitsAfter H (incidentCavityRay H x) n

/-- Bounded reflection-count predicate. -/
def HasAtMostReflections (H : HalfDiskCavity) (x : Length) (N : ℕ) : Prop :=
  ∃ n ≤ N, HasReflectionCount H x n

/-! ## Reflection thresholds -/

/-- Nonnegative absolute incident distances satisfying a reflection bound. -/
def AdmissibleDistances (H : HalfDiskCavity) (N : ℕ) : Set ℝ :=
  {d | 0 ≤ d ∧ ∃ x : Length, |x| = d ∧ HasAtMostReflections H x N}

/-- An attained maximal admissible distance strictly between axis and rim. -/
def IsThreshold (H : HalfDiskCavity) (N : ℕ) (T : Length) : Prop :=
  0 < T ∧ T < H.circle.radius ∧ T ∈ AdmissibleDistances H N ∧
    ∀ d ∈ AdmissibleDistances H N, d ≤ T

/-- An attained reflection threshold is unique when it exists. -/
theorem isThreshold_unique (H : HalfDiskCavity) (N : ℕ)
    {T₁ T₂ : Length} (h₁ : IsThreshold H N T₁) (h₂ : IsThreshold H N T₂) :
    T₁ = T₂ := by
  apply le_antisymm
  · exact h₂.2.2.2 T₁ h₁.2.2.1
  · exact h₁.2.2.2 T₂ h₂.2.2.1

/-- Either rim point is an aperture contact and not a reflecting-arc contact. -/
theorem cavity_rim_is_exit (H : HalfDiskCavity) (Q : Point2)
    (hRim :
      (Q = { x := H.circle.center.x - H.circle.radius,
             y := H.circle.center.y }) ∨
      (Q = { x := H.circle.center.x + H.circle.radius,
             y := H.circle.center.y })) :
    OnAperture H.toSemicircle Q ∧ ¬ OnReflectingArc H.toSemicircle Q := by
  rcases hRim with rfl | rfl
  · constructor
    · simp [OnAperture, HalfDiskCavity.toSemicircle,
        abs_of_pos H.circle.radius_pos]
    · simp [OnReflectingArc, HalfDiskCavity.toSemicircle]
  · constructor
    · simp [OnAperture, HalfDiskCavity.toSemicircle,
        abs_of_pos H.circle.radius_pos]
    · simp [OnReflectingArc, HalfDiskCavity.toSemicircle]

end Ipho2026Gpt56solBlind.Shared.GeometricOptics
