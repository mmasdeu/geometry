import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level04

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "PlaneSeparationWorld"
Level 5

Title "On the way to the final level (IV)"


open scoped Classical

Introduction
"
This is the last small lemma before the big ones. If two points are *not* on the same side of ℓ, then ℓ must touch the segment between them
(or pass through one of the points themselves).
"


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide


/--
If A and C are not on the same side of the line ℓ, then there is a point P on ℓ which is either A, or C, or lies strictly between them.
-/
Statement not_same_side_intersection (h : ¬ same_side ℓ A C) : ∃ P , (P = A ∨ P = C ∨ (A * P * C)) ∧ P ∈ ℓ := by
  by_contra hlAC
  simp at hlAC
  apply h
  rw [same_side]
  tauto

TheoremTab "PSep"
