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
This is the fourth and last lemma that we need to prove before jumping into the final level of the game!
"


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide


/--
If two points A and C are not on the same side of the line ℓ, there exists a point in the segment A·C which is incident with the line ℓ.
-/
Statement not_same_side_intersection (h : ¬ same_side ℓ A C) : ∃ P , (P = A ∨ P = C ∨ (A * P * C)) ∧ P ∈ ℓ := by
  by_contra hlAC
  simp at hlAC
  apply h
  rw [same_side]
  tauto

TheoremTab "PSep"
