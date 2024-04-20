import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level02

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "PlaneSeparationWorld"
Level 3

Title "Who is on the same side?"

Introduction
"
In this level we prove that being on the same side of a line is a symmetric concept. We only
ask you to prove one implication, the double implication is done in the same way and it will
be given to you for free in the Theorem list.
"


/--
A is at the same side as B of ℓ if and only if B is at the same side of A of ℓ.
-/
Statement : same_side ℓ A B → same_side ℓ B A:= by
  intro h
  simp at h ⊢
  simp [h]
  intro x hx
  rw [between_symmetric]
  apply h.2.2 x hx

lemma same_side_symmetric' : same_side ℓ A B → same_side ℓ B A:= by
  intro h
  simp at h ⊢
  simp [h]
  intro x hx
  rw [between_symmetric]
  apply h.2.2 x hx

theorem same_side_symmetric : same_side ℓ A B ↔ same_side ℓ B A
:= ⟨same_side_symmetric', λ h ↦ same_side_symmetric' h⟩

NewTheorem same_side_symmetric
TheoremTab "PSep"
