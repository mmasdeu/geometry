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
Here we show that being on the same side is symmetric: if A is on the same side as B, then B is on the same side as A.
You only need to prove one implication. The other one works the same way, so we'll hand you the full
`↔` for free in the Theorem list.

Tip: `between_symmetric` (from the previous world) turns `A * B * C` into `C * B * A` with `rw`.
"


/--
A is on the same side of ℓ as B if and only if B is on the same side of ℓ as A.
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
