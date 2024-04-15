import Game.Metadata
import Game.Levels.BetweennessWorld.level04

open IncidencePlane --hide



World "BetweeenessWorld"
Level 5

Title "Another version of the previous level"

Introduction
"
This version may also be useful later
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

/--
Given three points A B C such that A * B * C, the third one is in the line through the others.
-/
Statement mem_line_through_of_between_3 (h : A * B * C) : C ∈ line_through A B := by
  rcases (collinear_of_between h) with ⟨ℓ, hAℓ, hBℓ, hCℓ⟩
  have hAB : A ≠ B := different_of_between_12 h
  have h' : ℓ = line_through A B := incidence hAB hAℓ hBℓ
  rw [←h']
  assumption

Conclusion "Now on to the next level! We will add for you variations of this one that are proved in
a very similar way."
