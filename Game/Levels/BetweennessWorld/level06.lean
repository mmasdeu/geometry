import Game.Metadata
import Game.Levels.BetweennessWorld.level05

open IncidencePlane --hide



World "BetweeenessWorld"
Level 6

Title "Between knows no sides"

Introduction
"
In order to prove this variation, we will practice the use of  another axiom, namely the fact that
A * B * C ↔ C * B * A. This axiom is known as `between_symmetric`, and if you `rw` it at the
beginning of the next proof then you will be able to reduce to the previous version of the lemma.
 fact hta t
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

/- Lemma :
Given three points A B C such that A * B * C, the first one is in the line through the others.
-/
Statement mem_line_through_of_between_1 (h : A * B * C) : A ∈ line_through B C:= by
  rw [between_symmetric] at h
  rw [line_through_symmetric]
  exact mem_line_through_of_between_3 h

/- Lemma :
Given three points A B C such that A * B * C, the second one is in the line through the others.
-/
lemma mem_line_through_of_between_2 (h : A * B * C) : B ∈ line_through A C:= by
  rcases (collinear_of_between h) with ⟨ℓ, hAℓ, hBℓ, hCℓ⟩
  have hAB : A ≠ C := different_of_between_13 h
  have h' : ℓ = line_through A C := incidence hAB hAℓ hCℓ
  rw [←h']
  assumption

NewTheorem IncidencePlane.between_symmetric mem_line_through_of_between_2

Conclusion "Now on to the next level! We will add for you variations of this one that are proved in
a very similar way."
