import Game.Metadata
import Game.Levels.BetweennessWorld.level05

open IncidencePlane --hide



World "BetweeenessWorld"
Level 6

Title "Betweenness has no favourite side"

Introduction
"
Time to meet another axiom: `A * B * C ↔ C * B * A`, known as `between_symmetric`.
If you `rw` with it at the start of the proof, you can reduce to the previous lemma, `mem_line_through_of_between_3`.
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
  apply mem_line_through_of_between_3 h

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

Conclusion "On to the next level! We'll hand you the variations of this one for free,
since they're proved in a very similar way."

TheoremTab "· * · * ·"
