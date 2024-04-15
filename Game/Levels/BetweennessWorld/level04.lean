import Game.Metadata
import Game.Levels.BetweennessWorld.level03

open IncidencePlane --hide



World "BetweeenessWorld"
Level 4

Title "Another version of the previous level"

Introduction
"
You can try this variation of the previous lemma on your own.
Remember that it's best to have a paper proof before you start typing!
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

/--
Given two different collinear points A and B, there is a third C that shares the same line with them and satisfies A * B * C.
-/
Statement between_points_share_line_1 (h : A * B * C) (hAr : B ∈ r) (hBr : C ∈ r) : A ∈ r := by
    have h1 : B ≠ C := different_of_between_23 h
    have h2 : ∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ := collinear_of_between h
    rcases h2 with ⟨s, hs⟩
    have h3 : r = s
    · apply equal_lines_of_contain_two_points h1
    rw [h3]
    exact hs.1

/--
Given two different collinear points A and B, there is a third C that shares the same line with them and satisfies A * B * C.
-/
theorem between_points_share_line_3 (h : A * B * C) (hAr : A ∈ r) (hBr : B ∈ r) : C ∈ r := by
    have h1 : A ≠ B := different_of_between_12 h
    have h2 : ∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ := collinear_of_between h
    rcases h2 with ⟨s, hs⟩
    have h3 : r = s
    · apply equal_lines_of_contain_two_points h1
    rw [h3]
    exact hs.2.2

NewTheorem between_points_share_line_1 between_points_share_line_3
