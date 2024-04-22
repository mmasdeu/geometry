import Game.Metadata
import Game.Levels.IncidenceWorld

open IncidencePlane --hide


World "BetweeenessWorld"
Level 1

Title "Ordering matters"

Introduction
"
To solve this level, you will need to use two axioms of order.
You will notice that the list of theorems has been expanded. Take a look at the new
theorems and try to think of a mathematical proof in paper before typing your solution in Lean.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C : Ω} --hide

/--
Given three distinct collinear points A, B and C, if B lies between A and C, then A does not lie between B and C.
-/
Statement not_between_of_between : (A * B * C) → (B * A * C) → False := by
  intro h
  have h2 := between_of_collinear (collinear_of_between h)
  tauto

NewTheorem IncidencePlane.collinear_of_between IncidencePlane.between_of_collinear
TheoremTab "· * · * ·"
