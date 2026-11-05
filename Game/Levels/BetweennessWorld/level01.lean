import Game.Metadata
import Game.Levels.IncidenceWorld

open IncidencePlane --hide


World "BetweeenessWorld"
Level 1

Title "Ordering matters"

Introduction
"
This level needs two axioms of order: `collinear_of_between` (if `A * B * C` then the three points lie on a common line)
and `between_of_collinear` (see the *Theorems* tab for the exact statements).
The theorem list just grew, so have a peek at the new entries.
And as always, try to sketch the proof on paper before typing it in Lean!
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
