import Game.Metadata
import Game.Levels.TutorialWorld
open IncidencePlane --hide

World "IncidenceWorld"
Level 1

Title "The symmetry of the line through two points"

variable {Ω : Type} [IncidencePlane Ω] --hide


Introduction
"
In this level, we introduce the `by_cases` tactic. Mathematicians would use it to provide a *proof by cases*.
This is useful when we need to split a proof into different cases.

In the proof below there is a `trivial` case that we have to consider, which is the possibility
that `P = Q`. In If we type `by_cases h : P = Q` we will split the goal into two branches: the first one
will have the assumption `h : P = Q` in the context, while in the second we will have `h : P ≠ Q`.
"

variable {Ω : Type} [IncidencePlane Ω] -- hide
variable {P Q : Ω} -- hide

/--
The line through two points is a symmetric concept.
-/
Statement line_through_symmetric : line_through Q P = line_through P Q := by
  by_cases h : P = Q
  · rw [h]
  · exact incidence h (line_through_right Q P) (line_through_left Q P)

NewTheorem line_through_symmetric
NewTactic by_cases
