import Game.Metadata

World "TutorialWorld"
Level 4

Title "The `exact` tactic"

Introduction
"
# Tutorial World

## The `exact` tactic.

In this level, we learn the `exact` tactic, which solves a goal that is exactly one of the hypotheses.
For example, if the finishing goal is ⊢ `A = B` and we have the hypothesis `z : A = B`, then `exact z`
will complete the level.

This level is a new variant of the the previous one, but we will solve it in a different way. As you can imagine,
mathematical proofs can be solved in many differents ways, which is something that definitely makes this field special.
"

open Set IncidencePlane --hide

variable {Ω : Type} [IncidencePlane Ω] --hide

/--
If A, B and C are points with A = B and B = C, then A = C.
-/
Statement (A B C: Ω) (h1 : A = B) (h2 : B = C) : A = C := by
  rw [h1]
  exact h2

Conclusion
"Great!"

NewTactic exact

NewDefinition IncidencePlane.line_through
NewTheorem IncidencePlane.line_through_left IncidencePlane.line_through_right
