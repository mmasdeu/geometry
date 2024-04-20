import Game.Metadata

World "TutorialWorld"
Level 4

Title "The `apply` tactic"
TheoremTab "∈"
Introduction
"
# Tutorial World

## The `apply` tactic.

In this level, we learn the `apply` tactic, which solves a goal that coincides with the conclusion of
one of the hypotheses
or a known theorem.
For example, if the finishing goal is ⊢ `A = B` and we have the hypothesis `h : ℓ = r → A = B`, then `apply h`
will leave you to proving `⊢ ℓ = r`. If there are no leftover proofs, then it will solve the level.

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
  apply h2

Conclusion
"Great!"

NewTactic apply

NewDefinition IncidencePlane.line_through
NewTheorem IncidencePlane.line_through_left IncidencePlane.line_through_right
