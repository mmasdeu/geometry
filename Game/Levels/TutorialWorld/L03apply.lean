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
"

open Set IncidencePlane --hide

variable {Ω : Type} [IncidencePlane Ω] --hide

/--
A lemma involving lines and points.
-/
Statement (A B C: Ω) (r s : Line Ω) (h : r = s) (h1 : A = B) (h3 : r = s → B = C) : A = C := by
  rw [h1]
  apply h3
  assumption

Conclusion
"Great!"

NewTactic apply

NewDefinition IncidencePlane.line_through
NewTheorem IncidencePlane.line_through_left IncidencePlane.line_through_right
