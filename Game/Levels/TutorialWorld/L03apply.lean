import Game.Metadata

World "TutorialWorld"
Level 4

Title "The `apply` tactic"
TheoremTab "∈"
Introduction
"
## The `apply` tactic

Now for `apply`. It works when your goal matches the conclusion of a hypothesis
or of a known theorem.
For example, if your goal is `⊢ A = B` and you have `h : ℓ = r → A = B`, then `apply h`
leaves you with the goal `⊢ ℓ = r`. If nothing is left to prove, the level is solved.
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
