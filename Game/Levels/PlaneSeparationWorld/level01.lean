import Game.Metadata
import Game.Levels.BetweennessWorld

open IncidencePlane --hide


World "PlaneSeparationWorld"
Level 1

Title "Same side"

Introduction
"
Thanks to the Pash axiom we can define what *being on the same side* means.

**Definition:** Given a line ℓ and the points A and B, such that A, B ∉ ℓ, we say that A and B are on the same side if
the segment A·B does not meet ℓ or A = B.

In Lean, the definition of `same_side` is represented as follows:

* `def same_side (ℓ : Line Ω) (P Q : Ω) :=  P ∉ ℓ ∧ Q ∉ ℓ ∧ (∀ x, (P * x * Q) → x ∉ ℓ)`


[**Rule of thumb:** Whenever you see `same_side` in Lean, you may use the `rw` tactic to unfold its definition. In this way, it will be easier to understand what it means. If it is
located at the hypothesis `h2`, for example, then `rw [same_side] at h2` will make progress. If it is located at the goal, then `rw [same_side]` will be enough
to rewrite the goal.

As a bonus, we have added a useful lemma (you could prove it easily at this stage, we
are just saving you some time) that allows to change the order of the points that
appear in a collinearity statement

* `lemma collinear_of_equal (A B C D E F)
  ({A, B, C} = {D, E, F}) → collinear A B C ↔ collinear D E F`

Lean will help you by filling in the proof of the two sets being equal, when this is trivially true.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} --hide
variable {ℓ : Line Ω} --hide

/--
If the segment $PQ$ is on the same side of a line $\ell$, then $P \notin ℓ$.
-/
Statement not_in_line_of_same_side_left (h : same_side ℓ A B) : A ∉ ℓ := by
  rw [same_side] at h
  tauto


lemma not_in_line_of_same_side_right (h : same_side ℓ A B) : B ∉ ℓ := by
  rw [same_side] at h
  tauto

NewDefinition IncidencePlane.same_side
NewTheorem IncidencePlane.collinear_of_equal not_in_line_of_same_side_left not_in_line_of_same_side_right
