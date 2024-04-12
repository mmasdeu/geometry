import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level06

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "PlaneSeparationWorld"
Level 7

Title "On the way to the final level (III)"

Introduction
"
This is the third of five lemmas that we need to prove before jumping into the final level of the game! You will be provided with
its mathematical proof in paper right below. Remember that you can use all the theorem statements from the left-hand side box.

## Mathematical proof in paper...

**Claim:** Given a line ℓ and the segments A·B and B·C, if both segments are on the same side of ℓ, then `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`.

**Proof:**

By the lemma `not_in_line_of_same_side_left`, since the points A and B are on the same side of ℓ, then `A ∉ ℓ`.

By the lemma `not_in_line_of_same_side_right`, since the points A and B are on the same side of ℓ, then `B ∉ ℓ`.

By the lemma `not_in_line_of_same_side_right`, since the points B and C are on the same side of ℓ, then `C ∉ ℓ`.

Hence, we have shown that `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

/--
Given a line ℓ and the segments A·B and B·C, if both segments are on the same side of ℓ, then `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`.
-/
Statement same_side_of_noncollinear_ne_line (hlAB : same_side ℓ A B) (hlBC : same_side ℓ B C) :
A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ := by
  constructor
  · apply not_in_line_of_same_side_left hlAB
  constructor
  · apply not_in_line_of_same_side_right hlAB
  · apply not_in_line_of_same_side_right hlBC
