import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level05

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "PlaneSeparationWorld"
Level 6

Title "On the way to the final level (II)"

Introduction
"This is the second of five lemmas that we need to prove before jumping into the final level of the game! You will be provided with
its mathematical proof in paper right below. Remember that you can use all the theorem statements from the left-hand side box.

## Mathematical proof in paper...

**Claim:** Given three non-collinear points A, B and C, then B is not incident with the line through A and C.

**Proof:**

By the lemma `noncollinear_ne_points`, since A, B and C are non-collinear points, then `A ≠ C`.

By the lemma `collinear_iff_on_line_through`, since `A ≠ C`, then it suffices to prove that the points A, C, B are not collinear.

By the assumption of the lemma `hCol : ¬ collinear ({A, C, B} : set Ω))`, then we show that `B ∉ line_through A C`.
"

/- Hint : Click here for a hint, in case you get stuck.
If you have a theorem statement called `theorem`, which shows `x` by using the hypothesis `h : P`, then `have ht := theorem h` will
add the hypothesis `hth : x` to the local context.
-/


/--
Given three non-collinear points A, B and C, then B is not incident with the line through A and C.
-/
Statement not_mem_line_of_noncollinear (hCol : ¬ collinear A C B) : B ∉ line_through A C := by
  have hAC := neq_points_of_noncollinear hCol
  rw [← collinear_iff_on_line_through hAC]
  exact hCol
