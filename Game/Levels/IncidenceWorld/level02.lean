import Game.Metadata
import Game.Levels.IncidenceWorld.level01
open IncidencePlane --hide

World "IncidenceWorld"
Level 3

Title "The `by_contra` tactic"

variable {Ω : Type} [IncidencePlane Ω] --hide


Introduction
"
Congratulations! You are about to finish the second world of The Euclid Game!
In this level, we introduce the `by_contra` tactic. Mathematicians would use
it to provide a **proof by contradiction**. This tactic changes the goal from
`⊢ P` to `⊢ false` and adds a new hypothesis of the form `h : ¬ P` to the local context.

To finish this world, we would like to prove that two distinct lines have **at most**
one point in common. Delete the `sorry` to see the goal appear as `⊢ A = B`. Now, take a look
to the hypotheses that we have in our local context and try to do a drawing of the situation
by using all of them. Once you're done, note that the points A and B must be equal so that the
lines r and s satisfy the hypothesis `hrs: r ≠ s`. Then, try to look for a theorem statement which
could be useful for this level. As you've well deduced, `equal_lines_of_contain_two_points`
is the right path to choose. However, note that it states `A ≠ B` and `r = s` instead of `A = B`and
`r ≠ s`, respectively. Because of this, the `by_contra` tactic has to join the party.
"


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} --hide
variable {r s : Line Ω} --hide

/--
If points A and B are both in distinct lines r and s, then A = B.
-/
Statement equal_points_of_in_two_lines
(hrs: r ≠ s) (hAr: A ∈ r) (hBr: B ∈ r) (hAs: A ∈ s) (hBs: B ∈ s) : A = B := by
  Hint "Try to start a proof by contradiction here, by using the `by_contra` tactic."
  by_contra hc
  Hint "Use the new assumption `{hc}` to prove that `r = s`."
  have h : r = s := equal_lines_of_contain_two_points hc hAr hBr hAs hBs
  Hint "You have a contradiction now, the `tauto` tactic should do."
  tauto

NewTactic by_contra
TheoremTab "∈"
