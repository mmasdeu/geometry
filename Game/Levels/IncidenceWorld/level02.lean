import Game.Metadata
import Game.Levels.IncidenceWorld.level01
open IncidencePlane --hide

World "IncidenceWorld"
Level 2

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
`r ≠ s`, respectively. Because of this reason, the `by_contra` tactic has to join the party.

Now, try to solve this level on your own in just three lines of code. [**Remember:** whenever you see
a hypothesis of the form `h : P ≠ Q`, Lean can also understand it as `h : ¬ (P = Q)`, or `h : (P = Q) → false`.]
"


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} --hide
variable {r s : Line Ω} --hide

/--
Two distinct lines have at most one point in common.
-/
Statement
(hrs: r ≠ s)
(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :
A = B := by
  by_contra hc
  have h : r = s := equal_lines_of_contain_two_points hc
  tauto

theorem equal_points_of_in_two_lines
{r s : outParam (Line Ω) } (hrs: r ≠ s) (hAr: A ∈ r := by simp [*]) (hAs: A ∈ s := by simp [*]) (hBr: B ∈ r := by simp [*]) (hBs: B ∈ s := by simp [*]) :
A = B := by
  by_contra hc
  have h : r = s := equal_lines_of_contain_two_points hc
  tauto

NewTactic by_contra
NewTheorem equal_points_of_in_two_lines
