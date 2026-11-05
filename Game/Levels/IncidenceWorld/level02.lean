import Game.Metadata
import Game.Levels.IncidenceWorld.level01
open IncidencePlane --hide

World "IncidenceWorld"
Level 3

Title "The `by_contra` tactic"

variable {Ω : Type} [IncidencePlane Ω] --hide


Introduction
"
Congratulations, you're about to finish the second world of The Euclid Game!
Here comes the `by_contra` tactic, the Lean way of doing a **proof by contradiction**. It changes the goal from
`⊢ P` to `⊢ false` and adds a new hypothesis `h : ¬ P` to the local context.

Let's prove that two distinct lines have **at most** one point in common. Delete the `sorry` to see the
goal `⊢ A = B`. Now look at the hypotheses in your context and try to sketch the situation on paper using all of them.
Once you have it, notice that `A` and `B` must be equal, otherwise the lines `r` and `s` would be forced to be the
same, against `hrs: r ≠ s`. Which theorem could help? Spot on: `equal_lines_of_contain_two_points`.
But careful, it talks about `A ≠ B` and concludes `r = s`, while here we have `A = B` as goal and `r ≠ s` as hypothesis.
That's exactly why `by_contra` has to join the party.

```
   r     s
    \\   /
      X       two lines meet in at most one point
    /   \\
```
"


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} --hide
variable {r s : Line Ω} --hide

/--
If points A and B are both in distinct lines r and s, then A = B.
-/
Statement equal_points_of_in_two_lines
(hrs: r ≠ s) (hAr: A ∈ r) (hBr: B ∈ r) (hAs: A ∈ s) (hBs: B ∈ s) : A = B := by
  Hint "Start a proof by contradiction here, using the `by_contra` tactic."
  by_contra hc
  Hint "Use the new assumption `{hc}` to prove that `r = s`."
  have h : r = s := equal_lines_of_contain_two_points hc hAr hBr hAs hBs
  Hint "That's a contradiction! The `tauto` tactic should finish it."
  tauto

NewTactic by_contra
TheoremTab "∈"
