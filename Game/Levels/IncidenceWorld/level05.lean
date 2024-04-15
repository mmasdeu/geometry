import Game.Metadata
import Game.Levels.IncidenceWorld.level04

open IncidencePlane --hide



World "IncidenceWorld"
Level 5

Title "A point to show that two lines are different"

Introduction
"
## A useful lemma

We will see that
a point can help us deciding that two lines are different.

To solve this level, you just need three lines of code. Try to finish it on your own.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {P : Ω} {r s : Line Ω} --hide

/--
If two lines `r` and `s` do not share a point, then they are not equal.
-/
Statement ne_line_of_not_share_point (P : Ω) (hPr : P ∈ r)
(hPs : P ∉ s): r ≠ s:= by
  intro H
  rw [H] at hPr
  tauto

-- NewTheorem ne_line_of_not_share_point
