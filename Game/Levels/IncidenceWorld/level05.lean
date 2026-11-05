import Game.Metadata
import Game.Levels.IncidenceWorld.level04

open IncidencePlane --hide



World "IncidenceWorld"
Level 6

Title "A point to show that two lines are different"

Introduction
"
## A useful lemma

A single point can tell us that two lines are different. Neat, right?

You only need three lines of code here, so try to finish it on your own!

Hint on the strategy: to prove `r ≠ s`, assume the opposite (`intro H`, with `H : r = s`) and
ask yourself what happens to the point `P`.

```
  r ────●P────────
  s ─────────────      P is on r but not on s
```
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

NewTheorem ne_line_of_not_share_point
TheoremTab "∈"
