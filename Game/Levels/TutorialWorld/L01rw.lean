import Game.Metadata
open IncidencePlane --hide


World "TutorialWorld"
Level 2

Title "The `rw` (rewrite) tactic"
TheoremTab "∈"
Introduction "
Next up is `rw` (short for rewrite). Rewriting is one of the most basic proof methods:
if two things are equal, you can swap one for the other.

For example, if `h : A = B` is in your local context (that is, a proof of `A = B`)
and your goal contains some `A`s, then `rw [h]` turns them all into `B`s.

Look at the local context: `A`, `B` and `C` are points of the plane `Ω`. We want to prove that if $A = B$
and $B = C$, then $A = C$.

Try a sequence of rewrite steps by typing them in the box below.
"

open Set IncidencePlane

variable {Ω : Type} [IncidencePlane Ω]

/--
If A, B and C are points with A = B and B = C, then A = C.
-/
Statement (A B C: Ω) (h1 : A = B) (h2 : B = C) : A = C := by
  rw [h1]
  assumption


Conclusion
"
# Exploring your proof

If you're in 'Editor mode', click on the line `rw [h1]` and move your cursor around with the arrow keys.
Go up and down and watch the goal change. You can inspect Lean's state at every line of the proof
(hypotheses and goal). Can you spot exactly where the goal changes?
"

NewTactic rw
