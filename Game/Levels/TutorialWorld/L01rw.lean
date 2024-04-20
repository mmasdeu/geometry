import Game.Metadata
open IncidencePlane --hide


World "TutorialWorld"
Level 2

Title "The `rw` (rewrite) tactic"
TheoremTab "∈"
Introduction "
The next tactic in our list is `rw` (from rewrite). Rewriting is one of the most basic methods of proof,
where we 'substitute' one object that we know that is equal to another.

For example, if `h : A = B` is a hypothesis (i.e., a proof of `A = B`) in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw h` will change them all to `B`'s.

Now, take a look in the top right box at what we have. The variables `A`, `B` and `C` are
points that lie in the plane `Ω`. Here we have to prove that if the point $A$ is equal to the point $B$,
and the point $B$ is equal to the point $C$, then the point $A$ is equal to the point $C$.

Try to use a sequence of rewrite steps to prove the lemma below by typing them into the box underneath.
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

Click on `rw [h1]`, and then use the arrow keys to move your cursor around the proof.
Go up and down and note that the goal changes -- indeed you can inspect Lean's 'state' at
each line of the proof (the hypotheses, and the goal). Try to figure out the exact place
where the goal changes.
"

NewTactic rw
