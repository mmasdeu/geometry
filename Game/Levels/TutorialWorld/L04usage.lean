import Game.Metadata
open IncidencePlane --hide

World "TutorialWorld"
Level 5

Title "Using theorems / axioms"
TheoremTab "∈"
Introduction
"
Two new axioms just appeared in the *Axioms* tab of the *Theorems* list:

* line_through_left (P Q : Ω) : P ∈ (line_through P Q)

* line_through_right (P Q : Ω) : Q ∈ (line_through P Q)

Given two points P and Q, there's a line passing through them (that's one of the axioms).
We call it `line_through P Q`. To record that it really passes through both points, we have
the two axioms above. Notice the parentheses after each name: those are the inputs it takes.
For any two points, `line_through_left P Q` says the first one lies on `line_through P Q`,
and `line_through_right P Q` says the second one does too.

From now on, every statement in that list is remembered by the computer. They're either
axioms (in the *Axioms* tab) or theorems you've already proved in earlier levels (they unlock as you go).

Back to this level: look at the goal. It has the same shape as
`line_through_right (P Q : Point) : Q ∈ (line_through P Q)`.
Remember how `apply` closes a goal that matches a hypothesis? It works for known theorems too!
So type `apply line_through_right A B` and watch it finish the proof.
"


variable {Ω : Type} [IncidencePlane Ω]

/--
A point lies in the line that passes through it.
-/
Statement (A B : Ω) : B ∈ line_through A B := by
  apply line_through_right A B

Conclusion "Well done!"
