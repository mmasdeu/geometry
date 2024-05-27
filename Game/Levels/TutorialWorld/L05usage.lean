import Game.Metadata
open IncidencePlane --hide

World "TutorialWorld"
Level 5

Title "Using theorems / axioms"
TheoremTab "∈"
Introduction
"
You will see that two new axioms have been added to the *Axioms* tab in the *Theorems* list:

* line_through_left (P Q : Ω) : P ∈ (line_through P Q)

* line_through_right (P Q : Ω) : Q ∈ (line_through P Q)

Given two points P and Q, we can form the line passing through them (which is one of the axioms).
This line is called `line_through P Q`. To encode that it passes through these points, we have
the two *axioms* above. Just after the name, you see that two parentheses appear, with the variables
that these take. For each choice of two points, we get a statement that says that the first of them
belongs to `line_through P Q` (this is what `line_through_left P Q` says), and another corresponding
statement to say that the second point belongs to the same line (that is, `line_through_right P Q`).

From now on,
all the statements that appear on this list will be remembered by the computer. They will either
be axioms (which we will find in the *Axioms* tab) or theorems that we have already proved in
previous levels (and which will become available as you make progress).

Back to this level, if you look at the goal you will see the same structure as
the statement `line_through_right (P Q : Point) : Q ∈ (line_through P Q)`.
Then, we just have to write that statement in a different way!
Do you remember that the `apply`
tactic solved the goal by using a hypothesis of the same structure? Then, because the computer already knows what
`line_through_right (P Q : Point) : Q ∈ line_through P Q` means, why don't we type `apply line_through_right A B`?
Type that and see
how it finishes the proof!
"


variable {Ω : Type} [IncidencePlane Ω]

/--
A point lies in the line that passes through it.
-/
Statement (A B : Ω) : B ∈ line_through A B := by
  apply line_through_right A B

Conclusion "Well done!"
