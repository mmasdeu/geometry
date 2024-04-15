import Game.Metadata
open IncidencePlane --hide

World "TutorialWorld"
Level 5

Title "Using theorems"

Introduction
"
You will see that two new theorems have been added to the *Theorems* list:

* line_through_left (P Q : Ω) : P ∈ (line_through P Q)

* line_through_right (P Q : Ω) : Q ∈ (line_through P Q)

**Note the name of the two statements**. Mathematicians sometimes call them 'Lemma 2.1' or 'Hypothesis P6' or something. But
computer scientists call them `line_through_left` and `line_through_right` because they are easier to use and remember. From now on,
all the statements that appear on this list will be remembered by the computer. In this way, we won't have to provide their proofs again.
Instead, we will use them straightforwardly in case they are handy for solving the following levels.

Just after the name of the statements, two parentheses appear. Inside them, there are the exact number of variables that are needed to
put out that statements. Then, the colon `:` symbol introduces the statement as such. In this case, they are very similar to each other.
What they come to mean is that we can draw a line that passes through two distinct points (P and Q) that lie in a plane (Ω). They symbol `∈`
is read as *is an element of*. Then, P and Q are elements of the line that passes through the points P and Q. Seems obvious, right? Now, let's
try to solve this level!

Looking at the goal, you will see the same structure as
the statement `line_through_right (P Q : Point) : Q ∈ (line_through P Q)`.
Then, we just have to write that statement in a different way!
Do you remember that the `exact`
tactic solved the goal by using a hypothesis of the same structure? Then, because the computer already knows what
`line_through_right (P Q : Point) : Q ∈ (line_through P Q)` means, why don't we type `exact line_through_right A B`?
Type that and see
how it finishes the proof!
"


variable {Ω : Type} [IncidencePlane Ω]

/--
A point lies in the line that passes through it.
-/
Statement (A B : Ω) : B ∈ line_through A B := by
  exact line_through_right A B

Conclusion "Well done!"
