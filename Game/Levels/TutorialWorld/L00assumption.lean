import Game.Metadata

open Set IncidencePlane --hide

variable {Ω : Type} [IncidencePlane Ω] --hide

World "TutorialWorld"
Level 1
TheoremTab "∈"
Title "The assumption tactic"

Introduction "The first tactic that we'll learn is the `assumption` tactic.

In this level we will prove that, if we assume that $A=B$, that $C=D$ and that $B=C$, then
it is true that $C=D$. Of course it is, because we are assuming it!

Look at your goal: You will see a list of *Objects* (A, B, C, D are all points, so they belong
to our plane Ω), and a list of *Assumptions* (labeled h₁, h₂, h₃ in this case). We will refer to
the objects and assumptions together as the 'Local context'. Finally, you
can see the *Goal*, which in our case is to prove `B = C`.

The assumption tactic can be used
when your goal is exactly one of your hypotheses. In the following example,
there are three hypotheses, namely the fact that $A = B$ (hypothesis `h₁`), the
fact that $C = D$ (hypothesis `h₂`) and the fact that $B = C$ (hypothesis `h₃`).

Since we want to prove that $C = D$, which is one of our hypotheses, we should be able to
win by typing `assumption`.

**Note:** It will be best if you switch to *Editor mode* instead of the default *Typewriter mode*
you are probably in. This is done by clicking the top-right button with a `</>` symbol.
"


/-- If $A = B$, $C = D$ and $B = C$, then $C = D$. -/
Statement (A B C D : Ω) (h₁ : A = B) (h₂ : C = D) (h₃ : B = C) : B = C := by
  Hint "Type 'assumption' and you will be done with this level!"
  assumption

Conclusion "Great! Now let's move on to the next level..."


NewTactic assumption
NewDefinition UnicodeTable
