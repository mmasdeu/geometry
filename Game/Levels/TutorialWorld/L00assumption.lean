import Game.Metadata

open Set IncidencePlane --hide

variable {Ω : Type} [IncidencePlane Ω] --hide

World "TutorialWorld"
Level 1

Title "The assumption tactic"

Introduction "The first tactic that we'll learn is the `assumption` tactic. This can be used
when your goal is exactly one of your hypotheses. In the following example,
there are three hypotheses, namely the fact that $A = B$ (hypothesis `h₁`), the
fact that $C = D$ (hypothesis `h₂`) and the fact that $B = C$ (hypothesis `h₃`).

Since we want to prove that $C = D$, which is one of our hypotheses, we should be able to
win by typing `assumption,` (**don't forget the comma**). Delete the `sorry` and try it.

**Pro tip:** If the hypothesis to be used is called, say `hb`, you can also close the goal
by using `exact hb,` instead. Sometimes it is more efficient to do so, especially if we believe
that assumption should work and we don't know why. The `exact` tactic will give us information
about why that does not work."


/-- If $A = B$, $C = D$ and $B = C$, then $C = D$. -/
Statement (A B C D : Ω) (h₁ : A = B) (h₂ : C = D) (h₃ : B = C) : B = C := by
  Hint "Type 'assumption' and you will be done with this level!"
  assumption

Conclusion "Great! Now let's move on to the next level..."


NewTactic assumption
