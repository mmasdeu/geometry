import Game.Metadata

open Set IncidencePlane --hide

variable {Ω : Type} [IncidencePlane Ω] --hide

World "TutorialWorld"
Level 1
TheoremTab "∈"
Title "The assumption tactic"

Introduction "The first tactic you'll learn is `assumption`.

Here we assume that $A=B$, that $C=D$ and that $B=C$, and we want to prove that
$B=C$. Of course it's true: we're assuming it!

Look at the panel on the right. You'll see a list of *Objects* (A, B, C, D are points, so they live in
our plane Ω) and a list of *Assumptions* (here called h₁, h₂, h₃). Together they form the 'Local context'.
Below them is the *Goal*, which here is `B = C`.

`assumption` works when your goal is exactly one of your hypotheses. Here `h₃` says $B = C$,
which is precisely what we want, so you win by typing `assumption`.

**Note:** it's best to switch to *Editor mode* instead of the default *Typewriter mode*.
Click the top-right button with the `</>` symbol.
"


/-- If $A = B$, $C = D$ and $B = C$, then $B = C$. -/
Statement (A B C D : Ω) (h₁ : A = B) (h₂ : C = D) (h₃ : B = C) : B = C := by
  Hint "Type `assumption` and you're done with this level!"
  assumption

Conclusion "Great! Now let's move on to the next level..."


NewTactic assumption
NewDefinition UnicodeTable
