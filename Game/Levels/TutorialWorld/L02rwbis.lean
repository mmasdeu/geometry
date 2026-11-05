import Game.Metadata
open Set IncidencePlane --hide

World "TutorialWorld"
Level 3

Title "The `rw` (rewrite) tactic (II)"
TheoremTab "∈"
Introduction "
## The rewrite (`rw`) tactic (II)

Last time we saw that `rw [h]` changes A's into B's when `h : A = B`. You may be wondering
about the opposite: can we change B's into A's using the same `h : A = B`?

Yes! Here the hypotheses are set up a bit differently, so you'll want `rw [←h]`.
To type the little arrow, write **\\l** followed by a space and the system will convert it for you.
"

variable {Ω : Type} [IncidencePlane Ω] --hide

/--
If A, B and C are points with B = A and B = C, then A = C.
-/
Statement (A B C: Ω) (h1 : B = A) (h2 : B = C) : A = C := by
  rw [←h1]
  rw [h2]

Conclusion
"Nice one!"
