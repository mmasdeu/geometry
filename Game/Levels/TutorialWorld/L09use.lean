import Game.Metadata
import Game.Levels.TutorialWorld.L08have
open IncidencePlane --hide


World "TutorialWorld"
Level 9

Title "The use tactic"
TheoremTab "∈"

Introduction
"
Later on we'll need to prove that something *exists*.
The goal will look like `⊢ ∃ x, P x`, where `∃` reads *there exists* and
`P x` means *x satisfies property P*. So the goal says 'there is an x with property P'.
That's where `use` comes in. If you know that an object `a` satisfies `P`, then `use a`
turns the goal into `⊢ P a`.

In the example below, we need a line containing a given point $P$. Any line will do, for instance
the one given by the axiom `line_through P P`. It looks a bit odd, but the axiom always
gives us a line through the two given points, even if they're the same one. That's fine for us.
Type `use line_through P P` and then finish with tactics you already know.
"

variable {Ω : Type} [IncidencePlane Ω] --hide

/--
Find a line that contains the point $P$.
-/
Statement (P : Ω) :
∃ ℓ : Line Ω, P ∈ ℓ := by
  use line_through P P
  apply line_through_left

NewTactic use
