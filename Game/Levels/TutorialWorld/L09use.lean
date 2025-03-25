import Game.Metadata
import Game.Levels.TutorialWorld.L08have
open IncidencePlane --hide


World "TutorialWorld"
Level 8

Title "The use tactic"
TheoremTab "∈"

Introduction
"
In further proofs, we will need to prove that there exists an object satisfying certain properties.
The goal will then look like `⊢ ∃ x, P x`, where the symbol `∃` is read as *there exists* and
`P x` can be understood as *x satisfies property P*
In this case, the whole goal can be interpreted as *there exists x satisfying property P*.
Then, the `use` tactic is useful. If we know that an object `a` satisfies the  property `P`, then `use a`
will simplify the goal into `⊢ P a`.

In the example below, we must find a line containing a given point $P$. Any line will do, for example
the one that is given by the axiom `line_through P P`. Note that this is not really well defined,
but this axiom always gives us a line through the given two points (even if they are the same). So
that should work. Try to type `use line_through P P` and then you should see how to finish using
known tactics.
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
