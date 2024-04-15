import Game.Metadata
import Game.Levels.TutorialWorld.L08have
open IncidencePlane --hide


World "TutorialWorld"
Level 8

Title "The use tactic"


Introduction
"
In further proofs, we will need to prove that there exists an object satisfying certain properties.
The goal will then look like `⊢ ∃ x, P x`, where the symbol `∃` is read as *there exists* and
`P x` can be understood as *x satisfies property P*
In this case, the whole goal can be interpreted as *there exists x satisfying property P*.
Then, the `use` tactic is useful. If we know that an object `a` satisfies the  property `P`, then `use a`
will simplify the goal into `⊢ P a`.

In the example below, we are given three points and two lines. We know certain things about the points, and the
goal is to find a line $\\ell$ such that $P$, $Q$ and $R$ belong to $\\ell$. Think, looking at the hypotheses,
which line could do the trick. Then `use` it, and finish the proof using tactics you already know.
"

variable {Ω : Type} [IncidencePlane Ω] --hide

/--
Find a line that contains the point $P$.
-/
Statement (P : Ω) (ℓ : Line Ω) :
∃ ℓ : Line Ω, P ∈ ℓ := by
  use line_through P P
  exact line_through_left P P

NewTactic use
