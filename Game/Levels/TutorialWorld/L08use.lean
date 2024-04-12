import Game.Metadata
open IncidencePlane --hide

World "TutorialWorld"
Level 8

Title "The constructor tactic"


Introduction
"
In further proofs, we will need to prove that there exists an object satisfying certain properties.
The goal will then look like `⊢ ∃ x, P x`, where the symbol `∃` is read as *there exists* and
`P x` can be understood as *x satisfies property P*
In this case, the whole goal can be interpreted as *there exists x satisfying property P*.
Then, the `use` tactic is useful. If we know that an object `a` satisfies the  property `P`, then `use a`
will simplify the goal into `⊢ P a`.

In the example below, we are given three points and two lines. We know certain things about the points, and the
goal is to find a line $\\ell$ such that $P$ and $Q$ both belong to $\\ell$. Think, looking at the hypotheses,
which line could do the trick. Then `use` it, and finish the proof using tactics you already know.
"

variable {Ω : Type} [IncidencePlane Ω] --hide

/--
Finds a line that contains the points $P$ and $Q$ at the same time.
-/
Statement (P Q R: Ω) (r s : Line Ω) (hP1 : P ∈ r) (hP2 : P ∈ s) (hR : R ∈ r) (hQ : Q ∈ s) :
∃ ℓ : Line Ω, P ∈ ℓ ∧ Q ∈ ℓ := by
  use s

NewTactic use
