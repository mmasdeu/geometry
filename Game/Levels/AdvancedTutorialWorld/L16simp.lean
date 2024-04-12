import Game.Metadata
import Game.Levels.AdvancedTutorialWorld.L15apply
open IncidencePlane --hide

World "AdvancedTutorialWorld"
Level 7

Title "The `apply` tactic"

variable {Ω : Type} [IncidencePlane Ω] --hide


Introduction
"
In this level, we introduce a high level tactic called `simp`. This is an Artificial Intelligence (AI) tactic which
can nail some really tedious-for-a-human-to-solve goals. It uses lemmas that are already in our database to make
the goal simpler. You can simplify an hypothesis `h` by calling `simp at h,`. As the game progresses, this tactic
will become better (we are tagging some of the lemmas as *simp lemmas* along the way).

Just to illustrate, **LEAN** has a lemma  (called `not_not`) that says that double negation is the same as an affirmation:

`@[simp] lemma not_not (p : Prop) : ¬¬ p ↔ p`

The fact that it has `@[simp]` written in front of it instructs the `simp` tactic to replace all occurrences
of `¬¬ p` with `p`. There are lots of lemmas like these in **LEAN**, which makes this tactic really powerful.
"


variable {Ω : Type} [IncidencePlane Ω] --hide

/--
If a point $P$ is on a line $\ell$, then $P$ is not outside of $\ell$.
-/
Statement (P : Ω) (ℓ : Line Ω) (h : P ∈ ℓ) : ¬ (P ∉ ℓ) := by
  simp
  exact h

NewTactic simp
