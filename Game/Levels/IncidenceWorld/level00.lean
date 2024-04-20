import Game.Metadata
import Game.Levels.TutorialWorld
open IncidencePlane --hide

World "IncidenceWorld"
Level 1

Title "The `simp` tactic"

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
For example, we have added a `@[simp]` tag to the lemmas `line_through_left` and `line_through_right`. Since the `simp`
tactic can run until it cannot simplify further, you can prove solve this lemma in one go.
"

variable {Ω : Type} [IncidencePlane Ω] --hide

/--
It is not true that a point $P$ misses the line through $P$ and $Q$.
-/
Statement (P Q : Ω) : ¬ (P ∉ line_through P Q) := by
  Hint "Simply call `simp`!"
  simp


NewTactic simp
TheoremTab "∈"
