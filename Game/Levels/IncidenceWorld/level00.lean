import Game.Metadata
import Game.Levels.TutorialWorld
open IncidencePlane --hide

World "IncidenceWorld"
Level 1

Title "The `simp` tactic"

variable {Ω : Type} [IncidencePlane Ω] --hide


Introduction
"
Meet `simp`, a powerful tactic that can crush goals which would be really tedious to do by hand. It uses lemmas
already in our database to make the goal simpler. You can also simplify a hypothesis `h` by writing `simp at h`.
As the game goes on, `simp` will get better and better, because we tag more lemmas as *simp lemmas* along the way.

For example, **Lean** has a lemma called `not_not` saying that a double negation is the same as the plain statement:

`@[simp] lemma not_not (p : Prop) : ¬¬ p ↔ p`

The `@[simp]` in front tells the `simp` tactic to replace every `¬¬ p` with `p`. There are lots of lemmas like this
in **Lean**, which is what makes the tactic so strong. We've also tagged `line_through_left` and `line_through_right`
with `@[simp]`. Since `simp` keeps going until it can't simplify any further, you can solve this level in one go.
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
