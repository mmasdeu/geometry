import Game.Metadata
import Game.Levels.TutorialWorld.L13simp
open IncidencePlane --hide

World "TutorialWorld"
Level 13

Title "The `tauto` tactic"

variable {Ω : Type} [IncidencePlane Ω] --hide



variable {p q r : Prop} --hide

Introduction
"
When the goal follows from the hypotheses directly from the rules of logic, then we say that we are proving a tautology,
and there is a tactic that does this automatically for us. For example, the following is a tautology (if p, q and r are
arbitrary statements).

p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r)

You can see that this is true because regardless of whether each of `p`, `q` and `r` is true or false, the statement
above is true.
"

/--
If $p$, $q$ and $r$ are three true-false statements, and we know $p \lor q$ and $r \lor p \lor r$, then
we have $p \lor (q \land r)$.
-/
Statement (h1 : p ∨ q) (h2 : r ∨ p ∨ r):
p ∨ (q ∧ r) := by
  tauto

NewTactic tauto
