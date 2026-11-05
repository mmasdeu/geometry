import Game.Metadata
import Game.Levels.TutorialWorld.L11rcases2or
open IncidencePlane --hide

World "TutorialWorld"
Level 12

Title "The `tauto` tactic"
TheoremTab "∈"
variable {Ω : Type} [IncidencePlane Ω] --hide



variable {p q r : Prop} --hide

Introduction
"
Sometimes the goal follows from the hypotheses by pure logic. That's called a tautology,
and there's a tactic that handles it for you. For example, this is a tautology (for any
statements p, q and r):

p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r)

It's true whether each of `p`, `q` and `r` is true or false.

In the level below, the goal follows from the hypotheses by logic alone, so just try `tauto`.
"

/--
If $p$, $q$ and $r$ are three true-false statements, and we know $p \lor q$ and $r \lor p \lor r$, then
we have $p \lor (q \land r)$.
-/
Statement (h1 : p ∨ q) (h2 : r ∨ p ∨ r):
p ∨ (q ∧ r) := by
  tauto

NewTactic tauto
