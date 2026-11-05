import Game.Metadata
import Game.Levels.TutorialWorld.L10rcases1and
open IncidencePlane --hide

World "TutorialWorld"
Level 11

Title "The `rcases` tactic (II)"
TheoremTab "∈"

variable {Ω : Type} [IncidencePlane Ω] --hide

Introduction
"
# Advanced Tutorial World

## The `rcases` tactic (II)

Now suppose your hypothesis says that `P` or `Q` holds, that is, `h : P ∨ Q`. Then `rcases h` (same tactic as before, now applied to an *or* instead of an *and*) creates
two goals. In the first, `h` is replaced with `h : P`, and in the second with `h : Q`.

You may need to remember how `use` works. If the goal is
`⊢ ∃ (R : Ω), R ∈ ℓ`, then `use X` (where `X` is some point that you know lies on ℓ) turns
the goal into `⊢ X ∈ ℓ`. The point you need is either in the *Theorems* section or among the hypotheses
above the goal.
[**Reminder:** when the goal splits in two, handle each one on its own line starting with `·`
(typed `\\.`), like `· use P` and then `· use Q`.]
"

/--
If ℓ is any line in the plane Ω and either the point P or the point Q is in ℓ, then ℓ is not an empty line.
-/
Statement (P Q : Ω) (ℓ : Line Ω) (h : P ∈ ℓ ∨ Q ∈ ℓ) : ∃ R, R ∈ ℓ := by
  rcases h
  · use P
  · use Q
