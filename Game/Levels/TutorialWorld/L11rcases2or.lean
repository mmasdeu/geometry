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

## The `cases` tactic (II).

Suppose now that your hypothesis says that `P` or `Q` holds. That is, you have `h : P ∨ Q`. Then `cases h` will create
two new goals, and in each of them it will replace `h` with `h : P` in the first case, and with `h : Q` in the second.

To solve this level, you may need to remember how to employ the `use` tactic. As a reminder, note that if the goal is of
the form `⊢ ∃ (R : Ω), R ∈ ℓ`, then you can type `use X`, where `X` is any object that satisfies $X \\in R$ , so that it
turns the goal into `⊢ X ∈ ℓ`. The object you are looking for either is found in the *Theorems* section or in the hypotheses
right above the goal of this level.
[**Reminder:** if the goal breaks into two goals, remember that you can use `·` to make
the look of the proof more visual.]
"

/--
If ℓ is any line in the plane Ω and either the point P or the point Q is in ℓ, then ℓ is not an empty line.
-/
Statement (P Q : Ω) (ℓ : Line Ω) (h : P ∈ ℓ ∨ Q ∈ ℓ) : ∃ R, R ∈ ℓ := by
  rcases h
  · use P
  · use Q
