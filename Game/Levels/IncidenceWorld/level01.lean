import Game.Metadata
import Game.Levels.IncidenceWorld.level00
open IncidencePlane --hide

World "IncidenceWorld"
Level 2

Title "The symmetry of the line through two points"

variable {Ω : Type} [IncidencePlane Ω] --hide


Introduction
"
Time for the `by_cases` tactic, which is how you do a *proof by cases* in Lean. It's handy whenever
a proof splits naturally into different cases.

Here there's a `degenerate` case to worry about: what if `P = Q`? If you type `by_cases h : P = Q`, the goal splits
in two branches. The first one has `h : P = Q` in the context, and the second one has `h : P ≠ Q`.

In the second case you'll need the theorem `incidence` (see the *Theorems* tab): it says that if two distinct
points `P`, `Q` lie on a line `ℓ`, then `ℓ = line_through P Q`. Use it with `rw`.
"

variable {Ω : Type} [IncidencePlane Ω] -- hide
variable {P Q : Ω} -- hide

/--
The line through two points is a symmetric concept.
-/
Statement line_through_symmetric : line_through Q P = line_through P Q := by
  by_cases h : P = Q
  · rw [h]
  have h1 : P ∈ line_through Q P := by simp
  have h2 : Q ∈ line_through Q P := by simp
  rw [incidence h h1 h2]

NewTheorem line_through_symmetric
NewTactic by_cases
TheoremTab "∈"
