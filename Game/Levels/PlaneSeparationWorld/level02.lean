import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level01

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "PlaneSeparationWorld"
Level 2

Title "A useful rewrite"

Introduction
"
To solve the following levels it will be useful to have the following criterion for collinearity.
Here you have some hints that could help you to step through it!

**Hint 1:** Whenever you see the word `collinear`, the `rw` tactic will make progress.

**Hint 2:** Whenever you find a goal or hypothesis of the form `∀ {X : Ω}, X ∈ {A, B, C} → X ∈ r`, the `simp` tactic will make progress.

**Hint 3:** To solve the first goal, you may want to use the theorem statement `incidence` with the `rw` tactic.
"


/--
Given three distinct points, they are on the same line if and only if they are collinear.
-/
Statement collinear_iff_on_line_through (h : A ≠ B) : collinear A B C ↔ C ∈ line_through A B := by
  constructor
  · intro h1
    rw [collinear] at h1
    rcases h1 with ⟨ℓ, hℓ⟩
    rw [← (incidence h hℓ.1 hℓ.2.1)]
    exact hℓ.2.2
  · intro h1
    rw [collinear]
    use line_through A B
    simp
    exact h1
