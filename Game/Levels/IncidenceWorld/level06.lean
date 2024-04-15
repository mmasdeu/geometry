import Game.Metadata
import Game.Levels.IncidenceWorld.level05

open IncidencePlane --hide



World "IncidenceWorld"
Level 6

Title "A line-avoiding point"

Introduction
"
In this level we prove that given two different lines, there is a point in the first line that is not in the second.

Here is a possible plan of the proof, to help you get started. Make sure you have
all the details written down in paper before you start typing!

*Proof sketch:*

1. Consider two points $A$ and $B$ on the line $r$.
2. Do a proof by cases:
  - If $A \\notin s$, then there is nothing to do, $A$ is the sought point.
  - If $A \\in s$, then show that $B \\notin s$, and $B$ is the sought point.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

/--
If two lines are different, there is a point in one that is not in the other
-/
Statement point_in_line_difference (h : r ≠ s) : ∃ P ∈ r, P ∉ s := by
  rcases line_contains_two_points r with ⟨A, B, hAB, hABr⟩
  rw [hABr] at h ⊢
  by_cases hAs : A ∉ s
  · use A
    simp [hAs]
  · use B
    simp at *
    intro hBs
    rw [incidence hAB hAs hBs] at h
    tauto

-- NewTheorem point_in_line_difference
