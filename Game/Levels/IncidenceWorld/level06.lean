import Game.Metadata
import Game.Levels.IncidenceWorld.level05

open IncidencePlane --hide



World "IncidenceWorld"
Level 7

Title "A line-avoiding point"

Introduction
"
Here we prove that, given two different lines, some point of the first one is not on the second.

Here's a possible plan to get you started. Write all the details on paper before you start typing!

*Proof sketch:*

1. Take two points $A$ and $B$ on the line $r$.
2. Split into cases:
  - If $A \\notin s$, there's nothing to do: $A$ is the point we're after.
  - If $A \\in s$, show that $B \\notin s$, so $B$ is the point we want. (Indeed, if both $A$ and $B$ were in $s$, then
    $s$ would be the line through $A$ and $B$, which is $r$, contradicting $r \\neq s$.)

In Lean, the first step gives you `hABr : r = line_through A B`. Rewrite with it (`rw [hABr] at h ⊢`) so that `r` is
expressed through `A` and `B`, which is what `incidence` needs.
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
  by_cases hAs : A ∈ s
  · use B
    simp
    intro hBs
    rw [incidence hAB hAs hBs] at h
    tauto
  · use A
    simp [hAs]

NewTheorem point_in_line_difference
TheoremTab "∈"
