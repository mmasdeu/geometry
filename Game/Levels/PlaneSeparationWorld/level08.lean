import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level07

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C : Ω} --hide
variable {ℓ : Line Ω} --hide

World "PlaneSeparationWorld"
Level 8

Title "The Final Level!"

open scoped Classical

Introduction
"
After all that hard work, it's time to put the pieces together and prove transitivity
in the collinear case. We'll use the non-collinear case up to three times.
The key tool is `auxiliary_point` from the previous level, which gives us a point `E` off the line `m`. Here's the plan.

1. First, the cases $A = B$, $A = C$ and $B = C$ are easy, so deal with them separately. So we may
  assume for the rest of the proof that $A \\neq B$, $A \\neq C$ and $B \\neq C$.
1. Let $m$ be the line through $A$, $B$, $C$.
1. Consider the point $E$ obtained from the previous level, which is not in $m$ and is on the same side of $\\ell$ as $A$.
1. Show that the sets $\\{A, B, E\\}$, $\\{A, C, E\\}$ and $\\{B, C, E\\}$ are all non-collinear (they are all done similarly).
1. Using symmetry and transitivity for non-collinear points, show that $B$ is on the same side as $E$.
1. Show, with the previous step and a similar argument, that $E$ is on the same side as $C$.
1. Finally, use transitivity for non-collinear points a third time to finish.

Last level. You've got this!
"
Image "images/trans_collinear_diagram.png"

/--
Given three collinear points A, B, C and a line ℓ, if A and B are on the same side of
ℓ and B and C are on the same side of ℓ, then A and C are on the same side of ℓ.
-/
Statement same_side_trans_of_collinear (hCol : collinear A C B):
same_side ℓ A B → same_side ℓ B C → same_side ℓ A C := by
  intro hABℓ hBCℓ
  have hAℓ : A ∉ ℓ := not_in_line_of_same_side_left hABℓ
  Hint (hidden := true) "Let's deal with the boring cases first: A = B, A = C, B = C"
  by_cases hAB : A = B
  · rw [hAB]
    apply hBCℓ
  by_cases hAC : A = C
  · rw [hAC] at hAℓ ⊢
    apply same_side_reflexive hAℓ
  by_cases hBC : B = C
  · rw [hBC] at hABℓ
    apply hABℓ

  Hint (hidden := true) "Name the line through A, C, B"
  rcases hCol with ⟨m, hm⟩
  Hint (hidden := true) "Now invoke `auxiliary_point` to find a point `E` not in {m} and on the same side of ℓ as {A}"
  rcases hm with ⟨hAm, hCm, hBm⟩
  rcases auxiliary_point hAm hAℓ with ⟨E, ⟨hEm, hAE⟩⟩
  Hint (hidden := true) "Prove that A, B, {E} are not collinear"
  have hABE : ¬ collinear A B E
  · rw [collinear_iff_on_line_through hAB]
    rw [incidence hAB hAm hBm] at hEm
    apply hEm
  Hint (hidden := true) "Prove that A, C, {E} are not collinear"
  have hACE : ¬ collinear A C E
  · rw [collinear_iff_on_line_through hAC]
    rw [incidence hAC hAm hCm] at hEm
    apply hEm
  Hint (hidden := true) "Prove that B, C, {E} are not collinear"
  have hBCE : ¬ collinear B C E
  · rw [collinear_iff_on_line_through hBC]
    rw [incidence hBC hBm hCm] at hEm
    apply hEm
  Hint (hidden := true) "Prove that B and {E} are on the same side of ℓ. To apply transitivity with the points in the right order, you may need `collinear_of_equal` to reorder the points of a non-collinearity statement, e.g. `rw [collinear_of_equal A B E B E A] at hABE`; Lean fills in the proof that the two sets are equal."
  have hBE : same_side ℓ B E -- Use transitivity for non-collinear points
  · rw [same_side_symmetric] at hABℓ
    rw [collinear_of_equal A B E B E A] at hABE
    · apply same_side_trans_of_noncollinear hABE hABℓ hAE
  Hint (hidden := true) "Prove that {E} and C are on the same side of ℓ"
  have hEC : same_side ℓ E C -- Use transitivity for non-collinear points
  · rw [same_side_symmetric] at hBE
    rw [collinear_of_equal B C E E C B] at hBCE
    · apply same_side_trans_of_noncollinear hBCE hBE hBCℓ
  Hint (hidden := true) "Almost there. One line to go!"
  apply same_side_trans_of_noncollinear hACE hAE hEC -- And we are done in one line!

TheoremTab "PSep"
