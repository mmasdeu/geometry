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
After all this hard work, we are left with the final task of assembling the bits and proving transitivity
in the collinear case. We will prove this by applying up to three times the noncollinear case already proven.
For this, we need the auxiliary point from the previous level. Here is a sketch of the proof.

1. First, note that the case $A = B$, $A = C$ or $B = C$ are easy, and they can be proved separately. So we may
  assume for the rest of the proof that $A \\neq B$, $A \\neq C$ and $B \\neq C$.
1. Let $m$ be the line through $A$, $B$, $C$.
1. Consider the point $E$ obtained from the previous level, which is not in $m$ and is on the same side of $\\ell$ as $A$.
1. Show that the sets $\\{A, B, E\\}$, $\\{A, C, E\\}$ and $\\{B, C, E\\}$ are all non-collinear (they are all done similarly).
1. Using symmetry, and transitivity for non-collinear points, show that $B$ is on the same side as $E$.
1. Show, using the previous step and a similar argument, that $E$ is on the same side as  $C$.
1. Finally, finish the proof using a third time transitivity for non-collinear points.


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
  Hint (hidden := true) "Prove first the degenerate cases: A = B, A = C, B = C"
  by_cases hAB : A = B
  · rw [hAB]
    apply hBCℓ
  by_cases hAC : A = C
  · rw [hAC] at hAℓ ⊢
    apply same_side_reflexive hAℓ
  by_cases hBC : B = C
  · rw [hBC] at hABℓ
    apply hABℓ

  Hint (hidden := true) "Define the line through A, C, B"
  rcases hCol with ⟨m, hm⟩
  Hint (hidden := true) "Now invoke `auxiliary_point` to find a point not in {m} and on the same side as ℓ and {A}"
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
  Hint (hidden := true) "Prove that B and {E} are on the same side of ℓ"
  have hBE : same_side ℓ B E -- Use transitivity for non-collinear points
  · rw [same_side_symmetric] at hABℓ
    rw [collinear_of_equal A B E B E A] at hABE
    · apply same_side_trans_of_noncollinear hABE hABℓ hAE
  Hint (hidden := true) "Prove that {E} and C are on the same side of ℓ"
  have hEC : same_side ℓ E C -- Use transitivity for non-collinear points
  · rw [same_side_symmetric] at hBE
    rw [collinear_of_equal B C E E C B] at hBCE
    · apply same_side_trans_of_noncollinear hBCE hBE hBCℓ
  Hint (hidden := true) "Now we will be done in one line!"
  apply same_side_trans_of_noncollinear hACE hAE hEC -- And we are done in one line!

TheoremTab "PSep"
