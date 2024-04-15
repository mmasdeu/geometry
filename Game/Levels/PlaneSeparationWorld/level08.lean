import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level07
import Mathlib.Tactic

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "PlaneSeparationWorld"
Level 8

Title "The Pasch Axiom in action!"

open scoped Classical

Introduction
"
In this level we prove transitivity of the relation *being in the same side of $\\ell$*, provided that the three
points involved are non-collinear. So suppose that we are given three non-collinear points $A$, $B$, $C$, and suppose
that $A$ is on the same side of $\\ell$ as $B$, and $B$ is on the same side of $\\ell$ as $C$. We want to prove that $A$ is on
the same side of $\\ell$ as $C. Here is a sketch of the proof.

1. We argue by contradiction, so assume that the line $AC$ does meet $\\ell$.
2. Let $D \\in \\ell$ be the point of intersection, so $A * D * C$.
3. Use Pasch to prove that either $\\ell$ either meets the segment $AB$ or $BC$, thus
  obtaining a contradiction.

This is the first time that we will use Pasch's axiom. Remember what it says:

`
pasch {A B C D : Ω} {ℓ : Line Ω} (hnc : C ∉ line_through A B)
(hnAl : A ∉ ℓ) (hnBl : B ∉ ℓ) (hnCl : C ∉ ℓ) (hDl : D ∈ ℓ) (hADB : A*D*B) :
  (same_side ℓ A C ∧ ¬same_side ℓ C B) ∨ (¬same_side ℓ A C ∧ same_side ℓ C B)
`

![Proof sketch](trans_noncollinear_diagram.png 'Proof of transitivity, noncollinear case')

Try to write the structure of this proof in *LEAN* and then fill in the sorries.
"

/--
Given three non-collinear points A, B, C and a line ℓ, if A and B are on the same side of
ℓ and B and C are on the same side of ℓ, then A and C are on the same side of ℓ.
-/
Statement same_side_trans_of_noncollinear (hCol : ¬ collinear A C B):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C := by
  intro hAB hBC
  by_contra hc
  rcases not_same_side_intersection hc with ⟨D, hD1, hD2⟩
  have hB : B ∉ line_through A C := not_mem_line_of_noncollinear hCol
  have hAℓ : A ∉ ℓ := not_in_line_of_same_side_left hAB
  have hBℓ : B ∉ ℓ := not_in_line_of_same_side_right hAB
  have hCℓ : C ∉ ℓ :=not_in_line_of_same_side_right hBC
  rcases hD1 with hD1 | hD1 | hD1
  · rw [hD1] at hD2
    tauto
  · rw [hD1] at hD2
    tauto
  · have H := pasch hB hAℓ hCℓ hBℓ hD2 hD1
    rcases H with H | H
    · tauto
    · tauto

NewTheorem IncidencePlane.pasch
