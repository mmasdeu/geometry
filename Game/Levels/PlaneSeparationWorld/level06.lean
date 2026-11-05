import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level05
import Mathlib.Tactic

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "PlaneSeparationWorld"
Level 6

Title "The Pasch Axiom in action!"

open scoped Classical

Introduction
"
Time to use Pasch for real! We'll prove that *being on the same side of $\\ell$* is transitive, as long as the three
points are non-collinear. So take non-collinear points $A$, $B$, $C$, with $A$ on the same side of $\\ell$ as $B$, and
$B$ on the same side as $C$. We want $A$ on the same side as $C$. Here's the plan.

1. Argue by contradiction: assume the segment $AC$ does meet $\\ell$.
2. Let $D \\in \\ell$ be the meeting point, so $A * D * C$.
3. Use Pasch to show that $\\ell$ meets the segment $AB$ or $BC$. That contradicts our hypotheses.

```
      B
     / \\
    /   \\      ℓ goes through D
   A--D--C     (and must exit via AB or BC)
```

This is the first time we use Pasch's axiom. Here's what it says:

`
pasch {A B C : Ω} {ℓ : Line Ω} (hnc : C ∉ line_through A B)
(hnAl : A ∉ ℓ) (hnBl : B ∉ ℓ) (hnCl : C ∉ ℓ) (hAB : ¬ same_side ℓ A B) :
  (same_side ℓ A C ∧ ¬same_side ℓ C B) ∨ (¬same_side ℓ A C ∧ same_side ℓ C B)
`

Note that `pasch` takes its three points as implicit arguments: Lean figures them out from the hypotheses you give it, so
the order of the hypotheses matters. Also, once you've reached a contradiction in a branch, `tauto` can
finish the job: it hunts for a contradiction among your hypotheses.

Try to write the skeleton of this proof in Lean, then fill in the sorries.
"

Image "images/trans_noncollinear_diagram.png"

/--
Given three non-collinear points A, B, C and a line ℓ, if A and B are on the same side of
ℓ and B and C are on the same side of ℓ, then A and C are on the same side of ℓ.
-/
Statement same_side_trans_of_noncollinear (hCol : ¬ collinear A C B):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C := by
  intro hAB hBC
  by_contra hc
  rcases not_same_side_intersection hc with ⟨D, hD1, hD2⟩
  have hB : B ∉ line_through A C
  · rw [collinear_iff_on_line_through] at hCol
    · assumption
    · apply neq_points_of_noncollinear hCol
  have hAℓ : A ∉ ℓ := not_in_line_of_same_side_left hAB
  have hBℓ : B ∉ ℓ := not_in_line_of_same_side_right hAB
  have hCℓ : C ∉ ℓ :=not_in_line_of_same_side_right hBC
  rcases hD1 with hD1 | hD1 | hD1
  · rw [hD1] at hD2
    tauto
  · rw [hD1] at hD2
    tauto
  · have H := pasch hB hAℓ hCℓ hBℓ hc
    rcases H with H | H
    · tauto
    · tauto

NewTheorem IncidencePlane.pasch
TheoremTab "PSep"
