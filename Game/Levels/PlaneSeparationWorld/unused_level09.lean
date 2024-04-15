import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level08

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "PlaneSeparationWorld"
Level 9

Title "A reformulation of Pasch axiom"

Introduction
"
We prove a more useful way of stating Pasch axiom, using the concept of `same_side`. This form will be
the one that we will use in our application. Of course, we need to use Pasch's axiom in the proof!
"

/--
If a line cuts properly the segment AB, of a triangle ABC, then cuts properly either
AC or BC, but not both.
-/
Statement same_side_pasch {A B C : Ω} {ℓ : Line Ω} (hnc: C ∉ line_through A B)
(hnAl: (A ∉ ℓ)) (hnBl: B ∉ ℓ) (hnCl: C ∉ ℓ) (hAB : ¬ same_side ℓ A B) :
(same_side ℓ A C) ∨ (same_side ℓ B C) := by
  simp at hAB
  rcases hAB hnAl hnBl with ⟨D,⟨hD1,hD2⟩⟩
  have H := pasch hnc hnAl hnBl hnCl hD1 hD2
  rcases H
  · right
    have H' := h.2
    simp at H'
    simp [*]
    assumption
  · left
    have H' := h.1
    simp at H'
    simp [*]
    assumption

NewTheorem IncidencePlane.pasch
