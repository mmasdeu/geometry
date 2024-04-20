import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level01

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "PlaneSeparationWorld"
Level 2

Title "Reflexivity"

Introduction
"In this (easy!) level we prove that a point outside a line is on the same side of the line as itself.
It seems stupid, but needs to be proven nevertheless.
"


/--
A is at the same side as A of ℓ.
-/
@[simp] Statement same_side_reflexive (h : A ∉ ℓ): same_side ℓ A A := by
  simp
  assumption

TheoremTab "PSep"
