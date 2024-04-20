import Game.Metadata
import Game.Levels.BetweennessWorld.level01

open IncidencePlane --hide



World "BetweeenessWorld"
Level 2

Title "Don't try to break a point into two..."

Introduction
"
In this level, we are asked to show that points cannot be splitted.
You may want to use the first axiom of order `different_of_between_??`,
there are three variations you can use which you can find in the list of *Theorems*.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} --hide

/--
There are no points between a point and itself.
-/
@[simp] Statement no_point_between_a_point {A B : Ω} : ¬ (A * B * A) := by
  intro h
  have hAx : A ≠ A
  · apply different_of_between_13 h
  tauto

NewTheorem IncidencePlane.different_of_between_12
IncidencePlane.different_of_between_13
IncidencePlane.different_of_between_23
TheoremTab "· * · * ·"
