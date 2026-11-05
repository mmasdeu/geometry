import Game.Metadata
import Game.Levels.BetweennessWorld.level01

open IncidencePlane --hide



World "BetweeenessWorld"
Level 2

Title "Don't try to break a point into two..."

Introduction
"
Here we show that you can't squeeze a point between itself and itself. (Sorry, no point-splitting!)
The first axiom of order will help: `different_of_between_??`.
There are three variations in the *Theorems* list, and the numbers tell you which two of the three
points are different: `different_of_between_13` says that the first and third points of `A * B * C` are different.
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
