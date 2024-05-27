import Game.Metadata
import Game.Levels.BetweennessWorld.level06

open IncidencePlane --hide



World "BetweeenessWorld"
Level 7

Title "The `point_on_ray` axiom"

Introduction
"
In this level we will practice using another axiom of Betweenness, namely the `point_on_ray A B`. This is
supposed to be a point C such that A * B * C, but its the axiom that asserts this is called `point_on_ray_prop h`,
where `h` is a proof of the fact that A ≠ B.
You will have
to apply it twice to get the two points sought in this level.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} --hide

/--
Given two distinct points A, B, there exist points C, D such that A * B * C* and B * C * D.
-/
Statement  (h : A ≠ B) : ∃ C D, (A * B * C) ∧ (B * C * D) := by
  set C := point_on_ray A B
  set D := point_on_ray B C
  have hABC : A * B * C := point_on_ray_prop h
  have hBE : B ≠ C := different_of_between_23 hABC
  have hBCD : B * C * D := point_on_ray_prop hBE
  use C
  use D

NewDefinition IncidencePlane.point_on_ray
NewTheorem IncidencePlane.point_on_ray_prop

TheoremTab "· * · * ·"
