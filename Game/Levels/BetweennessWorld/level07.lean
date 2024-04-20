import Game.Metadata
import Game.Levels.BetweennessWorld.level06

open IncidencePlane --hide



World "BetweeenessWorld"
Level 7

Title "The `point_on_ray` axiom"

Introduction
"
In this level we will practice using another axiom of Betweenness, namely the `point_on_ray`. This says
that given two distinct points A, B, there exists a third point C such that A * B * C. You will have
to apply it twice to get the two points sought in this level.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} --hide

/--
Given two distinct points A, B, there exist points C, D such that A * B * C* and B * C * D.
-/
Statement  (h : A ≠ B) : ∃ C D, (A * B * C) ∧ (B * C * D) := by
  rcases (point_on_ray h) with ⟨C, hC⟩
  have hBC : B ≠ C
  · apply different_of_between_23 hC
  rcases (point_on_ray hBC) with ⟨D, hD⟩
  use C
  use D

NewTheorem IncidencePlane.point_on_ray

TheoremTab "· * · * ·"
