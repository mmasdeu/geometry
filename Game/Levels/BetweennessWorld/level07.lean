import Game.Metadata
import Game.Levels.BetweennessWorld.level06

open IncidencePlane --hide



World "BetweeenessWorld"
Level 7

Title "The `point_on_ray` axiom"

Introduction
"
Let's practice with one more axiom: `point_on_ray A B` is a point `C` with `A * B * C`.
The fact that it really works is called `point_on_ray_prop h`, where `h` is a proof that `A ≠ B`.

You'll use it twice: first with `A ≠ B` to get `C`, then with `B ≠ C`
(which follows from `A * B * C` via one of the `different_of_between_..` theorems) to get `D`.

```
A ---- B ---- C ---- D
```
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} --hide

/--
Given two distinct points A, B, there exist points C, D such that A * B * C and B * C * D.
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
