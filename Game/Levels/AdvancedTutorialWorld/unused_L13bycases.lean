import Game.Metadata
import Game.Levels.AdvancedTutorialWorld.L12rcases3exists

open IncidencePlane --hide

World "AdvancedTutorialWorld"
Level 4

Title "The `by_cases` tactic"

variable {Ω : Type} [IncidencePlane Ω] --hide


Introduction
"
In this level, we introduce the `by_cases` tactic. Mathematicians would use it to provide a *proof by cases*.
This is useful when we need to split a proof into different cases.
For example, if we are asked to solve a goal of the form `⊢ P ∨ ¬ P`, then `by_cases h : P` will split the goal into two cases,
assuming `h : P` in the first branch, and `h : ¬ P` in the second branch. With that being said, let's try to solve this level!

[**Tip:** You may want to write the `∈` symbol to solve this level. To do so, type `\\in` and then hit the space bar. Analogously,
you can write the `∉` symbol by typing `\notin` and then hitting the space bar.]
"

variable {Ω : Type} [IncidencePlane Ω] --hide

/--
Either a point is in a line or it is not.
-/
Statement {A : Ω} {r : Line Ω} : A ∈ r ∨ A ∉ r := by
  by_cases h : A ∈ r
  · tauto
  · tauto

NewTactic by_cases
