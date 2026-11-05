import Game.Metadata
import Game.Levels.BetweennessWorld.level04

open IncidencePlane --hide



World "BetweeenessWorld"
Level 5

Title "Another version of the previous level"

Introduction
"
Another version that will come in handy later. Like before, you'll need `incidence` plus one of the
`different_of_between_..` theorems to show that `A` and `B` are different.

```
A ---- B ---- C
=====line_through A B=====>
```
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

/--
Given three points A B C such that A * B * C, the third one is in the line through the others.
-/
Statement mem_line_through_of_between_3 (h : A * B * C) : C ∈ line_through A B := by
  rcases (collinear_of_between h) with ⟨ℓ, hAℓ, hBℓ, hCℓ⟩
  have hAB : A ≠ B := different_of_between_12 h
  have h' : ℓ = line_through A B := incidence hAB hAℓ hBℓ
  rw [←h']
  assumption

Conclusion "On to the next level! We'll hand you the variations of this one for free,
since they're proved in a very similar way."

TheoremTab "· * · * ·"
