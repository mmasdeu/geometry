import Game.Metadata
import Game.Levels.BetweennessWorld

open IncidencePlane --hide


World "PlaneSeparationWorld"
Level 1

Title "Same side"

Introduction
"
Thanks to Pasch's axiom we can say what *being on the same side* means. Let's do it!

**Definition:** Given a line ℓ and points A and B, both not on ℓ, we say that A and B are on the same side if
the segment A·B does not meet ℓ (or if A = B).

```
  A •        • B        <- same side: segment AB never touches ℓ
 ─────────────────── ℓ
```

In Lean, `same_side` is defined like this:

* `def same_side (ℓ : Line Ω) (P Q : Ω) :=  P ∉ ℓ ∧ Q ∉ ℓ ∧ (∀ x, (P * x * Q) → x ∉ ℓ)`


**Rule of thumb:** whenever you see `same_side` in Lean, you can use `rw` to unfold it. That usually makes it much easier to see what's going on.
If it's in a hypothesis `h2`, write `rw [same_side] at h2`. If it's in the goal, `rw [same_side]` is enough.

As a bonus, we're giving you a handy lemma for free (you could prove it easily by now, we're just saving you time). It lets you
shuffle the order of the points in a collinearity statement:

* `lemma collinear_of_equal (A B C D E F)
  ({A, B, C} = {D, E, F}) → collinear A B C ↔ collinear D E F`

Lean will even fill in the proof that the two sets are equal, whenever that's obvious.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} --hide
variable {ℓ : Line Ω} --hide

/--
If $A$ and $B$ are on the same side of a line $\ell$, then $A \notin ℓ$.
-/
Statement not_in_line_of_same_side_left (h : same_side ℓ A B) : A ∉ ℓ := by
  rw [same_side] at h
  tauto


lemma not_in_line_of_same_side_right (h : same_side ℓ A B) : B ∉ ℓ := by
  rw [same_side] at h
  tauto

NewDefinition IncidencePlane.same_side
NewTheorem IncidencePlane.collinear_of_equal not_in_line_of_same_side_left not_in_line_of_same_side_right

TheoremTab "PSep"
