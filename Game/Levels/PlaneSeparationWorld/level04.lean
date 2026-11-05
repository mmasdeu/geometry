import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level03

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "PlaneSeparationWorld"
Level 4

Title "On the way to the final level (I)"

Introduction
"
Welcome to the last trip of The Euclid Game! This is the first of a few small lemmas we need before the final level.
We'll give you the paper proof each time, so you can follow along. Read the lemma, sketch the situation on paper, and off we go!

## Mathematical proof in paper...

**Claim:** Given three non-collinear points A, B and C, then A ≠ C.

**Proof:**

We want to show `A ≠ C`, which means `(A = C) → false`. So let's assume `A = C` and look for a contradiction.
We know A, B, C are non-collinear, that is, `collinear {A, C, B} → false`. So it's enough to prove that A, B, C *are* collinear.
Since `A = C`, we have `collinear {A, C, B} = collinear {C, C, B}`. So we need a line ℓ such that every point P of `{C, C, B}` lies on ℓ.
Let's take ℓ to be the line through B and C. Now P is either C or B.
If P = C, we need `C ∈ line_through B C`. That's the first axiom of incidence (`line_through_right`).
If P = B, we need `B ∈ line_through B C`. That's the first axiom of incidence again (`line_through_left`).
"



/--
If A, B and C are three non-collinear points, then A ≠ C.
-/
Statement neq_points_of_noncollinear (hCol : ¬ collinear A C B) : A ≠ C := by
  intro h
  apply hCol
  rw [h] at hCol ⊢
  use line_through C B
  simp [hCol]

TheoremTab "PSep"
