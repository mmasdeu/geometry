import Game.Metadata
import Game.Levels.IncidenceWorld.level06

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

World "IncidenceWorld"
Level 8

Title "A useful rewrite"

Introduction
"
In the worlds to come we'll often need this criterion for collinearity. Here are some hints to help you through it!

**Hint 1:** Whenever you see the word `collinear`, the `rw` tactic will make progress.

**Hint 2:** Whenever you find a goal or hypothesis of the form `∀ {X : Ω}, X ∈ {A, B, C} → X ∈ r`, the `simp` tactic will make progress.

**Hint 2.5:** If `h : P ∧ Q ∧ R`, then `h.1 : P`, `h.2.1 : Q` and `h.2.2 : R`. After `rcases h1 with ⟨ℓ, hℓ⟩` the hypothesis `hℓ`
has exactly this form.

**Hint 3:** For the first goal, try the theorem `incidence` with the `rw` tactic. Writing `rw [← incidence ...]` (with the
arrow `←`, typed `\\l`) replaces `line_through A B` by `ℓ` instead of the other way round.
"


/--
Given three distinct points, they are collinear if and only if the last one is in the line through the first two.
-/
Statement collinear_iff_on_line_through (h : A ≠ B) : collinear A B C ↔ C ∈ line_through A B := by
  constructor
  · intro h1
    rw [collinear] at h1
    rcases h1 with ⟨ℓ, hℓ⟩
    rw [← (incidence h hℓ.1 hℓ.2.1)]
    apply hℓ.2.2
  · intro h1
    rw [collinear]
    use line_through A B
    simp
    assumption

TheoremTab "∈"

NewDefinition IncidencePlane.collinear
