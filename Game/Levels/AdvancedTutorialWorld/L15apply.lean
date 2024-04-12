import Game.Metadata
import Game.Levels.AdvancedTutorialWorld.L14bycases
open IncidencePlane --hide

World "AdvancedTutorialWorld"
Level 6

Title "The `apply` tactic"

variable {Ω : Type} [IncidencePlane Ω] --hide


Introduction
"
In this level, we introduce the new tactic `apply`. Suppose you are asked to prove a goal of the form `⊢ R` and you have a theorem statement called `h` which
ensures that `h : P → Q → R`. Then, `apply h` will change your goal into proving `⊢ Q` and `⊢ P`. Now, read the lemma and do a drawing of the situation. Once,
you're done, delete the 'sorry' and try to look for a theorem statement that ends with the form of the goal shown for this level: `⊢ line_through Q P = line_through P Q`.
Can you see that `incidence` is the right theorem statement to use? Type `apply incidence,` and make an effort to finish the proof on your own.
"

variable {Ω : Type} [IncidencePlane Ω] -- hide
variable {P Q : Ω} -- hide

/--
The line through two points is a symmetric concept.
-/
Statement line_through_symmetric : line_through Q P = line_through P Q := by
  by_cases h : P = Q
  · rw [h]
  · apply incidence
    exact h
    · exact line_through_right Q P
    · exact line_through_left Q P

NewTheorem line_through_symmetric
NewTactic apply
