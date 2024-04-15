import Game.Metadata
import Game.Levels.AdvancedTutorialWorld.L16simp
open IncidencePlane --hide

World "AdvancedTutorialWorld"
Level 9

Title "The `exfalso` tactic"

variable {Ω : Type} [IncidencePlane Ω] --hide


Introduction
"
In this level we introduce the new tactic `exfalso`. It satifies the *Principle of explosion* of classical logic,
according to which any statement can be proven from a contradiction. In Lean, if we type `exfalso`, the goal will turn
into `⊢ false`. Let's solve this level to see how it works!

Delete the `sorry` and take a look at the hypothesis `h`, according to which the point P is not an element of the line
that passes through the points P and Q. This is a contradiction that can be rewritten as `¬ (P ∈ line_through P Q)`, where
the symbol ¬ means *not*. Moreover, it can also be rewritten as `P ∈ line_through P Q → false`. This last way of representing
the contradiction is key to complete this level. By typing `exfalso`, we know that the goal will change into `⊢ false`. Then, look
for a tactic that can turn the goal into `⊢ P ∈ line_through P Q` and you will be almost done! In case you get stuck, click right below for a hint.
"


variable {Ω : Type} [IncidencePlane Ω] --hide

/--
Prove that 2+2 is 5, using a false hypothesis.
-/
Statement (P Q : Ω) (h: P ∉ line_through P Q) : 2 + 2 = 5:= by
  exfalso
  apply h
  exact line_through_left P Q

NewTactic exfalso
