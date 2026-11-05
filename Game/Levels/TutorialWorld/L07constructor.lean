import Game.Metadata
import Game.Levels.TutorialWorld.L06intro

open IncidencePlane --hide

World "TutorialWorld"
Level 7

Title "The constructor tactic"
TheoremTab "∈"
Introduction
"
Time for the `constructor` tactic. It splits a goal `P ∧ Q` into two goals (first prove `P`, then prove `Q`).
It also splits a goal `P ↔ Q` into the two implications: first `P → Q`, then `Q → P`.
The symbol **∧** reads as **and**. For example, `IT RAINS ∧ I AM IN THE STREET → I OPEN THE UMBRELLA`.
The symbol **`↔`** is a **double implication**, an **if and only if** statement. On paper you'll often
see it written **iff**.

After `constructor` you'll have two goals. Tackle them one at a time, starting each with the bullet `·`
(typed `\\.`), as in `· apply ...`. Remember `line_through_left` and `line_through_right` from before.

You can do this one on your own. Three lines of code are enough.

As a bonus, this level also adds the theorem `equal_lines_of_contain_two_points` to your list. It'll come in handy later.
"


variable {Ω : Type} [IncidencePlane Ω] --hide

theorem equal_lines_of_contain_two_points (hAB : A ≠ B) {r s : outParam (Line Ω)}
(hAr : A ∈ r) (hBr : B ∈ r) (hAs : A ∈ s) (hBs : B ∈ s) : r = s := by
  rw [incidence hAB hAr hBr]
  rw [incidence hAB hAs hBs]


/--
Both P and Q belong to the line through P and Q (!!)
-/
Statement (P Q : Ω) : P ∈ (line_through P Q) ∧ Q ∈ (line_through P Q) := by
  constructor
  · apply line_through_left P Q
  · apply line_through_right P Q

NewTactic constructor
NewTheorem equal_lines_of_contain_two_points
