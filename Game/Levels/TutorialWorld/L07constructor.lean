import Game.Metadata
import Game.Levels.TutorialWorld.L06intro

open IncidencePlane --hide

World "TutorialWorld"
Level 7

Title "The constructor tactic"
TheoremTab "∈"
Introduction
"
In this level we will learn the `constructor` tactic. It breaks a goal of the type `P ∧ Q` into two goals (proving `P`, and then proving `Q`),
and also breaks goals of the form `P ↔ Q` into proving each of the implications separately. That is to say, it asks us to prove `P → Q` first, and
then `Q → P`. In mathematics and logic, the **∧** symbol is read as **and**. For example, `IT RAINS ∧ I AM IN THE STREET → I OPEN THE UMBRELLA`.
Analogously, the **`↔`** symbol refers to a **double implication**, or an **if and only if** statement. In written mathematics, you could also
find the **`↔`** symbol written as **iff**.

You should be able to solve this level on your own. You can solve it in three lines of code.
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
