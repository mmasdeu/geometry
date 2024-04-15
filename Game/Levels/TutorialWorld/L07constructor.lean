import Game.Metadata
import Game.Levels.TutorialWorld.L06intro

open IncidencePlane --hide

World "TutorialWorld"
Level 7

Title "The constructor tactic"


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


/--
If two lines contain two distinct points, then they are the same line.
-/
Statement (P Q : Ω) : P ∈ (line_through P Q) ∧ Q ∈ (line_through P Q) := by
  constructor
  · exact line_through_left P Q
  · exact line_through_right P Q

NewTactic constructor
NewTheorem equal_lines_of_contain_two_points
