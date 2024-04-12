import Game.Metadata
open IncidencePlane --hide

World "TutorialWorld"
Level 6

Title "Intro(ducing) hypotheses"


Introduction
"
This level introduces the `intro` tactic. This allows you to create
a new hypothesis in the local context, just above the goal with the `⊢` symbol, whenever you see
the `→` symbol in the 'goal' section. [**Remember:** the `→` symbol refers to the idea of
an **implication**. `P → Q` is read as 'P implies Q' and interpreted as 'If P happens, then Q also happens'.]
In Lean, if we have the goal `⊢ IT RAINS → I GET WET`, by typing `intro h` we will get a new hypothesis in
the local context of the type `h : IT RAINS` and the goal will just change into  `⊢ I GET WET`.

To solve this level, you will need to use a theorem that has been added to the list of *Theorems*.
Its name is `incidence`, you can see what it does by clicking on it.


**Pro tip:** instead of writing
several lines of code with the `intro` tactic, you can put them all together. This will make the computer understand
that you want to create more than one hypothesis at the same time. For example, if you type `intro h1 h2 h3 h4,`, four
new hypotheses will be added to your local context. Once you've added all the possible hypotheses to it, try to compare
the goal with the `incidence` statement. Did you notice that we can `rewrite` that statement? Because we have the first
three **hypotheses** of the statement, we can change the line `r` into `line_through A B`! Type `rw incidence h1 h2 h4` and
see how the goal changes. To close the goal, try to apply the same argument to the line `s`.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} {r s : Line Ω} -- hide

/--
If two lines contain two distinct points, then they are the same line.
-/
Statement : A ≠ B → A ∈ r → A ∈ s → B ∈ r → B ∈ s → r = s := by
  intro h1 h2 h3 h4 h5
  rw [incidence h1 h2 h4]
  rw [incidence h1 h3 h5]

NewTactic intro

theorem equal_lines_of_contain_two_points (hAB : A ≠ B) (hAr : A ∈ r := by simp [*])
(hAs : A ∈ s := by simp [*]) (hBr : B ∈ r := by simp [*])
(hBs : B ∈ s := by simp [*]) : r = s := by
  rw [incidence hAB hAr hBr]
  rw [incidence hAB hAs hBs]

NewTheorem IncidencePlane.incidence equal_lines_of_contain_two_points
