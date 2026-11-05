import Game.Metadata
import Game.Levels.IncidenceWorld.level07

open IncidencePlane --hide



World "IncidenceWorld"
Level 9

Title "Triangles"

Introduction
"
We finish this world by proving that triangles exist. Almost there!

Some Lean tips to help you along:

**Tip 1:** Whenever a hypothesis looks like `h : P ∧ Q`, you can refer to `P` and `Q` as `h.1` and `h.2`, respectively.

**Tip 2:** Whenever your goal looks like `⊢ ∀ (P : Ω), ...`, the `intro` tactic will make progress.

**Strategy:** Take non-collinear points `A, B, C` and the three lines `AC`, `BC`, `AB`. A point `P` on all three would have to be `C`
(the only common point of `AC` and `BC`), but `C` is not on `AB`. For this you first need `line_through A C ≠ line_through B C`;
the theorem `ne_line_of_not_share_point` helps to prove that, and `equal_points_of_in_two_lines` (see the *Theorems* tab)
says two different lines share at most one point.

```
      C
     / \\
    /   \\       the three lines AC, BC, AB
   A-----B      have no common point
```

If you get stuck, go back to the previous levels to remember how the tactics work. Good luck, let's do this!
"

variable {Ω : Type} [IncidencePlane Ω] --hide

/--
There exist three lines that do not have a point in common.
-/
Statement three_distinct_lines : ∃ (r s t: Line Ω), (∀ (P : Ω),
¬(P ∈ r ∧ P ∈ s ∧ P ∈ t)) := by
  rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩
  use line_through A C
  use line_through B C
  use line_through A B
  simp
  intro P h1 h2
  have hkey : line_through A C ≠ line_through B C
  · apply ne_line_of_not_share_point A
    · simp
    · intro hc
      apply h
      have lABeqlBC : line_through A B = line_through B C
      · apply equal_lines_of_contain_two_points hAB <;> simp [*]
      rw [lABeqlBC]
      apply line_through_right
  rw [equal_points_of_in_two_lines hkey h1 (line_through_right A C) h2 (line_through_right B C)]
  assumption


NewTheorem three_distinct_lines


Conclusion "Great job! You're now ready to study a new set of axioms!"
TheoremTab "∈"
