import Game.Metadata
import Game.Levels.IncidenceWorld.level06

open IncidencePlane --hide



World "IncidenceWorld"
Level 7

Title "Triangles"

Introduction
"
We end this world by proving the existence of triangles. We will also make use of convenient tactic,
which is called `apply`. Suppose you are asked to prove a goal of the form `⊢ R` and you have a theorem statement called `h` which
ensures that `h : P → Q → R`. Then, `apply h` will change your goal into proving `⊢ Q` and `⊢ P`.

To give you some hints, remember these Lean tips that might help you to step through the proof.

**Tip 1:** whenever a hypothesis looks like `h : P ∧ Q`, we can refer to `P` and `Q` as `h.1` and `h.2`, respectively.

**Tip 2:** whenever you have a goal of the form `⊢ ∀ (P : Ω), ...`, the `intro` tactic will make progress.

If needed, you can go back to the previous levels to remember how to use some tactics. Good luck! Let's do this!
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
      have lABeqlBC : line_through A B = line_through B C := equal_lines_of_contain_two_points hAB
      rw [lABeqlBC]
      apply line_through_right
  rw [equal_points_of_in_two_lines (A := P) (B := C) hkey]
  assumption

-- NewTheorem three_distinct_lines

NewTactic apply

Conclusion "Great! Now you are ready to study a new set of axioms!"
