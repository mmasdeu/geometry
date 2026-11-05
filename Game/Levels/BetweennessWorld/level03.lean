import Game.Metadata
import Game.Levels.BetweennessWorld.level02

open IncidencePlane --hide



World "BetweeenessWorld"
Level 3

Title "Points that are in between of each other share a line"

Introduction
"
This time we hand you the paper proof. Remember you can use theorems from previous worlds too.

**Claim:** A point that lies between two different points lies on the same line as them.

**Proof:** Let $B$ be the point that lies between $A$ and $C$, where these two are different points that lie on the line `r`.

**(i)** First, there is a line, say $s$, containing $A$, $B$, and $C$: by the first axiom of order
`collinear_of_between`, since $A * B * C$, that gives it to us.

**(ii)** Next, $A\\neq C$. Why? If we had $A = C$, then $A * B * C$ would be equal to $C * B * C$. By the lemma `no_point_between_a_point`, that's
impossible, so $A \\neq C$.

**(iii)** Finally, $r = s$, by using the lemma `equal_lines_of_contain_two_points`.
So $B \\in s$ (from **(i)**) means $B \\in r$, and we are done: $B$ is on the same line $r$ as $A$ and $C$.
"


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

/- Lemma :
A point that lies between two different collinear points shares the same line with them.
-/
Statement between_points_share_line_2 (h : A * B * C) (hAr : A ∈ r) (hCr : C ∈ r) : B ∈ r := by
  have hs : collinear A B C := collinear_of_between h
  rcases hs with ⟨s, hAs, hBs, hCs⟩
  have hAC : A ≠ C
  · intro hAC
    rw [hAC] at h
    apply no_point_between_a_point h
  have hrs : r = s
  · apply equal_lines_of_contain_two_points hAC <;> simp [*]
  rw  [← hrs] at hBs
  assumption

TheoremTab "· * · * ·"
