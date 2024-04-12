import Game.Metadata
import Game.Levels.BetweennessWorld.level02

open IncidencePlane --hide



World "BetweeenessWorld"
Level 3

Title "Points that are in between of each other share a line"

Introduction
"
To solve this level, the mathematical proof in paper will be given to you. Remember that you can use theorem statements from previous worlds.

**Claim:** A point that lies between two different points shares the same line with them.

**Proof:** Let $B$ be the point that lies between $A$ and $C$, where these two are different points that lie on the line `r`.

**(i)** Observe first that there is a line, say $s$, containing $A$, $B$, and $C$: by the first axiom of order
`collinear_of_between`, since $A * B * C$, we can obtain it.

**(ii)** Note that $A\\neq C$. In fact if we had $A = C$, then $A * B * C$ would be equal to $C * B * C$. By the lemma `no_point_between_a_point`, this is
not possible, so we prove that $A \\neq C$.

**(iii)** Finally, we can prove that $r = s$, by using the lemma `equal_lines_of_contain_two_points`.
Therefore, $B \\in s$, which we proved in **(i)**, must be equivalent to $B \\in r$. Therefore, the point $B$ shares the same line $r$ with the points
$A$ and $C$, and we are done.
"


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B C P Q R : Ω} --hide
variable {ℓ r s t : Line Ω} --hide

/- Lemma :
A point that lies between two different collinear points shares the same line with them.
-/
Statement between_points_share_line (h : A * B * C) (hAr : A ∈ r) (hCr : C ∈ r) : B ∈ r := by
  have hs : ∃ s, A ∈ s ∧ B ∈ s ∧ C ∈ s := collinear_of_between h
  rcases hs with ⟨s, hAs, hBs, hCs⟩
  have hAC : A ≠ C
  · intro hAC
    rw [hAC] at h
    exact no_point_between_a_point h
  have hrs : r = s := equal_lines_of_contain_two_points hAC hAr hAs hCr hCs
  rw  [← hrs] at hBs
  assumption
