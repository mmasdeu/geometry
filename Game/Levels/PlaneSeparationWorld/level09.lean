import Game.Metadata
import Game.Levels.PlaneSeparationWorld.level08

open IncidencePlane --hide


variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A E : Ω} --hide
variable {ℓ m : Line Ω} --hide

World "PlaneSeparationWorld"
Level 9

Title "Getting ready for the final level!"

open scoped Classical

Introduction
"
We are left with proving transitivity for collinear points. The trick in this case is to reduce to the known
case by a quite slick argument. The key step lies in the lemma below: given two lines $m$ and $\\ell$, and a point
$A$ on $m$ but not on $\\ell$, the goal is to find a new point $E$ which is not on $m$ and which is on the same side of $\\ell$
as $A$.

Here is a sketch of the proof, most of which has been replicated already for you in **LEAN** code.

1. Prove first that $\\ell$ and $m$ are distinct.
1. Let $D$ be a point on $\\ell$ not lying on $m$ (in particular, $D \\neq A$).
1. Using axiom (B2), find a point $E$ such that $D * A * E$. Let $s$ be the line through these points.
1. Prove that $E \notin \\ell$ (because $A \\notin \\ell$ and the intersection of $s$ and $\\ell$ already contains $D$). Note that this implies,
  in particular, that $\\ell ≠ s$.
1. Prove that $E \\notin m$:
    - Suppose it where, and show in that case that m = s.
    - Since $D \\in s$ but $D \\notin m$ we get a contradiction.
1. Show that $A$ is on the same side as $E$:
    - If the segment $AE$ did meet $\\ell$, the intersection point would be $D$.
    - This would mean that $A * D * E$.
    - Since we also have $D * A * E$, we would get a contradiction.

![Proof sketch](trans_collinear_diagram.png 'Proof of transitivity, collinear case')
"
/--
Given lines $m$ and $\ell$ and a point $A$ in $m$ and not in $\ell$, there
exists a point $E$ not in $m$ on the same side of $\ell$ as $A$.
-/
Statement auxiliary_point (hAm : A ∈ m) (hAs : A ∉ ℓ) :
  ∃ E, E ∉ m ∧ same_side ℓ A E := by
  have hℓm : ℓ ≠ m -- Prove that ℓ ≠ m
  · intro hc
    rw [hc] at hAs
    tauto
  have hD : ∃ D, D ∈ ℓ ∧ D ∉ m -- Therefore, there is a point in ℓ not in m.
  · exact point_in_line_difference hℓm
  rcases hD with ⟨D, ⟨hDℓ, hDm⟩⟩
  have hDA : D ≠ A
  · intro hc
    rw [hc] at hDm
    tauto
  have hE : ∃ E, D * A * E -- Prove that there is point E such that D * A * E
  · exact point_on_ray hDA
  rcases hE with ⟨E, hDAE⟩
  use E -- This is the sought E, prove it!
  constructor
  -- Prove that E ∉ m
  · intro hEm
    have hAE : A ≠ E := different_of_between_23 hDAE
    have hm : m = line_through A E
    · exact incidence hAE hAm hEm
    have : D ∈ m
    · rw [between_symmetric] at hDAE
      have hD : D ∈ line_through E A := mem_line_through_of_between_3 hDAE
      rw [line_through_symmetric] at hD
      rw [← hm] at hD
      exact hD
    tauto
  -- Prove that same_side ℓ A E
  · have hA : A ∈ line_through D E := mem_line_through_of_between_2 hDAE
    have hDE : D ≠ E := different_of_between_13 hDAE
    have hAE : A ≠ E
    · apply different_of_between_23 hDAE
    have hs' : line_through A E = line_through D E
    · apply equal_lines_of_contain_two_points hAE
    have hs : line_through A E = line_through A D
    · rw [hs']
      apply equal_lines_of_contain_two_points hDA
    simp [*]
    have hEℓ : E ∉ ℓ
    · intro hEℓ
      have hkey : ℓ = line_through D E := incidence hDE hDℓ hEℓ
      rw [← hkey] at hA
      tauto
    constructor
    · assumption
    · intro x hx hAxE
      have hℓs : line_through A E ≠ ℓ
      · apply ne_line_of_not_share_point _ _ hEℓ
        exact line_through_right A E
      have hxD : x = D
      · apply equal_points_of_in_two_lines hℓs (by exact mem_line_through_of_between_2 hAxE) hx _ hDℓ
        rw [between_symmetric] at hDAE
        rw [line_through_symmetric]
        exact mem_line_through_of_between_3 hDAE
      rw [hxD] at hAxE
      apply not_between_of_between hAxE hDAE
