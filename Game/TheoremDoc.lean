import GameServer.Commands


/--
The line through `A` and `B`
-/
DefinitionDoc IncidencePlane.line_through as "line_through A B"

/--
Two points `A` and `B` are on the `same_side` of `ℓ` if they do not belong
to `ℓ`, and there is not point in `ℓ` between `A` and `B`.
-/
DefinitionDoc IncidencePlane.same_side as "same_side ℓ A B"
/--
The line through `A` and `B` contains `A`
-/
TheoremDoc IncidencePlane.line_through_left as "line_through_left" in "∈"

/--
The line through `A` and `B` contains `B`
-/
TheoremDoc IncidencePlane.line_through_right as "line_through_right" in "∈"

/--
If two distinct points `P` and `Q` are on the line `ℓ`, then `ℓ = line_trhough P Q`
-/
TheoremDoc IncidencePlane.incidence as "incidence" in "∈"

/--
If two lines contain two different points, then they are equal
-/
TheoremDoc equal_lines_of_contain_two_points as "equal_lines_of_contain_two_points" in "∈"

/--
The line through two points does not depend on the order of the two points
-/
TheoremDoc line_through_symmetric as "line_through_symmetric" in "∈"

/--
If two points lie in two distinct lines, then they are equal
-/
TheoremDoc equal_points_of_in_two_lines as "equal_points_of_in_two_lines" in "∈"

/--
There exists three distinct non-collinear points
-/
TheoremDoc IncidencePlane.existence as "existence" in "∈"

/--
One can show that two lines are different if there is a point in one of them and not in the other
-/
TheoremDoc ne_line_of_not_share_point as "ne_line_of_not_share_point" in "∈"

/--
If two lines are different, then there is a point in the first one and not in the second
-/
TheoremDoc point_in_line_difference as "point_in_line_difference" in "∈"

/--
There exists three pairwise distinct lines
-/
TheoremDoc three_distinct_lines as "three_distinct_lines" in "∈"

/--
Every line contains at least two points
-/
TheoremDoc IncidencePlane.line_contains_two_points as "line_contains_two_points" in "∈"


/--
(A * B * C) ↔ (C * B * A)
-/
TheoremDoc IncidencePlane.between_symmetric as "between_symmetric" in "· * · * ·"


/--
(A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C)
-/
TheoremDoc IncidencePlane.different_of_between as "different_of_between" in "· * · * ·"

/--
(A * B * C) → A ≠ B
-/
TheoremDoc IncidencePlane.different_of_between_12 as "different_of_between_12" in "· * · * ·"

/--
(A * B * C) → A ≠ C
-/
TheoremDoc IncidencePlane.different_of_between_13 as "different_of_between_13" in "· * · * ·"

/--
(A * B * C) → B ≠ C
-/
TheoremDoc IncidencePlane.different_of_between_23 as "different_of_between_23" in "· * · * ·"

/--
(A * B * C) → ∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ
-/
TheoremDoc IncidencePlane.collinear_of_between as "collinear_of_between" in "· * · * ·"

/--
If A B C D E F are any six points such that the set {A, B, C} = {D, E, F},
then A, B, C are collinear if and only if D, E, F are.
-/
TheoremDoc IncidencePlane.collinear_of_equal as "collinear_of_equal" in "∈"

/--
A ≠ B → ∃ C, A * B * C
-/
TheoremDoc IncidencePlane.point_on_ray as "point_on_ray" in "· * · * ·"

/--
((A * B * C) ∧ ¬ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
(¬ (A * B * C) ∧ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
(¬ (A * B * C) ∧ ¬ ( B * A * C ) ∧ (A * C * B))
-/
TheoremDoc IncidencePlane.between_of_collinear as "between_of_collinear" in "· * · * ·"

/--
  Given three non-collinear points A B C and a line ℓ not containing any of them, suppose there
  is a point D ∈ ℓ between A and B. Then there is a point in ℓ between A and C or between B and C.
-/
TheoremDoc IncidencePlane.pasch as "pasch" in "PSep"

/--
Given three distinct collinear points A, B and C, if B lies between A and C, then A does not lie between B and C.
-/
TheoremDoc not_between_of_between as "not_between_of_between" in "· * · * ·"

/--
Points that are between each other are different
-/
TheoremDoc IncidencePlane.different_of_between as "different_of_between" in "· * · * ·"

/--
There are no points between a point and itself.
-/
TheoremDoc no_point_between_a_point as "no_point_between_a_point" in "· * · * ·"

/--
A point that lies between two different collinear points shares the same line with them.
-/
TheoremDoc between_points_share_line as "between_points_share_line" in "· * · * ·"

/--
Given two different collinear points A and B, there is a third C that shares the same line with them and satisfies A * B * C.
-/
TheoremDoc between_points_share_line_v2 as "between_points_share_line_v2" in "· * · * ·"

/--
Given three points A B C such that A * B * C, the third one is in the line through the first two.
-/
TheoremDoc mem_line_through_of_between as "mem_line_through_of_between" in "· * · * ·"

/--
Given three points A B C such that A * B * C, the third one is in the line through the first two.
-/
TheoremDoc mem_line_through_of_between' as "mem_line_through_of_between'" in "· * · * ·"

/--
The only point on the segment $AA$ is $A itself.
-/
TheoremDoc one_point_segment as "one_point_segment" in "· * · * ·"

/--
If the segment $PQ$ is on the same side of a line $\ell$, then $P \notin ℓ$.
-/
TheoremDoc not_in_line_of_same_side_left as "not_in_line_of_same_side_left" in "PSep"

/--
If the segment $PQ$ is on the same side of a line $\ell$, then $Q \notin ℓ$.
-/
TheoremDoc not_in_line_of_same_side_right as "not_in_line_of_same_side_right" in "PSep"

/--
Given three distinct points, they are on the same line if and only if they are collinear.
-/
TheoremDoc collinear_iff_on_line_through as "collinear_iff_on_line_through" in "PSep"

/--
A is at the same side as A of ℓ.
-/
TheoremDoc same_side_reflexive as "same_side_reflexive" in "PSep"

/--
A is at the same side as B of ℓ if and only if B is at the same side of A of ℓ.
-/
TheoremDoc same_side_symmetric as "same_side_symmetric" in "PSep"

/--
Given a line ℓ and the segments A·B and B·C, if both segments are on the same side of ℓ, then `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`.
-/
TheoremDoc same_side_of_noncollinear_ne_line as "same_side_of_noncollinear_ne_line" in "PSep"

/--
If two points A and C are not on the same side of the line ℓ, there exists a point in the segment A·C which is incident with the line ℓ.
-/
TheoremDoc not_same_side_intersection as "not_same_side_intersection" in "PSep"

/--
If a line cuts properly the segment AB, of a triangle ABC, then cuts properly either
AC or BC, but not both.
-/
TheoremDoc same_side_pasch as "same_side_pasch" in "PSep"

/--
Given lines $m$ and $\ell$ and a point $A$ in $m$ and not in $\ell$, there
exists a point $E$ not in $m$ on the same side of $\ell$ as $A$.
-/
TheoremDoc auxiliary_point as "auxiliary_point" in "PSep"

/--
Given three non-collinear points A, B and C, then B is not incident with the line through A and C.
-/
TheoremDoc not_mem_line_of_noncollinear as "not_mem_line_of_noncollinear" in "PSep"

/--
Given three non-collinear points A, B and C, then A ≠ C.
-/
TheoremDoc neq_points_of_noncollinear as "new_points_of_noncollinear" in "PSep"

/--
Given three non-collinear points A, B, C and a line ℓ, if A and B are on the same side of
ℓ and B and C are on the same side of ℓ, then A and C are on the same side of ℓ.
-/
TheoremDoc same_side_trans_of_noncollinear as "same_side_of_noncollinear" in "PSep"

/--
Given three collinear points A, B, C and a line ℓ, if A and B are on the same side of
ℓ and B and C are on the same side of ℓ, then A and C are on the same side of ℓ.
-/
TheoremDoc same_side_trans_of_collinear as "same_side_trans_of_collinear" in "PSep"
