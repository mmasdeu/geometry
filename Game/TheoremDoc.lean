import GameServer.Commands


/--
### **Logic Constants & Operators**
| **Name** | **ASCII**| **Unicode** | **Unicode Cmd**|
| --- | :---: | :---: | --- |
| True | `True` |  |  |
| False | `False` |  |  |
| Not | `Not` | ¬ | `\n` `\not` `\neg` `\lnot` |
| And | `/\` | ∧ | `\and` `\an` `\wedge` |
| Or | `\/` | ∨ | `\v` `\or` `\vee` |
| Implies | `->` | → | `\r` `\imp` `\->` `\to` `\r-` `\rightarrow` |
| Iff | `<->` | ↔ | `\iff` `\lr-` `\lr` `\<->` `\leftrightarrow` |
| For All | `forall` | ∀ | `\all` `\forall` |
| Exists | `exists` | ∃ | `\ex` `\exists` |


### **Other Unicode**
| **Name** | **Unicode** | **Unicode Cmd** |
| --- | :---: | --- |
| Membership | ∈ ∉  | `\in` `\notin` |
| Angle brackets | ⟨ ⟩ | `\<` `\>` `\langle` `\rangle` |
| Subscript Numbers | ₁ ₂ ₃ ... | `\1` `\2` `\3` ... |
| Left Arrow | ← | `\l` `\leftarrow` `\gets` `\<-` |
| Turnstyle | ⊢ | `\│-` `\entails` `\vdash` `\goal` |
-/
DefinitionDoc UnicodeTable as "Unicode Table"


/--
The line through `A` and `B`. (It's only meant to be the right line when `A ≠ B`.)
-/
DefinitionDoc IncidencePlane.line_through as "line_through A B"

/--
Two points `A` and `B` are on the `same_side` of `ℓ` if neither of them is on
`ℓ`, and no point of `ℓ` lies between `A` and `B`.
```
 A •        • B      same side of ℓ
 ────────────────  ℓ
```
-/
DefinitionDoc IncidencePlane.same_side as "same_side ℓ A B"

/--
Three points `A`, `B`, `C` are `collinear` if one single line contains all of them:
`collinear A B C ↔ ∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ`.
-/
DefinitionDoc IncidencePlane.collinear as "collinear A B C"

/--
Good news: the line through `A` and `B` always contains `A`.
-/
TheoremDoc IncidencePlane.line_through_left as "line_through_left" in "Axioms"

/--
And it always contains `B` too.
-/
TheoremDoc IncidencePlane.line_through_right as "line_through_right" in "Axioms"

/--
If two different points `P` and `Q` are on a line `ℓ`, then `ℓ` is *the* line through `P` and `Q`:
`ℓ = line_through P Q`. In other words, two points pin down a line.
```
 ──P────Q──── ℓ
```
Handy with `rw`: `rw [incidence h1 h2 h3]`, where `h1 : P ∈ ℓ`, `h2 : Q ∈ ℓ` and `h3 : P ≠ Q`.
-/
TheoremDoc IncidencePlane.incidence as "incidence" in "Axioms"

/--
If two lines share two different points, they're really the same line.
-/
TheoremDoc equal_lines_of_contain_two_points as "equal_lines_of_contain_two_points" in "∈"

/--
The line through `A` and `B` is the same as the line through `B` and `A`. Order doesn't matter.
-/
TheoremDoc line_through_symmetric as "line_through_symmetric" in "∈"

/--
If two different lines both contain two points `A` and `B`, then `A = B`. (Two lines can't share two different points.)
-/
TheoremDoc equal_points_of_in_two_lines as "equal_points_of_in_two_lines" in "∈"

/--
There are three distinct points that are not on a common line. (So the plane isn't just a line!)
-/
TheoremDoc IncidencePlane.existence as "existence" in "Axioms"

/--
To show two lines are different, find a point that's on one but not on the other.
-/
TheoremDoc ne_line_of_not_share_point as "ne_line_of_not_share_point" in "∈"

/--
If two lines are different, there's a point on the first that isn't on the second.
-/
TheoremDoc point_in_line_difference as "point_in_line_difference" in "∈"

/--
There are three lines that are pairwise different.
-/
TheoremDoc three_distinct_lines as "three_distinct_lines" in "∈"

/--
Every line has at least two points on it.
-/
TheoremDoc IncidencePlane.line_contains_two_points as "line_contains_two_points" in "Axioms"


/--
`(A * B * C) ↔ (C * B * A)`: `B` is between `A` and `C` exactly when it's between `C` and `A`.
```
 A ─── B ─── C
```
-/
TheoremDoc IncidencePlane.between_symmetric as "between_symmetric" in "Axioms"


/--
If `A * B * C` (`B` is between `A` and `C`), then `A ≠ B`.
-/
TheoremDoc IncidencePlane.different_of_between_12 as "different_of_between_12" in "Axioms"

/--
If `A * B * C`, then `A ≠ C`.
-/
TheoremDoc IncidencePlane.different_of_between_13 as "different_of_between_13" in "Axioms"

/--
If `A * B * C`, then `B ≠ C`.
-/
TheoremDoc IncidencePlane.different_of_between_23 as "different_of_between_23" in "Axioms"

/--
If `A * B * C`, then the three points lie on a common line: `∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ`.
-/
TheoremDoc IncidencePlane.collinear_of_between as "collinear_of_between" in "Axioms"

/--
If `A B C D E F` are six points and the set `{A, B, C}` equals the set `{D, E, F}`
(same points, maybe in a different order or repeated), then `A, B, C` are collinear
if and only if `D, E, F` are.
-/
TheoremDoc IncidencePlane.collinear_of_equal as "collinear_of_equal" in "∈"

/--
If `A ≠ B`, then `A * B * (point_on_ray A B)`: going from `A` through `B`, you can always go a bit further.
-/
TheoremDoc IncidencePlane.point_on_ray_prop as "point_on_ray_prop" in "Axioms"

/--
Given `A` and `B`, it gives you a point `C` further along the ray from `A` through `B`.
-/
DefinitionDoc IncidencePlane.point_on_ray as "point_on_ray"

/--
Among three collinear points, exactly one of them lies between the other two:
```
 A ─ B ─ C    or    B ─ A ─ C    or    A ─ C ─ B
```
Formally:

((A * B * C) ∧ ¬ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
(¬ (A * B * C) ∧ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
(¬ (A * B * C) ∧ ¬ ( B * A * C ) ∧ (A * C * B))
-/
TheoremDoc IncidencePlane.between_of_collinear as "between_of_collinear" in "· * · * ·"

/--
Pasch's axiom. Take three points `A B C` that aren't collinear, and a line `ℓ` that
contains none of them. If `A` and `B` are on opposite sides of `ℓ`, then exactly one
of these happens:
· `A` and `C` are on opposite sides of `ℓ`, or
· `B` and `C` are on opposite sides of `ℓ`.
```
     C
    / \
 ──/───\── ℓ     (ℓ cuts the triangle ABC
  A     B         through exactly two sides)
```
-/
TheoremDoc IncidencePlane.pasch as "pasch" in "PSep"

/--
Take three distinct collinear points `A, B, C`. If `B` is between `A` and `C`, then `A` is *not* between `B` and `C`.
-/
TheoremDoc not_between_of_between as "not_between_of_between" in "· * · * ·"

/--
There's no point between a point and itself: `A * B * A` is never true.
-/
TheoremDoc no_point_between_a_point as "no_point_between_a_point" in "· * · * ·"

/--
Betweenness is symmetric: `A * B * C ↔ C * B * A`.
-/
TheoremDoc IncidencePlane.between_symmetric as "between_symmetric" in "· * · * ·"
/--
Given `A * B * C`, if `B` and `C` are on a line `r`, then `A` is on `r` too.
-/
TheoremDoc between_points_share_line_1 as "between_points_share_line_1" in "· * · * ·"

/--
Given `A * B * C`, if `A` and `C` are on a line `r`, then `B` is on `r` too.
-/
TheoremDoc between_points_share_line_2 as "between_points_share_line_2" in "· * · * ·"

/--
Given `A * B * C`, if `A` and `B` are on a line `r`, then `C` is on `r` too.
-/
TheoremDoc between_points_share_line_3 as "between_points_share_line_3" in "· * · * ·"

/--
If `A * B * C`, then `A` is on the line through `B` and `C`.
-/
TheoremDoc mem_line_through_of_between_1 as "mem_line_through_of_between_1" in "· * · * ·"

/--
If `A * B * C`, then `B` is on the line through `A` and `C`.
-/
TheoremDoc mem_line_through_of_between_2 as "mem_line_through_of_between_2" in "· * · * ·"

/--
If `A * B * C`, then `C` is on the line through `A` and `B`.
-/
TheoremDoc mem_line_through_of_between_3 as "mem_line_through_of_between_3" in "· * · * ·"


/--
If `P` and `Q` are on the same side of a line $\ell$, then $P \notin \ell$.
-/
TheoremDoc not_in_line_of_same_side_left as "not_in_line_of_same_side_left" in "PSep"

/--
If `P` and `Q` are on the same side of a line $\ell$, then $Q \notin \ell$.
-/
TheoremDoc not_in_line_of_same_side_right as "not_in_line_of_same_side_right" in "PSep"

/--
For three distinct points, being collinear is the same as lying on the line through two of them.
-/
TheoremDoc collinear_iff_on_line_through as "collinear_iff_on_line_through" in "PSep"

/--
`A` is on the same side of `ℓ` as itself (as long as `A ∉ ℓ`).
-/
TheoremDoc same_side_reflexive as "same_side_reflexive" in "PSep"

/--
`A` is on the same side of `ℓ` as `B` if and only if `B` is on the same side as `A`.
-/
TheoremDoc same_side_symmetric as "same_side_symmetric" in "PSep"

/--
If `A` and `C` are not on the same side of `ℓ`, then some point of `ℓ` lies between `A` and `C`.
```
 A •
 ───X─── ℓ
     • C
```
-/
TheoremDoc not_same_side_intersection as "not_same_side_intersection" in "PSep"

/--
Given lines $m$ and $\ell$ and a point $A$ on $m$ but not on $\ell$, there is
a point $E$, not on $m$, on the same side of $\ell$ as $A$.
-/
TheoremDoc auxiliary_point as "auxiliary_point" in "PSep"

/--
If `A, B, C` are not collinear, then `A ≠ C`.
-/
TheoremDoc neq_points_of_noncollinear as "neq_points_of_noncollinear" in "PSep"

/--
Take three non-collinear points `A, B, C` and a line `ℓ`. If `A` and `B` are on the same side of
`ℓ`, and `B` and `C` are on the same side of `ℓ`, then `A` and `C` are on the same side of `ℓ`.
-/
TheoremDoc same_side_trans_of_noncollinear as "same_side_trans_of_noncollinear" in "PSep"

/--
Same as before, but for three collinear points `A, B, C`: if `A` and `B` are on the same side of
`ℓ`, and `B` and `C` are on the same side of `ℓ`, then `A` and `C` are on the same side of `ℓ`.
-/
TheoremDoc same_side_trans_of_collinear as "same_side_trans_of_collinear" in "PSep"
