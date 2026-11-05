import Game.Levels.BetweennessWorld.level01
import Game.Levels.BetweennessWorld.level02
import Game.Levels.BetweennessWorld.level03
import Game.Levels.BetweennessWorld.level04
import Game.Levels.BetweennessWorld.level05
import Game.Levels.BetweennessWorld.level06
import Game.Levels.BetweennessWorld.level07

World "BetweeenessWorld"
Title "Betweenness World"

Introduction
"
## The axioms of order

These are the axioms of order (or betweenness). Hilbert (1862-1943) wrote them down while untangling Euclid's `Elements`,
where Euclid used ideas like \"between\" without ever saying what they mean.
There are four of them, and along the way we'll meet **segments**, **betweenness**, **line separation** and
**plane separation**. The star symbol **`*`** means betweenness: `A * B * C` reads \"B is between A and C\", like this:

```
A ------ B ------ C
```

Let's look at the axioms.

**B.1)** If $A ∗ B ∗ C$, then $A$, $B$, $C$ are three distinct points all lying on the same line, and $C ∗ B ∗ A$.

**B.2)** Given two distinct collinear points $A$ and $B$, there is a third point $C$ such that $A * B * C$.

**B.3)** Given 3 distinct collinear points $A$, $B$ and $C$, exactly one of them is between the other two.

**B.4)** [This axiom will be learned in the following world.]

Later we will define **segments**, which come out of the first three axioms.

## The axioms of order in Lean

You'll need the first three axioms to solve the levels here, so here they are in Lean.

The first axiom of order is divided into three statements:

* `between_symmetric {A B C : Ω} : (A * B * C) ↔ (C * B * A)`

* `different_of_between {A B C : Ω} : (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C)`

* `collinear_of_between {A B C : Ω} : (A * B * C) → ∃ ℓ : Line Ω, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ`

The second axiom of order is represented as follows:

* `point_on_ray (A B : Ω) : Ω`
* `point_on_ray_prop {A B : Ω} (h: A ≠ B) : A * B * (point_on_ray A B)`

The third axiom is a bit of a mouthful in Lean:

* `between_of_collinear {A B C : Ω} (h: ∃(ℓ : Line Ω), A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ) :
	  ((A * B * C) ∧ ¬ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	  (¬ (A * B * C) ∧ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	  (¬ (A * B * C) ∧ ¬ ( B * A * C ) ∧ (A * C * B))`
"

Image "images/between.png"
