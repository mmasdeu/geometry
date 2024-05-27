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

Also called the axioms of betweenness, the axioms of order were formalized by David Hilbert (1862-1943 AD) on the occasion of studying the Euclid's `Elements`.
When it comes to them, there are up to four axioms of order. Their learning involves the definition of **segment**, **betweenness**, **line separation** and
**plane separation**, among others. In written mathematics, the notion of **betweenness** is represented by the **`*`** symbol. Now, let's take a look at the axioms of order.

**B.1)** If $A ∗ B ∗ C$, then $A$, $B$, $C$ are three distinct points all lying on the same line, and $C ∗ B ∗ A$.

**B.2)** Given two distinct collinear points $A$ and $B$, there is a third point $C$ such that $A * B * C$.

**B.3)** Given 3 distinct collinear points $A$, $B$ and $C$, exactly one of them is between the other two.

**B.4)** [This axiom will be learned in the following world.]

Later on this world we will learn the definition of **segment**, which can be inferred from the first three axioms of order.

## The axioms of order in Lean

To solve the levels of this world, we may need to use the first three axioms of order, so below
you have them in Lean format.

The first axiom of order is divided into three statements:

* `between_symmetric {A B C : Ω} : (A * B * C) ↔ (C * B * A)`

* `different_of_between {A B C : Ω} : (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C)`

* `collinear_of_between {A B C : Ω} : (A * B * C) → ∃ ℓ : Line Ω, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ`

The second axiom of order is represented as follows:

* `point_on_ray (A B : Ω) : C : Ω
* `point_on_ray_prop {A B : Ω} (h: A ≠ B) : A * B * (point_on_ray A B)`

The third axiom of order is a bit long to spell out in Lean:

* `between_of_collinear {A B C : Ω} (h: ∃(ℓ : Line Ω), A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ) :
	  ((A * B * C) ∧ ¬ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	  (¬ (A * B * C) ∧ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	  (¬ (A * B * C) ∧ ¬ ( B * A * C ) ∧ (A * C * B))`
"

Image "images/between.png"
