import Game.Levels.IncidenceWorld.level00
import Game.Levels.IncidenceWorld.level01
import Game.Levels.IncidenceWorld.level02
import Game.Levels.IncidenceWorld.level03
import Game.Levels.IncidenceWorld.level04
import Game.Levels.IncidenceWorld.level05
import Game.Levels.IncidenceWorld.level06
import Game.Levels.IncidenceWorld.level07
import Game.Levels.IncidenceWorld.level08

World "IncidenceWorld"

Title "Incidence World"

Introduction
"
To build any theory, you need some starting points, and that's where axioms join the party.
Axioms are statements we don't prove: we simply agree to accept them as true *because they're self-evident*.
They're the raw material for all further reasoning, so we can reach new conclusions from them.

Let's hop in a time machine to 300 B.C. and meet Euclid, who wrote down the very first postulates of geometry
in his famous book **Elements**. Much later, David Hilbert (1862-1943 AD) gave geometry a much sturdier foundation.
Euclidean geometry can be built from three blocks of axioms, each adding new independent notions that we need to
define the plane: **incidence**, **order** and **congruence**. (We'll also want the **parallel axiom**, but that comes later.)

In this world we focus on the first block, the axioms of **incidence**. There are three of them, and they
describe how the primitive notions of **point** and **line** relate to each other. Here's the twist: *point* and *line*
are not defined anywhere! They can be whatever objects you like, as long as they satisfy the axioms. Before the
axioms, these notions are **undefined**.

So here are the axioms of incidence:

A.1. For every point $P$ and for every point $Q$ not equal to $P$, there exists a unique line $\\ell$
*passing through* (= incident with) $P$ and $Q$.

A.2. For every line $\\ell$, there exist two distinct points that belong to it.


A.3. There exist three distinct points with the property that no line *passes through* (= is incident with) all three of them.


The picture of the axioms (in the middle panel of the world page) may help you understand (or remember) each axiom, but they
have no meaning in mathematics. We can't use them in our proofs!

## The axioms of incidence in Lean.

How do we make the computer understand these statements? With **Lean**, of course! It's easier if we split
some of them into several pieces, so in Lean we get the following axioms:

* `line_through (P Q : Ω) : Line Ω`

Given two points, this produces a line through them. Think of it as a function that eats
two points $P$ and $Q$ and spits out a line $\\ell$ called `line_through P Q`.

* `line_through_left (P Q : Ω) : P ∈ (line_through P Q)`

* `line_through_right (P Q : Ω) : Q ∈ (line_through P Q)`

These two guarantee that `line_through P Q` really contains both $P$ and $Q$.
The next one is about uniqueness, so we need $P \\neq Q$ here. We already know one line through $P$ and $Q$,
namely `line_through P Q`. The `incidence` statement says that if some
line $\\ell$ contains both $P$ and $Q$, then $\\ell$ has to be `line_through P Q`.

* `incidence {P Q : Ω} {ℓ : Line Ω} : P ≠ Q → P ∈ ℓ → Q ∈ ℓ → ℓ = line_through P Q`

The second axiom is quite direct in **Lean**:

* `line_contains_two_points (ℓ : Line Ω) : ∃ P Q : Ω, P ≠ Q ∧ ℓ = line_through P Q`

The third axiom translates easily too. To say that three points are
non-collinear, we say that the third point $R$ does not lie on the (unique) line through $P$ and $Q$.

* `existence (Ω : Type) : ∃ P Q R : Ω, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ R ∉ (line_through P Q)`

Let's get started!
"

Image "images/incidenceAxioms.png"
