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
In mathematics, we need to set down some starting points
to build our knowledge, and this is why axioms should join the game. What are axioms, then?
They are unprovable statements which are assumed to be true *because of their self-evidence*.
They serve as a premise for further reasoning and arguments, so that we can reach new conclusions from them.

By travelling back in time to 300 B.C., we meet the great mathematician Euclid, who suggested the very
first postulates of geometry in his well-known book **Elements**. Euclidean geometry can be built up from three
sets of axioms, each of them adding new independent notions that are needed to define the plane. These sets of axioms
were proposed by David Hilbert (1862-1943 AD), who made remarkable improvements in the foundations of geometry.
These three blocks of axioms are called **incidence**, **order** and **congruence** (we might also want to add the **parallel axiom**,
but that would come later).

In this world we concentrate on the first block, the axioms of **incidence**. There are three axioms of incidence, that
will give the relationships between the primitive notions of
**point** and **line**. Notice
that by *incidence* we mean whatever idea that satifies the axioms of incidence. Then, you will be wondering... are the
notions of *point* and *line* referring to whatever object of reality that satisfies the axioms of incidence? Exactly!
Before the axioms of incidence, these notions are **undefined**!

Let's then introduce the axioms of incidence:

A.1. For every point $P$ and for every point $Q$ not equal to $P$, there exists a unique line $\\ell$
*passing through* (= incident with) $P$ and $Q$.

A.2. For every line $\\ell$, there exist two distinct points that belong to it.


A.3. There exist three distinct points with the property that no line *passes through* (= is incident with) all three of them.


The drawings above may help you understand (or remember) each of the axioms, but they
have no meaning in mathematics. We will not be able to use them in our proofs!

## The axioms of incidence in Lean.

How do we make the computer understand such complex statements? We use the **Lean** language! However,
it is easier to divide some of them into more than one statements. In this case, we have
the following four axioms:

* `line_through (P Q : Ω) : Line Ω`

This produces, given two points, a certain line through them. Think of it as a function that eats
two points $P$ and $Q$ and outputs a line $\\ell$ called `line_through P Q`.

* `line_through_left (P Q : Ω) : P ∈ (line_through P Q)`

* `line_through_right (P Q : Ω) : Q ∈ (line_through P Q)`

These two statements guarantee that the line `line_through P Q` does indeed contain both $P$ and $Q$.
The next statement is about uniqueness, and here we need to ask that $P \\neq Q$. We know that there
is a line through $P$ and $Q$, namely `line_through P Q`. The `incidence` statement says that if a
line $\\ell$ is so that $P$ and $Q$ are both in $\\ell$, then this line $\\ell$ must be `line_through P Q`.

* `incidence {P Q : Ω} {ℓ : Line Ω} : P ≠ Q → P ∈ ℓ → Q ∈ ℓ → ℓ = line_through P Q`

The second axiom of incidence is quite straightforward in **Lean**:

* `line_contains_two_points (ℓ : Line Ω) : ∃ P Q : Ω, P ≠ Q ∧ ℓ = line_through P Q`

The third axiom also translates rather easily. In order to state that the three points are
non-collinear, we say that the third point $R$ does not lie in the (unique) line through $P$ and $Q$.

* `existence (Ω : Type) : ∃ P Q R : Ω, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ R ∉ (line_through P Q)`

Let's get started!
"

Image "images/incidenceAxioms.png"
