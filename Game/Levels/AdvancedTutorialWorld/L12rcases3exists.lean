import Game.Metadata
import Game.Levels.TutorialWorld

open IncidencePlane --hide

World "AdvancedTutorialWorld"
Level 3

Title "The `rcases` tactic (III)"

variable {Ω : Type} [IncidencePlane Ω] --hide

Introduction
"
Suppose now that your hypothesis says there is some element `x` satisfying a certain
property `P`. That is, you have `h : ∃ x, P x`. Then `cases h with z hz` will
replace `h` with `z : x` and `hz : P z`. That is, from the fact that you assume that
some `z` exists (`z : x`), it will give you another hypothesis in which `z` satisfies the
property `P` (`hz : P z`).
"
/-
Let's try to understand this with a real life example! Say that we have the hypothesis
`h: ∃ GALAXY, SOLAR_SYSTEM GALAXY`. That is, *there exists a GALAXY such that `SOLAR_SYSTEM`
is an element of `GALAXY`*.
Then, `cases h with MILKY_WAY hMILKY_WAY` will break `h` into two goals:
`MILKY_WAY : GALAXY`, which is read as *the `MILKY_WAY` is a term of the type `GALAXY`*, and
`hMILKY_WAY : SOLAR_SYSTEM MILKY_WAY, which is read as *the hypothesis `hMILKY_WAY` assumes that `SOLAR_SYSTEM`
is an element of the `MILKY_WAY`*. Is it better for you now?

Now, let's try to solve this level! From now on, it will be better if we start by reading the lemma
as many times as we need to understand it. Then, do a drawing of the situation. In this way, we can
think of a clearer path to close the goal. Once you feel ready, delete the `sorry` and take a look
to the hypothesis h1 and h2. As you may be thinking, we can apply the `cases` tactic to them. Following
the guiding thread of the real life example, we need to think about a specific line for each of them.
In geometry, lines are usually represented by the letters `r` and `s`. Then, type `cases h1 with r hr,`,
click on enter, and write `cases h2 with s hs,`. If you look at the local context, you'll see that we've
assumed that `r` and `s`are lines in the plane Ω.

Right after, it comes the genius idea. After reading the lemmma and trying to do a draw that represents
the situation, you should be wondering if we could create a hypothesis to state that the lines we've just
added to the local context are the same (`r = s`). Do you remember how we could add a hypothesis? Exactly,
the `have` tactic will do it for us! Now, type `have H : r = s,` (don't forget the comma).

Subsequently, we will have to prove two goals. First, try to look for a theorem statement that might help us
to close the `⊢ r = s` goal. Can you see that `equal_lines_of_contain_two_points` ends with exactly the `r = s`
statement? Then, try to look if we have all the previous implications of this statement in the local context of
this level. If so, why don't we use the `exact` tactic? [**Pro tip:** Whenever we have a hypothesis of the form
`h : P ∧ Q ∧ R`, we write `h.1` to refer to `P` and we type `h.2` to refer to `Q ∧ R`. If we want to refer to just
`Q`, we need to write `h.2.1`. Analogously, if we want to refer to just `R`, then we type `h.2.2`. With that being said,
you can solve the first goal!

When it comes to the second goal, you should remember what tactic comes handy for solving goals of the form
`⊢ ∃ x, P x`. Once you have it mind, try to use it with the hypotheses `r` or `s`. From there, some `split`'s, `exact`'s
and a `rewrite` will close the goal.
"
 -/

/--
Given 4 distinct points that pass through a line, then that line passes through two different subsets of three points.
-/
Statement (P Q R S : Ω) (h : Q ≠ R) (h1 : ∃ ℓ : Line Ω, P ∈ ℓ ∧ Q ∈ ℓ ∧ R ∈ ℓ)
(h2 : ∃ ℓ : Line Ω, Q ∈ ℓ ∧ R ∈ ℓ ∧ S ∈ ℓ) :
∃ ℓ : Line Ω, P ∈ ℓ ∧ Q ∈ ℓ ∧ R ∈ ℓ ∧ S ∈ ℓ := by
  rcases h1 with ⟨r, hr⟩
  rcases h2 with ⟨s, hs⟩
  have H : r = s
  · apply equal_lines_of_contain_two_points h
  use r
  constructor
  exact hr.1
  constructor
  exact hr.2.1
  constructor
  exact hr.2.2
  rw [H]
  exact hs.2.2

Conclusion "Great!"
