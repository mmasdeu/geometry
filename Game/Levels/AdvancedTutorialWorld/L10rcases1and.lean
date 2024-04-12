import Game.Metadata


open IncidencePlane --hide

World "AdvancedTutorialWorld"
Level 1

Title "The `rcases` tactic"


variable {Ω : Type} [IncidencePlane Ω] --hide

Introduction
"
# Advanced Tutorial World

## The `rcases` tactic.

The next tactic we introduce is `cases`, and since it does many things
we will have a couple levels seeing when to apply it. This tactic works
always on hypotheses, and it transforms them in different ways. The first
instance that we learn arises when you have a hypothesis that says that `P`
and `Q` holds. That is, you have `h : P ∧ Q`. Then `cases h with h1 h2` will
replace `h` with two new hypotheses, namely `h1 : P` and `h2 : Q`.

This is done usually for aesthetic reasons, since `h.1` and `h.2` also serve
as proofs of `P` and `Q`.

Knowing that, I'm sure you can complete this level on your own. It's only two lines of code!
"


/--
The line ℓ is the line through P and Q as long as P ≠ Q and both P and Q are in ℓ.
-/
Statement (P Q : Ω) (ℓ : Line Ω) (h1 : P ≠ Q)
(h2 : P ∈ ℓ ∧ Q ∈ ℓ) : ℓ = line_through P Q := by
  rcases h2 with ⟨hP, hQ⟩
  exact incidence h1 hP hQ

NewTactic rcases
