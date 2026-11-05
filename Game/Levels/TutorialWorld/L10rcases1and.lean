import Game.Metadata
import Game.Levels.TutorialWorld.L09use

open IncidencePlane --hide

World "TutorialWorld"
Level 10

Title "The `rcases` tactic"
TheoremTab "∈"

variable {Ω : Type} [IncidencePlane Ω] --hide

Introduction
"
# Advanced Tutorial World

## The `rcases` tactic

Next tactic: `rcases` (the `r` stands for *recursive*: it can take apart
nested hypotheses in one go). It does many things, so we'll spend a couple of levels on it.
It always works on hypotheses and transforms them in different ways. The first
case is when you have a hypothesis saying that both `P`
and `Q` hold, that is, `h : P ∧ Q`. Then `rcases h with ⟨h1, h2⟩`
replaces `h` with two new hypotheses, `h1 : P` and `h2 : Q`. The angle brackets `⟨ ⟩`
(typed `\\<` and `\\>`) just list the names you want to give to the pieces.

You usually do this for tidiness, since `h.1` and `h.2` are also proofs of `P` and `Q`.

I'm sure you can finish this level on your own. It's only two lines!
"


/--
The line ℓ is the line through P and Q as long as P ≠ Q and both P and Q are in ℓ.
-/
Statement (P Q : Ω) (ℓ : Line Ω) (h1 : P ≠ Q)
(h2 : P ∈ ℓ ∧ Q ∈ ℓ) : ℓ = line_through P Q := by
  rcases h2 with ⟨hP, hQ⟩
  apply incidence h1 hP hQ

NewTactic rcases
