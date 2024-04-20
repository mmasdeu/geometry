import Game.Metadata
import Game.Levels.IncidenceWorld.level02
open IncidencePlane


World "IncidenceWorld"
Level 4

Title "Lines are thin"



Introduction
"
We start by proving that every line misses at least one point. Note that, although this seems obvious,
it is not directly one of our axioms, and thus we must prove it from them.

This lemma uses in a crucial way the fact that we have three distinc non-collinear points. Remember that
the axiom which guarantees this is called `existence` and is formalized as
`existence Ω : ∃ A B C : Ω, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ ...`

To use this axiom, the very versatile `rcases` tactic comes to help us again. If we type `rcases existence Ω`
we will see all the new variables (A, B, C, ...) appearing in our context. We can name them for later usage,
using the syntax
`rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩`.

In general, if we have a theorem `h` that says `∃ x y, P x y ∧ Q x y`, we will extract it with
`rcases h with ⟨x, y, ⟨hP, hQ⟩⟩`.
"

variable {Ω : Type} [IncidencePlane Ω]

/--
Every line misses at least one point.
-/
Statement (ℓ : Line Ω) : ∃ (P : Ω), P ∉ ℓ := by
  rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩
  by_cases hA : A ∈ ℓ
  · by_cases hB : B ∈ ℓ
    · use C
      rw [incidence hAB hA hB]
      assumption
    · use B
  · use A

NewTheorem IncidencePlane.existence
TheoremTab "∈"
