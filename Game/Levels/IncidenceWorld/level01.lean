import Game.Metadata
import Game.Levels.TutorialWorld
import Game.Levels.AdvancedTutorialWorld
open IncidencePlane


World "IncidenceWorld"
Level 1

Title "Lines are thin"



Introduction
"
We start by proving that every line misses at least one point. Note that, although this seems obvious,
it is not directly one of our axioms, and thus we must prove it from them.
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
      exact h
    · use B
  · use A

NewTheorem IncidencePlane.existence
