import Game.Metadata
import Game.Levels.IncidenceWorld.level02
open IncidencePlane


World "IncidenceWorld"
Level 4

Title "Lines are thin"



Introduction
"
First, let's show that every line misses at least one point. It sounds obvious, but it isn't one of our axioms,
so we have to prove it from them!

The key is that we have three distinct non-collinear points. Remember, the axiom giving them is called `existence`:
`existence Ω : ∃ A B C : Ω, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ ...`

To use it, our versatile friend `rcases` comes to the rescue again. If you type `rcases existence Ω`,
all the new variables (A, B, C, ...) show up in your context. You can name them with
`rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩`.

In general, if you have a theorem `h` saying `∃ x y, P x y ∧ Q x y`, you extract its pieces with
`rcases h with ⟨x, y, ⟨hP, hQ⟩⟩`.

```
  A       B       C       three points, not all on one line:
  o-------o       o       at least one of them is off any given line
```
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
