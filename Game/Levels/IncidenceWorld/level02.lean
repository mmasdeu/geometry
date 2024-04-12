import Game.Metadata
import Game.Levels.IncidenceWorld.level01

open IncidencePlane --hide



World "IncidenceWorld"
Level 2

Title "Lines are thin"

Introduction
"
## Proving useful lemmas (I).

To solve this level, you will need to use the second axiom of incidence.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable  {P Q: Ω} {r : Line Ω}  -- hide


/--
Given a line, there exists one point on that line.
-/
Statement (ℓ : Line Ω): ∃ A : Ω, A ∈ ℓ := by
  have A2 : ∃ (P Q : Ω), P ≠ Q ∧ ℓ = line_through P Q
  · exact line_contains_two_points ℓ
  rcases A2 with ⟨A, hA⟩
  rcases hA with ⟨B, hB⟩
  rcases hB with ⟨HAB, hl⟩
  use A
  rw [hl]
  exact line_through_left A B

NewTheorem IncidencePlane.line_contains_two_points
