import Game.Levels.PlaneSeparationWorld.level01
import Game.Levels.PlaneSeparationWorld.level02
import Game.Levels.PlaneSeparationWorld.level03
import Game.Levels.PlaneSeparationWorld.level04
import Game.Levels.PlaneSeparationWorld.level05
import Game.Levels.PlaneSeparationWorld.level06
import Game.Levels.PlaneSeparationWorld.level07
import Game.Levels.PlaneSeparationWorld.level08


World "PlaneSeparationWorld"
Title "Plane Separation World"

Introduction
"
# Plane Separation World

## A new world of possibilities...

Ever noticed that a line cuts a sheet of paper into two halves? That's **plane separation**, and it
comes from the fourth axiom of order: Pasch's Axiom.

**B.4) Pasch's Axiom:** Let A, B, C be three non-collinear points and let ℓ be a line lying in the plane ABC
and not passing through any of the points A, B, C. Then, if the line ℓ passes through a point of the segment A·B,
it will also pass through either a point of the segment B·C or a point of the segment A·C (but not both).

In plain words: if a line walks into a triangle through one side, it has to walk out through another one.

In Lean, Pasch's Axiom looks like this. You'll find it in the `Betweenness` tab.

`lemma pasch {A B C D : Ω} {ℓ : Line Ω} (hnc: C ∉ line_through A B)
(hnAl: A ∉ ℓ) (hnBl: B ∉ ℓ) (hnCl: C ∉ ℓ) (hDl: D ∈ ℓ) (hADB: A * D * B) :
(∃ E ,  E ∈ ℓ ∧ (A * E * C)) xor (∃ E, E ∈ ℓ ∧ (B * E * C))`
"
Image "images/pasch.png"
