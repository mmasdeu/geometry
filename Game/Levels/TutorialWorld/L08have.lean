import Game.Metadata
import Game.Levels.TutorialWorld.L07constructor
open IncidencePlane --hide

World "TutorialWorld"
Level 8

Title "The have tactic"
TheoremTab "∈"
Introduction
"
Here's a new tactic: `have`. It adds a new hypothesis to your context (which, of course, you have to prove!).
It's great for structuring proofs. In this level, it's handy to first prove `r = line_through A B`, then
`s = line_through A B`, and after that the rest follows easily.

The syntax is `have h : P = Q`. It adds the hypothesis `h : P = Q` to the local
context and splits the proof into two goals. First, Lean asks you to prove `⊢ P = Q` (without having `h`).
Then it asks you to prove the goal you had before, this time with the help of `h : P = Q`.

**Pro tip:** proofs are getting longer now. Whenever you have two or more goals at once, use *bullet points*
to keep them apart. Type them with `\\·`, or, if you have a Catalan keyboard, directly
(middle dot, `Shift+3`). Inside each bullet block you'll only see one goal.

For example, you could start with `have hr : r = line_through B C` (call `hr` whatever you like).
Since two goals appear, you can write:

```
have hr : r = line_through B C
· sorry
· sorry
```

Replace each `sorry` with a proof of the corresponding goal.

Let's go!
"

variable {Ω : Type} [IncidencePlane Ω] --hide

/--
If two lines share two distinct points, then they are the same line.
-/
Statement (hAB : A ≠ B) (r s : (Line Ω)) (hAr : A ∈ r) (hAs : A ∈ s)
(hBr : B ∈ r) (hBs : B ∈ s) : r = s := by
  Hint "Introduce the hypothesis `r = line_through A B` using the tactic `have`."
  have h : r = line_through A B
  · apply incidence hAB hAr hBr
  Hint "Now introduce a new hypothesis `s = line_through A B`."
  have h' : s = line_through A B
  · apply incidence hAB hAs hBs
  Hint "You can finish with two `rw`s (you can even do it in one line)."
  rw [h, h']

NewTactic «have» set

Conclusion "Great! On to more tactics..."
