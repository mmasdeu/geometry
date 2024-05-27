import Game.Metadata
import Game.Levels.TutorialWorld.L07constructor
open IncidencePlane --hide

World "TutorialWorld"
Level 9

Title "The have tactic"
TheoremTab "∈"
Introduction
"
In this level, we introduce the new tactic `have`. It is used to add a new hypothesis
to the context (which, of course, you will have to prove!). This is sometimes useful to structure our proofs.
In this particular level, it is convenient
to prove first that `r = line_through A B`, and then that `s = line_through A B`, and with these two statements
the proof will follow very easily.

To use the tactic `have`, we should follow the following structure: `have h : P = Q`. This line will add the hypothesis `h : A = B` to the local
context and break the proof into two goals. First, Lean will ask us to prove `⊢ P = Q` without the hypothesis `h : P = Q`.
Then, it will ask us to
prove the goal that existed before using the tactic `have` with the support of the new hypothesis `h : P = Q` that we have added to the local context.

**Pro tip:** Because you're getting better at this, proofs are going to be more challenging. Whenever you see that you have to prove two
or more goals to finish one level, you may want to use *bullet points* to isolate them. You type them with `\\·`, or if you are lucky to have a Catalan keyboard
then you can directly enter it (middle dot, press `Shift+3`). After each of these bullet points, you will only see one goal.

For example, the first line of this proof will be `have hr : r = line_through B C` (you can change `hr` into whatever name you are comfortable with to
make reference to the hypothesis `r = line_through B C`). Now, because two goals have appeared, you can type the following structure:

```
have hr : r = line_through B C
· sorry
· sorry
```

In this way, by deleting the `sorry`'s, you will be able to prove the goals separately.

Let's go!
"


variable {Ω : Type} [IncidencePlane Ω] --hide

/--
If two lines share two distinct points, then they are the same line.
-/
Statement (hAB : A ≠ B) (r s : (Line Ω)) (hAr : A ∈ r) (hAs : A ∈ s)
(hBr : B ∈ r) (hBs : B ∈ s) : r = s := by
  Hint "Introduce the hypothesis `r = line_through A B` using the tactic `have`"
  have h : r = line_through A B
  · apply incidence hAB hAr hBr
  Hint "Now introduce a new hypotheis `s = line_through A B`"
  have h' : s = line_through A B
  · apply incidence hAB hAs hBs
  Hint "You can now complete the level with two `rw`'s (which you can do in one line, of course)."
  rw [h, h']

NewTactic «have» set

Conclusion "Great! Now on to learning more tactics..."
