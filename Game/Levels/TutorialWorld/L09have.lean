import Game.Metadata
open IncidencePlane --hide

World "TutorialWorld"
Level 9

Title "The have tactic"

Introduction
"
Congratulations! You are just finishing the tutorial world! In this level, we introduce the new tactic `have`. It is used to add a new hypothesis
to the context (which, of course, you will have to prove!). This is sometimes useful to structure our proofs. In this particular level, it is convenient
to prove first that `r = line_through B C`, and then that `s = line_through B C`. This strategy will allow us to finish the proof very easily!

To use the tactic `have`, we should follow the following structure: `have h : A = B`. This line will add the hypothesis `h : A = B` to the local
context and break the proof into two goals. First, Lean will ask us to prove `⊢ A = B` without the hypothesis `h : A = B`. Then, it will ask us to
prove the goal that existed before using the tactic `have` with the support of the new hypothesis `h : A = B` that we have added to the local context.

**Pro tip:** Because you're getting better at this, proofs are going to be more challenging. Whenever you see that you have to prove two
or more goals to finsih one level, you may want to use *bullet points* to isolate them. You type them with `\\·`, or if you are lucky to have a Catalan keyboard
then you can directly enter it (middle dot, press `Shift+3`). After each of these bullet points, you will only see one goal.

For example, the first line of this proof will be `have hr : r = line_through B C` (you can change `hr` into whatever name you are comfortable with to
make reference to the hypothesis `r = line_through B C`). Now, because two goals have appeared, you can type the following structure:

```
have hr : r = line_through B C
· sorry
· sorry
```

In this way, by deleting the `sorry`'s, you will be able to prove the goals separately. Now, let's try solve this level together so that you can
easily understand how the syntax of Lean works!

First, we are going to prove the first goal, which is `⊢ r = line_through B C`. To begin with, let's look at the *Theorems* we have.
Can you note that `incidence` finishes with the same structure as our goal? Then, we have to check if we have the previous implications of `incidence`
in our local context. On the face of it, `h : B ≠ C` and `h1 : B ∈ r ∧ C ∈ r` are what we are looking for. However, `h1` should be divided into `B ∈ r`
and `C ∈ r`, right? [**Rule of thumb:** whenever a hypothesis looks like `h1 : P ∧ Q`, we can refer to `P` and `Q` as `h1.1` and `h1.2`, respectively.]
Then, notice how `exact incidence h h1.1 h1.2` closes the first goal!

Before jumping onto the second goal, we may want to rewrite something first. Can you see that we can `rw [hr]` (where `hr : r = line_through B C`) to change
the goal `⊢ r = s` into `⊢ line_through B C = s`. Now, you will be wondering if `exact incidence h h2.1 h2.2,` finishes the proof, but it does not. Do you
know why? Because the theorem statement called `incidence` works with the goal `⊢ s = line_through B C`, but not with `⊢ line_through B C = s`. Because of
this reason, we should create another hypothesis by using the `have` tactic. That is to say, type `have hs : s = line_through B C` right before the curly braces.
"


variable {Ω : Type} [IncidencePlane Ω] --hide

/--
If two lines share two distinct points, then they are the same line.
-/
Statement (B C : Ω) (h : B ≠ C) (r s : Line Ω)
(h1 :  B ∈ r ∧ C ∈ r)
(h2 : B ∈ s ∧ C ∈ s)
: r = s := by
  have hr : r = line_through B C
  · exact incidence h h1.1 h1.2
  rw [hr]
  have hs : s = line_through B C
  · exact incidence h h2.1 h2.2
  rw [hs]

NewTactic «have»

Conclusion "Great! Now on to learning more tactics..."
