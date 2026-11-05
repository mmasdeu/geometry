import Game.Levels.TutorialWorld.L00assumption
import Game.Levels.TutorialWorld.L01rw
import Game.Levels.TutorialWorld.L02rwbis
import Game.Levels.TutorialWorld.L03apply
import Game.Levels.TutorialWorld.L04usage
import Game.Levels.TutorialWorld.L06intro
import Game.Levels.TutorialWorld.L07constructor
import Game.Levels.TutorialWorld.L08have
import Game.Levels.TutorialWorld.L09use
import Game.Levels.TutorialWorld.L10rcases1and
import Game.Levels.TutorialWorld.L11rcases2or
import Game.Levels.TutorialWorld.L12tauto

World "TutorialWorld"
Title "Tutorial World"

Introduction
"
# Tutorial World

## The setup

Welcome! Here you'll prove some geometric statements and pick up your first Lean tricks.
Your *goal* (what you're trying to prove) shows up after the ⊢ symbol in the top right box.
How do you get there? With *tactics*. A tactic is just an instruction you give **Lean** to make progress
on the proof. Sometimes a tactic splits your goal into smaller partial goals. Once you close all of them,
you'll see 'Level Completed! 🎉' and you can move on.

**Read this:** read the help texts as you go. You'll learn a lot more that way!


## The language

In **Lean**, everything (points, lines, sets of points, theorems, proofs) is a *term*, and each term has a *type*,
exactly one. We write `x : T` to say that the term $x$ has type $T$ (read the ':' as 'is an element of'). And since
everything is a term, *types* are terms too (of type `Type`, which is a term of type `Type 1`, and so on).
For example, a point $P$ is a term of type $\\Omega$ (our name for the plane). We write `P : Ω`.
The plane $\\Omega$ itself has type `Type` (a special type whose terms are things like the plane, or the real numbers).

There's another special type called `Prop`. A term of type `Prop` is a true-or-false statement, like 'it rains', '2 + 2 = 4'
or '2 + 3 = 7' (yes, false statements count too). Each statement is itself a type, and its terms
are *proofs* of it. So a term of type `2 + 2 = 4` is a proof that 2 + 2 = 4.
We write `h : 2 + 2 = 4` to say: `h` is a proof of `2 + 2 = 4`, and we can use it in our proof.
If we ever got our hands on `h' : 2 + 3 = 7`, we could prove anything, like `5 = 7` or `0 = 1`. Fair enough:
it's like saying 'Give me a lever and a place to stand, and I shall move the world', but in **Lean**.
"
Conclusion
"Great!"

Image "images/cover.png"
