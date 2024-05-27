import Game.Levels.TutorialWorld.L00assumption
import Game.Levels.TutorialWorld.L01rw
import Game.Levels.TutorialWorld.L02rwbis
import Game.Levels.TutorialWorld.L03apply
import Game.Levels.TutorialWorld.L05usage
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

Welcome to the Tutorial World! In this world, you're going to prove some geometric statements.
Your 'goal' (i.e. what you're supposed to be proving) will be displayed in front of a ⊢ symbol on the top right hand box.
How do you get there? By using tactics. These tactics are just instructions you give **Lean** to make progress in a mathematical
proof until you achieve the goal. On your way, you may have generated some partial goals. Once you close all the goals,
you will see a message saying 'Level Completed! 🎉' and you can move on to the next level in the world you're in.

**Read this:** It is important that you read the help text as you move on, you will learn a lot more this way!


## The language

In **Lean**, everything (points, lines, a set of points, a theorem, a proof) is a *term*, and each term is of a certain *type*,
and only one. One writes `x : T` to say that the term $x$ is of type $T$ (you can read the ':' as 'is an element of'). By the way,
since everything is a term, also *types* are themselves terms (of type `Type`, which in turn is a term of type `Type 1`, and so on).
For example, a point $P$ will be a term of type $\\Omega$ (which will
denote the plane). We will write this as `P : Ω`. The plane $\\Omega$ is of type `Type` (this is a special type, whose terms are
things like the plane, or the set of the real numbers).

There is also another special type called `Prop`. A term of type `Prop` is a true-false statement, like 'it rains', '2 + 2 = 4',
'2 + 3 = 7' (yes, they can be either True or False). The terms of type `Prop` are types themselves, whose terms
are proofs of the statement. For instance, a term of type '2 + 2 = 4' would be a proof of this fact.
We will write `h : 2 + 2 = 4` to mean exactly this: `h` is a proof of the fact that `2 + 2 = 4`, and we can use it in our proof.
If we ever have `h' : 2 + 3 = 7` then we will be able to prove anything we want, like `5 = 7`, or `0 = 1`. But this makes
sense, right? It is like saying 'Give me a lever and a place to stand, and I shall move the world.', but in **Lean**.
"
Conclusion
"Great!"

Image "images/cover.png"
