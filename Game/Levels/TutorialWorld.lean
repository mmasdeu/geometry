import Game.Levels.TutorialWorld.L00assumption
import Game.Levels.TutorialWorld.L01rw
import Game.Levels.TutorialWorld.L02rwbis
import Game.Levels.TutorialWorld.L03exact
import Game.Levels.TutorialWorld.L05usage
import Game.Levels.TutorialWorld.L06intro
import Game.Levels.TutorialWorld.L07constructor
import Game.Levels.TutorialWorld.L08use
import Game.Levels.TutorialWorld.L09have


World "TutorialWorld"
Title "Tutorial World"

Introduction
"
# Tutorial World

## The setup

Welcome to the Tutorial World! In this world, you're going to prove some geometric facts by using **`tactics`**.
These *tactics* are just instructions that make progress in a mathematical proof.
During your proofs, your 'goal' (i.e. what you're
supposed to be proving) will be displayed in front of a `⊢` symbol on the top
right hand box, so you will need to use *tactics* to close that goals. Once you close all the goals, the top
right hand box will report 'Proof complete!', so that you
can move on to the next level in the world you're in.

## The language

In **LEAN**, everything (points, lines, a set of points, a theorem, a proof) is a *term*, and each term is of a certain *type*,
and only one. One writes `x : T` to say that the term $x$ is of type $T$ (you can read the ':' as 'is an element of'). By the way,
*types* are themselves terms (rembember, **everything** is a term). For example, a point $P$ will be a term of type $\\Omega$ (which will
denote the plane). We will write this as `P : Ω`. The plane $\\Omega$ is of type `Type` (this is a special type, whose terms are
things like the plane, or the set of the real numbers).

There is also another special type called `Prop`. A term of type `Prop` is a true-false statement, like 'it rains', '2 + 2 = 4',
'2 + 3 = 7' (yes, they can be either True or False). A term of type '2 + 2 = 4' would be a proof of this fact.
We will write `h : 2 + 2 = 4` to mean exactly this: `h` is a proof of the fact that `2 + 2 = 4`, and we can use it in our proof.
If we had `h' : 2 + 3 = 7` then we would probably be able to proof crazy things!
"
Conclusion
"Great!"
