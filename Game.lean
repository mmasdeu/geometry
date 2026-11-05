import Game.Levels.TutorialWorld
import Game.Levels.IncidenceWorld
import Game.Levels.BetweennessWorld
import Game.Levels.PlaneSeparationWorld

-- Here's what we'll put on the title screen
Title "Hilbert Geometry Game"
Introduction
"
# Welcome to the Hilbert Geometry game
#### Learning axiomatic geometry through Lean.

In this game, we'll visit some of the axioms Hilbert proposed to describe
the plane. By the end, you'll have proved the *Plane Separation Theorem*. Yes, really!

You'll do it by solving little puzzles in a proof assistant called Lean.
No Lean experience needed. We'll start from zero.

# Read this.

Learning an interactive theorem prover takes a bit of time, so don't rush.
To get the most out of the game, read the help texts like this one. They're there for you.

Ready? Click on \"Tutorial World\" to start.

## More

Click on the three lines in the top right and select \"Game Info\" for resources,
links, and ways to chat with the Lean community.
"

Info "
Geometry Game. Based on the Hilbert Game, and made for Argo Summer school (Univ. Autònoma de Barcelona) 2024.

## Progress saving

The game stores your progress in your local browser storage.
If you delete it, your progress will be lost!

Heads up: In most browsers, deleting cookies will also clear the local storage
(or \"local site data\"). Make sure to download your game progress first!

## Credits

* **Game Author:** Marc Masdeu
* **Past Contributors:** Carlos Caralps, Luis Castillo
* **Game Engine:** Alexander Bentkamp, Jon Eugster, Patrick Massot

## Resources

* The [Lean Zulip chat](https://leanprover.zulipchat.com/) forum
* Github: [A Lean Intro to Logic](https://github.com/mmasdeu/geometry)
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Hilbert Geometry"
CaptionLong "Discover Lean through Hilbert's Geometry"
-- Prerequisites "" -- add this if your game depends on other games
CoverImage "images/cover.png"
-- Dependency TutorialWorld → IncidenceWorld → BetweennessWorld → PlaneSeparationWorld
/-! Build the game. Shows warnings if it found a problem with your game. -/
MakeGame
