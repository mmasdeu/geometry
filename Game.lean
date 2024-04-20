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

In this game, we visit some of the axioms proposed by Hilbert to describe
the plane. At the end, we will prove the *Plane Separation Theorem*.

All of this is done by solving levels of a computer puzzle game called Lean.

# Read this.

Learning how to use an interactive theorem prover takes time. To
get the the most out of this game you need to read the help texts like this one.

To start, click on \"Tutorial World\".

## More

Click on the three lines in the top right and select \"Game Info\" for resources,
links, and ways to interact with the Lean community.
"

Info "
Geometry Game. Based on Hilbert Game, and made for Argo Summer school (Univ. Autònoma de Barcelona) 2024.

## Progress saving

The game stores your progress in your local browser storage.
If you delete it, your progress will be lost!

Warning: In most browsers, deleting cookies will also clear the local storage
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
-- Dependency TutorialWorld → IncidenceWorld → BetweeenessWorld → PlaneSeparationWorld
/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
