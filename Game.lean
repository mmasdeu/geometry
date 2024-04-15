import Game.Levels.TutorialWorld
import Game.Levels.IncidenceWorld
import Game.Levels.BetweennessWorld
import Game.Levels.PlaneSeparationWorld

-- Here's what we'll put on the title screen
Title "Hilbert Geometry Game"
Introduction
"
Welcome to the Hilbert Geometry Game! Select an unlocked level to get started!
"

Info "
Geometry Game. Based on Hilbert Game, and made for Argo Summer school (Univ. Autònoma de Barcelona) 2024.

Author: Marc Masdeu
Contributors: Carlos Caralps, Luis Castillo
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Hilbert Geometry"
CaptionLong "Discover Lean through Hilbert's Geometry"
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"
Dependency TutorialWorld → IncidenceWorld → BetweeenessWorld --→ PlaneSeparationWorld
/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
