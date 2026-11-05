import Game.Metadata
open IncidencePlane --hide

World "TutorialWorld"
Level 6

Title "Intro(ducing) hypotheses"


Introduction
"
Meet the `intro` tactic. Whenever the goal has a `→`, `intro` moves the left side into your
local context as a new hypothesis, just above the `⊢`. [**Remember:** `→` means
**implication**. `P → Q` reads 'P implies Q', i.e. 'if P happens, then Q happens'.]
For example, with the goal `⊢ IT RAINS → I GET WET`, typing `intro h` gives you a new hypothesis
`h : IT RAINS` and the goal becomes `⊢ I GET WET`.

To solve this level you'll need a theorem that was just added to the *Theorems* list.
It's called `incidence`. Click on it in the *Theorems* panel to see what it says.

**Pro tip:** you don't need one `intro` per line. Put them together: `intro h1 h2 h3 h4` adds four
new hypotheses at once. Once you've introduced them all, compare
your goal with `incidence`. Notice that we can `rewrite` with it! Given the first
three hypotheses it asks for, we can turn the line `r` into `line_through A B`. Type `rw [incidence h1 h2 h4]` and
see how the goal changes. (Here `incidence` is applied to the hypotheses `h1 h2 h4`: we hand it the proofs it asks for,
and in return it gives us an equation `r = line_through A B` that `rw` can use.) To finish, do the same for the line `s`.
"

variable {Ω : Type} [IncidencePlane Ω] --hide
variable {A B : Ω} {r s : Line Ω} -- hide

/--
If two lines contain two distinct points, then they are the same line.
-/
Statement : A ≠ B → A ∈ r → A ∈ s → B ∈ r → B ∈ s → r = s := by
  intro h1 h2 h3 h4 h5
  rw [incidence h1 h2 h4]
  rw [incidence h1 h3 h5]

NewTactic intro

NewTheorem IncidencePlane.incidence
