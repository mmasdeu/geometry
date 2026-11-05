import GameServer.Commands

/--
## Summary

If your goal is exactly one of your hypotheses, `assumption` spots it
and closes the goal for you. No typing the name needed!

### Example
If it looks like this in the top right hand box:
```
A B C : Ω
h1 : A = B
h2 : B = C
⊢ A = B
```

then `assumption` will close the goal, because `h1` is exactly what we want.
-/
TacticDoc assumption


/--
## Summary

If `h` is a proof of `X = Y`, then `rw [h]` swaps
every `X` in the goal for a `Y`.

**Variants:** `rw [← h]` swaps `Y` for `X`, and
`rw [h] at h2` does the swap in the hypothesis `h2` instead
of in the goal.

## Details

`rw` is the 'substitute in' tactic. You can use it in two ways.

1) If `h : A = B` is a hypothesis (that is, a proof of `A = B`)
in your local context (the box in the top right)
and your goal contains some `A`s, then `rw [h]`
turns them all into `B`s.

2) It also works with theorems that are equalities
(find them in the menu on the left, under Theorem Statements).
Many of these theorems need some inputs, and you can
hand them to `rw` right away, just like arguments of a function.
For example, if `incidence` needs two points and a proof that
they're on a line, you can write `rw [incidence h1 h2 h4]`.
If you leave the arguments out, Lean tries to figure them out
by itself, which works fine most of the time.

**Heads up:** `rw` only works when `h` is a proof of something like `A = B`
or `A ↔ B`. If `h` is a function or an implication, or if it's the
statement itself rather than its proof, `rw` isn't the tool you want.
For example, `rw (P = Q)` is never correct: `P = Q` is the statement,
not a proof of it. If `h : P = Q` is the proof, then `rw [h]` works.

**Pro tip:** If `h : A = B` and you'd rather turn
`B`s into `A`s, use `rw [←h]` (type the arrow with `\l`,
that's a small letter L, not the number 1).

### Example
If it looks like this in the top right hand box:
```
A B C : Point
h1 : A = B
h2 : B = C
⊢ A = C
```

then

`rw [h1]`

will change the goal into `⊢ B = C`.

### Example
You can use `rw` to change a hypothesis as well.
For example, if your local context looks like this:
```
A B C : Point
h1 : A = C
h2 : A = B
⊢ B = C
```
then `rw [h1] at h2` will turn `h2` into `h2 : C = B`.

-/
TacticDoc rw


/--
## Summary

If the goal is `⊢ X`, then `exact x` closes it exactly when
`x` is a term of type `X` (a proof of `X`).

## Details

Say `P`, `Q` and `R` are types (think of them as sets or as
propositions), and your local context looks like this:

```
p : P,
h : P → Q,
j : Q → R
⊢ R
```

If you can spot how to build a term of type `R`, just
write it down after `exact` and you're done. For example, the
goal above can be solved with

`exact j(h p)`

because `h p` has type `Q`, and then `j (h p)` has type `R`.
(That's an element of the set `R`, or a proof of the proposition `R`.)

-/
TacticDoc exact


/--
## Summary

`intro p` turns a goal `⊢ P → Q` into a hypothesis `p : P`
and a new goal `⊢ Q`. If `P` and `Q` are sets, `intro p` means "let $p$ be any element of $P$".
If they're propositions, it means "assume $P$ is true".

## Details

If your goal is a function or an implication `⊢ P → Q`, then `intro`
will always make progress. `intro p` turns

`⊢ P → Q`

into

```
p : P
⊢ Q
```

The opposite of `intro` is `revert`: in the situation
above, `revert p` turns the goal back into `⊢ P → Q`.

**Variant:** You can put several names after `intro` instead of calling it many times.
So `intro h₁ h₂` does the same as `intro h₁; intro h₂`.

## Example

If your goal is an implication $P\implies Q$, Lean writes
it as `⊢ P → Q`. Then `intro p` reads as
"let $p$ be a proof of $P$", or, more casually, "let's assume
$P$ is true". The goal becomes `⊢ Q` and `p : P`
shows up in your local context.

-/
TacticDoc intro

/--
## Summary

If the goal is `P ∧ Q` or `P ↔ Q`, `constructor` breaks it into two goals.

## Details

If `P Q : Prop` and the goal is `⊢ P ∧ Q`, then `constructor` gives you
two goals: `⊢ P` and `⊢ Q`.

If the goal is `⊢ P ↔ Q`, you get `⊢ P → Q` and `⊢ Q → P`.

## Example

If your local context (the top right box) looks like this
```
X : Type
A B : set X
x : X
⊢ x ∈ A ↔ x ∈ B
```

then after `constructor` it will look like this:

```
2 goals
X : Type
A B : set X
x : X
⊢ x ∈ A → x ∈ B


X : Type
A B : set X
x : X
⊢ x ∈ B → x ∈ A
```

### Working on one goal at a time
When you have several goals, it keeps things tidy to focus on one at a time
with a bullet `·` (type it with `\.`). Like so:
```
constructor
· tac1
  tac1'
· tac2
  tac2'
```
Here `tac1` and `tac1'` work on the first goal, and `tac2` and `tac2'` on the second.
Each bullet has to finish its goal completely. Line up the tactics under the first one
after the bullet. Bullets work after any tactic that creates several goals
(like `constructor`, `rcases` on an `∨`, or `by_cases`).
-/
TacticDoc constructor


/--
## Summary
`use` works on goals that look like `⊢ ∃ x, P x`. The symbol **`∃`** reads
**"there exists"**, and `P x` is some property of `x`. So the goal says
**"there is an `x` with property `P`"**.
To prove it, you just need to offer an example: if you know that `a` has the property,
then `use a` changes the goal into `⊢ P a`.

## Example
If your goal is `⊢ ∃ n : natural_numbers, 1 + x = x + n` then `use 1` will
turn the goal into `⊢ 1 + x = x + 1`, and the rather unwise `use 0` will
turn it into the impossible-to-prove `⊢ 1 + x = x + 0`.
-/
TacticDoc use

/--
## Summary
`have h : P` creates a new goal of proving `P`, and adds `h : P` to the hypotheses of the goal you were working on.

## Details
Use `have` when you want a fact (or any term) in your local context under a name, so you can use it later.

## Example (have q := ... or have q : Q := ...)
If the local context contains

```
f : P → Q
p : P
```
then `have q := f p` adds `q` to your local context, leaving it like this:

```
f : P → Q
p : P
q : Q
```

Strictly speaking you never need `q`, since you could always write `f p` instead. But a short name makes life easier.

## Example (have q : Q)
You can also just say what you want to have, without giving a proof, by leaving out the `:=`. Then Lean adds it as a new goal, so you'll have one more goal than before.

For example if the local context is

```
P Q R : Prop/Type
f : P → Q
g : Q → R
p : P
⊢ R
```
then after `have q : Q` you get a new goal

```
f : P → Q
g : Q → R
p : P
⊢ Q
```
and your original goal gets `q : Q` added to its hypotheses.
-/
TacticDoc «have»


/--
## Summary
`set a := some_complicated_expression` creates a new variable `a` that stands for
whatever expression you like, and replaces the expression by `a` everywhere.

## Details
Handy when an expression is long and you'd like a short name for it.

## Example (set q := ... or set q : Q := ...)
If your local context contains
```
a : ℕ
b : ℕ

⊢ a * b + 3 > 5
```
then using `set c := a * b + 3` will give you
```
a : ℕ
b : ℕ
c := a * b + 3 : ℕ

⊢ c > 5
```
which looks simpler. If instead you used `set c:= a * b + 3 with hc`, then you get an extra
hypothesis `hc` that you can use for rewriting:
```
a : ℕ
b : ℕ
c := a * b + 3 : ℕ
hc : c = a * b + 3
⊢ c > 5
```
-/
TacticDoc set

/--
## Summary

`rcases` works on hypotheses. If `h : P ∧ Q` or `h : P ↔ Q`, then `rcases h`
removes `h` and replaces it with its *ingredients*:
`left : P` and `right : Q`, or `mp : P → Q` and `mpr : Q → P`. It also
works with `h : P ∨ Q` and with `h : ∃ x, P x`.
Write `rcases h with ⟨h1, h2⟩` to pick your own names `h1` and `h2`
(type `⟨` and `⟩` with `\<` and `\>`).

## Details

How do you prove `P ∧ Q`? You prove `P` and you prove `Q`. So a proof of
`P ∧ Q` has two ingredients, and `rcases` pulls them out for you.

For example, if your local context contains
```
h : P ∧ Q
```

then after `rcases h with ⟨p, q⟩` it becomes
```
p : P
q : Q
```
and `h` is gone.

Likewise, `h : P ↔ Q` is proved by proving `P → Q` and `Q → P`,
and `rcases h with ⟨hpq, hqp⟩` replaces `h` with
```
hpq : P → Q
hqp : Q → P
```

**A shortcut:** if you don't need to rename anything, you can grab the
ingredients directly: `h.1` is the first one and `h.2` the second.
So with `h : P ∧ Q`, `h.1 : P` and `h.2 : Q`, and you can use them
right away, e.g. `exact h.2`. The same works for `P ↔ Q`
(`h.1 : P → Q` and `h.2 : Q → P`).

Also note that `rw [h]` works with `h : P ↔ Q` (`rw` understands
`=` and `↔`), but you can't rewrite with an implication.

`rcases` works with `P ∨ Q` too, but it's a bit different.
To prove `P ∨ Q` you give a proof of `P` *or* a proof of `Q`.
So if `h : P ∨ Q`, then `rcases h with p | q` splits your goal in
two: one with `p : P` and the other with `q : Q`.
-/
TacticDoc rcases


/--
## Summary
`left` and `right` work on the goal: they turn
`⊢ P ∨ Q` into `⊢ P` and `⊢ Q` respectively.
## Details
To prove `P ∨ Q` it's enough to prove `P` or to prove `Q`.
Once you've decided which one you're going for, use `left` or `right`
to switch the goal to that choice.
-/
TacticDoc left

/--
## Summary
`left` and `right` work on the goal: they turn
`⊢ P ∨ Q` into `⊢ P` and `⊢ Q` respectively.
## Details
To prove `P ∨ Q` it's enough to prove `P` or to prove `Q`.
Once you've decided which one you're going for, use `left` or `right`
to switch the goal to that choice.
-/
TacticDoc right

/--
## Summary

Splits your proof into two cases: a statement is true, or it's false.

## Details

Suppose you want to prove a statement `P x`, where `x`
is a number. Maybe you know how to do it when `x ≤ 5`,
and a different way when `x > 5`.
Then `by_cases h : x ≤ 5` gives you
two goals: the first has `h : x ≤ 5` in the context
and the second has `h : ¬ x ≤ 5`.
-/
TacticDoc by_cases

/--
## Summary

If `h : P → Q` is a hypothesis, and the goal is `⊢ Q` then
`apply h` changes the goal to `⊢ P`.

## Details

If you have `h : P → Q` and your goal is `⊢ Q`,
then `apply h` changes the goal to `⊢ P`. The idea is
simple: you want a term of type `Q`, and `h` turns terms of
type `P` into terms of type `Q`, so it's enough to build a term of type `P`.
In words: "we need to prove $Q$, but we know $P\implies Q$,
so it's enough to prove $P$".

-/
TacticDoc apply


/--
## Summary
`tauto` is a powerful tactic that proves statements which follow from your hypotheses by pure logic.

## Details
`tauto` does the boring logic for you. It breaks down hypotheses of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`,
and splits goals of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _`, until everything is easy.
It doesn't know any geometry, though, so it can't use the axioms by itself.

## Example
``example (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto``
-/
TacticDoc tauto

/--
## Summary

Changes the goal to `⊢ False`.

## Details

That sounds scary, but it's what you want when your hypotheses
contradict each other: from a contradiction, anything follows.

For example, if you have `h : ¬ P`, then after `exfalso` you can
`apply h` to turn the goal into `⊢ P`.
-/
TacticDoc exfalso

/--
## Summary

Proof by contradiction. It changes the goal from `⊢ P` to `⊢ False` and adds
a new hypothesis `h : ¬ P` to your local context.

## Real Life Example

Say you want to prove `⊢ SKY_ALWAYS_BLUE`, and you know `h : SKY_GREY_WHEN_RAINS`.
Type `by_contra z` to add `z : ¬ SKY_ALWAYS_BLUE` to your context and change the
goal into `⊢ False`. Then use `h` and `z` to find the contradiction.
-/
TacticDoc by_contra

/--
## Summary
`simp` tries to simplify the goal (or close it) using a big database of known facts.

## Details
`simp` uses lemmas that have been tagged with a special label to
simplify a goal or a hypothesis. Use `simp at h` to simplify the hypothesis `h`.
-/
TacticDoc simp
