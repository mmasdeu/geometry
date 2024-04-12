import GameServer.Commands

/--
## Summary

If the goal is exactly one of the assumption, then `assumption` will close
the goal automatically.

### Example
If it looks like this in the top right hand box:
```
A B C : Ω
h1 : A = B
h2 : B = C
⊢ A = B
```

then

`assumption`

will close the goal.
-/
TacticDoc assumption


/--
## Summary

If `h` is a proof of `X = Y`, then `rw [h]` will change
all `X`s in the goal to `Y`s.

**Variants:** `rw [← h]` changes
`Y` to `X` and
`rw [h] at h2` changes `X` to `Y` in hypothesis `h2` instead
of the goal.

## Details

The `rw` tactic is a way to do 'substituting in'. There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw [h]`
will change them all to `B`'s.

2) The `rw` tactic will also work with proofs of theorems
which are equalities (look for them in the drop down
menu on the left, within Theorem Statements).

**Important note:** if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw [h]` will work.

**Pro tip 1:** If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw [←h]` (get the arrow with `\l`,
note that this is a small letter L, not a number 1).

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
then `rw [h1] at h2` will turn `h2` into `h2 : C = B` (remember operator precedence).

-/
TacticDoc rw


/--
## Summary

If the goal is `⊢ X` then `exact x` will close the goal if
and only if `x` is a term of type `X`.

## Details

Say `P`, `Q` and `R` are types (i.e., what a mathematician
might think of as either sets or propositions),
and the local context looks like this:

```
p : P,
h : P → Q,
j : Q → R
⊢ R
```

If you can spot how to make a term of type `R`, then you
can just make it and say you're done using the `exact` tactic
together with the formula you have spotted. For example the
above goal could be solved with

`exact j(h p)`

because `j(h p)` is easily checked to be a term of type `R`
(i.e., an element of the set `R`, or a proof of the proposition `R`).

-/
TacticDoc exact


/--
## Summary

`intro p` will turn a goal `⊢ P → Q` into a hypothesis `p : P`
and goal `⊢ Q`. If `P` and `Q` are sets `intro p` means "let $p$ be an arbitrary element of $P$".
If `P` and `Q` are propositions then `intro p` says "assume $P$ is true".

## Details

If your goal is a function or an implication `⊢ P → Q` then `intro`
will always make progress. `intro p` turns

`⊢ P → Q`

into

```
p : P
⊢ Q
```

The opposite tactic to intro is `revert`; given the situation
just above, `revert p` turns the goal back into `⊢ P → Q`.

**Variant:** Instead of calling `intro` multiple times, you can put several names after `intro`.
That is, `intro h₁ h₂` is equivalent to `intro h₁; intro h₂`.

## Example

If your goal is an implication $P\implies Q$ then Lean writes
this as `⊢ P → Q`, and `intro p,` can be thought of as meaning
"let $p$ be a proof of $P$", or more informally "let's assume that
$P$ is true". The goal changes to `⊢ Q` and the hypothesis `p : P`
appears in the local context.

-/
TacticDoc intro

/--
## Summary

If the goal is `P ∧ Q` or `P ↔ Q` then `constructor` will break it into two goals.

## Details

If `P Q : Prop` and the goal is `⊢ P ∧ Q`, then `constructor` will change it into
two goals, namely `⊢ P` and `⊢ Q`.

If `P Q : Prop` and the goal is `⊢ P ↔ Q`, then `constructor` will change it into
two goals, namely `⊢ P → Q` and `⊢ Q → P`.

## Example

If your local context (the top right window) looks like this
```
X : Type
A B : set X
x : X
⊢ x ∈ A ↔ x ∈ B
```

then after

`constructor`

it will look like this:

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

You can isolate each of the two goals by inserting a `·` (type it with `\.`) for each of them, like so:
```
constructor
· tac1
  tac1'
· tac2
  tac2'
```
Here, `tac1` and `tac1'` are for the first goal, while `tac2` and `tac2'` are for the second.
-/
TacticDoc constructor


/--
## Summary
The `use` tactic works on the goal that looks like `⊢ ∃ x, P x`, where the symbol **`∃`** is read as **"there exists"** and
**`P x`** can be understood as **"P is an element of x"**, which could also be written as **`P ∈ x`**.
In this case, the whole goal can be interpreted as **"there exists x such that P is an element of x"**.
Then, the `use` tactic is useful. If we know that an object `a` satisfies the  property `x`, then `use a`
will simplify the goal into ⊢ P a.

## Example
If your goal is `⊢ ∃ n : natural_numbers, 1 + x = x + n` then `use 1` will
turn the goal into `⊢ 1 + x = x + 1`, and the rather more unwise `use 0` will
turn it into the impossible-to-prove `⊢ 1 + x = x + 0`.
-/
TacticDoc use

/--
## Summary
`have h : P,` will create a new goal of creating a term of type `P`, and will add `h : P` to the hypotheses for the goal you were working on.

## Details
If you want to name a term of some type (because you want it in your local context for some reason), and if you have the formula for the term, you can use have to give the term a name.

## Example (have q := ... or have q : Q := ...)
If the local context contains

```
f : P → Q
p : P
```
then the tactic `have q := f(p)` will add `q` to our local context, leaving it like this:

```
f : P → Q
p : P
q : Q
```

If you think about it, you don't ever really need `q`, because whenever you think you need it you coudl just use `f(p)` instead. But it's good that we can introduce convenient notation like this.

## Example (have q : Q)
A variant of this tactic can be used where you just declare the type of the term you want to have, finish the tactic statement with a comma and no :=, and then Lean just adds it as a new goal. The number of goals goes up by one if you use `have` like this.

For example if the local context is

```
P Q R : Prop/Type,
f : P → Q,
g : Q → R,
p : P
⊢ R
```
then after `have q : Q`, there will be the new goal

```
f : P → Q,
g : Q → R,
p : P,
⊢ Q
```
and your original goal will have `q : Q` added to the list of hypotheses.
-/
TacticDoc «have»

/--
## Summary

`rcases` is a tactic which works on hypotheses.
If `h : P ∧ Q` or `h : P ↔ Q` is a hypothesis then `rcases h`
will remove `h`
from the list of hypotheses and replace it with the *ingredients* of `h`,
i.e. `left : P` and `right : Q`, or `mp : P → Q` and `mpr : Q → P`. Also
works with `h : P ∨ Q` and with `h : ∃ x, P x`.
The syntax `rcases h with ⟨h1, h2⟩` renames the new hypotheses as `h1` and `h2`.

## Details

How does one prove `P ∧ Q`? The way to do it is to prove `P` and to
prove `Q`. There are hence two ingredients which go into a proof of
`P ∧ Q`, and the `rcases` tactic extracts them.

More precisely, if the local context contains
```
h : P ∧ Q`
```

then after the tactic `rcases h with ⟨p, q⟩` the local context will
change to
```
p : P
q : Q
```
and `h` will disappear.

Similarly `h : P ↔ Q` is proved by proving `P → Q` and `Q → P`,
and `rcases h with ⟨hpq, hqp⟩` will delete our assumption `h` and
replace it with
```
hpq : P → Q
hqp : Q → P
```

Be warned though -- `rw [h]` works with `h : P ↔ Q` (`rw` works with
`=` and `↔`), whereas you cannot rewrite with an implication.

`rcases` also works with hypotheses of the form `P ∨ Q`. Here the situation
is different however.
To prove `P ∨ Q` you need to give either a proof of `P` *or* a proof
of `Q`, so if `h : P ∨ Q` then r`rcases h` will change one goal
into two, one with `p : P` and the other with `q : Q`.
-/
TacticDoc rcases


/--
## Summary
`left` and `right` work on the goal, and they change
`⊢ P ∨ Q` to `⊢ P` and `⊢ Q` respectively.
## Details
The tactics `left` and `right` work on a goal which is a type with
two constructors, the classic example being `P ∨ Q`.
To prove `P ∨ Q` it suffices to either prove `P` or prove `Q`,
and once you know which one you are going for you can change
the goal with `left` or `right` to the appropriate choice.
-/
TacticDoc left

/--
## Summary
`left` and `right` work on the goal, and they change
`⊢ P ∨ Q` to `⊢ P` and `⊢ Q` respectively.
## Details
The tactics `left` and `right` work on a goal which is a type with
two constructors, the classic example being `P ∨ Q`.
To prove `P ∨ Q` it suffices to either prove `P` or prove `Q`,
and once you know which one you are going for you can change
the goal with `left` or `right` to the appropriate choice.
-/
TacticDoc right

/--
## Summary

Generates two goals corresponding to a given statement being
true or false

## Details

Suppose that we want to prove a statement `P x`, where `x`
is some number. We may know how to prove it when `x ≤ 5`
and also when `x > 5`, but using a different method.
In this situation, using `by_cases h : x ≤ 5` will produce
two new goals, the first one with `h : x ≤ 5` in the context
and the second one with `h : ¬ x ≤ 5`.
-/
TacticDoc by_cases

/--
## Summary

If `h : P → Q` is a hypothesis, and the goal is `⊢ Q` then
`apply h` changes the goal to `⊢ P`.

## Details

If you have a function `h : P → Q` and your goal is `⊢ Q`
then `apply h` changes the goal to `⊢ P`. The logic is
simple: if you are trying to create a term of type `Q`,
but `h` is a function which turns terms of type `P` into
terms of type `Q`, then it will suffice to construct a
term of type `P`. A mathematician might say: "we need
to construct an element of $Q$, but we have a function $h:P\to Q$
so it suffices to construct an element of $P$". Or alternatively
"we need to prove $Q$, but we have a proof $h$ that $P\implies Q$
so it suffices to prove $P$".

-/
TacticDoc apply


/--
## Summary
The `tauto` tactic is a high-level tactic which tries to prove statements that follow tautologically
from the hypotheses.

## Details
The `tauto` tactic does basic automation. It breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`,
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be proved using trivialities.

## Example
``example (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto``
-/
TacticDoc tauto

/--
## Summary

Changes the goal to `⊢ false`.

## Details

This may seem hard to prove,
but it is useful when we have a contradiction in the hypotheses.

For example, if we have `h : ¬ P` as a hypothesis and we apply `exfalso`
we can then `apply h` to transform the goal into `⊢ P`.
-/
TacticDoc exfalso

/--
## Summary

It changes the goal from `⊢ P` to `⊢ false` and adds a new hypothesis
of the form `h : ¬ P` to the local context.

## Real Life Example

If we want to prove `⊢ SKY_ALWAYS_BLUE`, but we assume that `h : SKY_GREY_WHEN_RAINS`,
type `by_contra z` to add `z : ¬ (SKY_ALWAYS_BLUE)` to the local context and change the
goal into `⊢ false`. Then, argue that `h : SKY_GREY_WHEN_RAINS` to finish the proof.
-/
TacticDoc by_contra

/--
## Summary
The `simp` tactic is a high-level tactic which tries to prove equalities using facts in its database.

## Details
The `simp` tactic does basic automation. It uses lemmas already proved that have been tagged
with a special label, to simplify either a goal or a hypothesis.
-/
TacticDoc simp
