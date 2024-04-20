import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Have
import Mathlib.Tactic.ByContra


open scoped Classical
open Set Function

class SSet (A : Type*) (B : outParam $ Type*) :=
(mem : B → A → Prop)

namespace subset
-- The following allows us to use the symbol `∈`
instance {A : Type*} {B : Type*} [SSet A B] : Membership B A := ⟨SSet.mem⟩

-- This says that two "subset"s are equivalent (written `≈`, type with \approx) when
-- they have the same points.
instance {A : Type*} {B : Type*} [SSet A B] : HasEquiv A :=
⟨λ X Y ↦ ∀ t, t ∈ X ↔ t ∈ Y⟩

@[simp] lemma equiv_iff {A : Type*} {B : Type*} [SSet A B] (X Y : A) :
X ≈ Y ↔ ∀ t, t ∈ X ↔ t ∈ Y := Iff.rfl

-- A "subset" can always be considered as an actual subset, in Lean this is `Set B`
instance {A : Type*} {B : Type*} [SSet A B] : CoeHead A (Set B) := ⟨λ x p ↦ p ∈ x⟩

--@[simp] lemma mem_pts  {A : Type*} {B : Type*} [SSet A B] (a : A) (P : B) :
--P ∈ (a : Set B) ↔ P ∈ a := Iff.rfl

end subset

@[simp] def pts {A : Type*} {B : Type*} [SSet A B] : A → Set B := λ a ↦ {x : B | x ∈ a}


set_option quotPrecheck false

class HasBetween (Point : Type*) where
  rel : Point → Point → Point → Prop

notation:37 A:max "*" B:max "*" C => HasBetween.rel A B C

notation p "xor" q => (p ∧ ¬ q) ∨ (¬ p ∧ q)

variable (Point : Type*)

/--
We define an incidence plane as having the undefined terms `Point` and `Line`,
a function `distance` that takes every two points to a real number, and a predicate
`belongs` that relates points and lines.

There are essentially two axioms: existence of two distinct points, and the incidence postulate.
-/
class IncidencePlane (Point : Type*) where
  (Line : Type*)

  -- Belongs is an undefined concept
  [belongs : Membership Point Line]

  -- A1 postulate is divided into 4 statements
  (line_through : Point → Point → Line)
  (line_through_left (P Q : Point) : P ∈ line_through P Q)
  (line_through_right (P Q : Point) : Q ∈ line_through P Q)
  (incidence {P Q : Point} {ℓ : Line} : P ≠ Q → P ∈ ℓ → Q ∈ ℓ → ℓ = line_through P Q)

  -- A2 postulate
  (line_contains_two_points (ℓ : Line) : ∃ P Q : Point, P ≠ Q ∧ ℓ = line_through P Q)

  -- A3 postulate (existence postulate)
  (existence' : ∃ P Q R : Point, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ ¬ R ∈ (line_through P Q))

  -- Betweenness is an undefined concept
  [between : HasBetween Point]

  /-- Betweenness is symmetric -/
  (between_symmetric {A B C : Point} : (A * B * C) ↔ C * B * A)

   /- If A * B * C then the three points are distinct and collinear. -/
  (different_of_between_12 {A B C : Point} : (A * B * C) → A ≠ B)
  (different_of_between_13 {A B C : Point} : (A * B * C) → A ≠ C)
  (different_of_between_23 {A B C : Point} : (A * B * C) → B ≠ C)

  (collinear_of_between' {A B C : Point} : (A * B * C) →
    ∃ (ℓ : Line), A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ)

  /-- Given two distinct points A, B, there is a third point C such that A * B * C.-/
  (point_on_ray {A B : Point} (h: A ≠ B) : ∃ C, A * B * C)

  /-- Given 3 distinct collinear points A B C, exactly one of them is between the other two.-/
  (between_of_collinear {A B C : Point} (h: ∃ (ℓ : Line), A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ) :
  ((A * B * C) ∧ ¬ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
  (¬ (A * B * C) ∧ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
  (¬ (A * B * C) ∧ ¬ ( B * A * C ) ∧ (A * C * B)))

  /-- Pasch -/
  (pasch' {A B C D : Point} {ℓ : Line}
  (hnc: ¬ C ∈ line_through A B)
  (hnAl: ¬ (A ∈ ℓ)) (hnBl: ¬ B ∈ ℓ) (hnCl: ¬ C ∈ ℓ)
  (hDl: D ∈ ℓ) (hADB: A * D * B) :
  (∃ (E : Point) , E ∈ ℓ ∧ (A * E * C)) xor (∃ (E : Point) , E ∈ ℓ ∧ (B * E * C)))


namespace IncidencePlane

instance (Point : Type*) [IncidencePlane Point] :
  Membership Point (IncidencePlane.Line Point) := IncidencePlane.belongs

instance (Point : Type*) [IncidencePlane Point] : HasBetween Point := between

variable {Ω Point : Type*} [IncidencePlane Ω] [IncidencePlane Point]

-- From here on, we can use the symbol `∈` for Lines
instance : SSet (Line Ω) Ω := ⟨belongs.mem⟩



lemma existence (Ω : Type*) [IncidencePlane Ω] :  ∃ P Q R : Ω, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ ¬ R ∈ (line_through P Q) := existence'

attribute [simp] line_through_left
attribute [simp] line_through_right

@[simp]
lemma different_of_between''
{A B : Ω} : (A * A * B) ↔ false := ⟨λ h ↦ ((different_of_between_12 h) (rfl)).elim, by tauto⟩

@[simp]
lemma different_of_between'''
{A B : Ω} : (A * B * B) ↔ false := ⟨λ h ↦ ((different_of_between_23 h) (rfl)).elim, by tauto⟩

/--
A set of points is collinear if they all lie on some line
-/
def collinear (A B C : Ω) := ∃ (ℓ : Line Ω), A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ

lemma collinear_of_between {A B C : Point} : (A * B * C) → collinear A B C := collinear_of_between'

lemma collinear_of_equal' (A B C D E F) (h : ({A, B, C} : Set Ω) = {D, E, F}) : collinear A B C → collinear D E F
:= by
  intro h1
  rcases h1 with ⟨ℓ, ⟨hA, hB, hC⟩⟩
  use ℓ
  have hABC : ∀ P, P ∈ ({A, B, C} : Set Ω) → P ∈ ℓ
  · simp [hA, hB, hC]
  simpa [h] using hABC

/--
If A B C D E F are any six points such that the set {A, B, C} = {D, E, F}, then A, B, C are collinear if and only if D, E, F are.
-/
lemma collinear_of_equal (A B C D E F) (h : ({A, B, C} : Set Ω) = ({D, E, F} : Set Ω) :=  by try {ext; simp; tauto}) : collinear A B C ↔ collinear D E F
:= by
constructor
· exact collinear_of_equal' (h := h)
· exact collinear_of_equal' (h := Eq.symm h)


/--
Two points P and Q lie on the same side of a line ℓ if the segment P⬝Q doesn't intersect ℓ
-/
@[simp]
def same_side (ℓ : Line Ω) (P Q : Ω) :=  P ∉ ℓ ∧ Q ∉ ℓ ∧ (∀ x ∈ ℓ,  ¬ (P * x * Q))

lemma pasch {A B C D : Ω} {ℓ : Line Ω}
  (hnc: ¬ C ∈ line_through A B)
  (hnAl: ¬ (A ∈ ℓ)) (hnBl: ¬ B ∈ ℓ) (hnCl: ¬ C ∈ ℓ)
  (hDl: D ∈ ℓ) (hADB: A * D * B) :
  same_side ℓ A C xor same_side ℓ C B := sorry
end IncidencePlane
