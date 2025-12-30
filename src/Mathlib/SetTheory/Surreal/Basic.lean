import VerifiedAgora.tagger
/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.SetTheory.Game.Ordinal

/-!
# Surreal numbers

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games.

A pregame is `Numeric` if all the Left options are strictly smaller than all the Right options, and
all those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

A surreal number is an equivalence class of numeric pregames.

In fact, the surreals form a complete ordered field, containing a copy of the reals (and much else
besides!) but we do not yet have a complete development.

## Order properties

Surreal numbers inherit the relations `≤` and `<` from games (`Surreal.instLE` and
`Surreal.instLT`), and these relations satisfy the axioms of a partial order.

## Algebraic operations

In this file, we show that the surreals form a linear ordered commutative group.

In `Mathlib.SetTheory.Surreal.Multiplication`, we define multiplication and show that the
surreals form a linear ordered commutative ring.

One can also map all the ordinals into the surreals!

## TODO

- Define the field structure on the surreals.

## References

* [Conway, *On numbers and games*][Conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][SchleicherStoll]

-/


universe u

namespace SetTheory

open scoped PGame

namespace PGame

/-- A pre-game is numeric if everything in the L set is less than everything in the R set,
and all the elements of L and R are also numeric. -/
def Numeric : PGame → Prop
  | ⟨_, _, L, R⟩ => (∀ i j, L i < R j) ∧ (∀ i, Numeric (L i)) ∧ ∀ j, Numeric (R j)

@[target]
theorem numeric_def {x : PGame} :
    Numeric x ↔
      (∀ i j, x.moveLeft i < x.moveRight j) ∧
        (∀ i, Numeric (x.moveLeft i)) ∧ ∀ j, Numeric (x.moveRight j) := by sorry

namespace Numeric

@[target]
theorem mk {x : PGame} (h₁ : ∀ i j, x.moveLeft i < x.moveRight j) (h₂ : ∀ i, Numeric (x.moveLeft i))
    (h₃ : ∀ j, Numeric (x.moveRight j)) : Numeric x := by sorry

@[target]
theorem left_lt_right {x : PGame} (o : Numeric x) (i : x.LeftMoves) (j : x.RightMoves) :
    x.moveLeft i < x.moveRight j := by sorry

@[target]
theorem moveLeft {x : PGame} (o : Numeric x) (i : x.LeftMoves) : Numeric (x.moveLeft i) := by sorry

@[target]
theorem moveRight {x : PGame} (o : Numeric x) (j : x.RightMoves) : Numeric (x.moveRight j) := by sorry

@[target]
lemma isOption {x' x} (h : IsOption x' x) (hx : Numeric x) : Numeric x' := by sorry

end Numeric

@[target, elab_as_elim]
theorem numeric_rec {C : PGame → Prop}
    (H : ∀ (l r) (L : l → PGame) (R : r → PGame), (∀ i j, L i < R j) →
      (∀ i, Numeric (L i)) → (∀ i, Numeric (R i)) → (∀ i, C (L i)) → (∀ i, C (R i)) →
      C ⟨l, r, L, R⟩) :
    ∀ x, Numeric x → C x := by sorry

@[target]
theorem Relabelling.numeric_imp {x y : PGame} (r : x ≡r y) (ox : Numeric x) : Numeric y := by sorry

/-- Relabellings preserve being numeric. -/
theorem Relabelling.numeric_congr {x y : PGame} (r : x ≡r y) : Numeric x ↔ Numeric y :=
  ⟨r.numeric_imp, r.symm.numeric_imp⟩

@[target]
theorem lf_asymm {x y : PGame} (ox : Numeric x) (oy : Numeric y) : x ⧏ y → ¬y ⧏ x := by sorry

@[target]
theorem le_of_lf {x y : PGame} (h : x ⧏ y) (ox : Numeric x) (oy : Numeric y) : x ≤ y := by sorry

@[target]
theorem lt_of_lf {x y : PGame} (h : x ⧏ y) (ox : Numeric x) (oy : Numeric y) : x < y := by sorry

@[target]
theorem lf_iff_lt {x y : PGame} (ox : Numeric x) (oy : Numeric y) : x ⧏ y ↔ x < y := by sorry

/-- Definition of `x ≤ y` on numeric pre-games, in terms of `<` -/
@[target]
theorem le_iff_forall_lt {x y : PGame} (ox : x.Numeric) (oy : y.Numeric) :
    x ≤ y ↔ (∀ i, x.moveLeft i < y) ∧ ∀ j, x < y.moveRight j := by sorry

/-- Definition of `x < y` on numeric pre-games, in terms of `≤` -/
@[target]
theorem lt_iff_exists_le {x y : PGame} (ox : x.Numeric) (oy : y.Numeric) :
    x < y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by sorry

@[target]
theorem lt_of_exists_le {x y : PGame} (ox : x.Numeric) (oy : y.Numeric) :
    ((∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y) → x < y := by sorry

/-- The definition of `x < y` on numeric pre-games, in terms of `<` two moves later. -/
@[target]
theorem lt_def {x y : PGame} (ox : x.Numeric) (oy : y.Numeric) :
    x < y ↔
      (∃ i, (∀ i', x.moveLeft i' < y.moveLeft i) ∧ ∀ j, x < (y.moveLeft i).moveRight j) ∨
        ∃ j, (∀ i, (x.moveRight j).moveLeft i < y) ∧ ∀ j', x.moveRight j < y.moveRight j' := by sorry

@[target]
theorem not_fuzzy {x y : PGame} (ox : Numeric x) (oy : Numeric y) : ¬Fuzzy x y := by sorry

@[target]
theorem lt_or_equiv_or_gt {x y : PGame} (ox : Numeric x) (oy : Numeric y) :
    x < y ∨ (x ≈ y) ∨ y < x := by sorry

@[target]
theorem numeric_of_isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : Numeric x := by sorry

@[target]
theorem numeric_of_isEmpty_leftMoves (x : PGame) [IsEmpty x.LeftMoves] :
    (∀ j, Numeric (x.moveRight j)) → Numeric x := by sorry

@[target]
theorem numeric_of_isEmpty_rightMoves (x : PGame) [IsEmpty x.RightMoves]
    (H : ∀ i, Numeric (x.moveLeft i)) : Numeric x := by sorry

@[target]
theorem numeric_zero : Numeric 0 := by sorry

@[target]
theorem numeric_one : Numeric 1 := by sorry

@[target]
theorem Numeric.neg : ∀ {x : PGame} (_ : Numeric x), Numeric (-x) := by sorry

/-- Inserting a smaller numeric left option into a numeric game results in a numeric game. -/
@[target]
theorem insertLeft_numeric {x x' : PGame} (x_num : x.Numeric) (x'_num : x'.Numeric)
    (h : x' ≤ x) : (insertLeft x x').Numeric := by sorry

/-- Inserting a larger numeric right option into a numeric game results in a numeric game. -/
@[target]
theorem insertRight_numeric {x x' : PGame} (x_num : x.Numeric) (x'_num : x'.Numeric)
    (h : x ≤ x') : (insertRight x x').Numeric := by sorry

namespace Numeric

@[target]
theorem moveLeft_lt {x : PGame} (o : Numeric x) (i) : x.moveLeft i < x := by sorry

theorem moveLeft_le {x : PGame} (o : Numeric x) (i) : x.moveLeft i ≤ x :=
  (o.moveLeft_lt i).le

@[target]
theorem lt_moveRight {x : PGame} (o : Numeric x) (j) : x < x.moveRight j := by sorry

@[target]
theorem le_moveRight {x : PGame} (o : Numeric x) (j) : x ≤ x.moveRight j := by sorry

@[target]
theorem add : ∀ {x y : PGame} (_ : Numeric x) (_ : Numeric y), Numeric (x + y) := by sorry

@[target]
theorem sub {x y : PGame} (ox : Numeric x) (oy : Numeric y) : Numeric (x - y) := by sorry

end Numeric

/-- Pre-games defined by natural numbers are numeric. -/
@[target]
theorem numeric_nat : ∀ n : ℕ, Numeric n := by sorry

/-- Ordinal games are numeric. -/
@[target]
theorem numeric_toPGame (o : Ordinal) : o.toPGame.Numeric := by sorry

end PGame

end SetTheory

open SetTheory PGame

/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a total order. -/
def Surreal :=
  Quotient (inferInstanceAs <| Setoid (Subtype Numeric))

namespace Surreal

/-- Construct a surreal number from a numeric pre-game. -/
def mk (x : PGame) (h : x.Numeric) : Surreal :=
  ⟦⟨x, h⟩⟧

instance : Zero Surreal :=
  ⟨mk 0 numeric_zero⟩

instance : One Surreal :=
  ⟨mk 1 numeric_one⟩

instance : Inhabited Surreal :=
  ⟨0⟩

@[target]
lemma mk_eq_mk {x y : PGame.{u}} {hx hy} : mk x hx = mk y hy ↔ x ≈ y := by sorry

@[target]
lemma mk_eq_zero {x : PGame.{u}} {hx} : mk x hx = 0 ↔ x ≈ 0 := by sorry

/-- Lift an equivalence-respecting function on pre-games to surreals. -/
def lift {α} (f : ∀ x, Numeric x → α)
    (H : ∀ {x y} (hx : Numeric x) (hy : Numeric y), x.Equiv y → f x hx = f y hy) : Surreal → α :=
  Quotient.lift (fun x : { x // Numeric x } => f x.1 x.2) fun x y => H x.2 y.2

/-- Lift a binary equivalence-respecting function on pre-games to surreals. -/
def lift₂ {α} (f : ∀ x y, Numeric x → Numeric y → α)
    (H :
      ∀ {x₁ y₁ x₂ y₂} (ox₁ : Numeric x₁) (oy₁ : Numeric y₁) (ox₂ : Numeric x₂) (oy₂ : Numeric y₂),
        x₁.Equiv x₂ → y₁.Equiv y₂ → f x₁ y₁ ox₁ oy₁ = f x₂ y₂ ox₂ oy₂) :
    Surreal → Surreal → α :=
  lift (fun x ox => lift (fun y oy => f x y ox oy) fun _ _ => H _ _ _ _ equiv_rfl)
    fun _ _ h => funext <| Quotient.ind fun _ => H _ _ _ _ h equiv_rfl

instance instLE : LE Surreal :=
  ⟨lift₂ (fun x y _ _ => x ≤ y) fun _ _ _ _ hx hy => propext (le_congr hx hy)⟩

@[target, simp]
lemma mk_le_mk {x y : PGame.{u}} {hx hy} : mk x hx ≤ mk y hy ↔ x ≤ y := by sorry

lemma zero_le_mk {x : PGame.{u}} {hx} : 0 ≤ mk x hx ↔ 0 ≤ x := Iff.rfl

instance instLT : LT Surreal :=
  ⟨lift₂ (fun x y _ _ => x < y) fun _ _ _ _ hx hy => propext (lt_congr hx hy)⟩

@[target]
lemma mk_lt_mk {x y : PGame.{u}} {hx hy} : mk x hx < mk y hy ↔ x < y := by sorry

@[target]
lemma zero_lt_mk {x : PGame.{u}} {hx} : 0 < mk x hx ↔ 0 < x := by sorry

/-- Same as `moveLeft_lt`, but for `Surreal` instead of `PGame` -/
@[target]
theorem mk_moveLeft_lt_mk {x : PGame} (o : Numeric x) (i) :
    Surreal.mk (x.moveLeft i) (Numeric.moveLeft o i) < Surreal.mk x o := by sorry

/-- Same as `lt_moveRight`, but for `Surreal` instead of `PGame` -/
@[target]
theorem mk_lt_mk_moveRight {x : PGame} (o : Numeric x) (j) :
    Surreal.mk x o < Surreal.mk (x.moveRight j) (Numeric.moveRight o j) := by sorry

/-- Addition on surreals is inherited from pre-game addition:
the sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add Surreal :=
  ⟨Surreal.lift₂ (fun (x y : PGame) ox oy => ⟦⟨x + y, ox.add oy⟩⟧) fun _ _ _ _ hx hy =>
      Quotient.sound (add_congr hx hy)⟩

/-- Negation for surreal numbers is inherited from pre-game negation:
the negation of `{L | R}` is `{-R | -L}`. -/
instance : Neg Surreal :=
  ⟨Surreal.lift (fun x ox => ⟦⟨-x, ox.neg⟩⟧) fun _ _ a => Quotient.sound (neg_equiv_neg_iff.2 a)⟩

instance orderedAddCommGroup : OrderedAddCommGroup Surreal where
  add := (· + ·)
  add_assoc := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound add_assoc_equiv
  zero := 0
  zero_add := by rintro ⟨a⟩; exact Quotient.sound (zero_add_equiv a)
  add_zero := by rintro ⟨a⟩; exact Quotient.sound (add_zero_equiv a)
  neg := Neg.neg
  neg_add_cancel := by rintro ⟨a⟩; exact Quotient.sound (neg_add_cancel_equiv a)
  add_comm := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound add_comm_equiv
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by rintro ⟨_⟩; apply @le_rfl PGame
  le_trans := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; apply @le_trans PGame
  lt_iff_le_not_le := by rintro ⟨_, ox⟩ ⟨_, oy⟩; apply @lt_iff_le_not_le PGame
  le_antisymm := by rintro ⟨_⟩ ⟨_⟩ h₁ h₂; exact Quotient.sound ⟨h₁, h₂⟩
  add_le_add_left := by rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩; exact @add_le_add_left PGame _ _ _ _ _ hx _
  nsmul := nsmulRec
  zsmul := zsmulRec

lemma mk_add {x y : PGame} (hx : x.Numeric) (hy : y.Numeric) :
    Surreal.mk (x + y) (hx.add hy) = Surreal.mk x hx + Surreal.mk y hy := by rfl

@[target]
lemma mk_sub {x y : PGame} (hx : x.Numeric) (hy : y.Numeric) :
    Surreal.mk (x - y) (hx.sub hy) = Surreal.mk x hx - Surreal.mk y hy := by sorry

@[target]
lemma zero_def : 0 = mk 0 numeric_zero := by sorry

noncomputable instance : LinearOrderedAddCommGroup Surreal :=
  { Surreal.orderedAddCommGroup with
    le_total := by
      rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩
      sorry
    decidableLE := Classical.decRel _ }

instance : AddMonoidWithOne Surreal :=
  AddMonoidWithOne.unary

/-- Casts a `Surreal` number into a `Game`. -/
def toGame : Surreal →+o Game where
  toFun := lift (fun x _ => ⟦x⟧) fun _ _ => Quot.sound
  map_zero' := rfl
  map_add' := by rintro ⟨_, _⟩ ⟨_, _⟩; rfl
  monotone' := by rintro ⟨_, _⟩ ⟨_, _⟩; exact id

@[target, simp]
theorem zero_toGame : toGame 0 = 0 := by sorry

@[target, simp]
theorem one_toGame : toGame 1 = 1 := by sorry

@[simp]
theorem nat_toGame : ∀ n : ℕ, toGame n = n :=
  map_natCast' _ one_toGame

/-- A small family of surreals is bounded above. -/
@[target]
lemma bddAbove_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Surreal.{u}) :
    BddAbove (Set.range f) := by sorry

/-- A small set of surreals is bounded above. -/
@[target]
lemma bddAbove_of_small (s : Set Surreal.{u}) [Small.{u} s] : BddAbove s := by sorry

/-- A small family of surreals is bounded below. -/
@[target]
lemma bddBelow_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Surreal.{u}) :
    BddBelow (Set.range f) := by sorry

/-- A small set of surreals is bounded below. -/
@[target]
lemma bddBelow_of_small (s : Set Surreal.{u}) [Small.{u} s] : BddBelow s := by sorry

end Surreal

open Surreal

namespace Ordinal

/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def toSurreal : Ordinal ↪o Surreal where
  toFun o := mk _ (numeric_toPGame o)
  inj' a b h := toPGame_equiv_iff.1 (by apply Quotient.exact h) -- Porting note: Added `by apply`
  map_rel_iff' := @toPGame_le_iff

end Ordinal
