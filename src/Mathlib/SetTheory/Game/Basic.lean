import VerifiedAgora.tagger
/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Kim Morrison, Apurva Nakade, Yuyang Zhao
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.SetTheory.Game.PGame
import Mathlib.Tactic.Abel

/-!
# Combinatorial games.

In this file we construct an instance `OrderedAddCommGroup SetTheory.Game`.

## Multiplication on pre-games

We define the operations of multiplication and inverse on pre-games, and prove a few basic theorems
about them. Multiplication is not well-behaved under equivalence of pre-games i.e. `x ≈ y` does not
imply `x * z ≈ y * z`. Hence, multiplication is not a well-defined operation on games. Nevertheless,
the abelian group structure on games allows us to simplify many proofs for pre-games.
-/

-- Porting note: many definitions here are noncomputable as the compiler does not support PGame.rec
noncomputable section

namespace SetTheory

open Function PGame

universe u

-- Porting note: moved the setoid instance to PGame.lean

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `PGame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
abbrev Game :=
  Quotient PGame.setoid

namespace Game

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11445): added this definition
/-- Negation of games. -/
instance : Neg Game where
  neg := Quot.map Neg.neg <| fun _ _ => (neg_equiv_neg_iff).2

instance : Zero Game where zero := ⟦0⟧
instance : Add Game where
  add := Quotient.map₂ HAdd.hAdd <| fun _ _ hx _ _ hy => PGame.add_congr hx hy

instance instAddCommGroupWithOneGame : AddCommGroupWithOne Game where
  zero := ⟦0⟧
  one := ⟦1⟧
  add_zero := by
    rintro ⟨x⟩
    exact Quot.sound (add_zero_equiv x)
  zero_add := by
    rintro ⟨x⟩
    exact Quot.sound (zero_add_equiv x)
  add_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    exact Quot.sound add_assoc_equiv
  neg_add_cancel := Quotient.ind <| fun x => Quot.sound (neg_add_cancel_equiv x)
  add_comm := by
    rintro ⟨x⟩ ⟨y⟩
    exact Quot.sound add_comm_equiv
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Inhabited Game :=
  ⟨0⟩

@[target]
theorem zero_def : (0 : Game) = ⟦0⟧ := by sorry

instance instPartialOrderGame : PartialOrder Game where
  le := Quotient.lift₂ (· ≤ ·) fun _ _ _ _ hx hy => propext (le_congr hx hy)
  le_refl := by
    rintro ⟨x⟩
    exact le_refl x
  le_trans := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    exact @le_trans _ _ x y z
  le_antisymm := by
    rintro ⟨x⟩ ⟨y⟩ h₁ h₂
    apply Quot.sound
    exact ⟨h₁, h₂⟩
  lt := Quotient.lift₂ (· < ·) fun _ _ _ _ hx hy => propext (lt_congr hx hy)
  lt_iff_le_not_le := by
    rintro ⟨x⟩ ⟨y⟩
    exact @lt_iff_le_not_le _ _ x y

/-- The less or fuzzy relation on games.

If `0 ⧏ x` (less or fuzzy with), then Left can win `x` as the first player. -/
def LF : Game → Game → Prop :=
  Quotient.lift₂ PGame.LF fun _ _ _ _ hx hy => propext (lf_congr hx hy)

/-- On `Game`, simp-normal inequalities should use as few negations as possible. -/
@[target, simp]
theorem not_le : ∀ {x y : Game}, ¬x ≤ y ↔ Game.LF y x := by sorry

/-- On `Game`, simp-normal inequalities should use as few negations as possible. -/
@[target, simp]
theorem not_lf : ∀ {x y : Game}, ¬Game.LF x y ↔ y ≤ x := by sorry

/-- The fuzzy, confused, or incomparable relation on games.

If `x ‖ 0`, then the first player can always win `x`. -/
def Fuzzy : Game → Game → Prop :=
  Quotient.lift₂ PGame.Fuzzy fun _ _ _ _ hx hy => propext (fuzzy_congr hx hy)

-- Porting note: had to replace ⧏ with LF, otherwise cannot differentiate with the operator on PGame
instance : IsTrichotomous Game LF :=
  ⟨by
    rintro ⟨x⟩ ⟨y⟩
    change _ ∨ ⟦x⟧ = ⟦y⟧ ∨ _
    rw [Quotient.eq]
    apply lf_or_equiv_or_gf⟩

/-! It can be useful to use these lemmas to turn `PGame` inequalities into `Game` inequalities, as
the `AddCommGroup` structure on `Game` often simplifies many proofs. -/

end Game

namespace PGame

-- Porting note: In a lot of places, I had to add explicitly that the quotient element was a Game.
-- In Lean4, quotients don't have the setoid as an instance argument,
-- but as an explicit argument, see https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/confusion.20between.20equivalence.20and.20instance.20setoid/near/360822354
theorem le_iff_game_le {x y : PGame} : x ≤ y ↔ (⟦x⟧ : Game) ≤ ⟦y⟧ :=
  Iff.rfl

@[target]
theorem lf_iff_game_lf {x y : PGame} : x ⧏ y ↔ Game.LF ⟦x⟧ ⟦y⟧ := by sorry

@[target]
theorem lt_iff_game_lt {x y : PGame} : x < y ↔ (⟦x⟧ : Game) < ⟦y⟧ := by sorry

@[target]
theorem equiv_iff_game_eq {x y : PGame} : x ≈ y ↔ (⟦x⟧ : Game) = ⟦y⟧ := by sorry

alias ⟨game_eq, _⟩ := equiv_iff_game_eq

theorem fuzzy_iff_game_fuzzy {x y : PGame} : x ‖ y ↔ Game.Fuzzy ⟦x⟧ ⟦y⟧ :=
  Iff.rfl

end PGame

namespace Game

local infixl:50 " ⧏ " => LF
local infixl:50 " ‖ " => Fuzzy

instance addLeftMono : AddLeftMono Game :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_le_add_left _ _ _ _ b c h a⟩

instance addRightMono : AddRightMono Game :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_le_add_right _ _ _ _ b c h a⟩

instance addLeftStrictMono : AddLeftStrictMono Game :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_lt_add_left _ _ _ _ b c h a⟩

instance addRightStrictMono : AddRightStrictMono Game :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_lt_add_right _ _ _ _ b c h a⟩

@[target]
theorem add_lf_add_right : ∀ {b c : Game} (_ : b ⧏ c) (a), (b + a : Game) ⧏ c + a := by sorry

@[target]
theorem add_lf_add_left : ∀ {b c : Game} (_ : b ⧏ c) (a), (a + b : Game) ⧏ a + c := by sorry

instance orderedAddCommGroup : OrderedAddCommGroup Game :=
  { Game.instAddCommGroupWithOneGame, Game.instPartialOrderGame with
    add_le_add_left := @add_le_add_left _ _ _ Game.addLeftMono }

/-- A small family of games is bounded above. -/
@[target]
lemma bddAbove_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Game.{u}) :
    BddAbove (Set.range f) := by sorry

/-- A small set of games is bounded above. -/
@[target]
lemma bddAbove_of_small (s : Set Game.{u}) [Small.{u} s] : BddAbove s := by sorry

/-- A small family of games is bounded below. -/
@[target]
lemma bddBelow_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Game.{u}) :
    BddBelow (Set.range f) := by sorry

/-- A small set of games is bounded below. -/
@[target]
lemma bddBelow_of_small (s : Set Game.{u}) [Small.{u} s] : BddBelow s := by sorry

end Game

namespace PGame

@[simp] theorem quot_zero : (⟦0⟧ : Game) = 0 := rfl
@[simp] theorem quot_one : (⟦1⟧ : Game) = 1 := rfl
@[simp] theorem quot_neg (a : PGame) : (⟦-a⟧ : Game) = -⟦a⟧ := rfl
@[simp] theorem quot_add (a b : PGame) : ⟦a + b⟧ = (⟦a⟧ : Game) + ⟦b⟧ := rfl
@[simp] theorem quot_sub (a b : PGame) : ⟦a - b⟧ = (⟦a⟧ : Game) - ⟦b⟧ := rfl

@[target, simp]
theorem quot_natCast : ∀ n : ℕ, ⟦(n : PGame)⟧ = (n : Game) := by sorry

@[target]
theorem quot_eq_of_mk'_quot_eq {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves)
    (R : x.RightMoves ≃ y.RightMoves) (hl : ∀ i, (⟦x.moveLeft i⟧ : Game) = ⟦y.moveLeft (L i)⟧)
    (hr : ∀ j, (⟦x.moveRight j⟧ : Game) = ⟦y.moveRight (R j)⟧) : (⟦x⟧ : Game) = ⟦y⟧ := by sorry

/-! Multiplicative operations can be defined at the level of pre-games,
but to prove their properties we need to use the abelian group structure of games.
Hence we define them here. -/


/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
`{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, xR*y + x*yL - xR*yL}`. -/
instance : Mul PGame.{u} :=
  ⟨fun x y => by
    induction x generalizing y with | mk xl xr _ _ IHxl IHxr => _
    induction y with | mk yl yr yL yR IHyl IHyr => _
    have y := mk yl yr yL yR
    refine ⟨(xl × yl) ⊕ (xr × yr), (xl × yr) ⊕ (xr × yl), ?_, ?_⟩ <;> rintro (⟨i, j⟩ | ⟨i, j⟩)
    · exact IHxl i y + IHyl j - IHxl i (yL j)
    · exact IHxr i y + IHyr j - IHxr i (yR j)
    · exact IHxl i y + IHyr j - IHxl i (yR j)
    · exact IHxr i y + IHyl j - IHxr i (yL j)⟩

@[target]
theorem leftMoves_mul :
    ∀ x y : PGame.{u},
      (x * y).LeftMoves = (x.LeftMoves × y.LeftMoves ⊕ x.RightMoves × y.RightMoves) := by sorry

theorem rightMoves_mul :
    ∀ x y : PGame.{u},
      (x * y).RightMoves = (x.LeftMoves × y.RightMoves ⊕ x.RightMoves × y.LeftMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl

/-- Turns two left or right moves for `x` and `y` into a left move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesMul {x y : PGame} :
    (x.LeftMoves × y.LeftMoves) ⊕ (x.RightMoves × y.RightMoves) ≃ (x * y).LeftMoves :=
  Equiv.cast (leftMoves_mul x y).symm

/-- Turns a left and a right move for `x` and `y` into a right move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesMul {x y : PGame} :
    (x.LeftMoves × y.RightMoves) ⊕ (x.RightMoves × y.LeftMoves) ≃ (x * y).RightMoves :=
  Equiv.cast (rightMoves_mul x y).symm

@[target, simp]
theorem mk_mul_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveLeft (Sum.inl (i, j)) =
      xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j := by sorry

@[simp]
theorem mul_moveLeft_inl {x y : PGame} {i j} :
    (x * y).moveLeft (toLeftMovesMul (Sum.inl (i, j))) =
      x.moveLeft i * y + x * y.moveLeft j - x.moveLeft i * y.moveLeft j := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_mul_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveLeft (Sum.inr (i, j)) =
      xR i * mk yl yr yL yR + mk xl xr xL xR * yR j - xR i * yR j :=
  rfl

@[target, simp]
theorem mul_moveLeft_inr {x y : PGame} {i j} :
    (x * y).moveLeft (toLeftMovesMul (Sum.inr (i, j))) =
      x.moveRight i * y + x * y.moveRight j - x.moveRight i * y.moveRight j := by sorry

@[target, simp]
theorem mk_mul_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveRight (Sum.inl (i, j)) =
      xL i * mk yl yr yL yR + mk xl xr xL xR * yR j - xL i * yR j := by sorry

@[target, simp]
theorem mul_moveRight_inl {x y : PGame} {i j} :
    (x * y).moveRight (toRightMovesMul (Sum.inl (i, j))) =
      x.moveLeft i * y + x * y.moveRight j - x.moveLeft i * y.moveRight j := by sorry

@[target, simp]
theorem mk_mul_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveRight (Sum.inr (i, j)) =
      xR i * mk yl yr yL yR + mk xl xr xL xR * yL j - xR i * yL j := by sorry

@[target, simp]
theorem mul_moveRight_inr {x y : PGame} {i j} :
    (x * y).moveRight (toRightMovesMul (Sum.inr (i, j))) =
      x.moveRight i * y + x * y.moveLeft j - x.moveRight i * y.moveLeft j := by sorry

@[target, simp]
theorem neg_mk_mul_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveLeft (Sum.inl (i, j)) =
      -(xL i * mk yl yr yL yR + mk xl xr xL xR * yR j - xL i * yR j) := by sorry

@[target, simp]
theorem neg_mk_mul_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveLeft (Sum.inr (i, j)) =
      -(xR i * mk yl yr yL yR + mk xl xr xL xR * yL j - xR i * yL j) := by sorry

@[target, simp]
theorem neg_mk_mul_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveRight (Sum.inl (i, j)) =
      -(xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j) := by sorry

@[target, simp]
theorem neg_mk_mul_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(mk xl xr xL xR * mk yl yr yL yR)).moveRight (Sum.inr (i, j)) =
      -(xR i * mk yl yr yL yR + mk xl xr xL xR * yR j - xR i * yR j) := by sorry

@[target]
theorem leftMoves_mul_cases {x y : PGame} (k) {P : (x * y).LeftMoves → Prop}
    (hl : ∀ ix iy, P <| toLeftMovesMul (Sum.inl ⟨ix, iy⟩))
    (hr : ∀ jx jy, P <| toLeftMovesMul (Sum.inr ⟨jx, jy⟩)) : P k := by sorry

@[target]
theorem rightMoves_mul_cases {x y : PGame} (k) {P : (x * y).RightMoves → Prop}
    (hl : ∀ ix jy, P <| toRightMovesMul (Sum.inl ⟨ix, jy⟩))
    (hr : ∀ jx iy, P <| toRightMovesMul (Sum.inr ⟨jx, iy⟩)) : P k := by sorry

/-- `x * y` and `y * x` have the same moves. -/
protected lemma mul_comm (x y : PGame) : x * y ≡ y * x :=
  match x, y with
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine Identical.of_equiv ((Equiv.prodComm _ _).sumCongr (Equiv.prodComm _ _))
      ((Equiv.sumComm _ _).trans ((Equiv.prodComm _ _).sumCongr (Equiv.prodComm _ _))) ?_ ?_ <;>
    · rintro (⟨_, _⟩ | ⟨_, _⟩) <;>
      exact ((((PGame.mul_comm _ (mk _ _ _ _)).add (PGame.mul_comm (mk _ _ _ _) _)).trans
        (PGame.add_comm _ _)).sub (PGame.mul_comm _ _))
  termination_by (x, y)

/-- `x * y` and `y * x` have the same moves. -/
def mulCommRelabelling (x y : PGame.{u}) : x * y ≡r y * x := by
  sorry

@[target]
theorem quot_mul_comm (x y : PGame.{u}) : (⟦x * y⟧ : Game) = ⟦y * x⟧ := by sorry

/-- `x * y` is equivalent to `y * x`. -/
@[target]
theorem mul_comm_equiv (x y : PGame) : x * y ≈ y * x := by sorry

instance isEmpty_leftMoves_mul (x y : PGame.{u})
    [IsEmpty (x.LeftMoves × y.LeftMoves ⊕ x.RightMoves × y.RightMoves)] :
    IsEmpty (x * y).LeftMoves := by
  cases x
  cases y
  assumption

instance isEmpty_rightMoves_mul (x y : PGame.{u})
    [IsEmpty (x.LeftMoves × y.RightMoves ⊕ x.RightMoves × y.LeftMoves)] :
    IsEmpty (x * y).RightMoves := by
  cases x
  cases y
  assumption

/-- `x * 0` has exactly the same moves as `0`. -/
protected lemma mul_zero (x : PGame) : x * 0 ≡ 0 := identical_zero _

/-- `x * 0` has exactly the same moves as `0`. -/
def mulZeroRelabelling (x : PGame) : x * 0 ≡r 0 :=
  Relabelling.isEmpty _

/-- `x * 0` is equivalent to `0`. -/
@[target]
theorem mul_zero_equiv (x : PGame) : x * 0 ≈ 0 := by sorry

@[target, simp]
theorem quot_mul_zero (x : PGame) : (⟦x * 0⟧ : Game) = 0 := by sorry

/-- `0 * x` has exactly the same moves as `0`. -/
protected lemma zero_mul (x : PGame) : 0 * x ≡ 0 := identical_zero _

/-- `0 * x` has exactly the same moves as `0`. -/
def zeroMulRelabelling (x : PGame) : 0 * x ≡r 0 :=
  Relabelling.isEmpty _

/-- `0 * x` is equivalent to `0`. -/
@[target]
theorem zero_mul_equiv (x : PGame) : 0 * x ≈ 0 := by sorry

@[target, simp]
theorem quot_zero_mul (x : PGame) : (⟦0 * x⟧ : Game) = 0 := by sorry

/-- `-x * y` and `-(x * y)` have the same moves. -/
def negMulRelabelling (x y : PGame.{u}) : -x * y ≡r -(x * y) :=
  match x, y with
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
      refine ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, ?_, ?_⟩ <;>
      rintro (⟨i, j⟩ | ⟨i, j⟩) <;>
      · dsimp
        apply ((negAddRelabelling _ _).trans _).symm
        apply ((negAddRelabelling _ _).trans (Relabelling.addCongr _ _)).subCongr
        -- Porting note: we used to just do `<;> exact (negMulRelabelling _ _).symm` from here.
        · exact (negMulRelabelling _ _).symm
        · exact (negMulRelabelling _ _).symm
        -- Porting note: not sure what has gone wrong here.
        -- The goal is hideous here, and the `exact` doesn't work,
        -- but if we just `change` it to look like the mathlib3 goal then we're fine!?
        change -(mk xl xr xL xR * _) ≡r _
        exact (negMulRelabelling _ _).symm
  termination_by (x, y)

/-- `x * -y` and `-(x * y)` have the same moves. -/
@[target, simp]
lemma mul_neg (x y : PGame) : x * -y = -(x * y) := by sorry

/-- `-x * y` and `-(x * y)` have the same moves. -/
@[target]
lemma neg_mul (x y : PGame) : -x * y ≡ -(x * y) := by sorry

@[target, simp]
theorem quot_neg_mul (x y : PGame) : (⟦-x * y⟧ : Game) = -⟦x * y⟧ := by sorry

/-- `x * -y` and `-(x * y)` have the same moves. -/
def mulNegRelabelling (x y : PGame) : x * -y ≡r -(x * y) :=
  (mulCommRelabelling x _).trans <| (negMulRelabelling _ x).trans (mulCommRelabelling y x).negCongr

@[target]
theorem quot_mul_neg (x y : PGame) : ⟦x * -y⟧ = (-⟦x * y⟧ : Game) := by sorry

@[target]
theorem quot_neg_mul_neg (x y : PGame) : ⟦-x * -y⟧ = (⟦x * y⟧ : Game) := by sorry

@[target, simp]
theorem quot_left_distrib (x y z : PGame) : (⟦x * (y + z)⟧ : Game) = ⟦x * y⟧ + ⟦x * z⟧ := by sorry

/-- `x * (y + z)` is equivalent to `x * y + x * z`. -/
@[target]
theorem left_distrib_equiv (x y z : PGame) : x * (y + z) ≈ x * y + x * z := by sorry

@[target, simp]
theorem quot_left_distrib_sub (x y z : PGame) : (⟦x * (y - z)⟧ : Game) = ⟦x * y⟧ - ⟦x * z⟧ := by sorry

@[target, simp]
theorem quot_right_distrib (x y z : PGame) : (⟦(x + y) * z⟧ : Game) = ⟦x * z⟧ + ⟦y * z⟧ := by sorry

/-- `(x + y) * z` is equivalent to `x * z + y * z`. -/
theorem right_distrib_equiv (x y z : PGame) : (x + y) * z ≈ x * z + y * z :=
  Quotient.exact <| quot_right_distrib _ _ _

@[target, simp]
theorem quot_right_distrib_sub (x y z : PGame) : (⟦(y - z) * x⟧ : Game) = ⟦y * x⟧ - ⟦z * x⟧ := by sorry

/-- `x * 1` has the same moves as `x`. -/
def mulOneRelabelling : ∀ x : PGame.{u}, x * 1 ≡r x := by
  intro x
  sorry

/-- `1 * x` has the same moves as `x`. -/
protected lemma one_mul : ∀ (x : PGame), 1 * x ≡ x := by
  intro x
  sorry

/-- `x * 1` has the same moves as `x`. -/
protected lemma mul_one (x : PGame) : x * 1 ≡ x := by sorry

@[simp]
theorem quot_mul_one (x : PGame) : (⟦x * 1⟧ : Game) = ⟦x⟧ := by sorry

/-- `x * 1` is equivalent to `x`. -/
@[target]
theorem mul_one_equiv (x : PGame) : x * 1 ≈ x := by sorry

/-- `1 * x` has the same moves as `x`. -/
def oneMulRelabelling (x : PGame) : 1 * x ≡r x :=
  (mulCommRelabelling 1 x).trans <| mulOneRelabelling x

@[target, simp]
theorem quot_one_mul (x : PGame) : (⟦1 * x⟧ : Game) = ⟦x⟧ := by sorry

/-- `1 * x` is equivalent to `x`. -/
@[target]
theorem one_mul_equiv (x : PGame) : 1 * x ≈ x := by sorry

@[target]
theorem quot_mul_assoc (x y z : PGame) : (⟦x * y * z⟧ : Game) = ⟦x * (y * z)⟧ := by sorry

/-- `x * y * z` is equivalent to `x * (y * z)`. -/
theorem mul_assoc_equiv (x y z : PGame) : x * y * z ≈ x * (y * z) :=
  Quotient.exact <| quot_mul_assoc _ _ _

/-- The left options of `x * y` of the first kind, i.e. of the form `xL * y + x * yL - xL * yL`. -/
def mulOption (x y : PGame) (i : LeftMoves x) (j : LeftMoves y) : PGame :=
  x.moveLeft i * y + x * y.moveLeft j - x.moveLeft i * y.moveLeft j

/-- Any left option of `x * y` of the first kind is also a left option of `x * -(-y)` of
  the first kind. -/
@[target]
lemma mulOption_neg_neg {x} (y) {i j} :
    mulOption x y i j = mulOption x (-(-y)) i (toLeftMovesNeg <| toRightMovesNeg j) := by sorry

/-- The left options of `x * y` agree with that of `y * x` up to equivalence. -/
@[target]
lemma mulOption_symm (x y) {i j} : ⟦mulOption x y i j⟧ = (⟦mulOption y x j i⟧ : Game) := by sorry

/-- The left options of `x * y` of the second kind are the left options of `(-x) * (-y)` of the
  first kind, up to equivalence. -/
lemma leftMoves_mul_iff {x y : PGame} (P : Game → Prop) :
    (∀ k, P ⟦(x * y).moveLeft k⟧) ↔
    (∀ i j, P ⟦mulOption x y i j⟧) ∧ (∀ i j, P ⟦mulOption (-x) (-y) i j⟧) := by sorry

/-- The right options of `x * y` are the left options of `x * (-y)` and of `(-x) * y` of the first
  kind, up to equivalence. -/
@[target]
lemma rightMoves_mul_iff {x y : PGame} (P : Game → Prop) :
    (∀ k, P ⟦(x * y).moveRight k⟧) ↔
    (∀ i j, P (-⟦mulOption x (-y) i j⟧)) ∧ (∀ i j, P (-⟦mulOption (-x) y i j⟧)) := by sorry

/-- Because the two halves of the definition of `inv` produce more elements
on each side, we have to define the two families inductively.
This is the indexing set for the function, and `invVal` is the function part. -/
inductive InvTy (l r : Type u) : Bool → Type u
  | zero : InvTy l r false
  | left₁ : r → InvTy l r false → InvTy l r false
  | left₂ : l → InvTy l r true → InvTy l r false
  | right₁ : l → InvTy l r false → InvTy l r true
  | right₂ : r → InvTy l r true → InvTy l r true

instance (l r : Type u) [IsEmpty l] [IsEmpty r] : IsEmpty (InvTy l r true) :=
  ⟨by rintro (_ | _ | _ | a | a) <;> exact isEmptyElim a⟩

instance InvTy.instInhabited (l r : Type u) : Inhabited (InvTy l r false) :=
  ⟨InvTy.zero⟩

instance uniqueInvTy (l r : Type u) [IsEmpty l] [IsEmpty r] : Unique (InvTy l r false) :=
  { InvTy.instInhabited l r with
    uniq := by
      rintro (a | a | a)
      · rfl
      all_goals exact isEmptyElim a }

/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the function part, defined by recursion on `InvTy`. -/
def invVal {l r} (L : l → PGame) (R : r → PGame) (IHl : l → PGame) (IHr : r → PGame)
    (x : PGame) : ∀ {b}, InvTy l r b → PGame
  | _, InvTy.zero => 0
  | _, InvTy.left₁ i j => (1 + (R i - x) * invVal L R IHl IHr x j) * IHr i
  | _, InvTy.left₂ i j => (1 + (L i - x) * invVal L R IHl IHr x j) * IHl i
  | _, InvTy.right₁ i j => (1 + (L i - x) * invVal L R IHl IHr x j) * IHl i
  | _, InvTy.right₂ i j => (1 + (R i - x) * invVal L R IHl IHr x j) * IHr i

@[target, simp]
theorem invVal_isEmpty {l r : Type u} {b} (L R IHl IHr) (i : InvTy l r b) (x) [IsEmpty l]
    [IsEmpty r] : invVal L R IHl IHr x i = 0 := by sorry

/-- The inverse of a positive surreal number `x = {L | R}` is
given by `x⁻¹ = {0,
  (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
  (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
definition, the sets and elements are inductively generated. -/
def inv' : PGame → PGame
  | ⟨l, r, L, R⟩ =>
    let l' := { i // 0 < L i }
    let L' : l' → PGame := fun i => L i.1
    let IHl' : l' → PGame := fun i => inv' (L i.1)
    let IHr i := inv' (R i)
    let x := mk l r L R
    ⟨InvTy l' r false, InvTy l' r true, invVal L' R IHl' IHr x, invVal L' R IHl' IHr x⟩

@[target]
theorem zero_lf_inv' : ∀ x : PGame, 0 ⧏ inv' x := by sorry

/-- `inv' 0` has exactly the same moves as `1`. -/
def inv'Zero : inv' 0 ≡r 1 := by sorry

@[target]
theorem inv'_zero_equiv : inv' 0 ≈ 1 := by sorry

/-- `inv' 1` has exactly the same moves as `1`. -/
@[target]
lemma inv'_one : inv' 1 ≡ 1 := by sorry

/-- `inv' 1` has exactly the same moves as `1`. -/
def inv'One : inv' 1 ≡r (1 : PGame.{u}) := by sorry

@[target]
theorem inv'_one_equiv : inv' 1 ≈ 1 := by sorry

/-- The inverse of a pre-game in terms of the inverse on positive pre-games. -/
noncomputable instance : Inv PGame :=
  ⟨by classical exact fun x => if x ≈ 0 then 0 else if 0 < x then inv' x else -inv' (-x)⟩

noncomputable instance : Div PGame :=
  ⟨fun x y => x * y⁻¹⟩

@[target]
theorem inv_eq_of_equiv_zero {x : PGame} (h : x ≈ 0) : x⁻¹ = 0 := by sorry

@[target, simp]
theorem inv_zero : (0 : PGame)⁻¹ = 0 := by sorry

@[target]
theorem inv_eq_of_pos {x : PGame} (h : 0 < x) : x⁻¹ = inv' x := by sorry

theorem inv_eq_of_lf_zero {x : PGame} (h : x ⧏ 0) : x⁻¹ = -inv' (-x) := by
  classical exact (if_neg h.not_equiv).trans (if_neg h.not_gt)

/-- `1⁻¹` has exactly the same moves as `1`. -/
lemma inv_one : 1⁻¹ ≡ 1 := by sorry

/-- `1⁻¹` has exactly the same moves as `1`. -/
def invOne : 1⁻¹ ≡r 1 := by sorry

@[target]
theorem inv_one_equiv : (1⁻¹ : PGame) ≈ 1 := by sorry

end PGame

end SetTheory
