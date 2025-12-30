import VerifiedAgora.tagger
/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.SetTheory.Game.Ordinal
import Mathlib.SetTheory.Ordinal.NaturalOps

/-!
# Birthdays of games

There are two related but distinct notions of a birthday within combinatorial game theory. One is
the birthday of a pre-game, which represents the "step" at which it is constructed. We define it
recursively as the least ordinal larger than the birthdays of its left and right options. On the
other hand, the birthday of a game is the smallest birthday among all pre-games that quotient to it.

The birthday of a pre-game can be understood as representing the depth of its game tree. On the
other hand, the birthday of a game more closely matches Conway's original description. The lemma
`SetTheory.Game.birthday_eq_pGameBirthday` links both definitions together.

# Main declarations

- `SetTheory.PGame.birthday`: The birthday of a pre-game.
- `SetTheory.Game.birthday`: The birthday of a game.

# Todo

- Characterize the birthdays of other basic arithmetical operations.
-/

universe u

open Ordinal

namespace SetTheory

open scoped NaturalOps PGame

namespace PGame

/-- The birthday of a pre-game is inductively defined as the least strict upper bound of the
birthdays of its left and right games. It may be thought as the "step" in which a certain game is
constructed. -/
noncomputable def birthday : PGame.{u} → Ordinal.{u}
  | ⟨_, _, xL, xR⟩ =>
    max (lsub.{u, u} fun i => birthday (xL i)) (lsub.{u, u} fun i => birthday (xR i))

@[target]
theorem birthday_def (x : PGame) :
    birthday x =
      max (lsub.{u, u} fun i => birthday (x.moveLeft i))
        (lsub.{u, u} fun i => birthday (x.moveRight i)) := by sorry

@[target]
theorem birthday_moveLeft_lt {x : PGame} (i : x.LeftMoves) :
    (x.moveLeft i).birthday < x.birthday := by sorry

@[target]
theorem birthday_moveRight_lt {x : PGame} (i : x.RightMoves) :
    (x.moveRight i).birthday < x.birthday := by sorry

@[target]
theorem lt_birthday_iff {x : PGame} {o : Ordinal} :
    o < x.birthday ↔
      (∃ i : x.LeftMoves, o ≤ (x.moveLeft i).birthday) ∨
        ∃ i : x.RightMoves, o ≤ (x.moveRight i).birthday := by sorry

@[target]
theorem Relabelling.birthday_congr : ∀ {x y : PGame.{u}}, x ≡r y → birthday x = birthday y := by sorry

@[target, simp]
theorem birthday_eq_zero {x : PGame} :
    birthday x = 0 ↔ IsEmpty x.LeftMoves ∧ IsEmpty x.RightMoves := by sorry

@[simp]
theorem birthday_zero : birthday 0 = 0 := by simp [inferInstanceAs (IsEmpty PEmpty)]

@[target, simp]
theorem birthday_one : birthday 1 = 1 := by sorry

@[target, simp]
theorem birthday_star : birthday star = 1 := by sorry

@[target, simp]
theorem birthday_neg : ∀ x : PGame, (-x).birthday = x.birthday := by sorry

@[target, simp]
theorem birthday_ordinalToPGame (o : Ordinal) : o.toPGame.birthday = o := by sorry

@[target]
theorem le_birthday : ∀ x : PGame, x ≤ x.birthday.toPGame := by sorry

variable (x : PGame.{u})

@[target]
theorem neg_birthday_le : -x.birthday.toPGame ≤ x := by sorry

@[target, simp]
theorem birthday_add : ∀ x y : PGame.{u}, (x + y).birthday = x.birthday ♯ y.birthday := by sorry

@[target, simp]
theorem birthday_sub (x y : PGame) : (x - y).birthday = x.birthday ♯ y.birthday := by sorry

@[target, simp]
theorem birthday_natCast : ∀ n : ℕ, birthday n = n := by sorry

end PGame

namespace Game

/-- The birthday of a game is defined as the least birthday among all pre-games that define it. -/
noncomputable def birthday (x : Game.{u}) : Ordinal.{u} :=
  sInf (PGame.birthday '' (Quotient.mk' ⁻¹' {x}))

@[target]
theorem birthday_eq_pGameBirthday (x : Game) :
    ∃ y : PGame.{u}, ⟦y⟧ = x ∧ y.birthday = birthday x := by sorry

theorem birthday_quot_le_pGameBirthday  (x : PGame) : birthday ⟦x⟧ ≤ x.birthday :=
  csInf_le' ⟨x, rfl, rfl⟩

@[target, simp]
theorem birthday_zero : birthday 0 = 0 := by sorry

@[simp]
theorem birthday_eq_zero {x : Game} : birthday x = 0 ↔ x = 0 := by
  constructor
  · intro h
    let ⟨y, hy₁, hy₂⟩ := birthday_eq_pGameBirthday x
    rw [← hy₁]
    rw [h, PGame.birthday_eq_zero] at hy₂
    exact PGame.game_eq (@PGame.Equiv.isEmpty _ hy₂.1 hy₂.2)
  · rintro rfl
    exact birthday_zero

@[simp]
theorem birthday_ordinalToGame (o : Ordinal) : birthday o.toGame = o := by
  apply le_antisymm
  · conv_rhs => rw [← PGame.birthday_ordinalToPGame o]
    apply birthday_quot_le_pGameBirthday
  · let ⟨x, hx₁, hx₂⟩ := birthday_eq_pGameBirthday o.toGame
    rw [← hx₂, ← toPGame_le_iff]
    rw [← mk_toPGame, ← PGame.equiv_iff_game_eq] at hx₁
    exact hx₁.2.trans (PGame.le_birthday x)

@[simp, norm_cast]
theorem birthday_natCast (n : ℕ) : birthday n = n := by
  rw [← toGame_natCast]
  exact birthday_ordinalToGame _

@[simp]
theorem birthday_ofNat (n : ℕ) [n.AtLeastTwo] :
    birthday ofNat(n) = OfNat.ofNat n :=
  birthday_natCast n

@[target, simp]
theorem birthday_one : birthday 1 = 1 := by sorry

@[target, simp]
theorem birthday_star : birthday ⟦PGame.star⟧ = 1 := by sorry

private theorem birthday_neg' (x : Game) : (-x).birthday ≤ x.birthday := by
  let ⟨y, hy₁, hy₂⟩ := birthday_eq_pGameBirthday x
  rw [← hy₂, ← PGame.birthday_neg y]
  conv_lhs => rw [← hy₁]
  apply birthday_quot_le_pGameBirthday

@[simp]
theorem birthday_neg (x : Game) : (-x).birthday = x.birthday := by
  apply le_antisymm (birthday_neg' x)
  conv_lhs => rw [← neg_neg x]
  exact birthday_neg' _

theorem le_birthday (x : Game) : x ≤ x.birthday.toGame := by
  let ⟨y, hy₁, hy₂⟩ := birthday_eq_pGameBirthday x
  rw [← hy₁]
  apply (y.le_birthday).trans
  rw [toPGame_le_iff, hy₁, hy₂]

@[target]
theorem neg_birthday_le (x : Game) : -x.birthday.toGame ≤ x := by sorry

@[target]
theorem birthday_add_le (x y : Game) : (x + y).birthday ≤ x.birthday ♯ y.birthday := by sorry

theorem birthday_sub_le (x y : Game) : (x - y).birthday ≤ x.birthday ♯ y.birthday := by
  apply (birthday_add_le x _).trans_eq
  rw [birthday_neg]

/- The bound `(x * y).birthday ≤ x.birthday ⨳ y.birthday` is currently an open problem. See
  https://mathoverflow.net/a/476829/147705. -/

/-- Games with bounded birthday are a small set. -/
@[target]
theorem small_setOf_birthday_lt (o : Ordinal) : Small.{u} {x : Game.{u} // birthday x < o} := by sorry

end Game

end SetTheory
