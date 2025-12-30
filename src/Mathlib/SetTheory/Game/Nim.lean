import VerifiedAgora.tagger
/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import Mathlib.SetTheory.Game.Birthday
import Mathlib.SetTheory.Game.Impartial
import Mathlib.SetTheory.Nimber.Basic

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `o`. In the game of `nim o₁` both players
may move to `nim o₂` for any `o₂ < o₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (grundyValue G)`.
Finally, we prove that the grundy value of a sum `G + H` corresponds to the nimber sum of the
individual grundy values.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim o` to be `Set.Iio o`.
However, this definition does not work for us because it would make the type of nim
`Ordinal.{u} → SetTheory.PGame.{u + 1}`, which would make it impossible for us to state the
Sprague-Grundy theorem, since that requires the type of `nim` to be
`Ordinal.{u} → SetTheory.PGame.{u}`. For this reason, we instead use `o.toType` for the possible
moves. We expose `toLeftMovesNim` and `toRightMovesNim` to conveniently convert an ordinal less than
`o` into a left or right move of `nim o`, and vice versa.
-/


noncomputable section

universe u

namespace SetTheory

open scoped PGame
open Ordinal Nimber

namespace PGame

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
  take a positive number of stones from it on their turn. -/
noncomputable def nim (o : Ordinal.{u}) : PGame.{u} :=
  ⟨o.toType, o.toType,
    fun x => nim ((enumIsoToType o).symm x).val,
    fun x => nim ((enumIsoToType o).symm x).val⟩
termination_by o
decreasing_by all_goals exact ((enumIsoToType o).symm x).prop

@[target, deprecated "you can use `rw [nim]` directly" (since := "2025-01-23")]
theorem nim_def (o : Ordinal) : nim o =
    ⟨o.toType, o.toType,
      fun x => nim ((enumIsoToType o).symm x).val,
      fun x => nim ((enumIsoToType o).symm x).val⟩ := by sorry

@[target]
theorem leftMoves_nim (o : Ordinal) : (nim o).LeftMoves = o.toType := by sorry

@[target]
theorem rightMoves_nim (o : Ordinal) : (nim o).RightMoves = o.toType := by sorry

@[target]
theorem moveLeft_nim_hEq (o : Ordinal) :
    HEq (nim o).moveLeft fun i : o.toType => nim ((enumIsoToType o).symm i) := by sorry

@[target]
theorem moveRight_nim_hEq (o : Ordinal) :
    HEq (nim o).moveRight fun i : o.toType => nim ((enumIsoToType o).symm i) := by sorry

/-- Turns an ordinal less than `o` into a left move for `nim o` and vice versa. -/
noncomputable def toLeftMovesNim {o : Ordinal} : Set.Iio o ≃ (nim o).LeftMoves :=
  (enumIsoToType o).toEquiv.trans (Equiv.cast (leftMoves_nim o).symm)

/-- Turns an ordinal less than `o` into a right move for `nim o` and vice versa. -/
noncomputable def toRightMovesNim {o : Ordinal} : Set.Iio o ≃ (nim o).RightMoves :=
  (enumIsoToType o).toEquiv.trans (Equiv.cast (rightMoves_nim o).symm)

@[target, simp]
theorem toLeftMovesNim_symm_lt {o : Ordinal} (i : (nim o).LeftMoves) :
    toLeftMovesNim.symm i < o := by sorry

@[target, simp]
theorem toRightMovesNim_symm_lt {o : Ordinal} (i : (nim o).RightMoves) :
    toRightMovesNim.symm i < o := by sorry

@[target, simp]
theorem moveLeft_nim {o : Ordinal} (i) : (nim o).moveLeft i = nim (toLeftMovesNim.symm i).val := by sorry

@[deprecated moveLeft_nim (since := "2024-10-30")]
alias moveLeft_nim' := moveLeft_nim

theorem moveLeft_toLeftMovesNim {o : Ordinal} (i) :
    (nim o).moveLeft (toLeftMovesNim i) = nim i := by
  simp

@[simp]
theorem moveRight_nim {o : Ordinal} (i) : (nim o).moveRight i = nim (toRightMovesNim.symm i).val :=
  (congr_heq (moveRight_nim_hEq o).symm (cast_heq _ i)).symm

@[deprecated moveRight_nim (since := "2024-10-30")]
alias moveRight_nim' := moveRight_nim

@[target]
theorem moveRight_toRightMovesNim {o : Ordinal} (i) :
    (nim o).moveRight (toRightMovesNim i) = nim i := by sorry

/-- A recursion principle for left moves of a nim game. -/
@[elab_as_elim]
def leftMovesNimRecOn {o : Ordinal} {P : (nim o).LeftMoves → Sort*} (i : (nim o).LeftMoves)
    (H : ∀ a (H : a < o), P <| toLeftMovesNim ⟨a, H⟩) : P i := by
  rw [← toLeftMovesNim.apply_symm_apply i]; apply H

/-- A recursion principle for right moves of a nim game. -/
@[elab_as_elim]
def rightMovesNimRecOn {o : Ordinal} {P : (nim o).RightMoves → Sort*} (i : (nim o).RightMoves)
    (H : ∀ a (H : a < o), P <| toRightMovesNim ⟨a, H⟩) : P i := by
  rw [← toRightMovesNim.apply_symm_apply i]; apply H

instance isEmpty_nim_zero_leftMoves : IsEmpty (nim 0).LeftMoves := by
  rw [nim]
  exact isEmpty_toType_zero

instance isEmpty_nim_zero_rightMoves : IsEmpty (nim 0).RightMoves := by
  rw [nim]
  exact isEmpty_toType_zero

/-- `nim 0` has exactly the same moves as `0`. -/
def nimZeroRelabelling : nim 0 ≡r 0 :=
  Relabelling.isEmpty _

@[target]
theorem nim_zero_equiv : nim 0 ≈ 0 := by sorry

noncomputable instance uniqueNimOneLeftMoves : Unique (nim 1).LeftMoves :=
  (Equiv.cast <| leftMoves_nim 1).unique

noncomputable instance uniqueNimOneRightMoves : Unique (nim 1).RightMoves :=
  (Equiv.cast <| rightMoves_nim 1).unique

@[target, simp]
theorem default_nim_one_leftMoves_eq :
    (default : (nim 1).LeftMoves) = @toLeftMovesNim 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by sorry

@[target, simp]
theorem default_nim_one_rightMoves_eq :
    (default : (nim 1).RightMoves) = @toRightMovesNim 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by sorry

@[simp]
theorem toLeftMovesNim_one_symm (i) :
    (@toLeftMovesNim 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by
  simp [eq_iff_true_of_subsingleton]

@[target, simp]
theorem toRightMovesNim_one_symm (i) :
    (@toRightMovesNim 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by sorry

@[target]
theorem nim_one_moveLeft (x) : (nim 1).moveLeft x = nim 0 := by sorry

@[target]
theorem nim_one_moveRight (x) : (nim 1).moveRight x = nim 0 := by sorry

/-- `nim 1` has exactly the same moves as `star`. -/
def nimOneRelabelling : nim 1 ≡r star := by sorry

@[target]
theorem nim_one_equiv : nim 1 ≈ star := by sorry

@[simp]
theorem nim_birthday (o : Ordinal) : (nim o).birthday = o := by sorry

@[target, simp]
theorem neg_nim (o : Ordinal) : -nim o = nim o := by sorry

instance impartial_nim (o : Ordinal) : Impartial (nim o) := by
  induction' o using Ordinal.induction with o IH
  rw [impartial_def, neg_nim]
  refine ⟨equiv_rfl, fun i => ?_, fun i => ?_⟩ <;> simpa using IH _ (typein_lt_self _)

theorem nim_fuzzy_zero_of_ne_zero {o : Ordinal} (ho : o ≠ 0) : nim o ‖ 0 := by
  rw [Impartial.fuzzy_zero_iff_lf, lf_zero_le]
  use toRightMovesNim ⟨0, Ordinal.pos_iff_ne_zero.2 ho⟩
  simp

@[target, simp]
theorem nim_add_equiv_zero_iff (o₁ o₂ : Ordinal) : (nim o₁ + nim o₂ ≈ 0) ↔ o₁ = o₂ := by sorry

@[target, simp]
theorem nim_add_fuzzy_zero_iff {o₁ o₂ : Ordinal} : nim o₁ + nim o₂ ‖ 0 ↔ o₁ ≠ o₂ := by sorry

@[target, simp]
theorem nim_equiv_iff_eq {o₁ o₂ : Ordinal} : (nim o₁ ≈ nim o₂) ↔ o₁ = o₂ := by sorry

/-- The Grundy value of an impartial game is recursively defined as the minimum excluded value
(the infimum of the complement) of the Grundy values of either its left or right options.

This is the ordinal which corresponds to the game of nim that the game is equivalent to.

This function takes a value in `Nimber`. This is a type synonym for the ordinals which has the same
ordering, but addition in `Nimber` is such that it corresponds to the grundy value of the addition
of games. See that file for more information on nimbers and their arithmetic. -/
noncomputable def grundyValue (G : PGame.{u}) : Nimber.{u} :=
  sInf (Set.range fun i => grundyValue (G.moveLeft i))ᶜ
termination_by G

@[target]
theorem grundyValue_eq_sInf_moveLeft (G : PGame) :
    grundyValue G = sInf (Set.range (grundyValue ∘ G.moveLeft))ᶜ := by sorry

set_option linter.deprecated false in
@[target, deprecated grundyValue_eq_sInf_moveLeft (since := "2024-09-16")]
theorem grundyValue_eq_mex_left (G : PGame) :
    grundyValue G = Ordinal.mex fun i => grundyValue (G.moveLeft i) := by sorry

theorem grundyValue_ne_moveLeft {G : PGame} (i : G.LeftMoves) :
    grundyValue (G.moveLeft i) ≠ grundyValue G := by
  conv_rhs => rw [grundyValue_eq_sInf_moveLeft]
  have := csInf_mem (nonempty_of_not_bddAbove <|
    Nimber.not_bddAbove_compl_of_small (Set.range fun i => grundyValue (G.moveLeft i)))
  rw [Set.mem_compl_iff, Set.mem_range, not_exists] at this
  exact this _

@[target]
theorem le_grundyValue_of_Iio_subset_moveLeft {G : PGame} {o : Nimber}
    (h : Set.Iio o ⊆ Set.range (grundyValue ∘ G.moveLeft)) : o ≤ grundyValue G := by sorry

@[target]
theorem exists_grundyValue_moveLeft_of_lt {G : PGame} {o : Nimber} (h : o < grundyValue G) :
    ∃ i, grundyValue (G.moveLeft i) = o := by sorry

@[target]
theorem grundyValue_le_of_forall_moveLeft {G : PGame} {o : Nimber}
    (h : ∀ i, grundyValue (G.moveLeft i) ≠ o) : G.grundyValue ≤ o := by sorry

/-- The **Sprague-Grundy theorem** states that every impartial game is equivalent to a game of nim,
namely the game of nim corresponding to the game's Grundy value. -/
@[target]
theorem equiv_nim_grundyValue (G : PGame.{u}) [G.Impartial] :
    G ≈ nim (toOrdinal (grundyValue G)) := by sorry

@[target]
theorem grundyValue_eq_iff_equiv_nim {G : PGame} [G.Impartial] {o : Nimber} :
    grundyValue G = o ↔ G ≈ nim (toOrdinal o) := by sorry

@[simp]
theorem nim_grundyValue (o : Ordinal.{u}) : grundyValue (nim o) = ∗o :=
  grundyValue_eq_iff_equiv_nim.2 PGame.equiv_rfl

@[target]
theorem grundyValue_eq_iff_equiv (G H : PGame) [G.Impartial] [H.Impartial] :
    grundyValue G = grundyValue H ↔ (G ≈ H) := by sorry

@[target, simp]
theorem grundyValue_zero : grundyValue 0 = 0 := by sorry

@[target]
theorem grundyValue_iff_equiv_zero (G : PGame) [G.Impartial] : grundyValue G = 0 ↔ G ≈ 0 := by sorry

@[simp]
theorem grundyValue_star : grundyValue star = 1 :=
  grundyValue_eq_iff_equiv_nim.2 (Equiv.symm nim_one_equiv)

@[simp]
theorem grundyValue_neg (G : PGame) [G.Impartial] : grundyValue (-G) = grundyValue G := by
  rw [grundyValue_eq_iff_equiv_nim, neg_equiv_iff, neg_nim, ← grundyValue_eq_iff_equiv_nim]

@[target]
theorem grundyValue_eq_sInf_moveRight (G : PGame) [G.Impartial] :
    grundyValue G = sInf (Set.range (grundyValue ∘ G.moveRight))ᶜ := by sorry

set_option linter.deprecated false in
@[target, deprecated grundyValue_eq_sInf_moveRight (since := "2024-09-16")]
theorem grundyValue_eq_mex_right (G : PGame) [G.Impartial] :
    grundyValue G = Ordinal.mex.{u, u} fun i => grundyValue (G.moveRight i) := by sorry

@[target]
theorem grundyValue_ne_moveRight {G : PGame} [G.Impartial] (i : G.RightMoves) :
    grundyValue (G.moveRight i) ≠ grundyValue G := by sorry

@[target]
theorem le_grundyValue_of_Iio_subset_moveRight {G : PGame} [G.Impartial] {o : Nimber}
    (h : Set.Iio o ⊆ Set.range (grundyValue ∘ G.moveRight)) : o ≤ grundyValue G := by sorry

@[target]
theorem exists_grundyValue_moveRight_of_lt {G : PGame} [G.Impartial] {o : Nimber}
    (h : o < grundyValue G) : ∃ i, grundyValue (G.moveRight i) = o := by sorry

@[target]
theorem grundyValue_le_of_forall_moveRight {G : PGame} [G.Impartial] {o : Nimber}
    (h : ∀ i, grundyValue (G.moveRight i) ≠ o) : G.grundyValue ≤ o := by sorry

/-- The Grundy value of the sum of two nim games equals their nimber addition. -/
@[target]
theorem grundyValue_nim_add_nim (x y : Ordinal) : grundyValue (nim x + nim y) = ∗x + ∗y := by sorry

@[target]
theorem nim_add_nim_equiv (x y : Ordinal) :
    nim x + nim y ≈ nim (toOrdinal (∗x + ∗y)) := by sorry

@[target, simp]
theorem grundyValue_add (G H : PGame) [G.Impartial] [H.Impartial] :
    grundyValue (G + H) = grundyValue G + grundyValue H := by sorry

end PGame

end SetTheory
