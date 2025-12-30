import VerifiedAgora.tagger
/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Game.Basic
import Mathlib.SetTheory.Ordinal.NaturalOps

/-!
# Ordinals as games

We define the canonical map `Ordinal → SetTheory.PGame`, where every ordinal is mapped to the
game whose left set consists of all previous ordinals.

The map to surreals is defined in `Ordinal.toSurreal`.

# Main declarations

- `Ordinal.toPGame`: The canonical map between ordinals and pre-games.
- `Ordinal.toPGameEmbedding`: The order embedding version of the previous map.
-/


universe u

open SetTheory PGame

open scoped NaturalOps PGame

namespace Ordinal

/-- Converts an ordinal into the corresponding pre-game. -/
noncomputable def toPGame (o : Ordinal.{u}) : PGame.{u} :=
  ⟨o.toType, PEmpty, fun x => ((enumIsoToType o).symm x).val.toPGame, PEmpty.elim⟩
termination_by o
decreasing_by exact ((enumIsoToType o).symm x).prop

@[target, deprecated "No deprecation message was provided." (since := "2024-09-22")]
theorem toPGame_def (o : Ordinal) : o.toPGame =
    ⟨o.toType, PEmpty, fun x => ((enumIsoToType o).symm x).val.toPGame, PEmpty.elim⟩ := by sorry

@[target, simp]
theorem toPGame_leftMoves (o : Ordinal) : o.toPGame.LeftMoves = o.toType := by sorry

@[target, simp]
theorem toPGame_rightMoves (o : Ordinal) : o.toPGame.RightMoves = PEmpty := by sorry

instance isEmpty_zero_toPGame_leftMoves : IsEmpty (toPGame 0).LeftMoves := by
  rw [toPGame_leftMoves]; infer_instance

instance isEmpty_toPGame_rightMoves (o : Ordinal) : IsEmpty o.toPGame.RightMoves := by
  rw [toPGame_rightMoves]; infer_instance

/-- Converts an ordinal less than `o` into a move for the `PGame` corresponding to `o`, and vice
versa. -/
noncomputable def toLeftMovesToPGame {o : Ordinal} : Set.Iio o ≃ o.toPGame.LeftMoves :=
  (enumIsoToType o).toEquiv.trans (Equiv.cast (toPGame_leftMoves o).symm)

@[simp]
theorem toLeftMovesToPGame_symm_lt {o : Ordinal} (i : o.toPGame.LeftMoves) :
    ↑(toLeftMovesToPGame.symm i) < o :=
  (toLeftMovesToPGame.symm i).prop

@[target, nolint unusedHavesSuffices]
theorem toPGame_moveLeft_hEq {o : Ordinal} :
    HEq o.toPGame.moveLeft fun x : o.toType => ((enumIsoToType o).symm x).val.toPGame := by sorry

@[target, simp]
theorem toPGame_moveLeft' {o : Ordinal} (i) :
    o.toPGame.moveLeft i = (toLeftMovesToPGame.symm i).val.toPGame := by sorry

@[target]
theorem toPGame_moveLeft {o : Ordinal} (i) :
    o.toPGame.moveLeft (toLeftMovesToPGame i) = i.val.toPGame := by sorry

/-- `0.toPGame` has the same moves as `0`. -/
noncomputable def zeroToPGameRelabelling : toPGame 0 ≡r 0 :=
  Relabelling.isEmpty _

@[target]
theorem toPGame_zero : toPGame 0 ≈ 0 := by sorry

noncomputable instance uniqueOneToPGameLeftMoves : Unique (toPGame 1).LeftMoves :=
  (Equiv.cast <| toPGame_leftMoves 1).unique

@[simp]
theorem one_toPGame_leftMoves_default_eq :
    (default : (toPGame 1).LeftMoves) = @toLeftMovesToPGame 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ :=
  rfl

@[simp]
theorem to_leftMoves_one_toPGame_symm (i) :
    (@toLeftMovesToPGame 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by
  simp [eq_iff_true_of_subsingleton]

@[target]
theorem one_toPGame_moveLeft (x) : (toPGame 1).moveLeft x = toPGame 0 := by sorry

/-- `1.toPGame` has the same moves as `1`. -/
noncomputable def oneToPGameRelabelling : toPGame 1 ≡r 1 :=
  ⟨Equiv.ofUnique _ _, Equiv.equivOfIsEmpty _ _, fun i => by
    simpa using zeroToPGameRelabelling, isEmptyElim⟩

@[target]
theorem toPGame_one : toPGame 1 ≈ 1 := by sorry

theorem toPGame_lf {a b : Ordinal} (h : a < b) : a.toPGame ⧏ b.toPGame := by
  convert moveLeft_lf (toLeftMovesToPGame ⟨a, h⟩); rw [toPGame_moveLeft]

theorem toPGame_le {a b : Ordinal} (h : a ≤ b) : a.toPGame ≤ b.toPGame := by
  refine le_iff_forall_lf.2 ⟨fun i => ?_, isEmptyElim⟩
  rw [toPGame_moveLeft']
  exact toPGame_lf ((toLeftMovesToPGame_symm_lt i).trans_le h)

@[target]
theorem toPGame_lt {a b : Ordinal} (h : a < b) : a.toPGame < b.toPGame := by sorry

theorem toPGame_nonneg (a : Ordinal) : 0 ≤ a.toPGame :=
  zeroToPGameRelabelling.ge.trans <| toPGame_le <| Ordinal.zero_le a

@[target, simp]
theorem toPGame_lf_iff {a b : Ordinal} : a.toPGame ⧏ b.toPGame ↔ a < b := by sorry

@[simp]
theorem toPGame_le_iff {a b : Ordinal} : a.toPGame ≤ b.toPGame ↔ a ≤ b :=
  ⟨by contrapose; rw [not_le, PGame.not_le]; exact toPGame_lf, toPGame_le⟩

@[target, simp]
theorem toPGame_lt_iff {a b : Ordinal} : a.toPGame < b.toPGame ↔ a < b := by sorry

@[target, simp]
theorem toPGame_equiv_iff {a b : Ordinal} : (a.toPGame ≈ b.toPGame) ↔ a = b := by sorry

theorem toPGame_injective : Function.Injective Ordinal.toPGame := fun _ _ h =>
  toPGame_equiv_iff.1 <| equiv_of_eq h

@[target, simp]
theorem toPGame_inj {a b : Ordinal} : a.toPGame = b.toPGame ↔ a = b := by sorry

@[deprecated (since := "2024-12-29")] alias toPGame_eq_iff := toPGame_inj

/-- The order embedding version of `toPGame`. -/
@[simps]
noncomputable def toPGameEmbedding : Ordinal.{u} ↪o PGame.{u} where
  toFun := Ordinal.toPGame
  inj' := toPGame_injective
  map_rel_iff' := @toPGame_le_iff

/-- Converts an ordinal into the corresponding game. -/
noncomputable def toGame : Ordinal.{u} ↪o Game.{u} where
  toFun o := ⟦o.toPGame⟧
  inj' a b := by simpa [AntisymmRel] using le_antisymm
  map_rel_iff' := toPGame_le_iff

@[target, simp]
theorem mk_toPGame (o : Ordinal) : ⟦o.toPGame⟧ = o.toGame := by sorry

@[deprecated toGame (since := "2024-11-23")]
alias toGameEmbedding := toGame

@[target, simp]
theorem toGame_zero : toGame 0 = 0 := by sorry

@[simp]
theorem toGame_one : toGame 1 = 1 :=
  game_eq toPGame_one

theorem toGame_injective : Function.Injective toGame :=
  toGame.injective

@[simp]
theorem toGame_lf_iff {a b : Ordinal} : Game.LF a.toGame b.toGame ↔ a < b :=
  toPGame_lf_iff

@[target]
theorem toGame_le_iff {a b : Ordinal} : a.toGame ≤ b.toGame ↔ a ≤ b := by sorry

@[target]
theorem toGame_lt_iff {a b : Ordinal} : a.toGame < b.toGame ↔ a < b := by sorry

@[target]
theorem toGame_inj {a b : Ordinal} : a.toGame = b.toGame ↔ a = b := by sorry

@[deprecated (since := "2024-12-29")] alias toGame_eq_iff := toGame_inj

/-- The natural addition of ordinals corresponds to their sum as games. -/
theorem toPGame_nadd (a b : Ordinal) : (a ♯ b).toPGame ≈ a.toPGame + b.toPGame := by
  refine ⟨le_of_forall_lf (fun i => ?_) isEmptyElim, le_of_forall_lf (fun i => ?_) isEmptyElim⟩
  · rw [toPGame_moveLeft']
    rcases lt_nadd_iff.1 (toLeftMovesToPGame_symm_lt i) with (⟨c, hc, hc'⟩ | ⟨c, hc, hc'⟩) <;>
    rw [← toPGame_le_iff, le_congr_right (toPGame_nadd _ _)] at hc' <;>
    apply lf_of_le_of_lf hc'
    · apply add_lf_add_right
      rwa [toPGame_lf_iff]
    · apply add_lf_add_left
      rwa [toPGame_lf_iff]
  · apply leftMoves_add_cases i <;>
    intro i <;>
    let wf := toLeftMovesToPGame_symm_lt i <;>
    (try rw [add_moveLeft_inl]) <;>
    (try rw [add_moveLeft_inr]) <;>
    rw [toPGame_moveLeft', ← lf_congr_left (toPGame_nadd _ _), toPGame_lf_iff]
    · exact nadd_lt_nadd_right wf _
    · exact nadd_lt_nadd_left wf _
termination_by (a, b)

theorem toGame_nadd (a b : Ordinal) : (a ♯ b).toGame = a.toGame + b.toGame :=
  game_eq (toPGame_nadd a b)

/-- The natural multiplication of ordinals corresponds to their product as pre-games. -/
@[target]
theorem toPGame_nmul (a b : Ordinal) : (a ⨳ b).toPGame ≈ a.toPGame * b.toPGame := by sorry

@[target]
theorem toGame_nmul (a b : Ordinal) : (a ⨳ b).toGame = ⟦a.toPGame * b.toPGame⟧ := by sorry

@[target, simp] -- used to be a norm_cast lemma
theorem toGame_natCast : ∀ n : ℕ, toGame n = n := by sorry

@[target]
theorem toPGame_natCast (n : ℕ) : toPGame n ≈ n := by sorry

end Ordinal
