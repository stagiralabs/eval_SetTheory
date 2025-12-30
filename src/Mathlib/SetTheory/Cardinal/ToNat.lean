import VerifiedAgora.tagger
/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Projection from cardinal numbers to natural numbers

In this file we define `Cardinal.toNat` to be the natural projection `Cardinal → ℕ`,
sending all infinite cardinals to zero.
We also prove basic lemmas about this definition.
-/

assert_not_exists Field

universe u v
open Function Set

namespace Cardinal

variable {α : Type u} {c d : Cardinal.{u}}

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to 0. -/
noncomputable def toNat : Cardinal →*₀ ℕ :=
  ENat.toNatHom.comp toENat

@[simp] lemma toNat_toENat (a : Cardinal) : ENat.toNat (toENat a) = toNat a := rfl

@[target, simp]
theorem toNat_ofENat (n : ℕ∞) : toNat n = ENat.toNat n := by sorry

@[simp, norm_cast] theorem toNat_natCast (n : ℕ) : toNat n = n := toNat_ofENat n

@[simp]
lemma toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ ≤ c := by
  rw [← toNat_toENat, ENat.toNat_eq_zero, toENat_eq_zero, toENat_eq_top]

@[target]
lemma toNat_ne_zero : toNat c ≠ 0 ↔ c ≠ 0 ∧ c < ℵ₀ := by sorry

@[simp] lemma toNat_pos : 0 < toNat c ↔ c ≠ 0 ∧ c < ℵ₀ := pos_iff_ne_zero.trans toNat_ne_zero

theorem cast_toNat_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ↑(toNat c) = c := by
  lift c to ℕ using h
  rw [toNat_natCast]

@[target]
theorem toNat_apply_of_lt_aleph0 {c : Cardinal.{u}} (h : c < ℵ₀) :
    toNat c = Classical.choose (lt_aleph0.1 h) := by sorry

@[target]
theorem toNat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : toNat c = 0 := by sorry

@[target]
theorem cast_toNat_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : ↑(toNat c) = (0 : Cardinal) := by sorry

theorem cast_toNat_eq_iff_lt_aleph0 {c : Cardinal} : (toNat c) = c ↔ c < ℵ₀ := by
  constructor
  · intro h; by_contra h'; rw [not_lt] at h'
    rw [toNat_apply_of_aleph0_le h'] at h; rw [← h] at h'
    absurd h'; rw [not_le]; exact nat_lt_aleph0 0
  · exact fun h ↦ (Cardinal.cast_toNat_of_lt_aleph0 h)

@[target]
theorem toNat_strictMonoOn : StrictMonoOn toNat (Iio ℵ₀) := by sorry

theorem toNat_monotoneOn : MonotoneOn toNat (Iio ℵ₀) := toNat_strictMonoOn.monotoneOn

@[target]
theorem toNat_injOn : InjOn toNat (Iio ℵ₀) := by sorry

/-- Two finite cardinals are equal
iff they are equal their `Cardinal.toNat` projections are equal. -/
@[target]
theorem toNat_inj_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c = toNat d ↔ c = d := by sorry

@[deprecated (since := "2024-12-29")] alias toNat_eq_iff_eq_of_lt_aleph0 := toNat_inj_of_lt_aleph0

theorem toNat_le_iff_le_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c ≤ toNat d ↔ c ≤ d :=
  toNat_strictMonoOn.le_iff_le hc hd

@[target]
theorem toNat_lt_iff_lt_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c < toNat d ↔ c < d := by sorry

@[target, gcongr]
theorem toNat_le_toNat (hcd : c ≤ d) (hd : d < ℵ₀) : toNat c ≤ toNat d := by sorry

@[target]
theorem toNat_lt_toNat (hcd : c < d) (hd : d < ℵ₀) : toNat c < toNat d := by sorry

@[target, simp]
theorem toNat_ofNat (n : ℕ) [n.AtLeastTwo] :
    Cardinal.toNat ofNat(n) = OfNat.ofNat n := by sorry

/-- `toNat` has a right-inverse: coercion. -/
@[target]
theorem toNat_rightInverse : Function.RightInverse ((↑) : ℕ → Cardinal) toNat := by sorry

@[target]
theorem toNat_surjective : Surjective toNat := by sorry

@[target, simp]
theorem mk_toNat_of_infinite [h : Infinite α] : toNat #α = 0 := by sorry

@[target, simp]
theorem aleph0_toNat : toNat ℵ₀ = 0 := by sorry

@[target]
theorem mk_toNat_eq_card [Fintype α] : toNat #α = Fintype.card α := by sorry

@[simp]
theorem zero_toNat : toNat 0 = 0 := map_zero _

theorem one_toNat : toNat 1 = 1 := map_one _

@[target]
theorem toNat_eq_iff {n : ℕ} (hn : n ≠ 0) : toNat c = n ↔ c = n := by sorry

/-- A version of `toNat_eq_iff` for literals -/
@[target]
theorem toNat_eq_ofNat {n : ℕ} [Nat.AtLeastTwo n] :
    toNat c = OfNat.ofNat n ↔ c = OfNat.ofNat n := by sorry

@[simp]
theorem toNat_eq_one : toNat c = 1 ↔ c = 1 := by
  rw [toNat_eq_iff one_ne_zero, Nat.cast_one]

theorem toNat_eq_one_iff_unique : toNat #α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  toNat_eq_one.trans eq_one_iff_unique

@[target, simp]
theorem toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} c) = toNat c := by sorry

theorem toNat_congr {β : Type v} (e : α ≃ β) : toNat #α = toNat #β := by
  -- Porting note: Inserted universe hint below
  rw [← toNat_lift, (lift_mk_eq.{_,_,v}).mpr ⟨e⟩, toNat_lift]

theorem toNat_mul (x y : Cardinal) : toNat (x * y) = toNat x * toNat y := map_mul toNat x y

@[target, simp]
theorem toNat_add (hc : c < ℵ₀) (hd : d < ℵ₀) : toNat (c + d) = toNat c + toNat d := by sorry

@[target, simp]
theorem toNat_lift_add_lift {a : Cardinal.{u}} {b : Cardinal.{v}} (ha : a < ℵ₀) (hb : b < ℵ₀) :
    toNat (lift.{v} a + lift.{u} b) = toNat a + toNat b := by sorry

end Cardinal
