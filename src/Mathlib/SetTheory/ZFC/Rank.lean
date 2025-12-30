import VerifiedAgora.tagger
/-
Copyright (c) 2024 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.Logic.UnivLE
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.ZFC.Basic

/-!
# Ordinal ranks of PSet and ZFSet

In this file, we define the ordinal ranks of `PSet` and `ZFSet`. These ranks are the same as
`IsWellFounded.rank` over `∈`, but are defined in a way that the universe levels of ranks are the
same as the indexing types.

## Definitions

* `PSet.rank`: Ordinal rank of a pre-set.
* `ZFSet.rank`: Ordinal rank of a ZFC set.
-/

universe u v

open Ordinal Order

/-! ### PSet rank -/

namespace PSet

/-- The ordinal rank of a pre-set -/
noncomputable def rank : PSet.{u} → Ordinal.{u}
  | ⟨_, A⟩ => ⨆ a, succ (rank (A a))

@[target]
theorem rank_congr : ∀ {x y : PSet}, Equiv x y → rank x = rank y := by sorry

@[target]
theorem rank_lt_of_mem : ∀ {x y : PSet}, y ∈ x → rank y < rank x := by sorry

@[target]
theorem rank_le_iff {o : Ordinal} : ∀ {x : PSet}, rank x ≤ o ↔ ∀ ⦃y⦄, y ∈ x → rank y < o := by sorry

@[target]
theorem lt_rank_iff {o : Ordinal} {x : PSet} : o < rank x ↔ ∃ y ∈ x, o ≤ rank y := by sorry

variable {x y : PSet.{u}}

@[gcongr] theorem rank_mono (h : x ⊆ y) : rank x ≤ rank y :=
  rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (mem_of_subset h h₁)

@[target, simp]
theorem rank_empty : rank ∅ = 0 := by sorry

@[target, simp]
theorem rank_insert (x y : PSet) : rank (insert x y) = max (succ (rank x)) (rank y) := by sorry

@[target, simp]
theorem rank_singleton (x : PSet) : rank {x} = succ (rank x) := by sorry

@[target]
theorem rank_pair (x y : PSet) : rank {x, y} = max (succ (rank x)) (succ (rank y)) := by sorry

@[target, simp]
theorem rank_powerset (x : PSet) : rank (powerset x) = succ (rank x) := by sorry

/-- For the rank of `⋃₀ x`, we only have `rank (⋃₀ x) ≤ rank x ≤ rank (⋃₀ x) + 1`.

This inequality is split into `rank_sUnion_le` and `le_succ_rank_sUnion`. -/
@[target]
theorem rank_sUnion_le (x : PSet) : rank (⋃₀ x) ≤ rank x := by sorry

@[target]
theorem le_succ_rank_sUnion (x : PSet) : rank x ≤ succ (rank (⋃₀ x)) := by sorry

/-- `PSet.rank` is equal to the `IsWellFounded.rank` over `∈`. -/
@[target]
theorem rank_eq_wfRank : lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := PSet) (· ∈ ·) x := by sorry

end PSet

/-! ### ZFSet rank -/

namespace ZFSet

variable {x y : ZFSet.{u}}

/-- The ordinal rank of a ZFC set -/
noncomputable def rank : ZFSet.{u} → Ordinal.{u} :=
  Quotient.lift _ fun _ _ => PSet.rank_congr

@[target]
theorem rank_lt_of_mem : y ∈ x → rank y < rank x := by sorry

@[target]
theorem rank_le_iff {o : Ordinal} : rank x ≤ o ↔ ∀ ⦃y⦄, y ∈ x → rank y < o := by sorry

@[target]
theorem lt_rank_iff {o : Ordinal} : o < rank x ↔ ∃ y ∈ x, o ≤ rank y := by sorry

@[gcongr] theorem rank_mono (h : x ⊆ y) : rank x ≤ rank y :=
  rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (h h₁)

@[target, simp]
theorem rank_empty : rank ∅ = 0 := by sorry

@[simp]
theorem rank_insert (x y : ZFSet) : rank (insert x y) = max (succ (rank x)) (rank y) :=
  Quotient.inductionOn₂ x y PSet.rank_insert

@[simp]
theorem rank_singleton (x : ZFSet) : rank {x} = succ (rank x) :=
  (rank_insert _ _).trans (by simp)

@[target]
theorem rank_pair (x y : ZFSet) : rank {x, y} = max (succ (rank x)) (succ (rank y)) := by sorry

@[target, simp]
theorem rank_union (x y : ZFSet) : rank (x ∪ y) = max (rank x) (rank y) := by sorry

@[target, simp]
theorem rank_powerset (x : ZFSet) : rank (powerset x) = succ (rank x) := by sorry

/-- For the rank of `⋃₀ x`, we only have `rank (⋃₀ x) ≤ rank x ≤ rank (⋃₀ x) + 1`.

This inequality is split into `rank_sUnion_le` and `le_succ_rank_sUnion`. -/
@[target]
theorem rank_sUnion_le (x : ZFSet) : rank (⋃₀ x) ≤ rank x := by sorry

@[target]
theorem le_succ_rank_sUnion (x : ZFSet) : rank x ≤ succ (rank (⋃₀ x)) := by sorry

@[target, simp]
theorem rank_range {α : Type*} [Small.{u} α] (f : α → ZFSet.{u}) :
    rank (range f) = ⨆ i, succ (rank (f i)) := by sorry

/-- `ZFSet.rank` is equal to the `IsWellFounded.rank` over `∈`. -/
@[target]
theorem rank_eq_wfRank : lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := ZFSet) (· ∈ ·) x := by sorry

end ZFSet
