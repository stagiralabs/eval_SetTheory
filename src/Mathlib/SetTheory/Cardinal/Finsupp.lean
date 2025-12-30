import VerifiedAgora.tagger
/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Junyan Xu
-/
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Multiset

/-! # Results on the cardinality of finitely supported functions and multisets. -/

universe u v

namespace Cardinal

@[target, simp]
theorem mk_finsupp_lift_of_fintype (α : Type u) (β : Type v) [Fintype α] [Zero β] :
    #(α →₀ β) = lift.{u} #β ^ Fintype.card α := by sorry

@[target]
theorem mk_finsupp_of_fintype (α β : Type u) [Fintype α] [Zero β] :
    #(α →₀ β) = #β ^ Fintype.card α := by sorry

@[target, simp]
theorem mk_finsupp_lift_of_infinite (α : Type u) (β : Type v) [Infinite α] [Zero β] [Nontrivial β] :
    #(α →₀ β) = max (lift.{v} #α) (lift.{u} #β) := by sorry

@[target]
theorem mk_finsupp_of_infinite (α β : Type u) [Infinite α] [Zero β] [Nontrivial β] :
    #(α →₀ β) = max #α #β := by sorry

@[target, simp]
theorem mk_finsupp_lift_of_infinite' (α : Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] :
    #(α →₀ β) = max (lift.{v} #α) (lift.{u} #β) := by sorry

theorem mk_finsupp_of_infinite' (α β : Type u) [Nonempty α] [Zero β] [Infinite β] :
    #(α →₀ β) = max #α #β := by simp

@[target]
theorem mk_finsupp_nat (α : Type u) [Nonempty α] : #(α →₀ ℕ) = max #α ℵ₀ := by sorry

@[target]
theorem mk_multiset_of_isEmpty (α : Type u) [IsEmpty α] : #(Multiset α) = 1 := by sorry

@[target, simp]
theorem mk_multiset_of_nonempty (α : Type u) [Nonempty α] : #(Multiset α) = max #α ℵ₀ := by sorry

@[target]
theorem mk_multiset_of_infinite (α : Type u) [Infinite α] : #(Multiset α) = #α := by sorry

@[target]
theorem mk_multiset_of_countable (α : Type u) [Countable α] [Nonempty α] : #(Multiset α) = ℵ₀ := by sorry

end Cardinal
