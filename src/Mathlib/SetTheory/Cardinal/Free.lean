import VerifiedAgora.tagger
/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Daniel Weber
-/
import Mathlib.Data.Finsupp.Fintype
import Mathlib.GroupTheory.FreeAbelianGroupFinsupp
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.RingTheory.FreeCommRing
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Cardinalities of free constructions

This file shows that all the free constructions over `α` have cardinality `max #α ℵ₀`,
and are thus infinite.

Combined with the ring `Fin n` for the finite cases, this lets us show that there is a `CommRing` of
any cardinality.
-/

universe u
variable (α : Type u)

section Infinite

@[to_additive]
instance [Nonempty α] : Infinite (FreeMonoid α) := inferInstanceAs <| Infinite (List α)

@[to_additive]
instance [Nonempty α] : Infinite (FreeGroup α) := by
  classical
  exact Infinite.of_surjective FreeGroup.norm FreeGroup.norm_surjective

instance [Nonempty α] : Infinite (FreeAbelianGroup α) :=
  (FreeAbelianGroup.equivFinsupp α).toEquiv.infinite_iff.2 inferInstance

instance : Infinite (FreeRing α) := by unfold FreeRing; infer_instance

instance : Infinite (FreeCommRing α) := by unfold FreeCommRing; infer_instance

end Infinite

namespace Cardinal

theorem mk_abelianization_le (G : Type u) [Group G] :
    #(Abelianization G) ≤ #G := Cardinal.mk_le_of_surjective Quotient.mk_surjective

@[target, to_additive (attr := simp)]
theorem mk_freeMonoid [Nonempty α] : #(FreeMonoid α) = max #α ℵ₀ := by sorry

@[target, to_additive (attr := simp)]
theorem mk_freeGroup [Nonempty α] : #(FreeGroup α) = max #α ℵ₀ := by sorry

@[target, simp]
theorem mk_freeAbelianGroup [Nonempty α] : #(FreeAbelianGroup α) = max #α ℵ₀ := by sorry

@[target, simp]
theorem mk_freeRing : #(FreeRing α) = max #α ℵ₀ := by sorry

@[simp]
theorem mk_freeCommRing : #(FreeCommRing α) = max #α ℵ₀ := by
  cases isEmpty_or_nonempty α <;> simp [FreeCommRing]

end Cardinal

section Nonempty

/-- A commutative ring can be constructed on any non-empty type.

See also `Infinite.nonempty_field`. -/
instance nonempty_commRing [Nonempty α] : Nonempty (CommRing α) := by
  obtain hR | hR := finite_or_infinite α
  · obtain ⟨x⟩ := nonempty_fintype α
    have : NeZero (Fintype.card α) := ⟨by inhabit α; simp⟩
    classical
    obtain ⟨e⟩ := Fintype.truncEquivFin α
    exact ⟨e.commRing⟩
  · have ⟨e⟩ : Nonempty (α ≃ FreeCommRing α) := by simp [← Cardinal.eq]
    exact ⟨e.commRing⟩

@[target, simp]
theorem nonempty_commRing_iff : Nonempty (CommRing α) ↔ Nonempty α := by sorry

@[simp]
theorem nonempty_ring_iff : Nonempty (Ring α) ↔ Nonempty α :=
  ⟨Nonempty.map (·.zero), fun _ => (nonempty_commRing _).map (·.toRing)⟩

@[target, simp]
theorem nonempty_commSemiring_iff : Nonempty (CommSemiring α) ↔ Nonempty α := by sorry

@[target, simp]
theorem nonempty_semiring_iff : Nonempty (Semiring α) ↔ Nonempty α := by sorry

end Nonempty
