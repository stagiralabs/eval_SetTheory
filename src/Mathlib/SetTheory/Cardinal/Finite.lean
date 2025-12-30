import VerifiedAgora.tagger
/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.ULift
import Mathlib.Data.ZMod.Defs
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Finite Cardinality Functions

## Main Definitions

* `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`.
* `ENat.card α` is the cardinality of `α` as an  extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`.
* `PartENat.card α` is the cardinality of `α` as an extended natural number
  (using the legacy definition `PartENat := Part ℕ`). If `α` is infinite, `PartENat.card α = ⊤`.
-/

assert_not_exists Field

open Cardinal Function

noncomputable section

variable {α β : Type*}

universe u v

namespace Nat

/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)

@[target, simp]
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α := by sorry

/-- Because this theorem takes `Fintype α` as a non-instance argument, it can be used in particular
when `Fintype.card` ends up with different instance than the one found by inference -/
@[target]
theorem _root_.Fintype.card_eq_nat_card {_ : Fintype α} : Fintype.card α = Nat.card α := by sorry

@[target]
lemma card_eq_finsetCard (s : Finset α) : Nat.card s = s.card := by sorry

@[target]
lemma card_eq_card_toFinset (s : Set α) [Fintype s] : Nat.card s = s.toFinset.card := by sorry

@[target]
lemma card_eq_card_finite_toFinset {s : Set α} (hs : s.Finite) : Nat.card s = hs.toFinset.card := by sorry

@[simp] theorem card_of_isEmpty [IsEmpty α] : Nat.card α = 0 := by simp [Nat.card]

@[target, simp] lemma card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 := mk_toNat_of_infinite


lemma cast_card [Finite α] : (Nat.card α : Cardinal) = Cardinal.mk α := by
  rw [Nat.card, Cardinal.cast_toNat_of_lt_aleph0]
  exact Cardinal.lt_aleph0_of_finite _

@[target]
lemma _root_.Set.Infinite.card_eq_zero {s : Set α} (hs : s.Infinite) : Nat.card s = 0 := by sorry

@[target]
lemma card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α := by sorry

@[target]
lemma card_ne_zero : Nat.card α ≠ 0 ↔ Nonempty α ∧ Finite α := by sorry

@[target]
lemma card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α := by sorry

@[target, simp] lemma card_pos [Nonempty α] [Finite α] : 0 < Nat.card α := card_pos_iff.2 ⟨‹_›, ‹_›⟩


theorem finite_of_card_ne_zero (h : Nat.card α ≠ 0) : Finite α := (card_ne_zero.1 h).2

@[target]
theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β := by sorry

@[target]
lemma card_le_card_of_injective {α : Type u} {β : Type v} [Finite β] (f : α → β)
    (hf : Injective f) : Nat.card α ≤ Nat.card β := by sorry

@[target]
lemma card_le_card_of_surjective {α : Type u} {β : Type v} [Finite α] (f : α → β)
    (hf : Surjective f) : Nat.card β ≤ Nat.card α := by sorry

@[target]
theorem card_eq_of_bijective (f : α → β) (hf : Function.Bijective f) : Nat.card α = Nat.card β := by sorry

protected theorem bijective_iff_injective_and_card [Finite β] (f : α → β) :
    Bijective f ↔ Injective f ∧ Nat.card α = Nat.card β := by
  rw [Bijective, and_congr_right_iff]
  intro h
  have := Fintype.ofFinite β
  have := Fintype.ofInjective f h
  revert h
  rw [← and_congr_right_iff, ← Bijective,
    card_eq_fintype_card, card_eq_fintype_card, Fintype.bijective_iff_injective_and_card]

protected theorem bijective_iff_surjective_and_card [Finite α] (f : α → β) :
    Bijective f ↔ Surjective f ∧ Nat.card α = Nat.card β := by
  classical
  rw [_root_.and_comm, Bijective, and_congr_left_iff]
  intro h
  have := Fintype.ofFinite α
  have := Fintype.ofSurjective f h
  revert h
  rw [← and_congr_left_iff, ← Bijective, ← and_comm,
    card_eq_fintype_card, card_eq_fintype_card, Fintype.bijective_iff_surjective_and_card]

@[target]
theorem _root_.Function.Injective.bijective_of_nat_card_le [Finite β] {f : α → β}
    (inj : Injective f) (hc : Nat.card β ≤ Nat.card α) : Bijective f := by sorry

@[target]
theorem _root_.Function.Surjective.bijective_of_nat_card_le [Finite α] {f : α → β}
    (surj : Surjective f) (hc : Nat.card α ≤ Nat.card β) : Bijective f := by sorry

@[target]
theorem card_eq_of_equiv_fin {α : Type*} {n : ℕ} (f : α ≃ Fin n) : Nat.card α = n := by sorry

section Set
open Set
variable {s t : Set α}

@[target]
lemma card_mono (ht : t.Finite) (h : s ⊆ t) : Nat.card s ≤ Nat.card t := by sorry

@[target]
lemma card_image_le {f : α → β} (hs : s.Finite) : Nat.card (f '' s) ≤ Nat.card s := by sorry

@[target]
lemma card_image_of_injOn {f : α → β} (hf : s.InjOn f) : Nat.card (f '' s) = Nat.card s := by sorry

@[target]
lemma card_image_of_injective {f : α → β} (hf : Injective f) (s : Set α) :
    Nat.card (f '' s) = Nat.card s := by sorry

@[target]
lemma card_image_equiv (e : α ≃ β) : Nat.card (e '' s) = Nat.card s := by sorry

@[target]
lemma card_preimage_of_injOn {f : α → β} {s : Set β} (hf : (f ⁻¹' s).InjOn f) (hsf : s ⊆ range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := by sorry

@[target]
lemma card_preimage_of_injective {f : α → β} {s : Set β} (hf : Injective f) (hsf : s ⊆ range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := by sorry

@[simp] lemma card_univ : Nat.card (univ : Set α) = Nat.card α :=
  card_congr (Equiv.Set.univ α)

@[target]
lemma card_range_of_injective {f : α → β} (hf : Injective f) :
    Nat.card (range f) = Nat.card α := by sorry

end Set

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `Fin (Nat.card α)`. See also `Finite.equivFin`. -/
def equivFinOfCardPos {α : Type*} (h : Nat.card α ≠ 0) : α ≃ Fin (Nat.card α) := by
  cases fintypeOrInfinite α
  · simpa only [card_eq_fintype_card] using Fintype.equivFin α
  · simp only [card_eq_zero_of_infinite, ne_eq, not_true_eq_false] at h

@[target]
theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 := by sorry

@[target]
theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α := by sorry

@[target, simp]
theorem card_unique [Nonempty α] [Subsingleton α] : Nat.card α = 1 := by sorry

@[target]
theorem card_eq_one_iff_exists : Nat.card α = 1 ↔ ∃ x : α, ∀ y : α, y = x := by sorry

@[target]
theorem card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.univ α := by sorry

@[target]
theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ ∃! y, y ≠ x := by sorry

@[target, simp]
theorem card_subtype_true : Nat.card {_a : α // True} = Nat.card α := by sorry

@[target, simp]
theorem card_sum [Finite α] [Finite β] : Nat.card (α ⊕ β) = Nat.card α + Nat.card β := by sorry

@[target, simp]
theorem card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α * Nat.card β := by sorry

@[target, simp]
theorem card_ulift (α : Type*) : Nat.card (ULift α) = Nat.card α := by sorry

@[simp]
theorem card_plift (α : Type*) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift

@[target]
theorem card_sigma {β : α → Type*} [Fintype α] [∀ a, Finite (β a)] :
    Nat.card (Sigma β) = ∑ a, Nat.card (β a) := by sorry

@[target]
theorem card_pi {β : α → Type*} [Fintype α] : Nat.card (∀ a, β a) = ∏ a, Nat.card (β a) := by sorry

@[target]
theorem card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α := by sorry

@[target, simp]
theorem card_zmod (n : ℕ) : Nat.card (ZMod n) = n := by sorry

end Nat

namespace Set
variable {s : Set α}

@[target]
lemma card_singleton_prod (a : α) (t : Set β) : Nat.card ({a} ×ˢ t) = Nat.card t := by sorry

@[target]
lemma card_prod_singleton (s : Set α) (b : β) : Nat.card (s ×ˢ {b}) = Nat.card s := by sorry

@[target]
theorem natCard_pos (hs : s.Finite) : 0 < Nat.card s ↔ s.Nonempty := by sorry

protected alias ⟨_, Nonempty.natCard_pos⟩ := natCard_pos

@[simp] lemma natCard_graphOn (s : Set α) (f : α → β) : Nat.card (s.graphOn f) = Nat.card s := by
  rw [← Nat.card_image_of_injOn fst_injOn_graph, image_fst_graphOn]

end Set


namespace ENat

/-- `ENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`. -/
def card (α : Type*) : ℕ∞ :=
  toENat (mk α)

@[target, simp]
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α := by sorry

@[target, simp high]
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ := by sorry

@[simp] lemma card_eq_top : card α = ⊤ ↔ Infinite α := by simp [card, aleph0_le_mk_iff]

@[simp] theorem card_lt_top_of_finite [Finite α] : card α < ⊤ := by simp [card]

@[target, simp]
theorem card_sum (α β : Type*) :
    card (α ⊕ β) = card α + card β := by sorry

@[target]
theorem card_congr {α β : Type*} (f : α ≃ β) : card α = card β := by sorry

@[simp] lemma card_ulift (α : Type*) : card (ULift α) = card α := card_congr Equiv.ulift

@[target, simp] lemma card_plift (α : Type*) : card (PLift α) = card α := card_congr Equiv.plift


theorem card_image_of_injOn {α β : Type*} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm

@[target]
theorem card_image_of_injective {α β : Type*} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s := by sorry

@[target, simp]
theorem _root_.Cardinal.natCast_le_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n ≤ toENat c ↔ ↑n ≤ c := by sorry

@[target]
theorem _root_.Cardinal.toENat_le_natCast_iff {c : Cardinal} {n : ℕ} :
    toENat c ≤ n ↔ c ≤ n := by sorry

@[target, simp]
theorem _root_.Cardinal.natCast_eq_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n = toENat c ↔ ↑n = c := by sorry

@[target]
theorem _root_.Cardinal.toENat_eq_natCast_iff {c : Cardinal} {n : ℕ} :
    Cardinal.toENat c = n ↔ c = n := by sorry

@[target, simp]
theorem _root_.Cardinal.natCast_lt_toENat_iff {n : ℕ} {c : Cardinal} :
    ↑n < toENat c ↔ ↑n < c := by sorry

@[target, simp]
theorem _root_.Cardinal.toENat_lt_natCast_iff {n : ℕ} {c : Cardinal} :
    toENat c < ↑n ↔ c < ↑n := by sorry

@[target]
theorem card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ IsEmpty α := by sorry

@[target]
theorem card_le_one_iff_subsingleton (α : Type*) : card α ≤ 1 ↔ Subsingleton α := by sorry

@[target]
theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α := by sorry

end ENat
