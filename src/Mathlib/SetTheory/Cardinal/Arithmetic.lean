import VerifiedAgora.tagger
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Cardinal arithmetic

Arithmetic operations on cardinals are defined in `SetTheory/Cardinal/Basic.lean`. However, proving
the important theorem `c * c = c` for infinite cardinals and its corollaries requires the use of
ordinal numbers. This is done within this file.

## Main statements

* `Cardinal.mul_eq_max` and `Cardinal.add_eq_max` state that the product (resp. sum) of two infinite
  cardinals is just their maximum. Several variations around this fact are also given.
* `Cardinal.mk_list_eq_mk`: when `α` is infinite, `α` and `List α` have the same cardinality.

## Tags

cardinal arithmetic (for infinite cardinals)
-/

assert_not_exists Module Finsupp

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

namespace Cardinal

/-! ### Properties of `mul` -/
section mul

/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
@[target]
theorem mul_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c * c = c := by sorry

/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
@[target]
theorem mul_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : ℵ₀ ≤ b) : a * b = max a b := by sorry

@[target, simp]
theorem mul_mk_eq_max {α β : Type u} [Infinite α] [Infinite β] : #α * #β = max #α #β := by sorry

@[target, simp]
theorem aleph_mul_aleph (o₁ o₂ : Ordinal) : ℵ_ o₁ * ℵ_ o₂ = ℵ_ (max o₁ o₂) := by sorry

@[target, simp]
theorem aleph0_mul_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : ℵ₀ * a = a := by sorry

@[target, simp]
theorem mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a * ℵ₀ = a := by sorry

@[target]
theorem aleph0_mul_mk_eq {α : Type*} [Infinite α] : ℵ₀ * #α = #α := by sorry

theorem mk_mul_aleph0_eq {α : Type*} [Infinite α] : #α * ℵ₀ = #α :=
  mul_aleph0_eq (aleph0_le_mk α)

@[target, simp]
theorem aleph0_mul_aleph (o : Ordinal) : ℵ₀ * ℵ_ o = ℵ_ o := by sorry

@[simp]
theorem aleph_mul_aleph0 (o : Ordinal) : ℵ_ o * ℵ₀ = ℵ_ o :=
  mul_aleph0_eq (aleph0_le_aleph o)

@[target]
theorem mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a * b < c := by sorry

@[target]
theorem mul_le_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) : a * b ≤ max a b := by sorry

@[target]
theorem mul_eq_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) (h' : b ≠ 0) :
    a * b = max a b := by sorry

@[target]
theorem mul_le_max_of_aleph0_le_right {a b : Cardinal} (h : ℵ₀ ≤ b) : a * b ≤ max a b := by sorry

@[target]
theorem mul_eq_max_of_aleph0_le_right {a b : Cardinal} (h' : a ≠ 0) (h : ℵ₀ ≤ b) :
    a * b = max a b := by sorry

theorem mul_eq_max' {a b : Cardinal} (h : ℵ₀ ≤ a * b) : a * b = max a b := by
  rcases aleph0_le_mul_iff.mp h with ⟨ha, hb, ha' | hb'⟩
  · exact mul_eq_max_of_aleph0_le_left ha' hb
  · exact mul_eq_max_of_aleph0_le_right ha hb'

@[target]
theorem mul_le_max (a b : Cardinal) : a * b ≤ max (max a b) ℵ₀ := by sorry

theorem mul_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : a * b = a := by
  rw [mul_eq_max_of_aleph0_le_left ha hb', max_eq_left hb]

@[target]
theorem mul_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : a * b = b := by sorry

@[target]
theorem le_mul_left {a b : Cardinal} (h : b ≠ 0) : a ≤ b * a := by sorry

@[target]
theorem le_mul_right {a b : Cardinal} (h : b ≠ 0) : a ≤ a * b := by sorry

@[target]
theorem mul_eq_left_iff {a b : Cardinal} : a * b = a ↔ max ℵ₀ b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0 := by sorry

end mul

/-! ### Properties of `add` -/
section add

/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
theorem add_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c + c = c :=
  le_antisymm
    (by
      convert mul_le_mul_right' ((nat_lt_aleph0 2).le.trans h) c using 1
      <;> simp [two_mul, mul_eq_self h])
    (self_le_add_left c c)

/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
@[target]
theorem add_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) : a + b = max a b := by sorry

@[target]
theorem add_eq_max' {a b : Cardinal} (ha : ℵ₀ ≤ b) : a + b = max a b := by sorry

@[target, simp]
theorem add_mk_eq_max {α β : Type u} [Infinite α] : #α + #β = max #α #β := by sorry

@[target, simp]
theorem add_mk_eq_max' {α β : Type u} [Infinite β] : #α + #β = max #α #β := by sorry

@[target]
theorem add_mk_eq_self {α : Type*} [Infinite α] : #α + #α = #α := by sorry

@[target]
theorem add_le_max (a b : Cardinal) : a + b ≤ max (max a b) ℵ₀ := by sorry

@[target]
theorem add_le_of_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) : a + b ≤ c := by sorry

@[target]
theorem add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a + b < c := by sorry

@[target]
theorem eq_of_add_eq_of_aleph0_le {a b c : Cardinal} (h : a + b = c) (ha : a < c) (hc : ℵ₀ ≤ c) :
    b = c := by sorry

@[target]
theorem add_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) : a + b = a := by sorry

@[target]
theorem add_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) : a + b = b := by sorry

@[target]
theorem add_eq_left_iff {a b : Cardinal} : a + b = a ↔ max ℵ₀ b ≤ a ∨ b = 0 := by sorry

@[target]
theorem add_eq_right_iff {a b : Cardinal} : a + b = b ↔ max ℵ₀ a ≤ b ∨ a = 0 := by sorry

@[target]
theorem add_nat_eq {a : Cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : a + n = a := by sorry

@[target]
theorem nat_add_eq {a : Cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : n + a = a := by sorry

@[target]
theorem add_one_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a + 1 = a := by sorry

@[target]
theorem mk_add_one_eq {α : Type*} [Infinite α] : #α + 1 = #α := by sorry

protected theorem eq_of_add_eq_add_left {a b c : Cardinal} (h : a + b = a + c) (ha : a < ℵ₀) :
    b = c := by
  rcases le_or_lt ℵ₀ b with hb | hb
  · have : a < b := ha.trans_le hb
    rw [add_eq_right hb this.le, eq_comm] at h
    rw [eq_of_add_eq_of_aleph0_le h this hb]
  · have hc : c < ℵ₀ := by
      rw [← not_le]
      intro hc
      apply lt_irrefl ℵ₀
      apply (hc.trans (self_le_add_left _ a)).trans_lt
      rw [← h]
      apply add_lt_aleph0 ha hb
    rw [lt_aleph0] at *
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    rcases hc with ⟨k, rfl⟩
    norm_cast at h ⊢
    apply add_left_cancel h

protected theorem eq_of_add_eq_add_right {a b c : Cardinal} (h : a + b = c + b) (hb : b < ℵ₀) :
    a = c := by
  rw [add_comm a b, add_comm c b] at h
  exact Cardinal.eq_of_add_eq_add_left h hb

end add

/-! ### Properties of `ciSup` -/
section ciSup

variable {ι : Type u} {ι' : Type w} (f : ι → Cardinal.{v})

section add

variable [Nonempty ι] [Nonempty ι']

protected theorem ciSup_add (hf : BddAbove (range f)) (c : Cardinal.{v}) :
    (⨆ i, f i) + c = ⨆ i, f i + c := by
  have : ∀ i, f i + c ≤ (⨆ i, f i) + c := fun i ↦ add_le_add_right (le_ciSup hf i) c
  refine le_antisymm ?_ (ciSup_le' this)
  have bdd : BddAbove (range (f · + c)) := ⟨_, forall_mem_range.mpr this⟩
  obtain hs | hs := lt_or_le (⨆ i, f i) ℵ₀
  · obtain ⟨i, hi⟩ := exists_eq_of_iSup_eq_of_not_isSuccLimit
      f hf (not_isSuccLimit_of_lt_aleph0 hs) rfl
    exact hi ▸ le_ciSup bdd i
  rw [add_eq_max hs, max_le_iff]
  exact ⟨ciSup_mono bdd fun i ↦ self_le_add_right _ c,
    (self_le_add_left _ _).trans (le_ciSup bdd <| Classical.arbitrary ι)⟩

protected theorem add_ciSup (hf : BddAbove (range f)) (c : Cardinal.{v}) :
    c + (⨆ i, f i) = ⨆ i, c + f i := by
  rw [add_comm, Cardinal.ciSup_add f hf]; simp_rw [add_comm]

protected theorem ciSup_add_ciSup (hf : BddAbove (range f)) (g : ι' → Cardinal.{v})
    (hg : BddAbove (range g)) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ (i) (j), f i + g j := by
  simp_rw [Cardinal.ciSup_add f hf, Cardinal.add_ciSup g hg]

end add

protected theorem ciSup_mul (c : Cardinal.{v}) : (⨆ i, f i) * c = ⨆ i, f i * c := by
  cases isEmpty_or_nonempty ι; · simp
  obtain rfl | h0 := eq_or_ne c 0; · simp
  by_cases hf : BddAbove (range f); swap
  · have hfc : ¬ BddAbove (range (f · * c)) := fun bdd ↦ hf
      ⟨⨆ i, f i * c, forall_mem_range.mpr fun i ↦ (le_mul_right h0).trans (le_ciSup bdd i)⟩
    simp [iSup, csSup_of_not_bddAbove, hf, hfc]
  have : ∀ i, f i * c ≤ (⨆ i, f i) * c := fun i ↦ mul_le_mul_right' (le_ciSup hf i) c
  refine le_antisymm ?_ (ciSup_le' this)
  have bdd : BddAbove (range (f · * c)) := ⟨_, forall_mem_range.mpr this⟩
  obtain hs | hs := lt_or_le (⨆ i, f i) ℵ₀
  · obtain ⟨i, hi⟩ := exists_eq_of_iSup_eq_of_not_isSuccLimit
      f hf (not_isSuccLimit_of_lt_aleph0 hs) rfl
    exact hi ▸ le_ciSup bdd i
  rw [mul_eq_max_of_aleph0_le_left hs h0, max_le_iff]
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup' (one_lt_aleph0.trans_le hs)
  exact ⟨ciSup_mono bdd fun i ↦ le_mul_right h0,
    (le_mul_left (zero_lt_one.trans hi).ne').trans (le_ciSup bdd i)⟩

protected theorem mul_ciSup (c : Cardinal.{v}) : c * (⨆ i, f i) = ⨆ i, c * f i := by
  rw [mul_comm, Cardinal.ciSup_mul f]; simp_rw [mul_comm]

protected theorem ciSup_mul_ciSup (g : ι' → Cardinal.{v}) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ (i) (j), f i * g j := by
  simp_rw [Cardinal.ciSup_mul f, Cardinal.mul_ciSup g]

@[target]
theorem sum_eq_iSup_lift {f : ι → Cardinal.{max u v}} (hι : ℵ₀ ≤ #ι)
    (h : lift.{v} #ι ≤ iSup f) : sum f = iSup f := by sorry

@[target]
theorem sum_eq_iSup {f : ι → Cardinal.{u}} (hι : ℵ₀ ≤ #ι) (h : #ι ≤ iSup f) : sum f = iSup f := by sorry

end ciSup

/-! ### Properties of `aleph` -/
section aleph

@[target, simp]
theorem aleph_add_aleph (o₁ o₂ : Ordinal) : ℵ_ o₁ + ℵ_ o₂ = ℵ_ (max o₁ o₂) := by sorry

@[target]
theorem add_right_inj_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < aleph0) : α + γ = β + γ ↔ α = β := by sorry

@[target, simp]
theorem add_nat_inj {α β : Cardinal} (n : ℕ) : α + n = β + n ↔ α = β := by sorry

@[target, simp]
theorem add_one_inj {α β : Cardinal} : α + 1 = β + 1 ↔ α = β := by sorry

@[target]
theorem add_le_add_iff_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < ℵ₀) :
    α + γ ≤ β + γ ↔ α ≤ β := by sorry

@[target, simp]
theorem add_nat_le_add_nat_iff {α β : Cardinal} (n : ℕ) : α + n ≤ β + n ↔ α ≤ β := by sorry

@[target, simp]
theorem add_one_le_add_one_iff {α β : Cardinal} : α + 1 ≤ β + 1 ↔ α ≤ β := by sorry

end aleph

/-! ### Properties about `power` -/
section power

@[target]
theorem pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : μ < ℵ₀) : κ ^ μ ≤ κ := by sorry

@[target]
theorem pow_eq {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : 1 ≤ μ) (H3 : μ < ℵ₀) : κ ^ μ = κ := by sorry

@[target]
theorem power_self_eq {c : Cardinal} (h : ℵ₀ ≤ c) : c ^ c = 2 ^ c := by sorry

@[target]
theorem prod_eq_two_power {ι : Type u} [Infinite ι] {c : ι → Cardinal.{v}} (h₁ : ∀ i, 2 ≤ c i)
    (h₂ : ∀ i, lift.{u} (c i) ≤ lift.{v} #ι) : prod c = 2 ^ lift.{v} #ι := by sorry

@[target]
theorem power_eq_two_power {c₁ c₂ : Cardinal} (h₁ : ℵ₀ ≤ c₁) (h₂ : 2 ≤ c₂) (h₂' : c₂ ≤ c₁) :
    c₂ ^ c₁ = 2 ^ c₁ := by sorry

@[target]
theorem nat_power_eq {c : Cardinal.{u}} (h : ℵ₀ ≤ c) {n : ℕ} (hn : 2 ≤ n) :
    (n : Cardinal.{u}) ^ c = 2 ^ c := by sorry

@[target]
theorem power_nat_le {c : Cardinal.{u}} {n : ℕ} (h : ℵ₀ ≤ c) : c ^ n ≤ c := by sorry

@[target]
theorem power_nat_eq {c : Cardinal.{u}} {n : ℕ} (h1 : ℵ₀ ≤ c) (h2 : 1 ≤ n) : c ^ n = c := by sorry

@[target]
theorem power_nat_le_max {c : Cardinal.{u}} {n : ℕ} : c ^ (n : Cardinal.{u}) ≤ max c ℵ₀ := by sorry

@[target]
lemma power_le_aleph0 {a b : Cardinal.{u}} (ha : a ≤ ℵ₀) (hb : b < ℵ₀) : a ^ b ≤ ℵ₀ := by sorry

@[target]
theorem powerlt_aleph0 {c : Cardinal} (h : ℵ₀ ≤ c) : c ^< ℵ₀ = c := by sorry

@[target]
theorem powerlt_aleph0_le (c : Cardinal) : c ^< ℵ₀ ≤ max c ℵ₀ := by sorry

end power

/-! ### Computing cardinality of various types -/
section computing

section Function

variable {α β : Type u} {β' : Type v}

@[target]
theorem mk_equiv_eq_zero_iff_lift_ne : #(α ≃ β') = 0 ↔ lift.{v} #α ≠ lift.{u} #β' := by sorry

@[target]
theorem mk_equiv_eq_zero_iff_ne : #(α ≃ β) = 0 ↔ #α ≠ #β := by sorry

/-- This lemma makes lemmas assuming `Infinite α` applicable to the situation where we have
  `Infinite β` instead. -/
@[target]
theorem mk_equiv_comm : #(α ≃ β') = #(β' ≃ α) := by sorry

@[target]
theorem mk_embedding_eq_zero_iff_lift_lt : #(α ↪ β') = 0 ↔ lift.{u} #β' < lift.{v} #α := by sorry

@[target]
theorem mk_embedding_eq_zero_iff_lt : #(α ↪ β) = 0 ↔ #β < #α := by sorry

@[target]
theorem mk_arrow_eq_zero_iff : #(α → β') = 0 ↔ #α ≠ 0 ∧ #β' = 0 := by sorry

@[target]
theorem mk_surjective_eq_zero_iff_lift :
    #{f : α → β' | Surjective f} = 0 ↔ lift.{v} #α < lift.{u} #β' ∨ (#α ≠ 0 ∧ #β' = 0) := by sorry

@[target]
theorem mk_surjective_eq_zero_iff :
    #{f : α → β | Surjective f} = 0 ↔ #α < #β ∨ (#α ≠ 0 ∧ #β = 0) := by sorry

variable (α β')

@[target]
theorem mk_equiv_le_embedding : #(α ≃ β') ≤ #(α ↪ β') := by sorry

@[target]
theorem mk_embedding_le_arrow : #(α ↪ β') ≤ #(α → β') := by sorry

variable [Infinite α] {α β'}

@[target]
theorem mk_perm_eq_self_power : #(Equiv.Perm α) = #α ^ #α := by sorry

@[target]
theorem mk_perm_eq_two_power : #(Equiv.Perm α) = 2 ^ #α := by sorry

@[target]
theorem mk_equiv_eq_arrow_of_lift_eq (leq : lift.{v} #α = lift.{u} #β') :
    #(α ≃ β') = #(α → β') := by sorry

@[target]
theorem mk_equiv_eq_arrow_of_eq (eq : #α = #β) : #(α ≃ β) = #(α → β) := by sorry

@[target]
theorem mk_equiv_of_lift_eq (leq : lift.{v} #α = lift.{u} #β') : #(α ≃ β') = 2 ^ lift.{v} #α := by sorry

@[target]
theorem mk_equiv_of_eq (eq : #α = #β) : #(α ≃ β) = 2 ^ #α := by sorry

@[target]
theorem mk_embedding_eq_arrow_of_lift_le (lle : lift.{u} #β' ≤ lift.{v} #α) :
    #(β' ↪ α) = #(β' → α) := by sorry

@[target]
theorem mk_embedding_eq_arrow_of_le (le : #β ≤ #α) : #(β ↪ α) = #(β → α) := by sorry

@[target]
theorem mk_surjective_eq_arrow_of_lift_le (lle : lift.{u} #β' ≤ lift.{v} #α) :
    #{f : α → β' | Surjective f} = #(α → β') := by sorry

@[target]
theorem mk_surjective_eq_arrow_of_le (le : #β ≤ #α) : #{f : α → β | Surjective f} = #(α → β) := by sorry

end Function

@[target, simp]
theorem mk_list_eq_mk (α : Type u) [Infinite α] : #(List α) = #α := by sorry

@[target]
theorem mk_list_eq_aleph0 (α : Type u) [Countable α] [Nonempty α] : #(List α) = ℵ₀ := by sorry

@[target]
theorem mk_list_eq_max_mk_aleph0 (α : Type u) [Nonempty α] : #(List α) = max #α ℵ₀ := by sorry

@[target]
theorem mk_list_le_max (α : Type u) : #(List α) ≤ max ℵ₀ #α := by sorry

@[target, simp]
theorem mk_finset_of_infinite (α : Type u) [Infinite α] : #(Finset α) = #α := by sorry

@[target]
theorem mk_bounded_set_le_of_infinite (α : Type u) [Infinite α] (c : Cardinal) :
    #{ t : Set α // #t ≤ c } ≤ #α ^ c := by sorry

@[target]
theorem mk_bounded_set_le (α : Type u) (c : Cardinal) :
    #{ t : Set α // #t ≤ c } ≤ max #α ℵ₀ ^ c := by sorry

@[target]
theorem mk_bounded_subset_le {α : Type u} (s : Set α) (c : Cardinal.{u}) :
    #{ t : Set α // t ⊆ s ∧ #t ≤ c } ≤ max #s ℵ₀ ^ c := by sorry

end computing

/-! ### Properties of `compl` -/
section compl

@[target]
theorem mk_compl_of_infinite {α : Type*} [Infinite α] (s : Set α) (h2 : #s < #α) :
    #(sᶜ : Set α) = #α := by sorry

@[target]
theorem mk_compl_finset_of_infinite {α : Type*} [Infinite α] (s : Finset α) :
    #((↑s)ᶜ : Set α) = #α := by sorry

@[target]
theorem mk_compl_eq_mk_compl_infinite {α : Type*} [Infinite α] {s t : Set α} (hs : #s < #α)
    (ht : #t < #α) : #(sᶜ : Set α) = #(tᶜ : Set α) := by sorry

@[target]
theorem mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} [Finite α] {s : Set α}
    {t : Set β} (h1 : (lift.{max v w, u} #α) = (lift.{max u w, v} #β))
    (h2 : lift.{max v w, u} #s = lift.{max u w, v} #t) :
    lift.{max v w} #(sᶜ : Set α) = lift.{max u w} #(tᶜ : Set β) := by sorry

@[target]
theorem mk_compl_eq_mk_compl_finite {α β : Type u} [Finite α] {s : Set α} {t : Set β}
    (h1 : #α = #β) (h : #s = #t) : #(sᶜ : Set α) = #(tᶜ : Set β) := by sorry

@[target]
theorem mk_compl_eq_mk_compl_finite_same {α : Type u} [Finite α] {s t : Set α} (h : #s = #t) :
    #(sᶜ : Set α) = #(tᶜ : Set α) := by sorry

end compl

/-! ### Extending an injection to an equiv -/
section extend

@[target]
theorem extend_function {α β : Type*} {s : Set α} (f : s ↪ β)
    (h : Nonempty ((sᶜ : Set α) ≃ ((range f)ᶜ : Set β))) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by sorry

@[target]
theorem extend_function_finite {α : Type u} {β : Type v} [Finite α] {s : Set α} (f : s ↪ β)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by sorry

@[target]
theorem extend_function_of_lt {α β : Type*} {s : Set α} (f : s ↪ β) (hs : #s < #α)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by sorry

end extend

/-! ### Cardinal operations with ordinal indices -/

/-- Bounds the cardinal of an ordinal-indexed union of sets. -/
@[target]
lemma mk_iUnion_Ordinal_lift_le_of_le {β : Type v} {o : Ordinal.{u}} {c : Cardinal.{v}}
    (ho : lift.{v} o.card ≤ lift.{u} c) (hc : ℵ₀ ≤ c) (A : Ordinal → Set β)
    (hA : ∀ j < o, #(A j) ≤ c) : #(⋃ j < o, A j) ≤ c := by sorry

@[target]
lemma mk_iUnion_Ordinal_le_of_le {β : Type*} {o : Ordinal} {c : Cardinal}
    (ho : o.card ≤ c) (hc : ℵ₀ ≤ c) (A : Ordinal → Set β)
    (hA : ∀ j < o, #(A j) ≤ c) : #(⋃ j < o, A j) ≤ c := by sorry

end Cardinal

@[deprecated mk_iUnion_Ordinal_le_of_le (since := "2024-11-02")]
alias Ordinal.Cardinal.mk_iUnion_Ordinal_le_of_le := mk_iUnion_Ordinal_le_of_le

/-! ### Cardinality of ordinals -/

namespace Ordinal

@[target]
theorem lift_card_iSup_le_sum_card {ι : Type u} [Small.{v} ι] (f : ι → Ordinal.{v}) :
    Cardinal.lift.{u} (⨆ i, f i).card ≤ Cardinal.sum fun i ↦ (f i).card := by sorry

@[target]
theorem card_iSup_le_sum_card {ι : Type u} (f : ι → Ordinal.{max u v}) :
    (⨆ i, f i).card ≤ Cardinal.sum (fun i ↦ (f i).card) := by sorry

@[target]
theorem card_iSup_Iio_le_sum_card {o : Ordinal.{u}} (f : Iio o → Ordinal.{max u v}) :
    (⨆ a : Iio o, f a).card ≤ Cardinal.sum fun i ↦ (f ((enumIsoToType o).symm i)).card := by sorry

@[target]
theorem card_iSup_Iio_le_card_mul_iSup {o : Ordinal.{u}} (f : Iio o → Ordinal.{max u v}) :
    (⨆ a : Iio o, f a).card ≤ Cardinal.lift.{v} o.card * ⨆ a : Iio o, (f a).card := by sorry

@[target]
theorem card_opow_le_of_omega0_le_left {a : Ordinal} (ha : ω ≤ a) (b : Ordinal) :
    (a ^ b).card ≤ max a.card b.card := by sorry

@[target]
theorem card_opow_le_of_omega0_le_right (a : Ordinal) {b : Ordinal} (hb : ω ≤ b) :
    (a ^ b).card ≤ max a.card b.card := by sorry

@[target]
theorem card_opow_le (a b : Ordinal) : (a ^ b).card ≤ max ℵ₀ (max a.card b.card) := by sorry

@[target]
theorem card_opow_eq_of_omega0_le_left {a b : Ordinal} (ha : ω ≤ a) (hb : 0 < b) :
    (a ^ b).card = max a.card b.card := by sorry

@[target]
theorem card_opow_eq_of_omega0_le_right {a b : Ordinal} (ha : 1 < a) (hb : ω ≤ b) :
    (a ^ b).card = max a.card b.card := by sorry

@[target]
theorem card_omega0_opow {a : Ordinal} (h : a ≠ 0) : card (ω ^ a) = max ℵ₀ a.card := by sorry

@[target]
theorem card_opow_omega0 {a : Ordinal} (h : 1 < a) : card (a ^ ω) = max ℵ₀ a.card := by sorry

@[target]
theorem principal_opow_omega (o : Ordinal) : Principal (· ^ ·) (ω_ o) := by sorry

@[target]
theorem IsInitial.principal_opow {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    Principal (· ^ ·) o := by sorry

@[target]
theorem principal_opow_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : Principal (· ^ ·) c.ord := by sorry

/-! ### Initial ordinals are principal -/

@[target]
theorem principal_add_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : Principal (· + ·) c.ord := by sorry

@[target]
theorem IsInitial.principal_add {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    Principal (· + ·) o := by sorry

@[target]
theorem principal_add_omega (o : Ordinal) : Principal (· + ·) (ω_ o) := by sorry

@[target]
theorem principal_mul_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : Principal (· * ·) c.ord := by sorry

@[target]
theorem IsInitial.principal_mul {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    Principal (· * ·) o := by sorry

@[target]
theorem principal_mul_omega (o : Ordinal) : Principal (· * ·) (ω_ o) := by sorry

@[target, deprecated principal_add_omega (since := "2024-11-08")]
theorem _root_.Cardinal.principal_add_aleph (o : Ordinal) : Principal (· + ·) (ℵ_ o).ord := by sorry

end Ordinal
