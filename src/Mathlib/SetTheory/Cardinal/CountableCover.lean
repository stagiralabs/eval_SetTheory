import VerifiedAgora.tagger
/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.Map

/-!
# Cardinality of a set with a countable cover

Assume that a set `t` is eventually covered by a countable family of sets, all with
cardinality `≤ a`. Then `t` itself has cardinality at most `a`. This is proved in
`Cardinal.mk_subtype_le_of_countable_eventually_mem`.

Versions are also given when `t = univ`, and with `= a` instead of `≤ a`.
-/

open Set Order Filter
open scoped Cardinal

namespace Cardinal

universe u v

/-- If a set `t` is eventually covered by a countable family of sets, all with cardinality at
most `a`, then the cardinality of `t` is also bounded by `a`.
Superseded by `mk_le_of_countable_eventually_mem` which does not assume
that the indexing set lives in the same universe. -/
@[target]
lemma mk_subtype_le_of_countable_eventually_mem_aux {α ι : Type u} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l]
    {t : Set α} (ht : ∀ x ∈ t, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #t ≤ a := by sorry

/-- If a set `t` is eventually covered by a countable family of sets, all with cardinality at
most `a`, then the cardinality of `t` is also bounded by `a`. -/
lemma mk_subtype_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l]
    {t : Set α} (ht : ∀ x ∈ t, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #t ≤ a := by
  let g : ULift.{u, v} ι → Set (ULift.{v, u} α) := (ULift.down ⁻¹' ·) ∘ f ∘ ULift.down
  suffices #(ULift.down.{v} ⁻¹' t) ≤ Cardinal.lift.{v, u} a by simpa
  let l' : Filter (ULift.{u} ι) := Filter.map ULift.up l
  have : NeBot l' := map_neBot
  apply mk_subtype_le_of_countable_eventually_mem_aux (ι := ULift.{u} ι) (l := l') (f := g)
  · intro x hx
    simpa only [Function.comp_apply, mem_preimage, eventually_map] using ht _ hx
  · intro i
    simpa [g] using h'f i.down

/-- If a space is eventually covered by a countable family of sets, all with cardinality at
most `a`, then the cardinality of the space is also bounded by `a`. -/
lemma mk_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l] (ht : ∀ x, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) ≤ a) : #α ≤ a := by
  rw [← mk_univ]
  exact mk_subtype_le_of_countable_eventually_mem (l := l) (fun x _ ↦ ht x) h'f

/-- If a space is eventually covered by a countable family of sets, all with cardinality `a`,
then the cardinality of the space is also `a`. -/
@[target]
lemma mk_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι → Set α} {l : Filter ι} [NeBot l] (ht : ∀ x, ∀ᶠ i in l, x ∈ f i)
    (h'f : ∀ i, #(f i) = a) : #α = a := by sorry

end Cardinal
