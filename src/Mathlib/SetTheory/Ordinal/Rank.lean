import VerifiedAgora.tagger
/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Rank in a well-founded relation

For `r` a well-founded relation, `IsWellFounded.rank r a` is recursively defined as the least
ordinal greater than the ranks of all elements below `a`.
-/

universe u

variable {α : Type u} {a b : α}

/-! ### Rank of an accessible value -/

namespace Acc

variable {r : α → α → Prop}

/-- The rank of an element `a` accessible under a relation `r` is defined recursively as the
smallest ordinal greater than the ranks of all elements below it (i.e. elements `b` such that
`r b a`). -/
noncomputable def rank (h : Acc r a) : Ordinal.{u} :=
  Acc.recOn h fun a _h ih => ⨆ b : { b // r b a }, Order.succ (ih b b.2)

theorem rank_eq (h : Acc r a) :
    h.rank = ⨆ b : { b // r b a }, Order.succ (h.inv b.2).rank := by
  change (Acc.intro a fun _ => h.inv).rank = _
  rfl

/-- if `r a b` then the rank of `a` is less than the rank of `b`. -/
@[target]
theorem rank_lt_of_rel (hb : Acc r b) (h : r a b) : (hb.inv h).rank < hb.rank := by sorry

@[target]
theorem mem_range_rank_of_le {o : Ordinal} (ha : Acc r a) (ho : o ≤ ha.rank) :
    ∃ (b : α) (hb : Acc r b), hb.rank = o := by sorry

end Acc

/-! ### Rank in a well-founded relation -/

namespace IsWellFounded

variable (r : α → α → Prop) [hwf : IsWellFounded α r]

/-- The rank of an element `a` under a well-founded relation `r` is defined recursively as the
smallest ordinal greater than the ranks of all elements below it (i.e. elements `b` such that
`r b a`). -/
noncomputable def rank (a : α) : Ordinal.{u} :=
  (hwf.apply r a).rank

@[target]
theorem rank_eq (a : α) : rank r a = ⨆ b : { b // r b a }, Order.succ (rank r b) := by sorry

variable {r : α → α → Prop} [hwf : IsWellFounded α r]

@[target]
theorem rank_lt_of_rel (h : r a b) : rank r a < rank r b := by sorry

@[target]
theorem mem_range_rank_of_le {o : Ordinal} (h : o ≤ rank r a) : o ∈ Set.range (rank r) := by sorry

end IsWellFounded

theorem WellFoundedLT.rank_strictMono [Preorder α] [WellFoundedLT α] :
    StrictMono (IsWellFounded.rank (α := α) (· < ·)) :=
  fun _ _ => IsWellFounded.rank_lt_of_rel

theorem WellFoundedGT.rank_strictAnti [Preorder α] [WellFoundedGT α] :
    StrictAnti (IsWellFounded.rank (α := α) (· > ·)) :=
  fun _ _ a => IsWellFounded.rank_lt_of_rel a

@[target, simp]
theorem IsWellFounded.rank_eq_typein (r) [IsWellOrder α r] : rank r = Ordinal.typein r := by sorry

namespace WellFounded

variable {r : α → α → Prop} (hwf : WellFounded r)

/-- The rank of an element `a` under a well-founded relation `r` is defined inductively as the
smallest ordinal greater than the ranks of all elements below it (i.e. elements `b` such that
`r b a`). -/
@[deprecated IsWellFounded.rank (since := "2024-09-07")]
noncomputable def rank (a : α) : Ordinal.{u} :=
  (hwf.apply a).rank

set_option linter.deprecated false in
@[target, deprecated IsWellFounded.rank_eq (since := "2024-09-07")]
theorem rank_eq : hwf.rank a = ⨆ b : { b // r b a }, Order.succ (hwf.rank b) := by sorry

set_option linter.deprecated false in
@[target, deprecated IsWellFounded.rank_lt_of_rel (since := "2024-09-07")]
theorem rank_lt_of_rel (h : r a b) : hwf.rank a < hwf.rank b := by sorry

set_option linter.deprecated false in
@[deprecated WellFoundedLT.rank_strictMono (since := "2024-09-07")]
theorem rank_strictMono [Preorder α] [WellFoundedLT α] :
    StrictMono (rank <| @wellFounded_lt α _ _) := fun _ _ => rank_lt_of_rel _

set_option linter.deprecated false in
@[deprecated WellFoundedGT.rank_strictAnti (since := "2024-09-07")]
theorem rank_strictAnti [Preorder α] [WellFoundedGT α] :
    StrictAnti (rank <| @wellFounded_gt α _ _) := fun _ _ => rank_lt_of_rel wellFounded_gt

end WellFounded
