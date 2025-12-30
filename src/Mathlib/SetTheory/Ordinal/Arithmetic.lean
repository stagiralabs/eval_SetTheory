import VerifiedAgora.tagger
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.SuccPred.InitialSeg
import Mathlib.SetTheory.Cardinal.UnivLE
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Ordinal arithmetic

Ordinals have an addition (corresponding to disjoint union) that turns them into an additive
monoid, and a multiplication (corresponding to the lexicographic order on the product) that turns
them into a monoid. One can also define correspondingly a subtraction, a division, a successor
function, a power function and a logarithm function.

We also define limit ordinals and prove the basic induction principle on ordinals separating
successor ordinals and limit ordinals, in `limitRecOn`.

## Main definitions and results

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
* `o₁ - o₂` is the unique ordinal `o` such that `o₂ + o = o₁`, when `o₂ ≤ o₁`.
* `o₁ * o₂` is the lexicographic order on `o₂ × o₁`.
* `o₁ / o₂` is the ordinal `o` such that `o₁ = o₂ * o + o'` with `o' < o₂`. We also define the
  divisibility predicate, and a modulo operation.
* `Order.succ o = o + 1` is the successor of `o`.
* `pred o` if the predecessor of `o`. If `o` is not a successor, we set `pred o = o`.

We discuss the properties of casts of natural numbers of and of `ω` with respect to these
operations.

Some properties of the operations are also used to discuss general tools on ordinals:

* `IsLimit o`: an ordinal is a limit ordinal if it is neither `0` nor a successor.
* `limitRecOn` is the main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals.
* `IsNormal`: a function `f : Ordinal → Ordinal` satisfies `IsNormal` if it is strictly increasing
  and order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.
* `sup`, `lsub`: the supremum / least strict upper bound of an indexed family of ordinals in
  `Type u`, as an ordinal in `Type u`.
* `bsup`, `blsub`: the supremum / least strict upper bound of a set of ordinals indexed by ordinals
  less than a given ordinal `o`.

Various other basic arithmetic results are given in `Principal.lean` instead.
-/

assert_not_exists Field Module

noncomputable section

open Function Cardinal Set Equiv Order
open scoped Ordinal

universe u v w

namespace Ordinal

variable {α β γ : Type*} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Further properties of addition on ordinals -/

@[target, simp]
theorem lift_add (a b : Ordinal.{v}) : lift.{u} (a + b) = lift.{u} a + lift.{u} b := by sorry

@[simp]
theorem lift_succ (a : Ordinal.{v}) : lift.{u} (succ a) = succ (lift.{u} a) := by
  rw [← add_one_eq_succ, lift_add, lift_one]
  rfl

instance instAddLeftReflectLE :
    AddLeftReflectLE Ordinal.{u} where
  elim c a b := by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ ↦ ?_
    have H₁ a : f (Sum.inl a) = Sum.inl a := by
      simpa using ((InitialSeg.leAdd t r).trans f).eq (InitialSeg.leAdd t s) a
    have H₂ a : ∃ b, f (Sum.inr a) = Sum.inr b := by
      generalize hx : f (Sum.inr a) = x
      obtain x | x := x
      · rw [← H₁, f.inj] at hx
        contradiction
      · exact ⟨x, rfl⟩
    choose g hg using H₂
    refine (RelEmbedding.ofMonotone g fun _ _ h ↦ ?_).ordinal_type_le
    rwa [← @Sum.lex_inr_inr _ t _ s, ← hg, ← hg, f.map_rel_iff, Sum.lex_inr_inr]

instance : IsLeftCancelAdd Ordinal where
  add_left_cancel a b c h := by simpa only [le_antisymm_iff, add_le_add_iff_left] using h

@[deprecated add_left_cancel_iff (since := "2024-12-11")]
protected theorem add_left_cancel (a) {b c : Ordinal} : a + b = a + c ↔ b = c :=
  add_left_cancel_iff

private theorem add_lt_add_iff_left' (a) {b c : Ordinal} : a + b < a + c ↔ b < c := by
  rw [← not_le, ← not_le, add_le_add_iff_left]

instance instAddLeftStrictMono : AddLeftStrictMono Ordinal.{u} :=
  ⟨fun a _b _c ↦ (add_lt_add_iff_left' a).2⟩

instance instAddLeftReflectLT : AddLeftReflectLT Ordinal.{u} :=
  ⟨fun a _b _c ↦ (add_lt_add_iff_left' a).1⟩

instance instAddRightReflectLT : AddRightReflectLT Ordinal.{u} :=
  ⟨fun _a _b _c ↦ lt_imp_lt_of_le_imp_le fun h => add_le_add_right h _⟩

@[target]
theorem add_le_add_iff_right {a b : Ordinal} : ∀ n : ℕ, a + n ≤ b + n ↔ a ≤ b := by sorry

@[target]
theorem add_right_cancel {a b : Ordinal} (n : ℕ) : a + n = b + n ↔ a = b := by sorry

@[target]
theorem add_eq_zero_iff {a b : Ordinal} : a + b = 0 ↔ a = 0 ∧ b = 0 := by sorry

@[target]
theorem left_eq_zero_of_add_eq_zero {a b : Ordinal} (h : a + b = 0) : a = 0 := by sorry

@[target]
theorem right_eq_zero_of_add_eq_zero {a b : Ordinal} (h : a + b = 0) : b = 0 := by sorry

/-! ### The predecessor of an ordinal -/

open Classical in
/-- The ordinal predecessor of `o` is `o'` if `o = succ o'`,
  and `o` otherwise. -/
def pred (o : Ordinal) : Ordinal :=
  if h : ∃ a, o = succ a then Classical.choose h else o

@[target, simp]
theorem pred_succ (o) : pred (succ o) = o := by sorry

@[target]
theorem pred_le_self (o) : pred o ≤ o := by sorry

@[target]
theorem pred_eq_iff_not_succ {o} : pred o = o ↔ ¬∃ a, o = succ a := by sorry

@[target]
theorem pred_eq_iff_not_succ' {o} : pred o = o ↔ ∀ a, o ≠ succ a := by sorry

@[target]
theorem pred_lt_iff_is_succ {o} : pred o < o ↔ ∃ a, o = succ a := by sorry

@[target, simp]
theorem pred_zero : pred 0 = 0 := by sorry

@[target]
theorem succ_pred_iff_is_succ {o} : succ (pred o) = o ↔ ∃ a, o = succ a := by sorry

@[target]
theorem succ_lt_of_not_succ {o b : Ordinal} (h : ¬∃ a, o = succ a) : succ b < o ↔ b < o := by sorry

@[target]
theorem lt_pred {a b} : a < pred b ↔ succ a < b := by sorry

@[target]
theorem pred_le {a b} : pred a ≤ b ↔ a ≤ succ b := by sorry

@[target, simp]
theorem lift_is_succ {o : Ordinal.{v}} : (∃ a, lift.{u} o = succ a) ↔ ∃ a, o = succ a := by sorry

@[target, simp]
theorem lift_pred (o : Ordinal.{v}) : lift.{u} (pred o) = pred (lift.{u} o) := by sorry

/-! ### Limit ordinals -/


/-- A limit ordinal is an ordinal which is not zero and not a successor.

TODO: deprecate this in favor of `Order.IsSuccLimit`. -/
def IsLimit (o : Ordinal) : Prop :=
  IsSuccLimit o

@[target]
theorem isLimit_iff {o} : IsLimit o ↔ o ≠ 0 ∧ IsSuccPrelimit o := by sorry

@[target]
theorem IsLimit.isSuccPrelimit {o} (h : IsLimit o) : IsSuccPrelimit o := by sorry

@[deprecated IsLimit.isSuccPrelimit (since := "2024-09-05")]
alias IsLimit.isSuccLimit := IsLimit.isSuccPrelimit

theorem IsLimit.succ_lt {o a : Ordinal} (h : IsLimit o) : a < o → succ a < o :=
  IsSuccLimit.succ_lt h

@[target]
theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Ordinal) := by sorry

@[deprecated isSuccPrelimit_zero (since := "2024-09-05")]
alias isSuccLimit_zero := isSuccPrelimit_zero

@[target]
theorem not_zero_isLimit : ¬IsLimit 0 := by sorry

@[target]
theorem not_succ_isLimit (o) : ¬IsLimit (succ o) := by sorry

@[target]
theorem not_succ_of_isLimit {o} (h : IsLimit o) : ¬∃ a, o = succ a := by sorry

@[target]
theorem succ_lt_of_isLimit {o a : Ordinal} (h : IsLimit o) : succ a < o ↔ a < o := by sorry

@[target]
theorem le_succ_of_isLimit {o} (h : IsLimit o) {a} : o ≤ succ a ↔ o ≤ a := by sorry

@[target]
theorem limit_le {o} (h : IsLimit o) {a} : o ≤ a ↔ ∀ x < o, x ≤ a := by sorry

@[target]
theorem lt_limit {o} (h : IsLimit o) {a} : a < o ↔ ∃ x < o, a < x := by sorry

@[target, simp]
theorem lift_isLimit (o : Ordinal.{v}) : IsLimit (lift.{u,v} o) ↔ IsLimit o := by sorry

@[target]
theorem IsLimit.pos {o : Ordinal} (h : IsLimit o) : 0 < o := by sorry

theorem IsLimit.ne_zero {o : Ordinal} (h : IsLimit o) : o ≠ 0 :=
  h.pos.ne'

@[target]
theorem IsLimit.one_lt {o : Ordinal} (h : IsLimit o) : 1 < o := by sorry

@[target]
theorem IsLimit.nat_lt {o : Ordinal} (h : IsLimit o) : ∀ n : ℕ, (n : Ordinal) < o := by sorry

@[target]
theorem zero_or_succ_or_limit (o : Ordinal) : o = 0 ∨ (∃ a, o = succ a) ∨ IsLimit o := by sorry

@[target]
theorem isLimit_of_not_succ_of_ne_zero {o : Ordinal} (h : ¬∃ a, o = succ a) (h' : o ≠ 0) :
    IsLimit o := by sorry

@[target]
theorem IsLimit.sSup_Iio {o : Ordinal} (h : IsLimit o) : sSup (Iio o) = o := by sorry

@[target]
theorem IsLimit.iSup_Iio {o : Ordinal} (h : IsLimit o) : ⨆ a : Iio o, a.1 = o := by sorry

/-- Main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals. -/
@[elab_as_elim]
def limitRecOn {C : Ordinal → Sort*} (o : Ordinal) (H₁ : C 0) (H₂ : ∀ o, C o → C (succ o))
    (H₃ : ∀ o, IsLimit o → (∀ o' < o, C o') → C o) : C o := by
  refine SuccOrder.limitRecOn o (fun a ha ↦ ?_) (fun a _ ↦ H₂ a) H₃
  convert H₁
  simpa using ha

@[target, simp]
theorem limitRecOn_zero {C} (H₁ H₂ H₃) : @limitRecOn C 0 H₁ H₂ H₃ = H₁ := by sorry

@[target, simp]
theorem limitRecOn_succ {C} (o H₁ H₂ H₃) :
    @limitRecOn C (succ o) H₁ H₂ H₃ = H₂ o (@limitRecOn C o H₁ H₂ H₃) := by sorry

@[target, simp]
theorem limitRecOn_limit {C} (o H₁ H₂ H₃ h) :
    @limitRecOn C o H₁ H₂ H₃ = H₃ o h fun x _h => @limitRecOn C x H₁ H₂ H₃ := by sorry

/-- Bounded recursion on ordinals. Similar to `limitRecOn`, with the assumption `o < l`
  added to all cases. The final term's domain is the ordinals below `l`. -/
@[elab_as_elim]
def boundedLimitRecOn {l : Ordinal} (lLim : l.IsLimit) {C : Iio l → Sort*} (o : Iio l)
    (H₁ : C ⟨0, lLim.pos⟩) (H₂ : (o : Iio l) → C o → C ⟨succ o, lLim.succ_lt o.2⟩)
    (H₃ : (o : Iio l) → IsLimit o → (Π o' < o, C o') → C o) : C o :=
  limitRecOn (C := fun p ↦ (h : p < l) → C ⟨p, h⟩) o.1 (fun _ ↦ H₁)
    (fun o ih h ↦ H₂ ⟨o, _⟩ <| ih <| (lt_succ o).trans h)
    (fun _o ho ih _ ↦ H₃ _ ho fun _o' h ↦ ih _ h _) o.2

@[target, simp]
theorem boundedLimitRec_zero {l} (lLim : l.IsLimit) {C} (H₁ H₂ H₃) :
    @boundedLimitRecOn l lLim C ⟨0, lLim.pos⟩ H₁ H₂ H₃ = H₁ := by sorry

@[target, simp]
theorem boundedLimitRec_succ {l} (lLim : l.IsLimit) {C} (o H₁ H₂ H₃) :
    @boundedLimitRecOn l lLim C ⟨succ o.1, lLim.succ_lt o.2⟩ H₁ H₂ H₃ = H₂ o
    (@boundedLimitRecOn l lLim C o H₁ H₂ H₃) := by sorry

@[target]
theorem boundedLimitRec_limit {l} (lLim : l.IsLimit) {C} (o H₁ H₂ H₃ oLim) :
    @boundedLimitRecOn l lLim C o H₁ H₂ H₃ = H₃ o oLim (fun x _ ↦
    @boundedLimitRecOn l lLim C x H₁ H₂ H₃) := by sorry

instance orderTopToTypeSucc (o : Ordinal) : OrderTop (succ o).toType :=
  @OrderTop.mk _ _ (Top.mk _) le_enum_succ

@[target]
theorem enum_succ_eq_top {o : Ordinal} :
    enum (α := (succ o).toType) (· < ·) ⟨o, type_toType _ ▸ lt_succ o⟩ = ⊤ := by sorry

@[target]
theorem has_succ_of_type_succ_lt {α} {r : α → α → Prop} [wo : IsWellOrder α r]
    (h : ∀ a < type r, succ a < type r) (x : α) : ∃ y, r x y := by sorry

@[target]
theorem toType_noMax_of_succ_lt {o : Ordinal} (ho : ∀ a < o, succ a < o) : NoMaxOrder o.toType := by sorry

@[deprecated toType_noMax_of_succ_lt (since := "2024-08-26")]
alias out_no_max_of_succ_lt := toType_noMax_of_succ_lt

@[target]
theorem bounded_singleton {r : α → α → Prop} [IsWellOrder α r] (hr : (type r).IsLimit) (x) :
    Bounded r {x} := by sorry

@[target, simp]
theorem typein_ordinal (o : Ordinal.{u}) :
    @typein Ordinal (· < ·) _ o = Ordinal.lift.{u + 1} o := by sorry

@[target]
theorem mk_Iio_ordinal (o : Ordinal.{u}) :
    #(Iio o) = Cardinal.lift.{u + 1} o.card := by sorry

@[target, deprecated mk_Iio_ordinal (since := "2024-09-19")]
theorem mk_initialSeg (o : Ordinal.{u}) :
    #{ o' : Ordinal | o' < o } = Cardinal.lift.{u + 1} o.card := by sorry

/-! ### Normal ordinal functions -/


/-- A normal ordinal function is a strictly increasing function which is
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`. -/
def IsNormal (f : Ordinal → Ordinal) : Prop :=
  (∀ o, f o < f (succ o)) ∧ ∀ o, IsLimit o → ∀ a, f o ≤ a ↔ ∀ b < o, f b ≤ a

@[target]
theorem IsNormal.limit_le {f} (H : IsNormal f) :
    ∀ {o}, IsLimit o → ∀ {a}, f o ≤ a ↔ ∀ b < o, f b ≤ a := by sorry

@[target]
theorem IsNormal.limit_lt {f} (H : IsNormal f) {o} (h : IsLimit o) {a} :
    a < f o ↔ ∃ b < o, a < f b := by sorry

@[target]
theorem IsNormal.strictMono {f} (H : IsNormal f) : StrictMono f := by sorry

@[target]
theorem IsNormal.monotone {f} (H : IsNormal f) : Monotone f := by sorry

theorem isNormal_iff_strictMono_limit (f : Ordinal → Ordinal) :
    IsNormal f ↔ StrictMono f ∧ ∀ o, IsLimit o → ∀ a, (∀ b < o, f b ≤ a) → f o ≤ a :=
  ⟨fun hf => ⟨hf.strictMono, fun a ha c => (hf.2 a ha c).2⟩, fun ⟨hs, hl⟩ =>
    ⟨fun a => hs (lt_succ a), fun a ha c =>
      ⟨fun hac _b hba => ((hs hba).trans_le hac).le, hl a ha c⟩⟩⟩

@[target]
theorem IsNormal.lt_iff {f} (H : IsNormal f) {a b} : f a < f b ↔ a < b := by sorry

@[target]
theorem IsNormal.le_iff {f} (H : IsNormal f) {a b} : f a ≤ f b ↔ a ≤ b := by sorry

@[target]
theorem IsNormal.inj {f} (H : IsNormal f) {a b} : f a = f b ↔ a = b := by sorry

@[target]
theorem IsNormal.id_le {f} (H : IsNormal f) : id ≤ f := by sorry

@[target]
theorem IsNormal.le_apply {f} (H : IsNormal f) {a} : a ≤ f a := by sorry

@[deprecated IsNormal.le_apply (since := "2024-09-11")]
theorem IsNormal.self_le {f} (H : IsNormal f) (a) : a ≤ f a :=
  H.strictMono.le_apply

@[target]
theorem IsNormal.le_iff_eq {f} (H : IsNormal f) {a} : f a ≤ a ↔ f a = a := by sorry

theorem IsNormal.le_set {f o} (H : IsNormal f) (p : Set Ordinal) (p0 : p.Nonempty) (b)
    (H₂ : ∀ o, b ≤ o ↔ ∀ a ∈ p, a ≤ o) : f b ≤ o ↔ ∀ a ∈ p, f a ≤ o :=
  ⟨fun h _ pa => (H.le_iff.2 ((H₂ _).1 le_rfl _ pa)).trans h, fun h => by
    -- Porting note: `refine'` didn't work well so `induction` is used
    induction b using limitRecOn with
    | H₁ =>
      obtain ⟨x, px⟩ := p0
      have := Ordinal.le_zero.1 ((H₂ _).1 (Ordinal.zero_le _) _ px)
      rw [this] at px
      exact h _ px
    | H₂ S _ =>
      rcases not_forall₂.1 (mt (H₂ S).2 <| (lt_succ S).not_le) with ⟨a, h₁, h₂⟩
      exact (H.le_iff.2 <| succ_le_of_lt <| not_le.1 h₂).trans (h _ h₁)
    | H₃ S L _ =>
      refine (H.2 _ L _).2 fun a h' => ?_
      rcases not_forall₂.1 (mt (H₂ a).2 h'.not_le) with ⟨b, h₁, h₂⟩
      exact (H.le_iff.2 <| (not_le.1 h₂).le).trans (h _ h₁)⟩

@[target]
theorem IsNormal.le_set' {f o} (H : IsNormal f) (p : Set α) (p0 : p.Nonempty) (g : α → Ordinal) (b)
    (H₂ : ∀ o, b ≤ o ↔ ∀ a ∈ p, g a ≤ o) : f b ≤ o ↔ ∀ a ∈ p, f (g a) ≤ o := by sorry

@[target]
theorem IsNormal.refl : IsNormal id := by sorry

@[target]
theorem IsNormal.trans {f g} (H₁ : IsNormal f) (H₂ : IsNormal g) : IsNormal (f ∘ g) := by sorry

@[target]
theorem IsNormal.isLimit {f} (H : IsNormal f) {o} (ho : IsLimit o) : IsLimit (f o) := by sorry

private theorem add_le_of_limit {a b c : Ordinal} (h : IsLimit b) :
    a + b ≤ c ↔ ∀ b' < b, a + b' ≤ c :=
  ⟨fun h _ l => (add_le_add_left l.le _).trans h, fun H =>
    le_of_not_lt <| by
      -- Porting note: `induction` tactics are required because of the parser bug.
      induction a using inductionOn with
      | H α r =>
        induction b using inductionOn with
        | H β s =>
          intro l
          suffices ∀ x : β, Sum.Lex r s (Sum.inr x) (enum _ ⟨_, l⟩) by
            -- Porting note: `revert` & `intro` is required because `cases'` doesn't replace
            --               `enum _ _ l` in `this`.
            revert this; rcases enum _ ⟨_, l⟩ with x | x <;> intro this
            · cases this (enum s ⟨0, h.pos⟩)
            · exact irrefl _ (this _)
          intro x
          rw [← typein_lt_typein (Sum.Lex r s), typein_enum]
          have := H _ (h.succ_lt (typein_lt_type s x))
          rw [add_succ, succ_le_iff] at this
          refine
            (RelEmbedding.ofMonotone (fun a => ?_) fun a b => ?_).ordinal_type_le.trans_lt this
          · rcases a with ⟨a | b, h⟩
            · exact Sum.inl a
            · exact Sum.inr ⟨b, by cases h; assumption⟩
          · rcases a with ⟨a | a, h₁⟩ <;> rcases b with ⟨b | b, h₂⟩ <;> cases h₁ <;> cases h₂ <;>
              rintro ⟨⟩ <;> constructor <;> assumption⟩

@[target]
theorem isNormal_add_right (a : Ordinal) : IsNormal (a + ·) := by sorry

@[deprecated isNormal_add_right (since := "2024-10-11")]
alias add_isNormal := isNormal_add_right

@[target]
theorem isLimit_add (a) {b} : IsLimit b → IsLimit (a + b) := by sorry

@[deprecated isLimit_add (since := "2024-10-11")]
alias add_isLimit := isLimit_add

alias IsLimit.add := add_isLimit

/-! ### Subtraction on ordinals -/


/-- The set in the definition of subtraction is nonempty. -/
private theorem sub_nonempty {a b : Ordinal} : { o | a ≤ b + o }.Nonempty :=
  ⟨a, le_add_left _ _⟩

/-- `a - b` is the unique ordinal satisfying `b + (a - b) = a` when `b ≤ a`. -/
instance sub : Sub Ordinal :=
  ⟨fun a b => sInf { o | a ≤ b + o }⟩

@[target]
theorem le_add_sub (a b : Ordinal) : a ≤ b + (a - b) := by sorry

theorem sub_le {a b c : Ordinal} : a - b ≤ c ↔ a ≤ b + c :=
  ⟨fun h => (le_add_sub a b).trans (add_le_add_left h _), fun h => csInf_le' h⟩

@[target]
theorem lt_sub {a b c : Ordinal} : a < b - c ↔ c + a < b := by sorry

@[target]
theorem add_sub_cancel (a b : Ordinal) : a + b - a = b := by sorry

@[target]
theorem sub_eq_of_add_eq {a b c : Ordinal} (h : a + b = c) : c - a = b := by sorry

@[target]
theorem sub_le_self (a b : Ordinal) : a - b ≤ a := by sorry

protected theorem add_sub_cancel_of_le {a b : Ordinal} (h : b ≤ a) : b + (a - b) = a :=
  (le_add_sub a b).antisymm'
    (by
      rcases zero_or_succ_or_limit (a - b) with (e | ⟨c, e⟩ | l)
      · simp only [e, add_zero, h]
      · rw [e, add_succ, succ_le_iff, ← lt_sub, e]
        exact lt_succ c
      · exact (add_le_of_limit l).2 fun c l => (lt_sub.1 l).le)

theorem le_sub_of_le {a b c : Ordinal} (h : b ≤ a) : c ≤ a - b ↔ b + c ≤ a := by
  rw [← add_le_add_iff_left b, Ordinal.add_sub_cancel_of_le h]

@[target]
theorem sub_lt_of_le {a b c : Ordinal} (h : b ≤ a) : a - b < c ↔ a < b + c := by sorry

instance existsAddOfLE : ExistsAddOfLE Ordinal :=
  ⟨fun h => ⟨_, (Ordinal.add_sub_cancel_of_le h).symm⟩⟩

@[target, simp]
theorem sub_zero (a : Ordinal) : a - 0 = a := by sorry

@[target, simp]
theorem zero_sub (a : Ordinal) : 0 - a = 0 := by sorry

@[target, simp]
theorem sub_self (a : Ordinal) : a - a = 0 := by sorry

protected theorem sub_eq_zero_iff_le {a b : Ordinal} : a - b = 0 ↔ a ≤ b :=
  ⟨fun h => by simpa only [h, add_zero] using le_add_sub a b, fun h => by
    rwa [← Ordinal.le_zero, sub_le, add_zero]⟩

protected theorem sub_ne_zero_iff_lt {a b : Ordinal} : a - b ≠ 0 ↔ b < a := by
  simpa using Ordinal.sub_eq_zero_iff_le.not

@[target]
theorem sub_sub (a b c : Ordinal) : a - b - c = a - (b + c) := by sorry

@[target, simp]
theorem add_sub_add_cancel (a b c : Ordinal) : a + b - (a + c) = b - c := by sorry

@[target]
theorem le_sub_of_add_le {a b c : Ordinal} (h : b + c ≤ a) : c ≤ a - b := by sorry

@[target]
theorem sub_lt_of_lt_add {a b c : Ordinal} (h : a < b + c) (hc : 0 < c) : a - b < c := by sorry

@[target]
theorem lt_add_iff {a b c : Ordinal} (hc : c ≠ 0) : a < b + c ↔ ∃ d < c, a ≤ b + d := by sorry

@[target]
theorem add_le_iff {a b c : Ordinal} (hb : b ≠ 0) : a + b ≤ c ↔ ∀ d < b, a + d < c := by sorry

@[target, deprecated add_le_iff (since := "2024-12-08")]
theorem add_le_of_forall_add_lt {a b c : Ordinal} (hb : 0 < b) (h : ∀ d < b, a + d < c) :
    a + b ≤ c := by sorry

@[target]
theorem isLimit_sub {a b} (ha : IsLimit a) (h : b < a) : IsLimit (a - b) := by sorry

@[deprecated isLimit_sub (since := "2024-10-11")]
alias sub_isLimit := isLimit_sub

/-! ### Multiplication of ordinals -/


/-- The multiplication of ordinals `o₁` and `o₂` is the (well founded) lexicographic order on
`o₂ × o₁`. -/
instance monoid : Monoid Ordinal.{u} where
  mul a b :=
    Quotient.liftOn₂ a b
      (fun ⟨α, r, _⟩ ⟨β, s, _⟩ => ⟦⟨β × α, Prod.Lex s r, inferInstance⟩⟧ :
        WellOrder → WellOrder → Ordinal)
      fun ⟨_, _, _⟩ _ _ _ ⟨f⟩ ⟨g⟩ => Quot.sound ⟨RelIso.prodLexCongr g f⟩
  one := 1
  mul_assoc a b c :=
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
      Eq.symm <|
        Quotient.sound
          ⟨⟨prodAssoc _ _ _, @fun a b => by
              rcases a with ⟨⟨a₁, a₂⟩, a₃⟩
              rcases b with ⟨⟨b₁, b₂⟩, b₃⟩
              simp [Prod.lex_def, and_or_left, or_assoc, and_assoc]⟩⟩
  mul_one a :=
    inductionOn a fun α r _ =>
      Quotient.sound
        ⟨⟨punitProd _, @fun a b => by
            rcases a with ⟨⟨⟨⟩⟩, a⟩; rcases b with ⟨⟨⟨⟩⟩, b⟩
            simp only [Prod.lex_def, EmptyRelation, false_or]
            simp only [eq_self_iff_true, true_and]
            rfl⟩⟩
  one_mul a :=
    inductionOn a fun α r _ =>
      Quotient.sound
        ⟨⟨prodPUnit _, @fun a b => by
            rcases a with ⟨a, ⟨⟨⟩⟩⟩; rcases b with ⟨b, ⟨⟨⟩⟩⟩
            simp only [Prod.lex_def, EmptyRelation, and_false, or_false]
            rfl⟩⟩

@[target, simp]
theorem type_prod_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r]
    [IsWellOrder β s] : type (Prod.Lex s r) = type r * type s := by sorry

private theorem mul_eq_zero' {a b : Ordinal} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  inductionOn a fun α _ _ =>
    inductionOn b fun β _ _ => by
      simp_rw [← type_prod_lex, type_eq_zero_iff_isEmpty]
      rw [or_comm]
      exact isEmpty_prod

instance monoidWithZero : MonoidWithZero Ordinal :=
  { Ordinal.monoid with
    zero := 0
    mul_zero := fun _a => mul_eq_zero'.2 <| Or.inr rfl
    zero_mul := fun _a => mul_eq_zero'.2 <| Or.inl rfl }

instance noZeroDivisors : NoZeroDivisors Ordinal :=
  ⟨fun {_ _} => mul_eq_zero'.1⟩

@[target, simp]
theorem lift_mul (a b : Ordinal.{v}) : lift.{u} (a * b) = lift.{u} a * lift.{u} b := by sorry

@[target, simp]
theorem card_mul (a b) : card (a * b) = card a * card b := by sorry

instance leftDistribClass : LeftDistribClass Ordinal.{u} :=
  ⟨fun a b c =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
      Quotient.sound
        ⟨⟨sumProdDistrib _ _ _, by
          rintro ⟨a₁ | a₁, a₂⟩ ⟨b₁ | b₁, b₂⟩ <;>
            simp only [Prod.lex_def, Sum.lex_inl_inl, Sum.Lex.sep, Sum.lex_inr_inl, Sum.lex_inr_inr,
              sumProdDistrib_apply_left, sumProdDistrib_apply_right, reduceCtorEq] <;>
            -- Porting note: `Sum.inr.inj_iff` is required.
            simp only [Sum.inl.inj_iff, Sum.inr.inj_iff, true_or, false_and, false_or]⟩⟩⟩

@[target]
theorem mul_succ (a b : Ordinal) : a * succ b = a * b + a := by sorry

instance mulLeftMono : MulLeftMono Ordinal.{u} :=
  ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : α × γ => (f a.1, a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ (f.toRelEmbedding.map_rel_iff.2 h')
      · exact Prod.Lex.right _ h'⟩

instance mulRightMono : MulRightMono Ordinal.{u} :=
  ⟨fun c a b =>
    Quotient.inductionOn₃ a b c fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      refine
        (RelEmbedding.ofMonotone (fun a : γ × α => (a.1, f a.2)) fun a b h => ?_).ordinal_type_le
      obtain ⟨-, -, h'⟩ | ⟨-, h'⟩ := h
      · exact Prod.Lex.left _ _ h'
      · exact Prod.Lex.right _ (f.toRelEmbedding.map_rel_iff.2 h')⟩

@[target]
theorem le_mul_left (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a ≤ a * b := by sorry

@[target]
theorem le_mul_right (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a ≤ b * a := by sorry

private theorem mul_le_of_limit_aux {α β r s} [IsWellOrder α r] [IsWellOrder β s] {c}
    (h : IsLimit (type s)) (H : ∀ b' < type s, type r * b' ≤ c) (l : c < type r * type s) :
    False := by
  suffices ∀ a b, Prod.Lex s r (b, a) (enum _ ⟨_, l⟩) by
    obtain ⟨b, a⟩ := enum _ ⟨_, l⟩
    exact irrefl _ (this _ _)
  intro a b
  rw [← typein_lt_typein (Prod.Lex s r), typein_enum]
  have := H _ (h.succ_lt (typein_lt_type s b))
  rw [mul_succ] at this
  have := ((add_lt_add_iff_left _).2 (typein_lt_type _ a)).trans_le this
  refine (RelEmbedding.ofMonotone (fun a => ?_) fun a b => ?_).ordinal_type_le.trans_lt this
  · rcases a with ⟨⟨b', a'⟩, h⟩
    by_cases e : b = b'
    · refine Sum.inr ⟨a', ?_⟩
      subst e
      obtain ⟨-, -, h⟩ | ⟨-, h⟩ := h
      · exact (irrefl _ h).elim
      · exact h
    · refine Sum.inl (⟨b', ?_⟩, a')
      obtain ⟨-, -, h⟩ | ⟨e, h⟩ := h
      · exact h
      · exact (e rfl).elim
  · rcases a with ⟨⟨b₁, a₁⟩, h₁⟩
    rcases b with ⟨⟨b₂, a₂⟩, h₂⟩
    intro h
    by_cases e₁ : b = b₁ <;> by_cases e₂ : b = b₂
    · substs b₁ b₂
      simpa only [subrel_val, Prod.lex_def, @irrefl _ s _ b, true_and, false_or,
        eq_self_iff_true, dif_pos, Sum.lex_inr_inr] using h
    · subst b₁
      simp only [subrel_val, Prod.lex_def, e₂, Prod.lex_def, dif_pos, subrel_val, eq_self_iff_true,
        or_false, dif_neg, not_false_iff, Sum.lex_inr_inl, false_and] at h ⊢
      obtain ⟨-, -, h₂_h⟩ | e₂ := h₂ <;> [exact asymm h h₂_h; exact e₂ rfl]
    · simp [e₂, dif_neg e₁, show b₂ ≠ b₁ from e₂ ▸ e₁]
    · simpa only [dif_neg e₁, dif_neg e₂, Prod.lex_def, subrel_val, Subtype.mk_eq_mk,
        Sum.lex_inl_inl] using h

@[target]
theorem mul_le_of_limit {a b c : Ordinal} (h : IsLimit b) : a * b ≤ c ↔ ∀ b' < b, a * b' ≤ c := by sorry

@[target]
theorem isNormal_mul_right {a : Ordinal} (h : 0 < a) : IsNormal (a * ·) := by sorry

@[deprecated isNormal_mul_right (since := "2024-10-11")]
alias mul_isNormal := isNormal_mul_right

@[target]
theorem lt_mul_of_limit {a b c : Ordinal} (h : IsLimit c) : a < b * c ↔ ∃ c' < c, a < b * c' := by sorry

@[target]
theorem mul_lt_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : a * b < a * c ↔ b < c := by sorry

@[target]
theorem mul_le_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c := by sorry

@[target]
theorem mul_lt_mul_of_pos_left {a b c : Ordinal} (h : a < b) (c0 : 0 < c) : c * a < c * b := by sorry

@[target]
theorem mul_pos {a b : Ordinal} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b := by sorry

@[target]
theorem mul_ne_zero {a b : Ordinal} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by sorry

@[target]
theorem le_of_mul_le_mul_left {a b c : Ordinal} (h : c * a ≤ c * b) (h0 : 0 < c) : a ≤ b := by sorry

@[target]
theorem mul_right_inj {a b c : Ordinal} (a0 : 0 < a) : a * b = a * c ↔ b = c := by sorry

@[target]
theorem isLimit_mul {a b : Ordinal} (a0 : 0 < a) : IsLimit b → IsLimit (a * b) := by sorry

@[deprecated isLimit_mul (since := "2024-10-11")]
alias mul_isLimit := isLimit_mul

@[target]
theorem isLimit_mul_left {a b : Ordinal} (l : IsLimit a) (b0 : 0 < b) : IsLimit (a * b) := by sorry

@[deprecated isLimit_mul_left (since := "2024-10-11")]
alias mul_isLimit_left := isLimit_mul_left

@[target]
theorem smul_eq_mul : ∀ (n : ℕ) (a : Ordinal), n • a = a * n := by sorry

private theorem add_mul_limit_aux {a b c : Ordinal} (ba : b + a = a) (l : IsLimit c)
    (IH : ∀ c' < c, (a + b) * succ c' = a * succ c' + b) : (a + b) * c = a * c :=
  le_antisymm
    ((mul_le_of_limit l).2 fun c' h => by
      apply (mul_le_mul_left' (le_succ c') _).trans
      rw [IH _ h]
      apply (add_le_add_left _ _).trans
      · rw [← mul_succ]
        exact mul_le_mul_left' (succ_le_of_lt <| l.succ_lt h) _
      · rw [← ba]
        exact le_add_right _ _)
    (mul_le_mul_right' (le_add_right _ _) _)

@[target]
theorem add_mul_succ {a b : Ordinal} (c) (ba : b + a = a) : (a + b) * succ c = a * succ c + b := by sorry

@[target]
theorem add_mul_limit {a b c : Ordinal} (ba : b + a = a) (l : IsLimit c) : (a + b) * c = a * c := by sorry

/-! ### Division on ordinals -/


/-- The set in the definition of division is nonempty. -/
private theorem div_nonempty {a b : Ordinal} (h : b ≠ 0) : { o | a < b * succ o }.Nonempty :=
  ⟨a, (succ_le_iff (a := a) (b := b * succ a)).1 <| by
    simpa only [succ_zero, one_mul] using
      mul_le_mul_right' (succ_le_of_lt (Ordinal.pos_iff_ne_zero.2 h)) (succ a)⟩

/-- `a / b` is the unique ordinal `o` satisfying `a = b * o + o'` with `o' < b`. -/
instance div : Div Ordinal :=
  ⟨fun a b => if b = 0 then 0 else sInf { o | a < b * succ o }⟩

@[target, simp]
theorem div_zero (a : Ordinal) : a / 0 = 0 := by sorry

private theorem div_def (a) {b : Ordinal} (h : b ≠ 0) : a / b = sInf { o | a < b * succ o } :=
  dif_neg h

@[target]
theorem lt_mul_succ_div (a) {b : Ordinal} (h : b ≠ 0) : a < b * succ (a / b) := by sorry

@[target]
theorem lt_mul_div_add (a) {b : Ordinal} (h : b ≠ 0) : a < b * (a / b) + b := by sorry

theorem div_le {a b c : Ordinal} (b0 : b ≠ 0) : a / b ≤ c ↔ a < b * succ c :=
  ⟨fun h => (lt_mul_succ_div a b0).trans_le (mul_le_mul_left' (succ_le_succ_iff.2 h) _), fun h => by
    rw [div_def a b0]; exact csInf_le' h⟩

theorem lt_div {a b c : Ordinal} (h : c ≠ 0) : a < b / c ↔ c * succ a ≤ b := by
  rw [← not_le, div_le h, not_lt]

@[target]
theorem div_pos {b c : Ordinal} (h : c ≠ 0) : 0 < b / c ↔ c ≤ b := by sorry

@[target]
theorem le_div {a b c : Ordinal} (c0 : c ≠ 0) : a ≤ b / c ↔ c * a ≤ b := by sorry

@[target]
theorem div_lt {a b c : Ordinal} (b0 : b ≠ 0) : a / b < c ↔ a < b * c := by sorry

@[target]
theorem div_le_of_le_mul {a b c : Ordinal} (h : a ≤ b * c) : a / b ≤ c := by sorry

@[target]
theorem mul_lt_of_lt_div {a b c : Ordinal} : a < b / c → c * a < b := by sorry

@[target, simp]
theorem zero_div (a : Ordinal) : 0 / a = 0 := by sorry

@[target]
theorem mul_div_le (a b : Ordinal) : b * (a / b) ≤ a := by sorry

@[target]
theorem div_le_left {a b : Ordinal} (h : a ≤ b) (c : Ordinal) : a / c ≤ b / c := by sorry

@[target]
theorem mul_add_div (a) {b : Ordinal} (b0 : b ≠ 0) (c) : (b * a + c) / b = a + c / b := by sorry

@[target]
theorem div_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a / b = 0 := by sorry

@[target, simp]
theorem mul_div_cancel (a) {b : Ordinal} (b0 : b ≠ 0) : b * a / b = a := by sorry

@[target]
theorem mul_add_div_mul {a c : Ordinal} (hc : c < a) (b d : Ordinal) :
    (a * b + c) / (a * d) = b / d := by sorry

@[target]
theorem mul_div_mul_cancel {a : Ordinal} (ha : a ≠ 0) (b c) : a * b / (a * c) = b / c := by sorry

@[target, simp]
theorem div_one (a : Ordinal) : a / 1 = a := by sorry

@[target, simp]
theorem div_self {a : Ordinal} (h : a ≠ 0) : a / a = 1 := by sorry

@[target]
theorem mul_sub (a b c : Ordinal) : a * (b - c) = a * b - a * c := by sorry

@[target]
theorem isLimit_add_iff {a b} : IsLimit (a + b) ↔ IsLimit b ∨ b = 0 ∧ IsLimit a := by sorry

@[target]
theorem dvd_add_iff : ∀ {a b c : Ordinal}, a ∣ b → (a ∣ b + c ↔ a ∣ c) := by sorry

@[target]
theorem div_mul_cancel : ∀ {a b : Ordinal}, a ≠ 0 → a ∣ b → a * (b / a) = b := by sorry

@[target]
theorem le_of_dvd : ∀ {a b : Ordinal}, b ≠ 0 → a ∣ b → a ≤ b := by
  intro a b h1 h2
  sorry

@[target]
theorem dvd_antisymm {a b : Ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b := by sorry

instance isAntisymm : IsAntisymm Ordinal (· ∣ ·) :=
  ⟨@dvd_antisymm⟩

/-- `a % b` is the unique ordinal `o'` satisfying
  `a = b * o + o'` with `o' < b`. -/
instance mod : Mod Ordinal :=
  ⟨fun a b => a - b * (a / b)⟩

@[target]
theorem mod_def (a b : Ordinal) : a % b = a - b * (a / b) := by sorry

@[target]
theorem mod_le (a b : Ordinal) : a % b ≤ a := by sorry

@[simp]
theorem mod_zero (a : Ordinal) : a % 0 = a := by simp only [mod_def, div_zero, zero_mul, sub_zero]

theorem mod_eq_of_lt {a b : Ordinal} (h : a < b) : a % b = a := by
  simp only [mod_def, div_eq_zero_of_lt h, mul_zero, sub_zero]

@[target, simp]
theorem zero_mod (b : Ordinal) : 0 % b = 0 := by sorry

@[target]
theorem div_add_mod (a b : Ordinal) : b * (a / b) + a % b = a := by sorry

@[target]
theorem mod_lt (a) {b : Ordinal} (h : b ≠ 0) : a % b < b := by sorry

@[target, simp]
theorem mod_self (a : Ordinal) : a % a = 0 := by sorry

@[target, simp]
theorem mod_one (a : Ordinal) : a % 1 = 0 := by sorry

@[target]
theorem dvd_of_mod_eq_zero {a b : Ordinal} (H : a % b = 0) : b ∣ a := by sorry

@[target]
theorem mod_eq_zero_of_dvd {a b : Ordinal} (H : b ∣ a) : a % b = 0 := by sorry

theorem dvd_iff_mod_eq_zero {a b : Ordinal} : b ∣ a ↔ a % b = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

@[target, simp]
theorem mul_add_mod_self (x y z : Ordinal) : (x * y + z) % x = z % x := by sorry

@[simp]
theorem mul_mod (x y : Ordinal) : x * y % x = 0 := by
  simpa using mul_add_mod_self x y 0

@[target]
theorem mul_add_mod_mul {w x : Ordinal} (hw : w < x) (y z : Ordinal) :
    (x * y + w) % (x * z) = x * (y % z) + w := by sorry

@[target]
theorem mul_mod_mul (x y z : Ordinal) : (x * y) % (x * z) = x * (y % z) := by sorry

@[target]
theorem mod_mod_of_dvd (a : Ordinal) {b c : Ordinal} (h : c ∣ b) : a % b % c = a % c := by sorry

@[target, simp]
theorem mod_mod (a b : Ordinal) : a % b % b = a % b := by sorry

/-! ### Families of ordinals

There are two kinds of indexed families that naturally arise when dealing with ordinals: those
indexed by some type in the appropriate universe, and those indexed by ordinals less than another.
The following API allows one to convert from one kind of family to the other.

In many cases, this makes it easy to prove claims about one kind of family via the corresponding
claim on the other. -/


/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a specified
well-ordering. -/
def bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    ∀ a < type r, α := fun a ha => f (enum r ⟨a, ha⟩)

/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a well-ordering
given by the axiom of choice. -/
def bfamilyOfFamily {ι : Type u} : (ι → α) → ∀ a < type (@WellOrderingRel ι), α :=
  bfamilyOfFamily' WellOrderingRel

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a specified
well-ordering. -/
def familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀ a < o, α) : ι → α := fun i =>
  f (typein r i)
    (by
      rw [← ho]
      exact typein_lt_type r i)

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a well-ordering
given by the axiom of choice. -/
def familyOfBFamily (o : Ordinal) (f : ∀ a < o, α) : o.toType → α :=
  familyOfBFamily' (· < ·) (type_toType o) f

@[target, simp]
theorem bfamilyOfFamily'_typein {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) (i) :
    bfamilyOfFamily' r f (typein r i) (typein_lt_type r i) = f i := by sorry

@[target, simp]
theorem bfamilyOfFamily_typein {ι} (f : ι → α) (i) :
    bfamilyOfFamily f (typein _ i) (typein_lt_type _ i) = f i := by sorry

@[target]
theorem familyOfBFamily'_enum {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) (i hi) :
    familyOfBFamily' r ho f (enum r ⟨i, by rwa [ho]⟩) = f i hi := by sorry

@[target]
theorem familyOfBFamily_enum (o : Ordinal) (f : ∀ a < o, α) (i hi) :
    familyOfBFamily o f (enum (α := o.toType) (· < ·) ⟨i, hi.trans_eq (type_toType _).symm⟩)
    = f i hi := by sorry

/-- The range of a family indexed by ordinals. -/
def brange (o : Ordinal) (f : ∀ a < o, α) : Set α :=
  { a | ∃ i hi, f i hi = a }

@[target]
theorem mem_brange {o : Ordinal} {f : ∀ a < o, α} {a} : a ∈ brange o f ↔ ∃ i hi, f i hi = a := by sorry

@[target]
theorem mem_brange_self {o} (f : ∀ a < o, α) (i hi) : f i hi ∈ brange o f := by sorry

@[target, simp]
theorem range_familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) : range (familyOfBFamily' r ho f) = brange o f := by sorry

@[target, simp]
theorem range_familyOfBFamily {o} (f : ∀ a < o, α) : range (familyOfBFamily o f) = brange o f := by sorry

@[target, simp]
theorem brange_bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    brange _ (bfamilyOfFamily' r f) = range f := by sorry

@[target, simp]
theorem brange_bfamilyOfFamily {ι : Type u} (f : ι → α) : brange _ (bfamilyOfFamily f) = range f := by sorry

@[target, simp]
theorem brange_const {o : Ordinal} (ho : o ≠ 0) {c : α} : (brange o fun _ _ => c) = {c} := by sorry

@[target]
theorem comp_bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α)
    (g : α → β) : (fun i hi => g (bfamilyOfFamily' r f i hi)) = bfamilyOfFamily' r (g ∘ f) := by sorry

@[target]
theorem comp_bfamilyOfFamily {ι : Type u} (f : ι → α) (g : α → β) :
    (fun i hi => g (bfamilyOfFamily f i hi)) = bfamilyOfFamily (g ∘ f) := by sorry

@[target]
theorem comp_familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : ∀ a < o, α) (g : α → β) :
    g ∘ familyOfBFamily' r ho f = familyOfBFamily' r ho fun i hi => g (f i hi) := by sorry

@[target]
theorem comp_familyOfBFamily {o} (f : ∀ a < o, α) (g : α → β) :
    g ∘ familyOfBFamily o f = familyOfBFamily o fun i hi => g (f i hi) := by sorry

/-! ### Supremum of a family of ordinals -/

/-- The supremum of a family of ordinals -/

@[deprecated iSup (since := "2024-08-27")]
def sup {ι : Type u} (f : ι → Ordinal.{max u v}) : Ordinal.{max u v} :=
  iSup f

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-08-27")]
theorem sSup_eq_sup {ι : Type u} (f : ι → Ordinal.{max u v}) : sSup (Set.range f) = sup.{_, v} f := by sorry

/-- The range of an indexed ordinal function, whose outputs live in a higher universe than the
    inputs, is always bounded above. See `Ordinal.lsub` for an explicit bound. -/
@[target]
theorem bddAbove_range {ι : Type u} (f : ι → Ordinal.{max u v}) : BddAbove (Set.range f) := by sorry

theorem bddAbove_of_small (s : Set Ordinal.{u}) [h : Small.{u} s] : BddAbove s := by
  obtain ⟨a, ha⟩ := bddAbove_range (fun x => ((@equivShrink s h).symm x).val)
  use a
  intro b hb
  simpa using ha (mem_range_self (equivShrink s ⟨b, hb⟩))

@[target]
theorem bddAbove_iff_small {s : Set Ordinal.{u}} : BddAbove s ↔ Small.{u} s := by sorry

@[target]
theorem bddAbove_image {s : Set Ordinal.{u}} (hf : BddAbove s)
    (f : Ordinal.{u} → Ordinal.{max u v}) : BddAbove (f '' s) := by sorry

@[target]
theorem bddAbove_range_comp {ι : Type u} {f : ι → Ordinal.{v}} (hf : BddAbove (range f))
    (g : Ordinal.{v} → Ordinal.{max v w}) : BddAbove (range (g ∘ f)) := by sorry

/-- `le_ciSup` whenever the input type is small in the output universe. This lemma sometimes
fails to infer `f` in simple cases and needs it to be given explicitly. -/
protected theorem le_iSup {ι} (f : ι → Ordinal.{u}) [Small.{u} ι] : ∀ i, f i ≤ iSup f :=
  le_ciSup (bddAbove_of_small _)

set_option linter.deprecated false in
@[target, deprecated Ordinal.le_iSup (since := "2024-08-27")]
theorem le_sup {ι : Type u} (f : ι → Ordinal.{max u v}) : ∀ i, f i ≤ sup.{_, v} f := by sorry

/-- `ciSup_le_iff'` whenever the input type is small in the output universe. -/
protected theorem iSup_le_iff {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  ciSup_le_iff' (bddAbove_of_small _)

set_option linter.deprecated false in
@[target, deprecated Ordinal.iSup_le_iff (since := "2024-08-27")]
theorem sup_le_iff {ι : Type u} {f : ι → Ordinal.{max u v}} {a} : sup.{_, v} f ≤ a ↔ ∀ i, f i ≤ a := by sorry

/-- An alias of `ciSup_le'` for discoverability. -/
protected theorem iSup_le {ι} {f : ι → Ordinal} {a} :
    (∀ i, f i ≤ a) → iSup f ≤ a :=
  ciSup_le'

set_option linter.deprecated false in
@[deprecated Ordinal.iSup_le (since := "2024-08-27")]
theorem sup_le {ι : Type u} {f : ι → Ordinal.{max u v}} {a} : (∀ i, f i ≤ a) → sup.{_, v} f ≤ a :=
  Ordinal.iSup_le

/-- `lt_ciSup_iff'` whenever the input type is small in the output universe. -/
protected theorem lt_iSup_iff {ι} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    a < iSup f ↔ ∃ i, a < f i :=
  lt_ciSup_iff' (bddAbove_of_small _)

@[deprecated "No deprecation message was provided." (since := "2024-11-12")]
alias lt_iSup := lt_iSup_iff

set_option linter.deprecated false in
@[target, deprecated Ordinal.lt_iSup (since := "2024-08-27")]
theorem lt_sup {ι : Type u} {f : ι → Ordinal.{max u v}} {a} : a < sup.{_, v} f ↔ ∃ i, a < f i := by sorry

@[target, deprecated "No deprecation message was provided."  (since := "2024-08-27")]
theorem ne_iSup_iff_lt_iSup {ι : Type u} {f : ι → Ordinal.{max u v}} :
    (∀ i, f i ≠ iSup f) ↔ ∀ i, f i < iSup f := by sorry

set_option linter.deprecated false in
@[deprecated ne_iSup_iff_lt_iSup (since := "2024-08-27")]
theorem ne_sup_iff_lt_sup {ι : Type u} {f : ι → Ordinal.{max u v}} :
    (∀ i, f i ≠ sup.{_, v} f) ↔ ∀ i, f i < sup.{_, v} f :=
  ne_iSup_iff_lt_iSup

-- TODO: state in terms of `IsSuccLimit`.
@[target]
theorem succ_lt_iSup_of_ne_iSup {ι} {f : ι → Ordinal.{u}} [Small.{u} ι]
    (hf : ∀ i, f i ≠ iSup f) {a} (hao : a < iSup f) : succ a < iSup f := by sorry

set_option linter.deprecated false in
@[target, deprecated succ_lt_iSup_of_ne_iSup (since := "2024-08-27")]
theorem sup_not_succ_of_ne_sup {ι : Type u} {f : ι → Ordinal.{max u v}}
    (hf : ∀ i, f i ≠ sup.{_, v} f) {a} (hao : a < sup.{_, v} f) : succ a < sup.{_, v} f := by sorry

@[target]
theorem iSup_eq_zero_iff {ι} {f : ι → Ordinal.{u}} [Small.{u} ι] :
    iSup f = 0 ↔ ∀ i, f i = 0 := by sorry

set_option linter.deprecated false in
@[target, deprecated iSup_eq_zero_iff (since := "2024-08-27")]
theorem sup_eq_zero_iff {ι : Type u} {f : ι → Ordinal.{max u v}} :
    sup.{_, v} f = 0 ↔ ∀ i, f i = 0 := by sorry

set_option linter.deprecated false in
@[target, deprecated ciSup_of_empty (since := "2024-08-27")]
theorem sup_empty {ι} [IsEmpty ι] (f : ι → Ordinal) : sup f = 0 := by sorry

set_option linter.deprecated false in
@[target, deprecated ciSup_const (since := "2024-08-27")]
theorem sup_const {ι} [_hι : Nonempty ι] (o : Ordinal) : (sup fun _ : ι => o) = o := by sorry

set_option linter.deprecated false in
@[target, deprecated ciSup_unique (since := "2024-08-27")]
theorem sup_unique {ι} [Unique ι] (f : ι → Ordinal) : sup f = f default := by sorry

set_option linter.deprecated false in
@[target, deprecated csSup_le_csSup' (since := "2024-08-27")]
theorem sup_le_of_range_subset {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f ⊆ Set.range g) : sup.{u, max v w} f ≤ sup.{v, max u w} g := by sorry

@[target]
theorem iSup_eq_of_range_eq {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f = Set.range g) : iSup f = iSup g := by sorry

set_option linter.deprecated false in
@[target, deprecated iSup_eq_of_range_eq (since := "2024-08-27")]
theorem sup_eq_of_range_eq {ι : Type u} {ι' : Type v}
    {f : ι → Ordinal.{max u v w}} {g : ι' → Ordinal.{max u v w}}
    (h : Set.range f = Set.range g) : sup.{u, max v w} f = sup.{v, max u w} g := by sorry

@[target]
theorem iSup_succ (o : Ordinal) : ⨆ a : Iio o, succ a.1 = o := by sorry

theorem iSup_sum {α β} (f : α ⊕ β → Ordinal.{u}) [Small.{u} α] [Small.{u} β]:
    iSup f = max (⨆ a, f (Sum.inl a)) (⨆ b, f (Sum.inr b)) := by
  apply (Ordinal.iSup_le _).antisymm (max_le _ _)
  · rintro (i | i)
    · exact le_max_of_le_left (Ordinal.le_iSup (fun x ↦ f (Sum.inl x)) i)
    · exact le_max_of_le_right (Ordinal.le_iSup (fun x ↦ f (Sum.inr x)) i)
  all_goals
    apply csSup_le_csSup' (bddAbove_of_small _)
    rintro i ⟨a, rfl⟩
    apply mem_range_self

set_option linter.deprecated false in
@[target, deprecated iSup_sum (since := "2024-08-27")]
theorem sup_sum {α : Type u} {β : Type v} (f : α ⊕ β → Ordinal) :
    sup.{max u v, w} f =
      max (sup.{u, max v w} fun a => f (Sum.inl a)) (sup.{v, max u w} fun b => f (Sum.inr b)) := by sorry

@[target]
theorem unbounded_range_of_le_iSup {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β → α)
    (h : type r ≤ ⨆ i, typein r (f i)) : Unbounded r (range f) := by sorry

set_option linter.deprecated false in
@[target, deprecated unbounded_range_of_le_iSup (since := "2024-08-27")]
theorem unbounded_range_of_sup_ge {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β → α)
    (h : type r ≤ sup.{u, u} (typein r ∘ f)) : Unbounded r (range f) := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-08-27")]
theorem le_sup_shrink_equiv {s : Set Ordinal.{u}} (hs : Small.{u} s) (a) (ha : a ∈ s) :
    a ≤ sup.{u, u} fun x => ((@equivShrink s hs).symm x).val := by sorry

@[target]
theorem IsNormal.map_iSup_of_bddAbove {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f)
    {ι : Type*} (g : ι → Ordinal.{u}) (hg : BddAbove (range g))
    [Nonempty ι] : f (⨆ i, g i) = ⨆ i, f (g i) := by sorry

@[target]
theorem IsNormal.map_iSup {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f)
    {ι : Type w} (g : ι → Ordinal.{u}) [Small.{u} ι] [Nonempty ι] :
    f (⨆ i, g i) = ⨆ i, f (g i) := by sorry

@[target]
theorem IsNormal.map_sSup_of_bddAbove {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f)
    {s : Set Ordinal.{u}} (hs : BddAbove s) (hn : s.Nonempty) : f (sSup s) = sSup (f '' s) := by sorry

@[target]
theorem IsNormal.map_sSup {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f)
    {s : Set Ordinal.{u}} (hn : s.Nonempty) [Small.{u} s] : f (sSup s) = sSup (f '' s) := by sorry

set_option linter.deprecated false in
@[target, deprecated IsNormal.map_iSup (since := "2024-08-27")]
theorem IsNormal.sup {f : Ordinal.{max u v} → Ordinal.{max u w}} (H : IsNormal f) {ι : Type u}
    (g : ι → Ordinal.{max u v}) [Nonempty ι] : f (sup.{_, v} g) = sup.{_, w} (f ∘ g) := by sorry

@[target]
theorem IsNormal.apply_of_isLimit {f : Ordinal.{u} → Ordinal.{v}} (H : IsNormal f) {o : Ordinal}
    (ho : IsLimit o) : f o = ⨆ a : Iio o, f a := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-08-27")]
theorem sup_eq_sSup {s : Set Ordinal.{u}} (hs : Small.{u} s) :
    (sup.{u, u} fun x => (@equivShrink s hs).symm x) = sSup s := by sorry

@[target]
theorem sSup_ord {s : Set Cardinal.{u}} (hs : BddAbove s) : (sSup s).ord = sSup (ord '' s) := by sorry

@[target]
theorem iSup_ord {ι} {f : ι → Cardinal} (hf : BddAbove (range f)) :
    (iSup f).ord = ⨆ i, (f i).ord := by sorry

@[target]
theorem lift_card_sInf_compl_le (s : Set Ordinal.{u}) :
    Cardinal.lift.{u + 1} (sInf sᶜ).card ≤ #s := by sorry

@[target]
theorem card_sInf_range_compl_le_lift {ι : Type u} (f : ι → Ordinal.{max u v}) :
    (sInf (range f)ᶜ).card ≤ Cardinal.lift.{v} #ι := by sorry

@[target]
theorem card_sInf_range_compl_le {ι : Type u} (f : ι → Ordinal.{u}) :
    (sInf (range f)ᶜ).card ≤ #ι := by sorry

@[target]
theorem sInf_compl_lt_lift_ord_succ {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sInf (range f)ᶜ < lift.{v} (succ #ι).ord := by sorry

@[target]
theorem sInf_compl_lt_ord_succ {ι : Type u} (f : ι → Ordinal.{u}) :
    sInf (range f)ᶜ < (succ #ι).ord := by sorry

section bsup

set_option linter.deprecated false in
private theorem sup_le_sup {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop)
    [IsWellOrder ι r] [IsWellOrder ι' r'] {o} (ho : type r = o) (ho' : type r' = o)
    (f : ∀ a < o, Ordinal.{max u v}) :
    sup.{_, v} (familyOfBFamily' r ho f) ≤ sup.{_, v} (familyOfBFamily' r' ho' f) :=
  sup_le fun i => by
    obtain ⟨j, hj⟩ := typein_surj r' (by rw [ho', ← ho]; exact typein_lt_type r i)
    simp_rw [familyOfBFamily', ← hj]
    apply le_sup

set_option linter.deprecated false in
theorem sup_eq_sup {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o : Ordinal.{u}} (ho : type r = o) (ho' : type r' = o)
    (f : ∀ a < o, Ordinal.{max u v}) :
    sup.{_, v} (familyOfBFamily' r ho f) = sup.{_, v} (familyOfBFamily' r' ho' f) :=
  sup_eq_of_range_eq.{u, u, v} (by simp)

set_option linter.deprecated false in
/-- The supremum of a family of ordinals indexed by the set of ordinals less than some
    `o : Ordinal.{u}`. This is a special case of `sup` over the family provided by
    `familyOfBFamily`. -/
def bsup (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  sup.{_, v} (familyOfBFamily o f)

set_option linter.deprecated false in
@[target, simp]
theorem sup_eq_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    sup.{_, v} (familyOfBFamily o f) = bsup.{_, v} o f := by sorry

set_option linter.deprecated false in
@[target, simp]
theorem sup_eq_bsup' {o : Ordinal.{u}} {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (ho : type r = o)
    (f : ∀ a < o, Ordinal.{max u v}) : sup.{_, v} (familyOfBFamily' r ho f) = bsup.{_, v} o f := by sorry

@[target]
theorem sSup_eq_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    sSup (brange o f) = bsup.{_, v} o f := by sorry

set_option linter.deprecated false in
@[target, simp]
theorem bsup_eq_sup' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → Ordinal.{max u v}) :
    bsup.{_, v} _ (bfamilyOfFamily' r f) = sup.{_, v} f := by sorry

@[target]
theorem bsup_eq_bsup {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι → Ordinal.{max u v}) :
    bsup.{_, v} _ (bfamilyOfFamily' r f) = bsup.{_, v} _ (bfamilyOfFamily' r' f) := by sorry

set_option linter.deprecated false in
@[target, simp]
theorem bsup_eq_sup {ι : Type u} (f : ι → Ordinal.{max u v}) :
    bsup.{_, v} _ (bfamilyOfFamily f) = sup.{_, v} f := by sorry

@[target, congr]
theorem bsup_congr {o₁ o₂ : Ordinal.{u}} (f : ∀ a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    bsup.{_, v} o₁ f = bsup.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by sorry

set_option linter.deprecated false in
@[target]
theorem bsup_le_iff {o f a} : bsup.{u, v} o f ≤ a ↔ ∀ i h, f i h ≤ a := by sorry

theorem bsup_le {o : Ordinal} {f : ∀ b < o, Ordinal} {a} :
    (∀ i h, f i h ≤ a) → bsup.{u, v} o f ≤ a :=
  bsup_le_iff.2

@[target]
theorem le_bsup {o} (f : ∀ a < o, Ordinal) (i h) : f i h ≤ bsup o f := by sorry

theorem lt_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) {a} :
    a < bsup.{_, v} o f ↔ ∃ i hi, a < f i hi := by
  simpa only [not_forall, not_le] using not_congr (@bsup_le_iff.{_, v} _ f a)

set_option linter.deprecated false in
@[target]
theorem IsNormal.bsup {f : Ordinal.{max u v} → Ordinal.{max u w}} (H : IsNormal f)
    {o : Ordinal.{u}} :
    ∀ (g : ∀ a < o, Ordinal), o ≠ 0 → f (bsup.{_, v} o g) = bsup.{_, w} o fun a h => f (g a h) := by sorry

@[target]
theorem lt_bsup_of_ne_bsup {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}} :
    (∀ i h, f i h ≠ bsup.{_, v} o f) ↔ ∀ i h, f i h < bsup.{_, v} o f := by sorry

set_option linter.deprecated false in
@[target]
theorem bsup_not_succ_of_ne_bsup {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}}
    (hf : ∀ {i : Ordinal} (h : i < o), f i h ≠ bsup.{_, v} o f) (a) :
    a < bsup.{_, v} o f → succ a < bsup.{_, v} o f := by sorry

@[target, simp]
theorem bsup_eq_zero_iff {o} {f : ∀ a < o, Ordinal} : bsup o f = 0 ↔ ∀ i hi, f i hi = 0 := by sorry

@[target]
theorem lt_bsup_of_limit {o : Ordinal} {f : ∀ a < o, Ordinal}
    (hf : ∀ {a a'} (ha : a < o) (ha' : a' < o), a < a' → f a ha < f a' ha')
    (ho : ∀ a < o, succ a < o) (i h) : f i h < bsup o f := by sorry

@[target]
theorem bsup_succ_of_mono {o : Ordinal} {f : ∀ a < succ o, Ordinal}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) : bsup _ f = f o (lt_succ o) := by sorry

@[target, simp]
theorem bsup_zero (f : ∀ a < (0 : Ordinal), Ordinal) : bsup 0 f = 0 := by sorry

@[target]
theorem bsup_const {o : Ordinal.{u}} (ho : o ≠ 0) (a : Ordinal.{max u v}) :
    (bsup.{_, v} o fun _ _ => a) = a := by sorry

set_option linter.deprecated false in
@[target, simp]
theorem bsup_one (f : ∀ a < (1 : Ordinal), Ordinal) : bsup 1 f = f 0 zero_lt_one := by sorry

theorem bsup_le_of_brange_subset {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f ⊆ brange o' g) : bsup.{u, max v w} o f ≤ bsup.{v, max u w} o' g :=
  bsup_le fun i hi => by
    obtain ⟨j, hj, hj'⟩ := h ⟨i, hi, rfl⟩
    rw [← hj']
    apply le_bsup

@[target]
theorem bsup_eq_of_brange_eq {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f = brange o' g) : bsup.{u, max v w} o f = bsup.{v, max u w} o' g := by sorry

set_option linter.deprecated false in
@[target]
theorem iSup_eq_bsup {o} {f : ∀ a < o, Ordinal} : ⨆ a : Iio o, f a.1 a.2 = bsup o f := by sorry

end bsup

-- TODO: bring the lsub API in line with the sSup / iSup API, or deprecate it altogether.

section lsub

set_option linter.deprecated false in
/-- The least strict upper bound of a family of ordinals. -/
def lsub {ι} (f : ι → Ordinal) : Ordinal :=
  sup (succ ∘ f)

set_option linter.deprecated false in
@[target, simp]
theorem sup_eq_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sup.{_, v} (succ ∘ f) = lsub.{_, v} f := by sorry

set_option linter.deprecated false in
theorem lsub_le_iff {ι : Type u} {f : ι → Ordinal.{max u v}} {a} :
    lsub.{_, v} f ≤ a ↔ ∀ i, f i < a := by
  convert sup_le_iff.{_, v} (f := succ ∘ f) (a := a) using 2
  -- Porting note: `comp_apply` is required.
  simp only [comp_apply, succ_le_iff]

theorem lsub_le {ι} {f : ι → Ordinal} {a} : (∀ i, f i < a) → lsub f ≤ a :=
  lsub_le_iff.2

set_option linter.deprecated false in
@[target]
theorem lt_lsub {ι} (f : ι → Ordinal) (i) : f i < lsub f := by sorry

@[target]
theorem lt_lsub_iff {ι : Type u} {f : ι → Ordinal.{max u v}} {a} :
    a < lsub.{_, v} f ↔ ∃ i, a ≤ f i := by sorry

set_option linter.deprecated false in
@[target]
theorem sup_le_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) : sup.{_, v} f ≤ lsub.{_, v} f := by sorry

set_option linter.deprecated false in
@[target]
theorem lsub_le_sup_succ {ι : Type u} (f : ι → Ordinal.{max u v}) :
    lsub.{_, v} f ≤ succ (sup.{_, v} f) := by sorry

set_option linter.deprecated false in
@[target]
theorem sup_eq_lsub_or_sup_succ_eq_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sup.{_, v} f = lsub.{_, v} f ∨ succ (sup.{_, v} f) = lsub.{_, v} f := by sorry

set_option linter.deprecated false in
@[target]
theorem sup_succ_le_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    succ (sup.{_, v} f) ≤ lsub.{_, v} f ↔ ∃ i, f i = sup.{_, v} f := by sorry

set_option linter.deprecated false in
@[target]
theorem sup_succ_eq_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    succ (sup.{_, v} f) = lsub.{_, v} f ↔ ∃ i, f i = sup.{_, v} f := by sorry

set_option linter.deprecated false in
theorem sup_eq_lsub_iff_succ {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sup.{_, v} f = lsub.{_, v} f ↔ ∀ a < lsub.{_, v} f, succ a < lsub.{_, v} f := by
  refine ⟨fun h => ?_, fun hf => le_antisymm (sup_le_lsub f) (lsub_le fun i => ?_)⟩
  · rw [← h]
    exact fun a => sup_not_succ_of_ne_sup fun i => (lsub_le_iff.1 (le_of_eq h.symm) i).ne
  by_contra! hle
  have heq := (sup_succ_eq_lsub f).2 ⟨i, le_antisymm (le_sup _ _) hle⟩
  have :=
    hf _
      (by
        rw [← heq]
        exact lt_succ (sup f))
  rw [heq] at this
  exact this.false

set_option linter.deprecated false in
@[target]
theorem sup_eq_lsub_iff_lt_sup {ι : Type u} (f : ι → Ordinal.{max u v}) :
    sup.{_, v} f = lsub.{_, v} f ↔ ∀ i, f i < sup.{_, v} f := by sorry

@[target, simp]
theorem lsub_empty {ι} [h : IsEmpty ι] (f : ι → Ordinal) : lsub f = 0 := by sorry

@[target]
theorem lsub_pos {ι : Type u} [h : Nonempty ι] (f : ι → Ordinal.{max u v}) : 0 < lsub.{_, v} f := by sorry

@[target, simp]
theorem lsub_eq_zero_iff {ι : Type u} (f : ι → Ordinal.{max u v}) :
    lsub.{_, v} f = 0 ↔ IsEmpty ι := by sorry

set_option linter.deprecated false in
@[target, simp]
theorem lsub_const {ι} [Nonempty ι] (o : Ordinal) : (lsub fun _ : ι => o) = succ o := by sorry

set_option linter.deprecated false in
@[target, simp]
theorem lsub_unique {ι} [Unique ι] (f : ι → Ordinal) : lsub f = succ (f default) := by sorry

set_option linter.deprecated false in
@[target]
theorem lsub_le_of_range_subset {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f ⊆ Set.range g) : lsub.{u, max v w} f ≤ lsub.{v, max u w} g := by sorry

@[target]
theorem lsub_eq_of_range_eq {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal}
    (h : Set.range f = Set.range g) : lsub.{u, max v w} f = lsub.{v, max u w} g := by sorry

set_option linter.deprecated false in
@[target, simp]
theorem lsub_sum {α : Type u} {β : Type v} (f : α ⊕ β → Ordinal) :
    lsub.{max u v, w} f =
      max (lsub.{u, max v w} fun a => f (Sum.inl a)) (lsub.{v, max u w} fun b => f (Sum.inr b)) := by sorry

@[target]
theorem lsub_not_mem_range {ι : Type u} (f : ι → Ordinal.{max u v}) :
    lsub.{_, v} f ∉ Set.range f := by sorry

@[target]
theorem nonempty_compl_range {ι : Type u} (f : ι → Ordinal.{max u v}) : (Set.range f)ᶜ.Nonempty := by sorry

set_option linter.deprecated false in
@[target, simp]
theorem lsub_typein (o : Ordinal) : lsub.{u, u} (typein (α := o.toType) (· < ·)) = o := by sorry

set_option linter.deprecated false in
@[target]
theorem sup_typein_limit {o : Ordinal} (ho : ∀ a, a < o → succ a < o) :
    sup.{u, u} (typein ((· < ·) : o.toType → o.toType → Prop)) = o := by sorry

set_option linter.deprecated false in
@[target, simp]
theorem sup_typein_succ {o : Ordinal} :
    sup.{u, u} (typein ((· < ·) : (succ o).toType → (succ o).toType → Prop)) = o := by sorry

end lsub

-- TODO: either deprecate this in favor of `lsub` when its universes are generalized, or deprecate
-- both of them at once.

section blsub

/-- The least strict upper bound of a family of ordinals indexed by the set of ordinals less than
    some `o : Ordinal.{u}`.

    This is to `lsub` as `bsup` is to `sup`. -/
def blsub (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  bsup.{_, v} o fun a ha => succ (f a ha)

@[simp]
theorem bsup_eq_blsub (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) :
    (bsup.{_, v} o fun a ha => succ (f a ha)) = blsub.{_, v} o f :=
  rfl

@[target]
theorem lsub_eq_blsub' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀ a < o, Ordinal.{max u v}) : lsub.{_, v} (familyOfBFamily' r ho f) = blsub.{_, v} o f := by sorry

@[target]
theorem lsub_eq_lsub {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o} (ho : type r = o) (ho' : type r' = o)
    (f : ∀ a < o, Ordinal.{max u v}) :
    lsub.{_, v} (familyOfBFamily' r ho f) = lsub.{_, v} (familyOfBFamily' r' ho' f) := by sorry

@[target, simp]
theorem lsub_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    lsub.{_, v} (familyOfBFamily o f) = blsub.{_, v} o f := by sorry

@[simp]
theorem blsub_eq_lsub' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r]
    (f : ι → Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamily' r f) = lsub.{_, v} f :=
  bsup_eq_sup'.{_, v} r (succ ∘ f)

@[target]
theorem blsub_eq_blsub {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι → Ordinal.{max u v}) :
    blsub.{_, v} _ (bfamilyOfFamily' r f) = blsub.{_, v} _ (bfamilyOfFamily' r' f) := by sorry

@[target, simp]
theorem blsub_eq_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) :
    blsub.{_, v} _ (bfamilyOfFamily f) = lsub.{_, v} f := by sorry

@[target, congr]
theorem blsub_congr {o₁ o₂ : Ordinal.{u}} (f : ∀ a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    blsub.{_, v} o₁ f = blsub.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by sorry

@[target]
theorem blsub_le_iff {o : Ordinal.{u}} {f : ∀ a < o, Ordinal.{max u v}} {a} :
    blsub.{_, v} o f ≤ a ↔ ∀ i h, f i h < a := by sorry

@[target]
theorem blsub_le {o : Ordinal} {f : ∀ b < o, Ordinal} {a} : (∀ i h, f i h < a) → blsub o f ≤ a := by sorry

theorem lt_blsub {o} (f : ∀ a < o, Ordinal) (i h) : f i h < blsub o f :=
  blsub_le_iff.1 le_rfl _ _

@[target]
theorem lt_blsub_iff {o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{max u v}} {a} :
    a < blsub.{_, v} o f ↔ ∃ i hi, a ≤ f i hi := by sorry

@[target]
theorem bsup_le_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f ≤ blsub.{_, v} o f := by sorry

@[target]
theorem blsub_le_bsup_succ {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    blsub.{_, v} o f ≤ succ (bsup.{_, v} o f) := by sorry

@[target]
theorem bsup_eq_blsub_or_succ_bsup_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ∨ succ (bsup.{_, v} o f) = blsub.{_, v} o f := by sorry

@[target]
theorem bsup_succ_le_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    succ (bsup.{_, v} o f) ≤ blsub.{_, v} o f ↔ ∃ i hi, f i hi = bsup.{_, v} o f := by sorry

@[target]
theorem bsup_succ_eq_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    succ (bsup.{_, v} o f) = blsub.{_, v} o f ↔ ∃ i hi, f i hi = bsup.{_, v} o f := by sorry

@[target]
theorem bsup_eq_blsub_iff_succ {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ↔ ∀ a < blsub.{_, v} o f, succ a < blsub.{_, v} o f := by sorry

@[target]
theorem bsup_eq_blsub_iff_lt_bsup {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ↔ ∀ i hi, f i hi < bsup.{_, v} o f := by sorry

@[target]
theorem bsup_eq_blsub_of_lt_succ_limit {o : Ordinal.{u}} (ho : IsLimit o)
    {f : ∀ a < o, Ordinal.{max u v}} (hf : ∀ a ha, f a ha < f (succ a) (ho.succ_lt ha)) :
    bsup.{_, v} o f = blsub.{_, v} o f := by sorry

@[target]
theorem blsub_succ_of_mono {o : Ordinal.{u}} {f : ∀ a < succ o, Ordinal.{max u v}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) : blsub.{_, v} _ f = succ (f o (lt_succ o)) := by sorry

@[target, simp]
theorem blsub_eq_zero_iff {o} {f : ∀ a < o, Ordinal} : blsub o f = 0 ↔ o = 0 := by sorry

@[target, simp]
theorem blsub_zero (f : ∀ a < (0 : Ordinal), Ordinal) : blsub 0 f = 0 := by sorry

theorem blsub_pos {o : Ordinal} (ho : 0 < o) (f : ∀ a < o, Ordinal) : 0 < blsub o f :=
  (Ordinal.zero_le _).trans_lt (lt_blsub f 0 ho)

@[target]
theorem blsub_type {α : Type u} (r : α → α → Prop) [IsWellOrder α r]
    (f : ∀ a < type r, Ordinal.{max u v}) :
    blsub.{_, v} (type r) f = lsub.{_, v} fun a => f (typein r a) (typein_lt_type _ _) := by sorry

theorem blsub_const {o : Ordinal} (ho : o ≠ 0) (a : Ordinal) :
    (blsub.{u, v} o fun _ _ => a) = succ a :=
  bsup_const.{u, v} ho (succ a)

@[target, simp]
theorem blsub_one (f : ∀ a < (1 : Ordinal), Ordinal) : blsub 1 f = succ (f 0 zero_lt_one) := by sorry

@[target, simp]
theorem blsub_id : ∀ o, (blsub.{u, u} o fun x _ => x) = o := by sorry

@[target]
theorem bsup_id_limit {o : Ordinal} : (∀ a < o, succ a < o) → (bsup.{u, u} o fun x _ => x) = o := by sorry

@[target, simp]
theorem bsup_id_succ (o) : (bsup.{u, u} (succ o) fun x _ => x) = o := by sorry

@[target]
theorem blsub_le_of_brange_subset {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : brange o f ⊆ brange o' g) : blsub.{u, max v w} o f ≤ blsub.{v, max u w} o' g := by sorry

@[target]
theorem blsub_eq_of_brange_eq {o o'} {f : ∀ a < o, Ordinal} {g : ∀ a < o', Ordinal}
    (h : { o | ∃ i hi, f i hi = o } = { o | ∃ i hi, g i hi = o }) :
    blsub.{u, max v w} o f = blsub.{v, max u w} o' g := by sorry

theorem bsup_comp {o o' : Ordinal.{max u v}} {f : ∀ a < o, Ordinal.{max u v w}}
    (hf : ∀ {i j} (hi) (hj), i ≤ j → f i hi ≤ f j hj) {g : ∀ a < o', Ordinal.{max u v}}
    (hg : blsub.{_, u} o' g = o) :
    (bsup.{_, w} o' fun a ha => f (g a ha) (by rw [← hg]; apply lt_blsub)) = bsup.{_, w} o f := by
  apply le_antisymm <;> refine bsup_le fun i hi => ?_
  · apply le_bsup
  · rw [← hg, lt_blsub_iff] at hi
    rcases hi with ⟨j, hj, hj'⟩
    exact (hf _ _ hj').trans (le_bsup _ _ _)

@[target]
theorem blsub_comp {o o' : Ordinal.{max u v}} {f : ∀ a < o, Ordinal.{max u v w}}
    (hf : ∀ {i j} (hi) (hj), i ≤ j → f i hi ≤ f j hj) {g : ∀ a < o', Ordinal.{max u v}}
    (hg : blsub.{_, u} o' g = o) :
    (blsub.{_, w} o' fun a ha => f (g a ha) (by rw [← hg]; apply lt_blsub)) = blsub.{_, w} o f := by sorry

theorem IsNormal.bsup_eq {f : Ordinal.{u} → Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
    (h : IsLimit o) : (Ordinal.bsup.{_, v} o fun x _ => f x) = f o := by
  rw [← IsNormal.bsup.{u, u, v} H (fun x _ => x) h.ne_bot, bsup_id_limit fun _ ↦ h.succ_lt]

@[target]
theorem IsNormal.blsub_eq {f : Ordinal.{u} → Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
    (h : IsLimit o) : (blsub.{_, v} o fun x _ => f x) = f o := by sorry

@[target]
theorem isNormal_iff_lt_succ_and_bsup_eq {f : Ordinal.{u} → Ordinal.{max u v}} :
    IsNormal f ↔ (∀ a, f a < f (succ a)) ∧ ∀ o, IsLimit o → (bsup.{_, v} o fun x _ => f x) = f o := by sorry

@[target]
theorem isNormal_iff_lt_succ_and_blsub_eq {f : Ordinal.{u} → Ordinal.{max u v}} :
    IsNormal f ↔ (∀ a, f a < f (succ a)) ∧
      ∀ o, IsLimit o → (blsub.{_, v} o fun x _ => f x) = f o := by sorry

@[target]
theorem IsNormal.eq_iff_zero_and_succ {f g : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f)
    (hg : IsNormal g) : f = g ↔ f 0 = g 0 ∧ ∀ a, f a = g a → f (succ a) = g (succ a) := by sorry

/-- A two-argument version of `Ordinal.blsub`.

Deprecated. If you need this value explicitly, write it in terms of `iSup`. If you just want an
upper bound for the image of `op`, use that `Iio a ×ˢ Iio b` is a small set. -/
@[deprecated "No deprecation message was provided."  (since := "2024-10-11")]
def blsub₂ (o₁ o₂ : Ordinal) (op : {a : Ordinal} → (a < o₁) → {b : Ordinal} → (b < o₂) → Ordinal) :
    Ordinal :=
  lsub (fun x : o₁.toType × o₂.toType => op (typein_lt_self x.1) (typein_lt_self x.2))

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-11")]
theorem lt_blsub₂ {o₁ o₂ : Ordinal}
    (op : {a : Ordinal} → (a < o₁) → {b : Ordinal} → (b < o₂) → Ordinal) {a b : Ordinal}
    (ha : a < o₁) (hb : b < o₂) : op ha hb < blsub₂ o₁ o₂ op := by sorry

end blsub

section mex

/-! ### Minimum excluded ordinals -/


/-- The minimum excluded ordinal in a family of ordinals. -/
@[deprecated "use sInf sᶜ instead" (since := "2024-09-20")]
def mex {ι : Type u} (f : ι → Ordinal.{max u v}) : Ordinal :=
  sInf (Set.range f)ᶜ

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem mex_not_mem_range {ι : Type u} (f : ι → Ordinal.{max u v}) : mex.{_, v} f ∉ Set.range f := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem le_mex_of_forall {ι : Type u} {f : ι → Ordinal.{max u v}} {a : Ordinal}
    (H : ∀ b < a, ∃ i, f i = b) : a ≤ mex.{_, v} f := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem ne_mex {ι : Type u} (f : ι → Ordinal.{max u v}) : ∀ i, f i ≠ mex.{_, v} f := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem mex_le_of_ne {ι} {f : ι → Ordinal} {a} (ha : ∀ i, f i ≠ a) : mex f ≤ a := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem exists_of_lt_mex {ι} {f : ι → Ordinal} {a} (ha : a < mex f) : ∃ i, f i = a := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem mex_le_lsub {ι : Type u} (f : ι → Ordinal.{max u v}) : mex.{_, v} f ≤ lsub.{_, v} f := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem mex_monotone {α β : Type u} {f : α → Ordinal.{max u v}} {g : β → Ordinal.{max u v}}
    (h : Set.range f ⊆ Set.range g) : mex.{_, v} f ≤ mex.{_, v} g := by sorry

set_option linter.deprecated false in
@[target, deprecated sInf_compl_lt_ord_succ (since := "2024-09-20")]
theorem mex_lt_ord_succ_mk {ι : Type u} (f : ι → Ordinal.{u}) :
    mex.{_, u} f < (succ #ι).ord := by sorry

set_option linter.deprecated false in
/-- The minimum excluded ordinal of a family of ordinals indexed by the set of ordinals less than
    some `o : Ordinal.{u}`. This is a special case of `mex` over the family provided by
    `familyOfBFamily`.

    This is to `mex` as `bsup` is to `sup`. -/
@[deprecated "use sInf sᶜ instead" (since := "2024-09-20")]
def bmex (o : Ordinal) (f : ∀ a < o, Ordinal) : Ordinal :=
  mex (familyOfBFamily o f)

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem bmex_not_mem_brange {o : Ordinal} (f : ∀ a < o, Ordinal) : bmex o f ∉ brange o f := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem le_bmex_of_forall {o : Ordinal} (f : ∀ a < o, Ordinal) {a : Ordinal}
    (H : ∀ b < a, ∃ i hi, f i hi = b) : a ≤ bmex o f := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem ne_bmex {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) {i} (hi) :
    f i hi ≠ bmex.{_, v} o f := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem bmex_le_of_ne {o : Ordinal} {f : ∀ a < o, Ordinal} {a} (ha : ∀ i hi, f i hi ≠ a) :
    bmex o f ≤ a := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem exists_of_lt_bmex {o : Ordinal} {f : ∀ a < o, Ordinal} {a} (ha : a < bmex o f) :
    ∃ i hi, f i hi = a := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem bmex_le_blsub {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{max u v}) :
    bmex.{_, v} o f ≤ blsub.{_, v} o f := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem bmex_monotone {o o' : Ordinal.{u}}
    {f : ∀ a < o, Ordinal.{max u v}} {g : ∀ a < o', Ordinal.{max u v}}
    (h : brange o f ⊆ brange o' g) : bmex.{_, v} o f ≤ bmex.{_, v} o' g := by sorry

set_option linter.deprecated false in
@[target, deprecated sInf_compl_lt_ord_succ (since := "2024-09-20")]
theorem bmex_lt_ord_succ_card {o : Ordinal.{u}} (f : ∀ a < o, Ordinal.{u}) :
    bmex.{_, u} o f < (succ o.card).ord := by sorry

end mex

end Ordinal

/-! ### Results about injectivity and surjectivity -/


@[target]
theorem not_surjective_of_ordinal {α : Type u} (f : α → Ordinal.{u}) : ¬Surjective f := by sorry

@[target]
theorem not_injective_of_ordinal {α : Type u} (f : Ordinal.{u} → α) : ¬Injective f := by sorry

@[target]
theorem not_surjective_of_ordinal_of_small {α : Type v} [Small.{u} α] (f : α → Ordinal.{u}) :
    ¬Surjective f := by sorry

@[target]
theorem not_injective_of_ordinal_of_small {α : Type v} [Small.{u} α] (f : Ordinal.{u} → α) :
    ¬Injective f := by sorry

/-- The type of ordinals in universe `u` is not `Small.{u}`. This is the type-theoretic analog of
the Burali-Forti paradox. -/
@[target]
theorem not_small_ordinal : ¬Small.{u} Ordinal.{max u v} := by sorry

instance Ordinal.uncountable : Uncountable Ordinal.{u} :=
  Uncountable.of_not_small not_small_ordinal.{u}

theorem Ordinal.not_bddAbove_compl_of_small (s : Set Ordinal.{u}) [hs : Small.{u} s] :
    ¬BddAbove sᶜ := by
  rw [bddAbove_iff_small]
  intro h
  have := small_union s sᶜ
  rw [union_compl_self, small_univ_iff] at this
  exact not_small_ordinal this

/-! ### Casting naturals into ordinals, compatibility with operations -/


namespace Ordinal

instance instCharZero : CharZero Ordinal := by
  refine ⟨fun a b h ↦ ?_⟩
  rwa [← Cardinal.ord_nat, ← Cardinal.ord_nat, Cardinal.ord_inj, Nat.cast_inj] at h

@[target, simp]
theorem one_add_natCast (m : ℕ) : 1 + (m : Ordinal) = succ m := by sorry

@[target, simp]
theorem one_add_ofNat (m : ℕ) [m.AtLeastTwo] :
    1 + (ofNat(m) : Ordinal) = Order.succ (OfNat.ofNat m : Ordinal) := by sorry

@[target, simp, norm_cast]
theorem natCast_mul (m : ℕ) : ∀ n : ℕ, ((m * n : ℕ) : Ordinal) = m * n := by sorry

@[target, deprecated Nat.cast_le (since := "2024-10-17")]
theorem natCast_le {m n : ℕ} : (m : Ordinal) ≤ n ↔ m ≤ n := by sorry

@[target, deprecated Nat.cast_inj (since := "2024-10-17")]
theorem natCast_inj {m n : ℕ} : (m : Ordinal) = n ↔ m = n := by sorry

@[target, deprecated Nat.cast_lt (since := "2024-10-17")]
theorem natCast_lt {m n : ℕ} : (m : Ordinal) < n ↔ m < n := by sorry

@[target, deprecated Nat.cast_eq_zero (since := "2024-10-17")]
theorem natCast_eq_zero {n : ℕ} : (n : Ordinal) = 0 ↔ n = 0 := by sorry

@[target, deprecated Nat.cast_ne_zero (since := "2024-10-17")]
theorem natCast_ne_zero {n : ℕ} : (n : Ordinal) ≠ 0 ↔ n ≠ 0 := by sorry

@[target, deprecated Nat.cast_pos' (since := "2024-10-17")]
theorem natCast_pos {n : ℕ} : (0 : Ordinal) < n ↔ 0 < n := by sorry

@[target, simp, norm_cast]
theorem natCast_sub (m n : ℕ) : ((m - n : ℕ) : Ordinal) = m - n := by sorry

@[target, simp, norm_cast]
theorem natCast_div (m n : ℕ) : ((m / n : ℕ) : Ordinal) = m / n := by sorry

@[target, simp, norm_cast]
theorem natCast_mod (m n : ℕ) : ((m % n : ℕ) : Ordinal) = m % n := by sorry

@[target, simp]
theorem lift_natCast : ∀ n : ℕ, lift.{u, v} n = n := by sorry

@[target, simp]
theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift.{u, v} ofNat(n) = OfNat.ofNat n := by sorry

/-! ### Properties of ω -/

@[target]
theorem lt_add_of_limit {a b c : Ordinal.{u}} (h : IsLimit c) :
    a < b + c ↔ ∃ c' < c, a < b + c' := by sorry

@[target]
theorem lt_omega0 {o : Ordinal} : o < ω ↔ ∃ n : ℕ, o = n := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias lt_omega := lt_omega0

@[target]
theorem nat_lt_omega0 (n : ℕ) : ↑n < ω := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias nat_lt_omega := nat_lt_omega0

@[target]
theorem eq_nat_or_omega0_le (o : Ordinal) : (∃ n : ℕ, o = n) ∨ ω ≤ o := by sorry

theorem omega0_pos : 0 < ω :=
  nat_lt_omega0 0

theorem omega0_ne_zero : ω ≠ 0 :=
  omega0_pos.ne'

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias omega_ne_zero := omega0_ne_zero

@[target]
theorem one_lt_omega0 : 1 < ω := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias one_lt_omega := one_lt_omega0

@[target]
theorem isLimit_omega0 : IsLimit ω := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-10-14")]
alias omega0_isLimit := isLimit_omega0

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias omega_isLimit := isLimit_omega0

@[target]
theorem omega0_le {o : Ordinal} : ω ≤ o ↔ ∀ n : ℕ, ↑n ≤ o := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias omega_le := omega0_le

@[target, simp]
theorem iSup_natCast : iSup Nat.cast = ω := by sorry

@[target]
theorem nat_lt_limit {o} (h : IsLimit o) : ∀ n : ℕ, ↑n < o := by sorry

@[target]
theorem omega0_le_of_isLimit {o} (h : IsLimit o) : ω ≤ o := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias omega_le_of_isLimit := omega0_le_of_isLimit

@[target]
theorem natCast_add_omega0 (n : ℕ) : n + ω = ω := by sorry

@[target]
theorem one_add_omega0 : 1 + ω = ω := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias one_add_omega := one_add_omega0

@[target]
theorem add_omega0 {a : Ordinal} (h : a < ω) : a + ω = ω := by sorry

@[deprecated (since := "2024-09-30")]
alias add_omega := add_omega0

@[target, simp]
theorem natCast_add_of_omega0_le {o} (h : ω ≤ o) (n : ℕ) : n + o = o := by sorry

@[target, simp]
theorem one_add_of_omega0_le {o} (h : ω ≤ o) : 1 + o = o := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias one_add_of_omega_le := one_add_of_omega0_le

@[target]
theorem isLimit_iff_omega0_dvd {a : Ordinal} : IsLimit a ↔ a ≠ 0 ∧ ω ∣ a := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias isLimit_iff_omega_dvd := isLimit_iff_omega0_dvd

@[target]
theorem IsNormal.apply_omega0 {f : Ordinal.{u} → Ordinal.{v}} (hf : IsNormal f) :
    ⨆ n : ℕ, f n = f ω := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias IsNormal.apply_omega := IsNormal.apply_omega0

@[target, simp]
theorem iSup_add_nat (o : Ordinal) : ⨆ n : ℕ, o + n = o + ω := by sorry

set_option linter.deprecated false in
@[deprecated iSup_add_nat (since := "2024-08-27")]
theorem sup_add_nat (o : Ordinal) : (sup fun n : ℕ => o + n) = o + ω :=
  (isNormal_add_right o).apply_omega0

@[target, simp]
theorem iSup_mul_nat (o : Ordinal) : ⨆ n : ℕ, o * n = o * ω := by sorry

set_option linter.deprecated false in
@[target, deprecated iSup_add_nat (since := "2024-08-27")]
theorem sup_mul_nat (o : Ordinal) : (sup fun n : ℕ => o * n) = o * ω := by sorry

end Ordinal

namespace Cardinal

open Ordinal

@[simp]
theorem add_one_of_aleph0_le {c} (h : ℵ₀ ≤ c) : c + 1 = c := by
  rw [add_comm, ← card_ord c, ← card_one, ← card_add, one_add_of_omega0_le]
  rwa [← ord_aleph0, ord_le_ord]

@[target]
theorem isLimit_ord {c} (co : ℵ₀ ≤ c) : (ord c).IsLimit := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-10-14")]
alias ord_isLimit := isLimit_ord

@[target]
theorem noMaxOrder {c} (h : ℵ₀ ≤ c) : NoMaxOrder c.ord.toType := by sorry

end Cardinal

set_option linter.style.longFile 2600
