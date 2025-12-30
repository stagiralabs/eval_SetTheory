import VerifiedAgora.tagger
/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic.Abel

/-!
# Natural operations on ordinals

The goal of this file is to define natural addition and multiplication on ordinals, also known as
the Hessenberg sum and product, and provide a basic API. The natural addition of two ordinals
`a ♯ b` is recursively defined as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for `a' < a`
and `b' < b`. The natural multiplication `a ⨳ b` is likewise recursively defined as the least
ordinal such that `a ⨳ b ♯ a' ⨳ b'` is greater than `a' ⨳ b ♯ a ⨳ b'` for any `a' < a` and
`b' < b`.

These operations form a rich algebraic structure: they're commutative, associative, preserve order,
have the usual `0` and `1` from ordinals, and distribute over one another.

Moreover, these operations are the addition and multiplication of ordinals when viewed as
combinatorial `Game`s. This makes them particularly useful for game theory.

Finally, both operations admit simple, intuitive descriptions in terms of the Cantor normal form.
The natural addition of two ordinals corresponds to adding their Cantor normal forms as if they were
polynomials in `ω`. Likewise, their natural multiplication corresponds to multiplying the Cantor
normal forms as polynomials.

## Implementation notes

Given the rich algebraic structure of these two operations, we choose to create a type synonym
`NatOrdinal`, where we provide the appropriate instances. However, to avoid casting back and forth
between both types, we attempt to prove and state most results on `Ordinal`.

## Todo

- Prove the characterizations of natural addition and multiplication in terms of the Cantor normal
  form.
-/

universe u v

open Function Order Set

noncomputable section

/-! ### Basic casts between `Ordinal` and `NatOrdinal` -/

/-- A type synonym for ordinals with natural addition and multiplication. -/
def NatOrdinal : Type _ :=
  -- Porting note: used to derive LinearOrder & SuccOrder but need to manually define
  Ordinal deriving Zero, Inhabited, One, WellFoundedRelation

instance NatOrdinal.instLinearOrder : LinearOrder NatOrdinal := Ordinal.instLinearOrder
instance NatOrdinal.instSuccOrder : SuccOrder NatOrdinal := Ordinal.instSuccOrder
instance NatOrdinal.instOrderBot : OrderBot NatOrdinal := Ordinal.instOrderBot
instance NatOrdinal.instNoMaxOrder : NoMaxOrder NatOrdinal := Ordinal.instNoMaxOrder
instance NatOrdinal.instZeroLEOneClass : ZeroLEOneClass NatOrdinal := Ordinal.instZeroLEOneClass
instance NatOrdinal.instNeZeroOne : NeZero (1 : NatOrdinal) := Ordinal.instNeZeroOne

instance NatOrdinal.uncountable : Uncountable NatOrdinal :=
  Ordinal.uncountable

/-- The identity function between `Ordinal` and `NatOrdinal`. -/
@[match_pattern]
def Ordinal.toNatOrdinal : Ordinal ≃o NatOrdinal :=
  OrderIso.refl _

/-- The identity function between `NatOrdinal` and `Ordinal`. -/
@[match_pattern]
def NatOrdinal.toOrdinal : NatOrdinal ≃o Ordinal :=
  OrderIso.refl _

namespace NatOrdinal

open Ordinal

@[target, simp]
theorem toOrdinal_symm_eq : NatOrdinal.toOrdinal.symm = Ordinal.toNatOrdinal := by sorry

@[simp]
theorem toOrdinal_toNatOrdinal (a : NatOrdinal) : a.toOrdinal.toNatOrdinal = a :=
  rfl

@[target]
theorem lt_wf : @WellFounded NatOrdinal (· < ·) := by sorry

instance : WellFoundedLT NatOrdinal :=
  Ordinal.wellFoundedLT

instance : ConditionallyCompleteLinearOrderBot NatOrdinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[target, simp]
theorem bot_eq_zero : ⊥ = 0 := by sorry

@[target, simp]
theorem toOrdinal_zero : toOrdinal 0 = 0 := by sorry

@[simp]
theorem toOrdinal_one : toOrdinal 1 = 1 :=
  rfl

@[target, simp]
theorem toOrdinal_eq_zero {a} : toOrdinal a = 0 ↔ a = 0 := by sorry

@[simp]
theorem toOrdinal_eq_one {a} : toOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl

@[target, simp]
theorem toOrdinal_max (a b : NatOrdinal) : toOrdinal (max a b) = max (toOrdinal a) (toOrdinal b) := by sorry

@[target, simp]
theorem toOrdinal_min (a b : NatOrdinal) : toOrdinal (min a b) = min (toOrdinal a) (toOrdinal b) := by sorry

theorem succ_def (a : NatOrdinal) : succ a = toNatOrdinal (toOrdinal a + 1) :=
  rfl

/-- A recursor for `NatOrdinal`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : NatOrdinal → Sort*} (h : ∀ a, β (toNatOrdinal a)) : ∀ a, β a := fun a =>
  h (toOrdinal a)

/-- `Ordinal.induction` but for `NatOrdinal`. -/
@[target]
theorem induction {p : NatOrdinal → Prop} : ∀ (i) (_ : ∀ j, (∀ k, k < j → p k) → p j), p i := by sorry

end NatOrdinal

namespace Ordinal

variable {a b c : Ordinal.{u}}

@[target, simp]
theorem toNatOrdinal_symm_eq : toNatOrdinal.symm = NatOrdinal.toOrdinal := by sorry

@[target, simp]
theorem toNatOrdinal_toOrdinal (a : Ordinal) : a.toNatOrdinal.toOrdinal = a := by sorry

@[target, simp]
theorem toNatOrdinal_zero : toNatOrdinal 0 = 0 := by sorry

@[target, simp]
theorem toNatOrdinal_one : toNatOrdinal 1 = 1 := by sorry

@[simp]
theorem toNatOrdinal_eq_zero (a) : toNatOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl

@[target, simp]
theorem toNatOrdinal_eq_one (a) : toNatOrdinal a = 1 ↔ a = 1 := by sorry

@[simp]
theorem toNatOrdinal_max (a b : Ordinal) :
    toNatOrdinal (max a b) = max (toNatOrdinal a) (toNatOrdinal b) :=
  rfl

@[target, simp]
theorem toNatOrdinal_min (a b : Ordinal) :
    toNatOrdinal (min a b) = min (toNatOrdinal a) (toNatOrdinal b) := by sorry

/-! We place the definitions of `nadd` and `nmul` before actually developing their API, as this
guarantees we only need to open the `NaturalOps` locale once. -/

/-- Natural addition on ordinals `a ♯ b`, also known as the Hessenberg sum, is recursively defined
as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for all `a' < a` and `b' < b`. In contrast
to normal ordinal addition, it is commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
noncomputable def nadd (a b : Ordinal.{u}) : Ordinal.{u} :=
  max (⨆ x : Iio a, succ (nadd x.1 b)) (⨆ x : Iio b, succ (nadd a x.1))
termination_by (a, b)
decreasing_by all_goals cases x; decreasing_tactic

@[inherit_doc]
scoped[NaturalOps] infixl:65 " ♯ " => Ordinal.nadd

open NaturalOps

/-- Natural multiplication on ordinals `a ⨳ b`, also known as the Hessenberg product, is recursively
defined as the least ordinal such that `a ⨳ b ♯ a' ⨳ b'` is greater than `a' ⨳ b ♯ a ⨳ b'` for all
`a' < a` and `b < b'`. In contrast to normal ordinal multiplication, it is commutative and
distributive (over natural addition).

Natural multiplication can equivalently be characterized as the ordinal resulting from multiplying
the Cantor normal forms of `a` and `b` as if they were polynomials in `ω`. Addition of exponents is
done via natural addition. -/
noncomputable def nmul (a b : Ordinal.{u}) : Ordinal.{u} :=
  sInf {c | ∀ a' < a, ∀ b' < b, nmul a' b ♯ nmul a b' < c ♯ nmul a' b'}
termination_by (a, b)

@[inherit_doc]
scoped[NaturalOps] infixl:70 " ⨳ " => Ordinal.nmul

/-! ### Natural addition -/

@[target]
theorem lt_nadd_iff : a < b ♯ c ↔ (∃ b' < b, a ≤ b' ♯ c) ∨ ∃ c' < c, a ≤ b ♯ c' := by sorry

@[target]
theorem nadd_le_iff : b ♯ c ≤ a ↔ (∀ b' < b, b' ♯ c < a) ∧ ∀ c' < c, b ♯ c' < a := by sorry

@[target]
theorem nadd_lt_nadd_left (h : b < c) (a) : a ♯ b < a ♯ c := by sorry

@[target]
theorem nadd_lt_nadd_right (h : b < c) (a) : b ♯ a < c ♯ a := by sorry

@[target]
theorem nadd_le_nadd_left (h : b ≤ c) (a) : a ♯ b ≤ a ♯ c := by sorry

theorem nadd_le_nadd_right (h : b ≤ c) (a) : b ♯ a ≤ c ♯ a := by
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact (nadd_lt_nadd_right h a).le
  · exact le_rfl

variable (a b)

theorem nadd_comm (a b) : a ♯ b = b ♯ a := by
  rw [nadd, nadd, max_comm]
  congr <;> ext x <;> cases x <;> apply congr_arg _ (nadd_comm _ _)
termination_by (a, b)

@[target, deprecated "blsub will soon be deprecated" (since := "2024-11-18")]
theorem blsub_nadd_of_mono {f : ∀ c < a ♯ b, Ordinal.{max u v}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) :
    blsub.{u,v} _ f =
      max (blsub.{u, v} a fun a' ha' => f (a' ♯ b) <| nadd_lt_nadd_right ha' b)
        (blsub.{u, v} b fun b' hb' => f (a ♯ b') <| nadd_lt_nadd_left hb' a) := by sorry

private theorem iSup_nadd_of_monotone {a b} (f : Ordinal.{u} → Ordinal.{u}) (h : Monotone f) :
    ⨆ x : Iio (a ♯ b), f x = max (⨆ a' : Iio a, f (a'.1 ♯ b)) (⨆ b' : Iio b, f (a ♯ b'.1)) := by
  apply (max_le _ _).antisymm'
  · rw [Ordinal.iSup_le_iff]
    rintro ⟨i, hi⟩
    obtain ⟨x, hx, hi⟩ | ⟨x, hx, hi⟩ := lt_nadd_iff.1 hi
    · exact le_max_of_le_left ((h hi).trans <| Ordinal.le_iSup (fun x : Iio a ↦ _) ⟨x, hx⟩)
    · exact le_max_of_le_right ((h hi).trans <| Ordinal.le_iSup (fun x : Iio b ↦ _) ⟨x, hx⟩)
  all_goals
    apply csSup_le_csSup' (bddAbove_of_small _)
    rintro _ ⟨⟨c, hc⟩, rfl⟩
    refine mem_range_self (⟨_, ?_⟩ : Iio _)
    apply_rules [nadd_lt_nadd_left, nadd_lt_nadd_right]

@[target]
theorem nadd_assoc (a b c) : a ♯ b ♯ c = a ♯ (b ♯ c) := by sorry

@[target, simp]
theorem nadd_zero (a : Ordinal) : a ♯ 0 = a := by sorry

@[target, simp]
theorem zero_nadd : 0 ♯ a = a := by sorry

@[target, simp]
theorem nadd_one (a : Ordinal) : a ♯ 1 = succ a := by sorry

@[simp]
theorem one_nadd : 1 ♯ a = succ a := by rw [nadd_comm, nadd_one]

@[target]
theorem nadd_succ : a ♯ succ b = succ (a ♯ b) := by sorry

@[target]
theorem succ_nadd : succ a ♯ b = succ (a ♯ b) := by sorry

@[target, simp]
theorem nadd_nat (n : ℕ) : a ♯ n = a + n := by sorry

@[target, simp]
theorem nat_nadd (n : ℕ) : ↑n ♯ a = a + n := by sorry

@[target]
theorem add_le_nadd : a + b ≤ a ♯ b := by sorry

end Ordinal

namespace NatOrdinal

open Ordinal NaturalOps

instance : Add NatOrdinal := ⟨nadd⟩
instance : SuccAddOrder NatOrdinal := ⟨fun x => (nadd_one x).symm⟩

instance : AddLeftStrictMono NatOrdinal.{u} :=
  ⟨fun a _ _ h => nadd_lt_nadd_left h a⟩

instance : AddLeftMono NatOrdinal.{u} :=
  ⟨fun a _ _ h => nadd_le_nadd_left h a⟩

instance : AddLeftReflectLE NatOrdinal.{u} :=
  ⟨fun a b c h => by
    by_contra! h'
    exact h.not_lt (add_lt_add_left h' a)⟩

instance : OrderedCancelAddCommMonoid NatOrdinal :=
  { NatOrdinal.instLinearOrder with
    add := (· + ·)
    add_assoc := nadd_assoc
    add_le_add_left := fun _ _ => add_le_add_left
    le_of_add_le_add_left := fun _ _ _ => le_of_add_le_add_left
    zero := 0
    zero_add := zero_nadd
    add_zero := nadd_zero
    add_comm := nadd_comm
    nsmul := nsmulRec }

instance : AddMonoidWithOne NatOrdinal :=
  AddMonoidWithOne.unary

@[target, deprecated Order.succ_eq_add_one (since := "2024-09-04")]
theorem add_one_eq_succ (a : NatOrdinal) : a + 1 = succ a := by sorry

@[target, simp]
theorem toOrdinal_cast_nat (n : ℕ) : toOrdinal n = n := by sorry

end NatOrdinal

open NatOrdinal

open NaturalOps

namespace Ordinal

@[target]
theorem nadd_eq_add (a b : Ordinal) : a ♯ b = toOrdinal (toNatOrdinal a + toNatOrdinal b) := by sorry

@[simp]
theorem toNatOrdinal_cast_nat (n : ℕ) : toNatOrdinal n = n := by
  rw [← toOrdinal_cast_nat n]
  rfl

theorem lt_of_nadd_lt_nadd_left : ∀ {a b c}, a ♯ b < a ♯ c → b < c :=
  @lt_of_add_lt_add_left NatOrdinal _ _ _

@[target]
theorem lt_of_nadd_lt_nadd_right : ∀ {a b c}, b ♯ a < c ♯ a → b < c := by sorry

@[target]
theorem le_of_nadd_le_nadd_left : ∀ {a b c}, a ♯ b ≤ a ♯ c → b ≤ c := by sorry

@[target]
theorem le_of_nadd_le_nadd_right : ∀ {a b c}, b ♯ a ≤ c ♯ a → b ≤ c := by sorry

@[target, simp]
theorem nadd_lt_nadd_iff_left : ∀ (a) {b c}, a ♯ b < a ♯ c ↔ b < c := by sorry

@[target, simp]
theorem nadd_lt_nadd_iff_right : ∀ (a) {b c}, b ♯ a < c ♯ a ↔ b < c := by sorry

@[target, simp]
theorem nadd_le_nadd_iff_left : ∀ (a) {b c}, a ♯ b ≤ a ♯ c ↔ b ≤ c := by sorry

@[simp]
theorem nadd_le_nadd_iff_right : ∀ (a) {b c}, b ♯ a ≤ c ♯ a ↔ b ≤ c :=
  @_root_.add_le_add_iff_right NatOrdinal _ _ _ _

@[target]
theorem nadd_le_nadd : ∀ {a b c d}, a ≤ b → c ≤ d → a ♯ c ≤ b ♯ d := by sorry

@[target]
theorem nadd_lt_nadd : ∀ {a b c d}, a < b → c < d → a ♯ c < b ♯ d := by sorry

@[target]
theorem nadd_lt_nadd_of_lt_of_le : ∀ {a b c d}, a < b → c ≤ d → a ♯ c < b ♯ d := by sorry

@[target]
theorem nadd_lt_nadd_of_le_of_lt : ∀ {a b c d}, a ≤ b → c < d → a ♯ c < b ♯ d := by sorry

@[target]
theorem nadd_left_cancel : ∀ {a b c}, a ♯ b = a ♯ c → b = c := by sorry

@[target]
theorem nadd_right_cancel : ∀ {a b c}, a ♯ b = c ♯ b → a = c := by sorry

@[simp]
theorem nadd_left_cancel_iff : ∀ {a b c}, a ♯ b = a ♯ c ↔ b = c :=
  @add_left_cancel_iff NatOrdinal _ _

@[target, simp]
theorem nadd_right_cancel_iff : ∀ {a b c}, b ♯ a = c ♯ a ↔ b = c := by sorry

theorem le_nadd_self {a b} : a ≤ b ♯ a := by simpa using nadd_le_nadd_right (Ordinal.zero_le b) a

@[target]
theorem le_nadd_left {a b c} (h : a ≤ c) : a ≤ b ♯ c := by sorry

@[target]
theorem le_self_nadd {a b} : a ≤ a ♯ b := by sorry

@[target]
theorem le_nadd_right {a b c} (h : a ≤ b) : a ≤ b ♯ c := by sorry

@[target]
theorem nadd_left_comm : ∀ a b c, a ♯ (b ♯ c) = b ♯ (a ♯ c) := by sorry

@[target]
theorem nadd_right_comm : ∀ a b c, a ♯ b ♯ c = a ♯ c ♯ b := by sorry

/-! ### Natural multiplication -/

variable {a b c d : Ordinal.{u}}

@[target, deprecated "avoid using the definition of `nmul` directly" (since := "2024-11-19")]
theorem nmul_def (a b : Ordinal) :
    a ⨳ b = sInf {c | ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'} := by sorry

/-- The set in the definition of `nmul` is nonempty. -/
private theorem nmul_nonempty (a b : Ordinal.{u}) :
    {c : Ordinal.{u} | ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'}.Nonempty := by
  obtain ⟨c, hc⟩ : BddAbove ((fun x ↦ x.1 ⨳ b ♯ a ⨳ x.2) '' Set.Iio a ×ˢ Set.Iio b) :=
    bddAbove_of_small _
  exact ⟨_, fun x hx y hy ↦
    (lt_succ_of_le <| hc <| Set.mem_image_of_mem _ <| Set.mk_mem_prod hx hy).trans_le le_self_nadd⟩

@[target]
theorem nmul_nadd_lt {a' b' : Ordinal} (ha : a' < a) (hb : b' < b) :
    a' ⨳ b ♯ a ⨳ b' < a ⨳ b ♯ a' ⨳ b' := by sorry

@[target]
theorem nmul_nadd_le {a' b' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) :
    a' ⨳ b ♯ a ⨳ b' ≤ a ⨳ b ♯ a' ⨳ b' := by sorry

@[target]
theorem lt_nmul_iff : c < a ⨳ b ↔ ∃ a' < a, ∃ b' < b, c ♯ a' ⨳ b' ≤ a' ⨳ b ♯ a ⨳ b' := by sorry

@[target]
theorem nmul_le_iff : a ⨳ b ≤ c ↔ ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b' := by sorry

@[target]
theorem nmul_comm (a b) : a ⨳ b = b ⨳ a := by sorry

@[target, simp]
theorem nmul_zero (a) : a ⨳ 0 = 0 := by sorry

@[target, simp]
theorem zero_nmul (a) : 0 ⨳ a = 0 := by sorry

@[simp]
theorem nmul_one (a : Ordinal) : a ⨳ 1 = a := by
  rw [nmul]
  convert csInf_Ici
  ext b
  refine ⟨fun H ↦ le_of_forall_lt (a := a) fun c hc ↦ ?_, fun ha c hc ↦ ?_⟩
  -- Porting note: had to add arguments to `nmul_one` in the next two lines
  -- for the termination checker.
  · simpa [nmul_one c] using H c hc
  · simpa [nmul_one c] using hc.trans_le ha
termination_by a

@[target, simp]
theorem one_nmul (a) : 1 ⨳ a = a := by sorry

@[target]
theorem nmul_lt_nmul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c ⨳ a < c ⨳ b := by sorry

theorem nmul_lt_nmul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a ⨳ c < b ⨳ c :=
  lt_nmul_iff.2 ⟨a, h₁, 0, h₂, by simp⟩

@[target]
theorem nmul_le_nmul_left (h : a ≤ b) (c) : c ⨳ a ≤ c ⨳ b := by sorry

@[deprecated nmul_le_nmul_left (since := "2024-08-20")]
alias nmul_le_nmul_of_nonneg_left := nmul_le_nmul_left

@[target]
theorem nmul_le_nmul_right (h : a ≤ b) (c) : a ⨳ c ≤ b ⨳ c := by sorry

@[deprecated nmul_le_nmul_left (since := "2024-08-20")]
alias nmul_le_nmul_of_nonneg_right := nmul_le_nmul_right

@[target]
theorem nmul_nadd (a b c : Ordinal) : a ⨳ (b ♯ c) = a ⨳ b ♯ a ⨳ c := by sorry

@[target]
theorem nadd_nmul (a b c) : (a ♯ b) ⨳ c = a ⨳ c ♯ b ⨳ c := by sorry

@[target]
theorem nmul_nadd_lt₃ {a' b' c' : Ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
      a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by sorry

@[target]
theorem nmul_nadd_le₃ {a' b' c' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' ≤
      a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by sorry

private theorem nmul_nadd_lt₃' {a' b' c' : Ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
      a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _)]
  convert nmul_nadd_lt₃ hb hc ha using 1 <;>
    (simp only [nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]; abel_nf)

@[target, deprecated nmul_nadd_le₃ (since := "2024-11-19")]
theorem nmul_nadd_le₃' {a' b' c' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') ≤
      a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by sorry

@[target]
theorem lt_nmul_iff₃ : d < a ⨳ b ⨳ c ↔ ∃ a' < a, ∃ b' < b, ∃ c' < c,
    d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' ≤
      a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' := by sorry

@[target]
theorem nmul_le_iff₃ : a ⨳ b ⨳ c ≤ d ↔ ∀ a' < a, ∀ b' < b, ∀ c' < c,
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
      d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by sorry

private theorem nmul_le_iff₃' : a ⨳ (b ⨳ c) ≤ d ↔ ∀ a' < a, ∀ b' < b, ∀ c' < c,
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
      d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _), nmul_le_iff₃, nadd_eq_add, toOrdinal_toNatOrdinal]
  constructor <;> intro h a' ha b' hb c' hc
  · convert h b' hb c' hc a' ha using 1 <;> abel_nf
  · convert h c' hc a' ha b' hb using 1 <;> abel_nf

@[deprecated lt_nmul_iff₃ (since := "2024-11-19")]
theorem lt_nmul_iff₃' : d < a ⨳ (b ⨳ c) ↔ ∃ a' < a, ∃ b' < b, ∃ c' < c,
    d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') ≤
      a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') := by
  simpa using nmul_le_iff₃'.not

theorem nmul_assoc (a b c : Ordinal) : a ⨳ b ⨳ c = a ⨳ (b ⨳ c) := by
  apply le_antisymm
  · rw [nmul_le_iff₃]
    intro a' ha b' hb c' hc
    repeat rw [nmul_assoc]
    exact nmul_nadd_lt₃' ha hb hc
  · rw [nmul_le_iff₃']
    intro a' ha b' hb c' hc
    repeat rw [← nmul_assoc]
    exact nmul_nadd_lt₃ ha hb hc
termination_by (a, b, c)

end Ordinal

open Ordinal

instance : Mul NatOrdinal :=
  ⟨nmul⟩

-- Porting note: had to add universe annotations to ensure that the
-- two sources lived in the same universe.
instance : OrderedCommSemiring NatOrdinal.{u} :=
  { NatOrdinal.instOrderedCancelAddCommMonoid.{u},
    NatOrdinal.instLinearOrder.{u} with
    mul := (· * ·)
    left_distrib := nmul_nadd
    right_distrib := nadd_nmul
    zero_mul := zero_nmul
    mul_zero := nmul_zero
    mul_assoc := nmul_assoc
    one := 1
    one_mul := one_nmul
    mul_one := nmul_one
    mul_comm := nmul_comm
    zero_le_one := @zero_le_one Ordinal _ _ _ _
    mul_le_mul_of_nonneg_left := fun _ _ c h _ => nmul_le_nmul_left h c
    mul_le_mul_of_nonneg_right := fun _ _ c h _ => nmul_le_nmul_right h c }

namespace Ordinal

@[target]
theorem nmul_eq_mul (a b) : a ⨳ b = toOrdinal (toNatOrdinal a * toNatOrdinal b) := by sorry

@[target]
theorem nmul_nadd_one : ∀ a b, a ⨳ (b ♯ 1) = a ⨳ b ♯ a := by sorry

@[target]
theorem nadd_one_nmul : ∀ a b, (a ♯ 1) ⨳ b = a ⨳ b ♯ b := by sorry

@[target]
theorem nmul_succ (a b) : a ⨳ succ b = a ⨳ b ♯ a := by sorry

@[target]
theorem succ_nmul (a b) : succ a ⨳ b = a ⨳ b ♯ b := by sorry

@[target]
theorem nmul_add_one : ∀ a b, a ⨳ (b + 1) = a ⨳ b ♯ a := by sorry

@[target]
theorem add_one_nmul : ∀ a b, (a + 1) ⨳ b = a ⨳ b ♯ b := by sorry

@[target]
theorem mul_le_nmul (a b : Ordinal.{u}) : a * b ≤ a ⨳ b := by sorry

@[deprecated mul_le_nmul (since := "2024-08-20")]
alias _root_.NatOrdinal.mul_le_nmul := mul_le_nmul

end Ordinal
