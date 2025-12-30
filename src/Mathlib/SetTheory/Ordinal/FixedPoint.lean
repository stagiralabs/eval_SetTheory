import VerifiedAgora.tagger
/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
import Mathlib.Logic.Small.List
import Mathlib.SetTheory.Ordinal.Enum
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
three forms: as statements about type-indexed families of normal functions, as statements about
ordinal-indexed families of normal functions, and as statements about a single normal function. For
the most part, the first case encompasses the others.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

## Main definitions and results

* `nfpFamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `not_bddAbove_fp_family`, `not_bddAbove_fp`: the (common) fixed points of a (family of) normal
  function(s) are unbounded in the ordinals.
* `deriv_add_eq_mul_omega0_add`: a characterization of the derivative of addition.
* `deriv_mul_eq_opow_omega0_mul`: a characterization of the derivative of multiplication.
-/


noncomputable section

universe u v

open Function Order

namespace Ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

section

variable {ι : Type*} {f : ι → Ordinal.{u} → Ordinal.{u}}

/-- The next common fixed point, at least `a`, for a family of normal functions.

This is defined for any family of functions, as the supremum of all values reachable by applying
finitely many functions in the family to `a`.

`Ordinal.nfpFamily_fp` shows this is a fixed point, `Ordinal.le_nfpFamily` shows it's at
least `a`, and `Ordinal.nfpFamily_le_fp` shows this is the least ordinal with these properties. -/
def nfpFamily (f : ι → Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) : Ordinal :=
  ⨆ i, List.foldr f a i

@[deprecated "No deprecation message was provided." (since := "2024-10-14")]
theorem nfpFamily_eq_sup (f : ι → Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    nfpFamily f a = ⨆ i, List.foldr f a i :=
  rfl

theorem foldr_le_nfpFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) (a l) :
    List.foldr f a l ≤ nfpFamily f a :=
  Ordinal.le_iSup _ _

@[target]
theorem le_nfpFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) (a) : a ≤ nfpFamily f a := by sorry

@[target]
theorem lt_nfpFamily_iff [Small.{u} ι] {a b} : a < nfpFamily f b ↔ ∃ l, a < List.foldr f b l := by sorry

@[deprecated (since := "2025-02-16")]
alias lt_nfpFamily := lt_nfpFamily_iff

theorem nfpFamily_le_iff [Small.{u} ι] {a b} : nfpFamily f a ≤ b ↔ ∀ l, List.foldr f a l ≤ b :=
  Ordinal.iSup_le_iff

theorem nfpFamily_le {a b} : (∀ l, List.foldr f a l ≤ b) → nfpFamily f a ≤ b :=
  Ordinal.iSup_le

@[target]
theorem nfpFamily_monotone [Small.{u} ι] (hf : ∀ i, Monotone (f i)) : Monotone (nfpFamily f) := by sorry

@[target]
theorem apply_lt_nfpFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b}
    (hb : b < nfpFamily f a) (i) : f i b < nfpFamily f a := by sorry

@[target]
theorem apply_lt_nfpFamily_iff [Nonempty ι] [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b < nfpFamily f a) ↔ b < nfpFamily f a := by sorry

theorem nfpFamily_le_apply [Nonempty ι] [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∃ i, nfpFamily f a ≤ f i b) ↔ nfpFamily f a ≤ b := by
  rw [← not_iff_not]
  push_neg
  exact apply_lt_nfpFamily_iff H

@[target]
theorem nfpFamily_le_fp (H : ∀ i, Monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
    nfpFamily f a ≤ b := by sorry

@[target]
theorem nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (a) :
    f i (nfpFamily f a) = nfpFamily f a := by sorry

@[target]
theorem apply_le_nfpFamily [Small.{u} ι] [hι : Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b ≤ nfpFamily f a) ↔ b ≤ nfpFamily f a := by sorry

@[target]
theorem nfpFamily_eq_self [Small.{u} ι] {a} (h : ∀ i, f i a = a) : nfpFamily f a = a := by sorry

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
@[target]
theorem not_bddAbove_fp_family [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    ¬ BddAbove (⋂ i, Function.fixedPoints (f i)) := by sorry

/-- The derivative of a family of normal functions is the sequence of their common fixed points.

This is defined for all functions such that `Ordinal.derivFamily_zero`,
`Ordinal.derivFamily_succ`, and `Ordinal.derivFamily_limit` are satisfied. -/
def derivFamily (f : ι → Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  limitRecOn o (nfpFamily f 0) (fun _ IH => nfpFamily f (succ IH))
    fun a _ g => ⨆ b : Set.Iio a, g _ b.2

@[target, simp]
theorem derivFamily_zero (f : ι → Ordinal → Ordinal) :
    derivFamily f 0 = nfpFamily f 0 := by sorry

@[target, simp]
theorem derivFamily_succ (f : ι → Ordinal → Ordinal) (o) :
    derivFamily f (succ o) = nfpFamily f (succ (derivFamily f o)) := by sorry

theorem derivFamily_limit (f : ι → Ordinal → Ordinal) {o} :
    IsLimit o → derivFamily f o = ⨆ b : Set.Iio o, derivFamily f b :=
  limitRecOn_limit _ _ _ _

theorem isNormal_derivFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) :
    IsNormal (derivFamily f) := by
  refine ⟨fun o ↦ ?_, fun o h a ↦ ?_⟩
  · rw [derivFamily_succ, ← succ_le_iff]
    exact le_nfpFamily _ _
  · simp_rw [derivFamily_limit _ h, Ordinal.iSup_le_iff, Subtype.forall, Set.mem_Iio]

@[deprecated isNormal_derivFamily (since := "2024-10-11")]
alias derivFamily_isNormal := isNormal_derivFamily

@[target]
theorem derivFamily_strictMono [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) :
    StrictMono (derivFamily f) := by sorry

@[target]
theorem derivFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (o : Ordinal) :
    f i (derivFamily f o) = derivFamily f o := by sorry

@[target]
theorem le_iff_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a ≤ a) ↔ ∃ o, derivFamily f o = a := by sorry

theorem fp_iff_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a = a) ↔ ∃ o, derivFamily f o = a :=
  Iff.trans ⟨fun h i => le_of_eq (h i), fun h i => (H i).le_iff_eq.1 (h i)⟩ (le_iff_derivFamily H)

/-- For a family of normal functions, `Ordinal.derivFamily` enumerates the common fixed points. -/
@[target]
theorem derivFamily_eq_enumOrd [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    derivFamily f = enumOrd (⋂ i, Function.fixedPoints (f i)) := by sorry

end

/-! ### Fixed points of ordinal-indexed families of ordinals -/

section

variable {o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{max u v} → Ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions indexed by ordinals.

This is defined as `Ordinal.nfpFamily` of the type-indexed family associated to `f`. -/
@[deprecated nfpFamily (since := "2024-10-14")]
def nfpBFamily (o : Ordinal.{u}) (f : ∀ b < o, Ordinal.{max u v} → Ordinal.{max u v}) :
    Ordinal.{max u v} → Ordinal.{max u v} :=
  nfpFamily (familyOfBFamily o f)

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem nfpBFamily_eq_nfpFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    nfpBFamily.{u, v} o f = nfpFamily (familyOfBFamily o f) := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem foldr_le_nfpBFamily {o : Ordinal}
    (f : ∀ b < o, Ordinal → Ordinal) (a l) :
    List.foldr (familyOfBFamily o f) a l ≤ nfpBFamily.{u, v} o f a := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem le_nfpBFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) (a) :
    a ≤ nfpBFamily.{u, v} o f a := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem lt_nfpBFamily {a b} :
    a < nfpBFamily.{u, v} o f b ↔ ∃ l, a < List.foldr (familyOfBFamily o f) b l := by sorry

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem nfpBFamily_le_iff {o : Ordinal} {f : ∀ b < o, Ordinal → Ordinal} {a b} :
    nfpBFamily.{u, v} o f a ≤ b ↔ ∀ l, List.foldr (familyOfBFamily o f) a l ≤ b :=
  Ordinal.iSup_le_iff

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem nfpBFamily_le {o : Ordinal} {f : ∀ b < o, Ordinal → Ordinal} {a b} :
    (∀ l, List.foldr (familyOfBFamily o f) a l ≤ b) → nfpBFamily.{u, v} o f a ≤ b := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem nfpBFamily_monotone (hf : ∀ i hi, Monotone (f i hi)) : Monotone (nfpBFamily.{u, v} o f) := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem apply_lt_nfpBFamily (H : ∀ i hi, IsNormal (f i hi)) {a b} (hb : b < nfpBFamily.{u, v} o f a)
    (i hi) : f i hi b < nfpBFamily.{u, v} o f a := by sorry

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem apply_lt_nfpBFamily_iff (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b < nfpBFamily.{u, v} o f a) ↔ b < nfpBFamily.{u, v} o f a :=
  ⟨fun h => by
    haveI := toType_nonempty_iff_ne_zero.2 ho
    refine (apply_lt_nfpFamily_iff ?_).1 fun _ => h _ _
    exact fun _ => H _ _, apply_lt_nfpBFamily H⟩

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem nfpBFamily_le_apply (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∃ i hi, nfpBFamily.{u, v} o f a ≤ f i hi b) ↔ nfpBFamily.{u, v} o f a ≤ b := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem nfpBFamily_le_fp (H : ∀ i hi, Monotone (f i hi)) {a b} (ab : a ≤ b)
    (h : ∀ i hi, f i hi b ≤ b) : nfpBFamily.{u, v} o f a ≤ b := by sorry

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem nfpBFamily_fp {i hi} (H : IsNormal (f i hi)) (a) :
    f i hi (nfpBFamily.{u, v} o f a) = nfpBFamily.{u, v} o f a := by
  rw [← familyOfBFamily_enum o f]
  apply nfpFamily_fp
  rw [familyOfBFamily_enum]
  exact H

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem apply_le_nfpBFamily (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b ≤ nfpBFamily.{u, v} o f a) ↔ b ≤ nfpBFamily.{u, v} o f a := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem nfpBFamily_eq_self {a} (h : ∀ i hi, f i hi a = a) : nfpBFamily.{u, v} o f a = a := by sorry

set_option linter.deprecated false in
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem not_bddAbove_fp_bfamily (H : ∀ i hi, IsNormal (f i hi)) :
    ¬ BddAbove (⋂ (i) (hi), Function.fixedPoints (f i hi)) := by sorry

set_option linter.deprecated false in
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
@[deprecated not_bddAbove_fp_bfamily (since := "2024-09-20")]
theorem fp_bfamily_unbounded (H : ∀ i hi, IsNormal (f i hi)) :
    (⋂ (i) (hi), Function.fixedPoints (f i hi)).Unbounded (· < ·) := fun a =>
  ⟨nfpBFamily.{u, v} _ f a, by
    rw [Set.mem_iInter₂]
    exact fun i hi => nfpBFamily_fp (H i hi) _, (le_nfpBFamily f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points.

This is defined as `Ordinal.derivFamily` of the type-indexed family associated to `f`. -/
@[deprecated derivFamily (since := "2024-10-14")]
def derivBFamily (o : Ordinal.{u}) (f : ∀ b < o, Ordinal.{max u v} → Ordinal.{max u v}) :
    Ordinal.{max u v} → Ordinal.{max u v} :=
  derivFamily (familyOfBFamily o f)

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem derivBFamily_eq_derivFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    derivBFamily.{u, v} o f = derivFamily (familyOfBFamily o f) := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem isNormal_derivBFamily {o : Ordinal} (f : ∀ b < o, Ordinal → Ordinal) :
    IsNormal (derivBFamily o f) := by sorry

@[deprecated isNormal_derivBFamily (since := "2024-10-11")]
alias derivBFamily_isNormal := isNormal_derivBFamily

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem derivBFamily_fp {i hi} (H : IsNormal (f i hi)) (a : Ordinal) :
    f i hi (derivBFamily.{u, v} o f a) = derivBFamily.{u, v} o f a := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem le_iff_derivBFamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a ≤ a) ↔ ∃ b, derivBFamily.{u, v} o f b = a := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem fp_iff_derivBFamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a = a) ↔ ∃ b, derivBFamily.{u, v} o f b = a := by sorry

set_option linter.deprecated false in
/-- For a family of normal functions, `Ordinal.derivBFamily` enumerates the common fixed points. -/
@[target, deprecated "No deprecation message was provided."  (since := "2024-10-14")]
theorem derivBFamily_eq_enumOrd (H : ∀ i hi, IsNormal (f i hi)) :
    derivBFamily.{u, v} o f = enumOrd (⋂ (i) (hi), Function.fixedPoints (f i hi)) := by sorry

end

/-! ### Fixed points of a single function -/

section

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- The next fixed point function, the least fixed point of the normal function `f`, at least `a`.

This is defined as `nfpFamily` applied to a family consisting only of `f`. -/
def nfp (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily fun _ : Unit => f

@[target]
theorem nfp_eq_nfpFamily (f : Ordinal → Ordinal) : nfp f = nfpFamily fun _ : Unit => f := by sorry

@[target]
theorem iSup_iterate_eq_nfp (f : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    ⨆ n : ℕ, f^[n] a = nfp f a := by sorry

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided."  (since := "2024-08-27")]
theorem sup_iterate_eq_nfp (f : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    (sup fun n : ℕ => f^[n] a) = nfp f a := by
  refine le_antisymm ?_ (sup_le fun l => ?_)
  · rw [sup_le_iff]
    intro n
    rw [← List.length_replicate n Unit.unit, ← List.foldr_const f a]
    apply le_sup
  · rw [List.foldr_const f a l]
    exact le_sup _ _

@[target]
theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a := by sorry

@[target]
theorem le_nfp (f a) : a ≤ nfp f a := by sorry

@[target]
theorem lt_nfp_iff {a b} : a < nfp f b ↔ ∃ n, a < f^[n] b := by sorry

@[deprecated lt_nfp_iff (since := "2024-02-16")]
alias lt_nfp := lt_nfp_iff

@[target]
theorem nfp_le_iff {a b} : nfp f a ≤ b ↔ ∀ n, f^[n] a ≤ b := by sorry

@[target]
theorem nfp_le {a b} : (∀ n, f^[n] a ≤ b) → nfp f a ≤ b := by sorry

@[target, simp]
theorem nfp_id : nfp id = id := by sorry

@[target]
theorem nfp_monotone (hf : Monotone f) : Monotone (nfp f) := by sorry

@[target]
theorem IsNormal.apply_lt_nfp (H : IsNormal f) {a b} : f b < nfp f a ↔ b < nfp f a := by sorry

@[target]
theorem IsNormal.nfp_le_apply (H : IsNormal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b := by sorry

@[target]
theorem nfp_le_fp (H : Monotone f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b := by sorry

@[target]
theorem IsNormal.nfp_fp (H : IsNormal f) : ∀ a, f (nfp f a) = nfp f a := by sorry

@[target]
theorem IsNormal.apply_le_nfp (H : IsNormal f) {a b} : f b ≤ nfp f a ↔ b ≤ nfp f a := by sorry

@[target]
theorem nfp_eq_self {a} (h : f a = a) : nfp f a = a := by sorry

/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
@[target]
theorem not_bddAbove_fp (H : IsNormal f) : ¬ BddAbove (Function.fixedPoints f) := by sorry

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`.

This is defined as `Ordinal.derivFamily` applied to a trivial family consisting only of `f`. -/
def deriv (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily fun _ : Unit => f

@[target]
theorem deriv_eq_derivFamily (f : Ordinal → Ordinal) : deriv f = derivFamily fun _ : Unit => f := by sorry

@[simp]
theorem deriv_zero_right (f) : deriv f 0 = nfp f 0 :=
  derivFamily_zero _

@[simp]
theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  derivFamily_succ _ _

@[target]
theorem deriv_limit (f) {o} : IsLimit o → deriv f o = ⨆ a : {a // a < o}, deriv f a := by sorry

@[target]
theorem isNormal_deriv (f) : IsNormal (deriv f) := by sorry

@[deprecated isNormal_deriv (since := "2024-10-11")]
alias deriv_isNormal := isNormal_deriv

@[target]
theorem deriv_strictMono (f) : StrictMono (deriv f) := by sorry

theorem deriv_id_of_nfp_id (h : nfp f = id) : deriv f = id :=
  ((isNormal_deriv _).eq_iff_zero_and_succ IsNormal.refl).2 (by simp [h])

@[target]
theorem IsNormal.deriv_fp (H : IsNormal f) : ∀ o, f (deriv f o) = deriv f o := by sorry

@[target]
theorem IsNormal.le_iff_deriv (H : IsNormal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a := by sorry

@[target]
theorem IsNormal.fp_iff_deriv (H : IsNormal f) {a} : f a = a ↔ ∃ o, deriv f o = a := by sorry

/-- `Ordinal.deriv` enumerates the fixed points of a normal function. -/
@[target]
theorem deriv_eq_enumOrd (H : IsNormal f) : deriv f = enumOrd (Function.fixedPoints f) := by sorry

@[target]
theorem deriv_eq_id_of_nfp_eq_id (h : nfp f = id) : deriv f = id := by sorry

theorem nfp_zero_left (a) : nfp 0 a = a := by
  rw [← iSup_iterate_eq_nfp]
  apply (Ordinal.iSup_le ?_).antisymm (Ordinal.le_iSup _ 0)
  intro n
  cases n
  · rfl
  · rw [Function.iterate_succ']
    simp

@[target, simp]
theorem nfp_zero : nfp 0 = id := by sorry

@[target, simp]
theorem deriv_zero : deriv 0 = id := by sorry

theorem deriv_zero_left (a) : deriv 0 a = a := by
  rw [deriv_zero, id_eq]

end

/-! ### Fixed points of addition -/

@[target, simp]
theorem nfp_add_zero (a) : nfp (a + ·) 0 = a * ω := by sorry

@[target]
theorem nfp_add_eq_mul_omega0 {a b} (hba : b ≤ a * ω) : nfp (a + ·) b = a * ω := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias nfp_add_eq_mul_omega := nfp_add_eq_mul_omega0

@[target]
theorem add_eq_right_iff_mul_omega0_le {a b : Ordinal} : a + b = b ↔ a * ω ≤ b := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias add_eq_right_iff_mul_omega_le := add_eq_right_iff_mul_omega0_le

@[target]
theorem add_le_right_iff_mul_omega0_le {a b : Ordinal} : a + b ≤ b ↔ a * ω ≤ b := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias add_le_right_iff_mul_omega_le := add_le_right_iff_mul_omega0_le

theorem deriv_add_eq_mul_omega0_add (a b : Ordinal.{u}) : deriv (a + ·) b = a * ω + b := by
  revert b
  rw [← funext_iff, IsNormal.eq_iff_zero_and_succ (isNormal_deriv _) (isNormal_add_right _)]
  refine ⟨?_, fun a h => ?_⟩
  · rw [deriv_zero_right, add_zero]
    exact nfp_add_zero a
  · rw [deriv_succ, h, add_succ]
    exact nfp_eq_self (add_eq_right_iff_mul_omega0_le.2 ((le_add_right _ _).trans (le_succ _)))

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias deriv_add_eq_mul_omega_add := deriv_add_eq_mul_omega0_add

/-! ### Fixed points of multiplication -/

@[target, simp]
theorem nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp (a * ·) 1 = a ^ ω := by sorry

@[simp]
theorem nfp_mul_zero (a : Ordinal) : nfp (a * ·) 0 = 0 := by
  rw [← Ordinal.le_zero, nfp_le_iff]
  intro n
  induction' n with n hn; · rfl
  dsimp only; rwa [iterate_succ_apply, mul_zero]

theorem nfp_mul_eq_opow_omega0 {a b : Ordinal} (hb : 0 < b) (hba : b ≤ a ^ ω) :
    nfp (a * ·) b = a ^ ω := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_opow omega0_ne_zero] at hba ⊢
    simp_rw [Ordinal.le_zero.1 hba, zero_mul]
    exact nfp_zero_left 0
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone hba
    rw [← opow_one_add, one_add_omega0]
  rw [← nfp_mul_one ha]
  exact nfp_monotone (isNormal_mul_right ha).monotone (one_le_iff_pos.2 hb)

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias nfp_mul_eq_opow_omega := nfp_mul_eq_opow_omega0

theorem eq_zero_or_opow_omega0_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b) :
    b = 0 ∨ a ^ ω ≤ b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_opow omega0_ne_zero]
    exact Or.inr (Ordinal.zero_le b)
  rw [or_iff_not_imp_left]
  intro hb
  rw [← nfp_mul_one ha]
  rw [← Ne, ← one_le_iff_ne_zero] at hb
  exact nfp_le_fp (isNormal_mul_right ha).monotone hb (le_of_eq hab)

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias eq_zero_or_opow_omega_le_of_mul_eq_right := eq_zero_or_opow_omega0_le_of_mul_eq_right

theorem mul_eq_right_iff_opow_omega0_dvd {a b : Ordinal} : a * b = b ↔ a ^ ω ∣ b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_mul, zero_opow omega0_ne_zero, zero_dvd_iff]
    exact eq_comm
  refine ⟨fun hab => ?_, fun h => ?_⟩
  · rw [dvd_iff_mod_eq_zero]
    rw [← div_add_mod b (a ^ ω), mul_add, ← mul_assoc, ← opow_one_add, one_add_omega0,
      add_left_cancel_iff] at hab
    rcases eq_zero_or_opow_omega0_le_of_mul_eq_right hab with hab | hab
    · exact hab
    refine (not_lt_of_le hab (mod_lt b (opow_ne_zero ω ?_))).elim
    rwa [← Ordinal.pos_iff_ne_zero]
  obtain ⟨c, hc⟩ := h
  rw [hc, ← mul_assoc, ← opow_one_add, one_add_omega0]

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias mul_eq_right_iff_opow_omega_dvd := mul_eq_right_iff_opow_omega0_dvd

@[target]
theorem mul_le_right_iff_opow_omega0_dvd {a b : Ordinal} (ha : 0 < a) :
    a * b ≤ b ↔ (a ^ ω) ∣ b := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias mul_le_right_iff_opow_omega_dvd := mul_le_right_iff_opow_omega0_dvd

@[target]
theorem nfp_mul_opow_omega0_add {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c)
    (hca : c ≤ a ^ ω) : nfp (a * ·) (a ^ ω * b + c) = a ^ ω * succ b := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias nfp_mul_opow_omega_add := nfp_mul_opow_omega0_add

@[target]
theorem deriv_mul_eq_opow_omega0_mul {a : Ordinal.{u}} (ha : 0 < a) (b) :
    deriv (a * ·) b = a ^ ω * b := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias deriv_mul_eq_opow_omega_mul := deriv_mul_eq_opow_omega0_mul

end Ordinal
