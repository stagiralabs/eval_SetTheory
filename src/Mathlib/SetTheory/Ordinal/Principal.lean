import VerifiedAgora.tagger
/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

## Main definitions and results

* `Principal`: A principal or indecomposable ordinal under some binary operation. We include 0 and
  any other typically excluded edge cases for simplicity.
* `not_bddAbove_principal`: Principal ordinals (under any operation) are unbounded.
* `principal_add_iff_zero_or_omega0_opow`: The main characterization theorem for additive principal
  ordinals.
* `principal_mul_iff_le_two_or_omega0_opow_opow`: The main characterization theorem for
  multiplicative principal ordinals.

## TODO

* Prove that exponential principal ordinals are 0, 1, 2, ω, or epsilon numbers, i.e. fixed points
  of `fun x ↦ ω ^ x`.
-/

universe u

open Order

namespace Ordinal

variable {a b c o : Ordinal.{u}}

section Arbitrary

variable {op : Ordinal → Ordinal → Ordinal}

/-! ### Principal ordinals -/

/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard `0` as principal. -/
def Principal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o

@[target]
theorem principal_swap_iff : Principal (Function.swap op) o ↔ Principal op o := by sorry

@[target, deprecated principal_swap_iff (since := "2024-08-18")]
theorem principal_iff_principal_swap : Principal op o ↔ Principal (Function.swap op) o := by sorry

@[target]
theorem not_principal_iff : ¬ Principal op o ↔ ∃ a < o, ∃ b < o, o ≤ op a b := by sorry

theorem principal_iff_of_monotone
    (h₁ : ∀ a, Monotone (op a)) (h₂ : ∀ a, Monotone (Function.swap op a)) :
    Principal op o ↔ ∀ a < o, op a a < o := by
  use fun h a ha => h ha ha
  intro H a b ha hb
  obtain hab | hba := le_or_lt a b
  · exact (h₂ b hab).trans_lt <| H b hb
  · exact (h₁ a hba.le).trans_lt <| H a ha

@[target]
theorem not_principal_iff_of_monotone
    (h₁ : ∀ a, Monotone (op a)) (h₂ : ∀ a, Monotone (Function.swap op a)) :
    ¬ Principal op o ↔ ∃ a < o, o ≤ op a a := by sorry

@[target]
theorem principal_zero : Principal op 0 := by sorry

@[simp]
theorem principal_one_iff : Principal op 1 ↔ op 0 0 = 0 := by
  refine ⟨fun h => ?_, fun h a b ha hb => ?_⟩
  · rw [← lt_one_iff_zero]
    exact h zero_lt_one zero_lt_one
  · rwa [lt_one_iff_zero, ha, hb] at *

@[target]
theorem Principal.iterate_lt (hao : a < o) (ho : Principal op o) (n : ℕ) : (op a)^[n] a < o := by sorry

@[target]
theorem op_eq_self_of_principal (hao : a < o) (H : IsNormal (op a))
    (ho : Principal op o) (ho' : IsLimit o) : op a o = o := by sorry

theorem nfp_le_of_principal (hao : a < o) (ho : Principal op o) : nfp (op a) a ≤ o :=
  nfp_le fun n => (ho.iterate_lt hao n).le

end Arbitrary

/-! ### Principal ordinals are unbounded -/

/-- We give an explicit construction for a principal ordinal larger or equal than `o`. -/
private theorem principal_nfp_iSup (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    Principal op (nfp (fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2)) o) := by
  intro a b ha hb
  rw [lt_nfp_iff] at *
  obtain ⟨m, ha⟩ := ha
  obtain ⟨n, hb⟩ := hb
  obtain h | h := le_total
    ((fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[m] o)
    ((fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[n] o)
  · use n + 1
    rw [Function.iterate_succ']
    apply (lt_succ _).trans_le
    exact Ordinal.le_iSup (fun y : Set.Iio _ ×ˢ Set.Iio _ ↦ succ (op y.1.1 y.1.2))
      ⟨_, Set.mk_mem_prod (ha.trans_le h) hb⟩
  · use m + 1
    rw [Function.iterate_succ']
    apply (lt_succ _).trans_le
    exact Ordinal.le_iSup (fun y : Set.Iio _ ×ˢ Set.Iio _ ↦ succ (op y.1.1 y.1.2))
      ⟨_, Set.mk_mem_prod ha (hb.trans_le h)⟩

/-- Principal ordinals under any operation are unbounded. -/
@[target]
theorem not_bddAbove_principal (op : Ordinal → Ordinal → Ordinal) :
    ¬ BddAbove { o | Principal op o } := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided." (since := "2024-10-11")]
theorem principal_nfp_blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    Principal op (nfp (fun o' => blsub₂.{u, u, u} o' o' (@fun a _ b _ => op a b)) o) := by sorry

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-10-11")]
theorem unbounded_principal (op : Ordinal → Ordinal → Ordinal) :
    Set.Unbounded (· < ·) { o | Principal op o } := fun o =>
  ⟨_, principal_nfp_blsub₂ op o, (le_nfp _ o).not_lt⟩

/-! #### Additive principal ordinals -/

@[target]
theorem principal_add_one : Principal (· + ·) 1 := by sorry

@[target]
theorem principal_add_of_le_one (ho : o ≤ 1) : Principal (· + ·) o := by sorry

@[target]
theorem isLimit_of_principal_add (ho₁ : 1 < o) (ho : Principal (· + ·) o) : o.IsLimit := by sorry

@[deprecated (since := "2024-10-16")]
alias principal_add_isLimit := isLimit_of_principal_add

@[target]
theorem principal_add_iff_add_left_eq_self : Principal (· + ·) o ↔ ∀ a < o, a + o = o := by sorry

@[target]
theorem exists_lt_add_of_not_principal_add (ha : ¬ Principal (· + ·) a) :
    ∃ b < a, ∃ c < a, b + c = a := by sorry

theorem principal_add_iff_add_lt_ne_self : Principal (· + ·) a ↔ ∀ b < a, ∀ c < a, b + c ≠ a :=
  ⟨fun ha _ hb _ hc => (ha hb hc).ne, fun H => by
    by_contra! ha
    rcases exists_lt_add_of_not_principal_add ha with ⟨b, hb, c, hc, rfl⟩
    exact (H b hb c hc).irrefl⟩

theorem principal_add_omega0 : Principal (· + ·) ω :=
  principal_add_iff_add_left_eq_self.2 fun _ => add_omega0

theorem add_omega0_opow (h : a < ω ^ b) : a + ω ^ b = ω ^ b := by
  refine le_antisymm ?_ (le_add_left _ a)
  induction' b using limitRecOn with b _ b l IH
  · rw [opow_zero, ← succ_zero, lt_succ_iff, Ordinal.le_zero] at h
    rw [h, zero_add]
  · rw [opow_succ] at h
    rcases (lt_mul_of_limit isLimit_omega0).1 h with ⟨x, xo, ax⟩
    apply (add_le_add_right ax.le _).trans
    rw [opow_succ, ← mul_add, add_omega0 xo]
  · rcases (lt_opow_of_limit omega0_ne_zero l).1 h with ⟨x, xb, ax⟩
    apply (((isNormal_add_right a).trans <| isNormal_opow one_lt_omega0).limit_le l).2
    intro y yb
    calc a + ω ^ y ≤ a + ω ^ max x y :=
      add_le_add_left (opow_le_opow_right omega0_pos (le_max_right x y)) _
    _ ≤ ω ^ max x y :=
      IH _ (max_lt xb yb) <| ax.trans_le <| opow_le_opow_right omega0_pos <| le_max_left x y
    _ ≤ ω ^ b :=
      opow_le_opow_right omega0_pos <| (max_lt xb yb).le

@[deprecated (since := "2024-09-30")]
alias add_omega_opow := add_omega0_opow

@[target]
theorem principal_add_omega0_opow (o : Ordinal) : Principal (· + ·) (ω ^ o) := by sorry

@[deprecated (since := "2024-09-30")]
alias principal_add_omega_opow := principal_add_omega0_opow

/-- The main characterization theorem for additive principal ordinals. -/
theorem principal_add_iff_zero_or_omega0_opow :
    Principal (· + ·) o ↔ o = 0 ∨ o ∈ Set.range (ω ^ · : Ordinal → Ordinal) := by
  rcases eq_or_ne o 0 with (rfl | ho)
  · simp only [principal_zero, Or.inl]
  · rw [principal_add_iff_add_left_eq_self]
    simp only [ho, false_or]
    refine
      ⟨fun H => ⟨_, ((lt_or_eq_of_le (opow_log_le_self _ ho)).resolve_left fun h => ?_)⟩,
        fun ⟨b, e⟩ => e.symm ▸ fun a => add_omega0_opow⟩
    have := H _ h
    have := lt_opow_succ_log_self one_lt_omega0 o
    rw [opow_succ, lt_mul_of_limit isLimit_omega0] at this
    rcases this with ⟨a, ao, h'⟩
    rcases lt_omega0.1 ao with ⟨n, rfl⟩
    clear ao
    revert h'
    apply not_lt_of_le
    suffices e : ω ^ log ω o * n + o = o by
      simpa only [e] using le_add_right (ω ^ log ω o * ↑n) o
    induction' n with n IH
    · simp [Nat.cast_zero, mul_zero, zero_add]
    · simp only [Nat.cast_succ, mul_add_one, add_assoc, this, IH]

@[deprecated (since := "2024-09-30")]
alias principal_add_iff_zero_or_omega_opow := principal_add_iff_zero_or_omega0_opow

@[target]
theorem principal_add_opow_of_principal_add {a} (ha : Principal (· + ·) a) (b : Ordinal) :
    Principal (· + ·) (a ^ b) := by sorry

@[deprecated (since := "2024-10-16")]
alias opow_principal_add_of_principal_add := principal_add_opow_of_principal_add

@[target]
theorem add_absorp (h₁ : a < ω ^ b) (h₂ : ω ^ b ≤ c) : a + c = c := by sorry

@[target]
theorem principal_add_mul_of_principal_add (a : Ordinal.{u}) {b : Ordinal.{u}} (hb₁ : b ≠ 1)
    (hb : Principal (· + ·) b) : Principal (· + ·) (a * b) := by sorry

@[deprecated (since := "2024-10-16")]
alias mul_principal_add_is_principal_add := principal_add_mul_of_principal_add

/-! #### Multiplicative principal ordinals -/

@[target]
theorem principal_mul_one : Principal (· * ·) 1 := by sorry

@[target]
theorem principal_mul_two : Principal (· * ·) 2 := by sorry

theorem principal_mul_of_le_two (ho : o ≤ 2) : Principal (· * ·) o := by
  rcases lt_or_eq_of_le ho with (ho | rfl)
  · rw [← succ_one, lt_succ_iff] at ho
    rcases lt_or_eq_of_le ho with (ho | rfl)
    · rw [lt_one_iff_zero.1 ho]
      exact principal_zero
    · exact principal_mul_one
  · exact principal_mul_two

@[target]
theorem principal_add_of_principal_mul (ho : Principal (· * ·) o) (ho₂ : o ≠ 2) :
    Principal (· + ·) o := by sorry

theorem isLimit_of_principal_mul (ho₂ : 2 < o) (ho : Principal (· * ·) o) : o.IsLimit :=
  isLimit_of_principal_add ((lt_succ 1).trans (succ_one ▸ ho₂))
    (principal_add_of_principal_mul ho (ne_of_gt ho₂))

@[deprecated (since := "2024-10-16")]
alias principal_mul_isLimit := isLimit_of_principal_mul

@[target]
theorem principal_mul_iff_mul_left_eq : Principal (· * ·) o ↔ ∀ a, 0 < a → a < o → a * o = o := by sorry

@[target]
theorem principal_mul_omega0 : Principal (· * ·) ω := by sorry

@[target]
theorem mul_omega0 (a0 : 0 < a) (ha : a < ω) : a * ω = ω := by sorry

@[deprecated (since := "2024-09-30")]
alias mul_omega := mul_omega0

@[target]
theorem natCast_mul_omega0 {n : ℕ} (hn : 0 < n) : n * ω = ω := by sorry

@[target]
theorem mul_lt_omega0_opow (c0 : 0 < c) (ha : a < ω ^ c) (hb : b < ω) : a * b < ω ^ c := by sorry

@[deprecated (since := "2024-09-30")]
alias mul_lt_omega_opow := mul_lt_omega0_opow

@[target]
theorem mul_omega0_opow_opow (a0 : 0 < a) (h : a < ω ^ ω ^ b) : a * ω ^ ω ^ b = ω ^ ω ^ b := by sorry

@[deprecated (since := "2024-09-30")]
alias mul_omega_opow_opow := mul_omega0_opow_opow

theorem principal_mul_omega0_opow_opow (o : Ordinal) : Principal (· * ·) (ω ^ ω ^ o) :=
  principal_mul_iff_mul_left_eq.2 fun _ => mul_omega0_opow_opow

@[deprecated (since := "2024-09-30")]
alias principal_mul_omega_opow_opow := principal_mul_omega0_opow_opow

@[target]
theorem principal_add_of_principal_mul_opow (hb : 1 < b) (ho : Principal (· * ·) (b ^ o)) :
    Principal (· + ·) o := by sorry

/-- The main characterization theorem for multiplicative principal ordinals. -/
@[target]
theorem principal_mul_iff_le_two_or_omega0_opow_opow :
    Principal (· * ·) o ↔ o ≤ 2 ∨ o ∈ Set.range (ω ^ ω ^ · : Ordinal → Ordinal) := by sorry

@[deprecated (since := "2024-09-30")]
alias principal_mul_iff_le_two_or_omega_opow_opow := principal_mul_iff_le_two_or_omega0_opow_opow

@[target]
theorem mul_omega0_dvd (a0 : 0 < a) (ha : a < ω) : ∀ {b}, ω ∣ b → a * b = b := by sorry

@[deprecated (since := "2024-09-30")]
alias mul_omega_dvd := mul_omega0_dvd

@[target]
theorem mul_eq_opow_log_succ (ha : a ≠ 0) (hb : Principal (· * ·) b) (hb₂ : 2 < b) :
    a * b = b ^ succ (log b a) := by sorry

/-! #### Exponential principal ordinals -/

@[target]
theorem principal_opow_omega0 : Principal (· ^ ·) ω := by sorry

theorem opow_omega0 (a1 : 1 < a) (h : a < ω) : a ^ ω = ω :=
  ((opow_le_of_limit (one_le_iff_ne_zero.1 <| le_of_lt a1) isLimit_omega0).2 fun _ hb =>
      (principal_opow_omega0 h hb).le).antisymm
  (right_le_opow _ a1)

@[deprecated (since := "2024-09-30")]
alias opow_omega := opow_omega0

@[target]
theorem natCast_opow_omega0 {n : ℕ} (hn : 1 < n) : n ^ ω = ω := by sorry

end Ordinal
