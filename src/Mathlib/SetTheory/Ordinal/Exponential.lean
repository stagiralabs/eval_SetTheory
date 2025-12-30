import VerifiedAgora.tagger
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic

/-! # Ordinal exponential

In this file we define the power function and the logarithm function on ordinals. The two are
related by the lemma `Ordinal.opow_le_iff_le_log : b ^ c ≤ x ↔ c ≤ log b x` for nontrivial inputs
`b`, `c`.
-/

noncomputable section

open Function Set Equiv Order
open scoped Cardinal Ordinal

universe u v w

namespace Ordinal

/-- The ordinal exponential, defined by transfinite recursion.

We call this `opow` in theorems in order to disambiguate from other exponentials. -/
instance instPow : Pow Ordinal Ordinal :=
  ⟨fun a b ↦ if a = 0 then 1 - b else
    limitRecOn b 1 (fun _ x ↦ x * a) fun o _ f ↦ ⨆ x : Iio o, f x.1 x.2⟩

private theorem opow_of_ne_zero {a b : Ordinal} (h : a ≠ 0) : a ^ b =
    limitRecOn b 1 (fun _ x ↦ x * a) fun o _ f ↦ ⨆ x : Iio o, f x.1 x.2 :=
  if_neg h

/-- `0 ^ a = 1` if `a = 0` and `0 ^ a = 0` otherwise. -/
theorem zero_opow' (a : Ordinal) : 0 ^ a = 1 - a :=
  if_pos rfl

@[target]
theorem zero_opow_le (a : Ordinal) : (0 : Ordinal) ^ a ≤ 1 := by sorry

@[simp]
theorem zero_opow {a : Ordinal} (a0 : a ≠ 0) : (0 : Ordinal) ^ a = 0 := by
  rwa [zero_opow', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp]
theorem opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1 := by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow', Ordinal.sub_zero]
  · rw [opow_of_ne_zero h, limitRecOn_zero]

@[target, simp]
theorem opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a := by sorry

@[target]
theorem opow_limit {a b : Ordinal} (ha : a ≠ 0) (hb : IsLimit b) :
    a ^ b = ⨆ x : Iio b, a ^ x.1 := by sorry

@[target]
theorem opow_le_of_limit {a b c : Ordinal} (a0 : a ≠ 0) (h : IsLimit b) :
    a ^ b ≤ c ↔ ∀ b' < b, a ^ b' ≤ c := by sorry

theorem lt_opow_of_limit {a b c : Ordinal} (b0 : b ≠ 0) (h : IsLimit c) :
    a < b ^ c ↔ ∃ c' < c, a < b ^ c' := by
  rw [← not_iff_not, not_exists]
  simp only [not_lt, opow_le_of_limit b0 h, exists_prop, not_and]

@[simp]
theorem opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a := by
  rw [← succ_zero, opow_succ]
  simp only [opow_zero, one_mul]

@[target, simp]
theorem one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1 := by sorry

@[target]
theorem opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 < a ^ b := by sorry

@[target]
theorem opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a ≠ 0) : a ^ b ≠ 0 := by sorry

@[simp]
theorem opow_eq_zero {a b : Ordinal} : a ^ b = 0 ↔ a = 0 ∧ b ≠ 0 := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hb := eq_or_ne b 0
    · simp
    · simp [hb]
  · simp [opow_ne_zero b ha, ha]

@[target, simp, norm_cast]
theorem opow_natCast (a : Ordinal) (n : ℕ) : a ^ (n : Ordinal) = a ^ n := by sorry

@[target]
theorem isNormal_opow {a : Ordinal} (h : 1 < a) : IsNormal (a ^ ·) := by sorry

@[deprecated isNormal_opow (since := "2024-10-11")]
alias opow_isNormal := isNormal_opow

theorem opow_lt_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c :=
  (isNormal_opow a1).lt_iff

@[target]
theorem opow_le_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b ≤ a ^ c ↔ b ≤ c := by sorry

theorem opow_right_inj {a b c : Ordinal} (a1 : 1 < a) : a ^ b = a ^ c ↔ b = c :=
  (isNormal_opow a1).inj

theorem isLimit_opow {a b : Ordinal} (a1 : 1 < a) : IsLimit b → IsLimit (a ^ b) :=
  (isNormal_opow a1).isLimit

@[deprecated isLimit_opow (since := "2024-10-11")]
alias opow_isLimit := isLimit_opow

@[target]
theorem isLimit_opow_left {a b : Ordinal} (l : IsLimit a) (hb : b ≠ 0) : IsLimit (a ^ b) := by sorry

@[deprecated isLimit_opow_left (since := "2024-10-11")]
alias opow_isLimit_left := isLimit_opow_left

@[target]
theorem opow_le_opow_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b ≤ c) : a ^ b ≤ a ^ c := by sorry

@[target]
theorem opow_le_opow_left {a b : Ordinal} (c : Ordinal) (ab : a ≤ b) : a ^ c ≤ b ^ c := by sorry

@[target]
theorem opow_le_opow {a b c d : Ordinal} (hac : a ≤ c) (hbd : b ≤ d) (hc : 0 < c) : a ^ b ≤ c ^ d := by sorry

@[target]
theorem left_le_opow (a : Ordinal) {b : Ordinal} (b1 : 0 < b) : a ≤ a ^ b := by sorry

@[target]
theorem left_lt_opow {a b : Ordinal} (ha : 1 < a) (hb : 1 < b) : a < a ^ b := by sorry

theorem right_le_opow {a : Ordinal} (b : Ordinal) (a1 : 1 < a) : b ≤ a ^ b :=
  (isNormal_opow a1).le_apply

theorem opow_lt_opow_left_of_succ {a b c : Ordinal} (ab : a < b) : a ^ succ c < b ^ succ c := by
  rw [opow_succ, opow_succ]
  exact
    (mul_le_mul_right' (opow_le_opow_left c ab.le) a).trans_lt
      (mul_lt_mul_of_pos_left ab (opow_pos c ((Ordinal.zero_le a).trans_lt ab)))

@[target]
theorem opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^ c := by sorry

@[target]
theorem opow_one_add (a b : Ordinal) : a ^ (1 + b) = a * a ^ b := by sorry

theorem opow_dvd_opow (a : Ordinal) {b c : Ordinal} (h : b ≤ c) : a ^ b ∣ a ^ c :=
  ⟨a ^ (c - b), by rw [← opow_add, Ordinal.add_sub_cancel_of_le h]⟩

@[target]
theorem opow_dvd_opow_iff {a b c : Ordinal} (a1 : 1 < a) : a ^ b ∣ a ^ c ↔ b ≤ c := by sorry

@[target]
theorem opow_mul (a b c : Ordinal) : a ^ (b * c) = (a ^ b) ^ c := by sorry

@[target]
theorem opow_mul_add_pos {b v : Ordinal} (hb : b ≠ 0) (u : Ordinal) (hv : v ≠ 0) (w : Ordinal) :
    0 < b ^ u * v + w := by sorry

@[target]
theorem opow_mul_add_lt_opow_mul_succ {b u w : Ordinal} (v : Ordinal) (hw : w < b ^ u) :
    b ^ u * v + w < b ^ u * succ v := by sorry

@[target]
theorem opow_mul_add_lt_opow_succ {b u v w : Ordinal} (hvb : v < b) (hw : w < b ^ u) :
    b ^ u * v + w < b ^ succ u := by sorry

/-! ### Ordinal logarithm -/


/-- The ordinal logarithm is the solution `u` to the equation `x = b ^ u * v + w` where `v < b` and
`w < b ^ u`. -/
@[pp_nodot]
def log (b : Ordinal) (x : Ordinal) : Ordinal :=
  if 1 < b then pred (sInf { o | x < b ^ o }) else 0

/-- The set in the definition of `log` is nonempty. -/
private theorem log_nonempty {b x : Ordinal} (h : 1 < b) : { o : Ordinal | x < b ^ o }.Nonempty :=
  ⟨_, succ_le_iff.1 (right_le_opow _ h)⟩

theorem log_def {b : Ordinal} (h : 1 < b) (x : Ordinal) : log b x = pred (sInf { o | x < b ^ o }) :=
  if_pos h

@[target]
theorem log_of_left_le_one {b : Ordinal} (h : b ≤ 1) (x : Ordinal) : log b x = 0 := by sorry

@[target, deprecated log_of_left_le_one (since := "2024-10-10")]
theorem log_of_not_one_lt_left {b : Ordinal} (h : ¬1 < b) (x : Ordinal) : log b x = 0 := by sorry

@[target, simp]
theorem log_zero_left : ∀ b, log 0 b = 0 := by sorry

@[target, simp]
theorem log_zero_right (b : Ordinal) : log b 0 = 0 := by sorry

@[simp]
theorem log_one_left : ∀ b, log 1 b = 0 :=
  log_of_left_le_one le_rfl

@[target]
theorem succ_log_def {b x : Ordinal} (hb : 1 < b) (hx : x ≠ 0) :
    succ (log b x) = sInf { o : Ordinal | x < b ^ o } := by sorry

@[target]
theorem lt_opow_succ_log_self {b : Ordinal} (hb : 1 < b) (x : Ordinal) :
    x < b ^ succ (log b x) := by sorry

theorem opow_log_le_self (b : Ordinal) {x : Ordinal} (hx : x ≠ 0) : b ^ log b x ≤ x := by
  rcases eq_or_ne b 0 with (rfl | b0)
  · exact (zero_opow_le _).trans (one_le_iff_ne_zero.2 hx)
  rcases lt_or_eq_of_le (one_le_iff_ne_zero.2 b0) with (hb | rfl)
  · refine le_of_not_lt fun h => (lt_succ (log b x)).not_le ?_
    have := @csInf_le' _ _ { o | x < b ^ o } _ h
    rwa [← succ_log_def hb hx] at this
  · rwa [one_opow, one_le_iff_ne_zero]

/-- `opow b` and `log b` (almost) form a Galois connection.

See `opow_le_iff_le_log'` for a variant assuming `c ≠ 0` rather than `x ≠ 0`. See also
`le_log_of_opow_le` and `opow_le_of_le_log`, which are both separate implications under weaker
assumptions. -/
@[target]
theorem opow_le_iff_le_log {b x c : Ordinal} (hb : 1 < b) (hx : x ≠ 0) :
    b ^ c ≤ x ↔ c ≤ log b x := by sorry

/-- `opow b` and `log b` (almost) form a Galois connection.

See `opow_le_iff_le_log` for a variant assuming `x ≠ 0` rather than `c ≠ 0`. See also
`le_log_of_opow_le` and `opow_le_of_le_log`, which are both separate implications under weaker
assumptions. -/
@[target]
theorem opow_le_iff_le_log' {b x c : Ordinal} (hb : 1 < b) (hc : c ≠ 0) :
    b ^ c ≤ x ↔ c ≤ log b x := by sorry

@[target]
theorem le_log_of_opow_le {b x c : Ordinal} (hb : 1 < b) (h : b ^ c ≤ x) : c ≤ log b x := by sorry

@[target]
theorem opow_le_of_le_log {b x c : Ordinal} (hc : c ≠ 0) (h : c ≤ log b x) : b ^ c ≤ x := by sorry

/-- `opow b` and `log b` (almost) form a Galois connection.

See `lt_opow_iff_log_lt'` for a variant assuming `c ≠ 0` rather than `x ≠ 0`. See also
`lt_opow_of_log_lt` and `lt_log_of_lt_opow`, which are both separate implications under weaker
assumptions. -/
@[target]
theorem lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1 < b) (hx : x ≠ 0) : x < b ^ c ↔ log b x < c := by sorry

/-- `opow b` and `log b` (almost) form a Galois connection.

See `lt_opow_iff_log_lt` for a variant assuming `x ≠ 0` rather than `c ≠ 0`. See also
`lt_opow_of_log_lt` and `lt_log_of_lt_opow`, which are both separate implications under weaker
assumptions. -/
@[target]
theorem lt_opow_iff_log_lt' {b x c : Ordinal} (hb : 1 < b) (hc : c ≠ 0) : x < b ^ c ↔ log b x < c := by sorry

@[target]
theorem lt_opow_of_log_lt {b x c : Ordinal} (hb : 1 < b) : log b x < c → x < b ^ c := by sorry

@[target]
theorem lt_log_of_lt_opow {b x c : Ordinal} (hc : c ≠ 0) : x < b ^ c → log b x < c := by sorry

theorem log_pos {b o : Ordinal} (hb : 1 < b) (ho : o ≠ 0) (hbo : b ≤ o) : 0 < log b o := by
  rwa [← succ_le_iff, succ_zero, ← opow_le_iff_le_log hb ho, opow_one]

@[target]
theorem log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o = 0 := by sorry

@[target, mono]
theorem log_mono_right (b : Ordinal) {x y : Ordinal} (xy : x ≤ y) : log b x ≤ log b y := by sorry

@[target]
theorem log_le_self (b x : Ordinal) : log b x ≤ x := by sorry

@[target, simp]
theorem log_one_right (b : Ordinal) : log b 1 = 0 := by sorry

theorem mod_opow_log_lt_self (b : Ordinal) {o : Ordinal} (ho : o ≠ 0) : o % (b ^ log b o) < o := by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simpa using Ordinal.pos_iff_ne_zero.2 ho
  · exact (mod_lt _ <| opow_ne_zero _ hb).trans_le (opow_log_le_self _ ho)

@[target]
theorem log_mod_opow_log_lt_log_self {b o : Ordinal} (hb : 1 < b) (hbo : b ≤ o) :
    log b (o % (b ^ log b o)) < log b o := by sorry

@[target]
theorem log_eq_iff {b x : Ordinal} (hb : 1 < b) (hx : x ≠ 0) (y : Ordinal) :
    log b x = y ↔ b ^ y ≤ x ∧ x < b ^ succ y := by sorry

theorem log_opow_mul_add {b u v w : Ordinal} (hb : 1 < b) (hv : v ≠ 0) (hw : w < b ^ u) :
    log b (b ^ u * v + w) = u + log b v := by
  rw [log_eq_iff hb]
  · constructor
    · rw [opow_add]
      exact (mul_le_mul_left' (opow_log_le_self b hv) _).trans (le_add_right _ w)
    · apply (add_lt_add_left hw _).trans_le
      rw [← mul_succ, ← add_succ, opow_add]
      apply mul_le_mul_left'
      rw [succ_le_iff]
      exact lt_opow_succ_log_self hb _
  · exact fun h ↦ mul_ne_zero (opow_ne_zero u (bot_lt_of_lt hb).ne') hv <|
      left_eq_zero_of_add_eq_zero h

theorem log_opow_mul {b v : Ordinal} (hb : 1 < b) (u : Ordinal) (hv : v ≠ 0) :
    log b (b ^ u * v) = u + log b v := by
  simpa using log_opow_mul_add hb hv (opow_pos u (bot_lt_of_lt hb))

theorem log_opow {b : Ordinal} (hb : 1 < b) (x : Ordinal) : log b (b ^ x) = x := by
  convert log_opow_mul hb x zero_ne_one.symm using 1
  · rw [mul_one]
  · rw [log_one_right, add_zero]

@[target]
theorem div_opow_log_pos (b : Ordinal) {o : Ordinal} (ho : o ≠ 0) : 0 < o / (b ^ log b o) := by sorry

@[target]
theorem div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb : 1 < b) : o / (b ^ log b o) < b := by sorry

theorem add_log_le_log_mul {x y : Ordinal} (b : Ordinal) (hx : x ≠ 0) (hy : y ≠ 0) :
    log b x + log b y ≤ log b (x * y) := by
  obtain hb | hb := lt_or_le 1 b
  · rw [← opow_le_iff_le_log hb (mul_ne_zero hx hy), opow_add]
    exact mul_le_mul' (opow_log_le_self b hx) (opow_log_le_self b hy)
  · simpa only [log_of_left_le_one hb, zero_add] using le_rfl

theorem omega0_opow_mul_nat_lt {a b : Ordinal} (h : a < b) (n : ℕ) : ω ^ a * n < ω ^ b := by
  apply lt_of_lt_of_le _ (opow_le_opow_right omega0_pos (succ_le_of_lt h))
  rw [opow_succ]
  exact mul_lt_mul_of_pos_left (nat_lt_omega0 n) (opow_pos a omega0_pos)

@[target]
theorem lt_omega0_opow {a b : Ordinal} (hb : b ≠ 0) :
    a < ω ^ b ↔ ∃ c < b, ∃ n : ℕ, a < ω ^ c * n := by sorry

theorem lt_omega0_opow_succ {a b : Ordinal} : a < ω ^ succ b ↔ ∃ n : ℕ, a < ω ^ b * n := by
  refine ⟨fun ha ↦ ?_, fun ⟨n, hn⟩ ↦ hn.trans (omega0_opow_mul_nat_lt (lt_succ b) n)⟩
  obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow (succ_ne_zero b)).1 ha
  refine ⟨n, hn.trans_le (mul_le_mul_right' ?_ _)⟩
  rwa [opow_le_opow_iff_right one_lt_omega0, ← lt_succ_iff]

/-! ### Interaction with `Nat.cast` -/

@[simp, norm_cast]
theorem natCast_opow (m : ℕ) : ∀ n : ℕ, ↑(m ^ n : ℕ) = (m : Ordinal) ^ (n : Ordinal)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, natCast_mul, natCast_opow m n, Nat.cast_succ, add_one_eq_succ, opow_succ]

theorem iSup_pow {o : Ordinal} (ho : 0 < o) : ⨆ n : ℕ, o ^ n = o ^ ω := by
  simp_rw [← opow_natCast]
  rcases (one_le_iff_pos.2 ho).lt_or_eq with ho₁ | rfl
  · exact (isNormal_opow ho₁).apply_omega0
  · rw [one_opow]
    refine le_antisymm (Ordinal.iSup_le fun n => by rw [one_opow]) ?_
    exact_mod_cast Ordinal.le_iSup _ 0

set_option linter.deprecated false in
@[deprecated iSup_pow (since := "2024-08-27")]
theorem sup_opow_nat {o : Ordinal} (ho : 0 < o) : (sup fun n : ℕ => o ^ n) = o ^ ω := by
  simp_rw [← opow_natCast]
  rcases (one_le_iff_pos.2 ho).lt_or_eq with ho₁ | rfl
  · exact (isNormal_opow ho₁).apply_omega0
  · rw [one_opow]
    refine le_antisymm (sup_le fun n => by rw [one_opow]) ?_
    convert le_sup (fun n : ℕ => 1 ^ (n : Ordinal)) 0
    rw [Nat.cast_zero, opow_zero]

end Ordinal

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: Port this meta code.

-- namespace Tactic

-- open Ordinal Mathlib.Meta.Positivity

-- /-- Extension for the `positivity` tactic: `ordinal.opow` takes positive values on positive
-- inputs. -/
-- @[positivity]
-- unsafe def positivity_opow : expr → tactic strictness
--   | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => positive <$> mk_app `` opow_pos [b, p]
--       | _ => failed
--   |-- We already know that `0 ≤ x` for all `x : Ordinal`
--     _ =>
--     failed

-- end Tactic
