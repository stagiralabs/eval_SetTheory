import VerifiedAgora.tagger
/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Enumerating sets of ordinals by ordinals

The ordinals have the peculiar property that every subset bounded above is a small type, while
themselves not being small. As a consequence of this, every unbounded subset of `Ordinal` is order
isomorphic to `Ordinal`.

We define this correspondence as `enumOrd`, and use it to then define an order isomorphism
`enumOrdOrderIso`.

This can be thought of as an ordinal analog of `Nat.nth`.
-/

universe u

open Order Set

namespace Ordinal

variable {o a b : Ordinal.{u}}

/-- Enumerator function for an unbounded set of ordinals. -/
noncomputable def enumOrd (s : Set Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  sInf (s ∩ { b | ∀ c, c < o → enumOrd s c < b })
termination_by o

variable {s : Set Ordinal.{u}}

@[target, deprecated "No deprecation message was provided."  (since := "2024-09-20")]
theorem enumOrd_def (o : Ordinal.{u}) :
    enumOrd s o = sInf (s ∩ { b | ∀ c, c < o → enumOrd s c < b }) := by sorry

@[target]
theorem enumOrd_le_of_forall_lt (ha : a ∈ s) (H : ∀ b < o, enumOrd s b < a) : enumOrd s o ≤ a := by sorry

/-- The set in the definition of `enumOrd` is nonempty. -/
private theorem enumOrd_nonempty (hs : ¬ BddAbove s) (o : Ordinal) :
    (s ∩ { b | ∀ c, c < o → enumOrd s c < b }).Nonempty := by
  rw [not_bddAbove_iff] at hs
  obtain ⟨a, ha⟩ := bddAbove_of_small (enumOrd s '' Iio o)
  obtain ⟨b, hb, hba⟩ := hs a
  exact ⟨b, hb, fun c hc ↦ (ha (mem_image_of_mem _ hc)).trans_lt hba⟩

private theorem enumOrd_mem_aux (hs : ¬ BddAbove s) (o : Ordinal) :
    enumOrd s o ∈ s ∩ { b | ∀ c, c < o → enumOrd s c < b } := by
  rw [enumOrd]
  exact csInf_mem (enumOrd_nonempty hs o)

@[target]
theorem enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enumOrd s o ∈ s := by sorry

@[target]
theorem enumOrd_strictMono (hs : ¬ BddAbove s) : StrictMono (enumOrd s) := by sorry

theorem enumOrd_injective (hs : ¬ BddAbove s) : Function.Injective (enumOrd s) :=
  (enumOrd_strictMono hs).injective

@[target]
theorem enumOrd_inj (hs : ¬ BddAbove s) {a b : Ordinal} : enumOrd s a = enumOrd s b ↔ a = b := by sorry

@[target]
theorem enumOrd_le_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} :
    enumOrd s a ≤ enumOrd s b ↔ a ≤ b := by sorry

@[target]
theorem enumOrd_lt_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} :
    enumOrd s a < enumOrd s b ↔ a < b := by sorry

@[target]
theorem id_le_enumOrd (hs : ¬ BddAbove s) : id ≤ enumOrd s := by sorry

@[target]
theorem le_enumOrd_self (hs : ¬ BddAbove s) {a} : a ≤ enumOrd s a := by sorry

@[target]
theorem enumOrd_succ_le (hs : ¬ BddAbove s) (ha : a ∈ s) (hb : enumOrd s b < a) :
    enumOrd s (succ b) ≤ a := by sorry

@[target]
theorem range_enumOrd (hs : ¬ BddAbove s) : range (enumOrd s) = s := by sorry

@[target]
theorem enumOrd_surjective (hs : ¬ BddAbove s) {b : Ordinal} (hb : b ∈ s) :
    ∃ a, enumOrd s a = b := by sorry

@[target]
theorem enumOrd_le_of_subset {t : Set Ordinal} (hs : ¬ BddAbove s) (hst : s ⊆ t) :
    enumOrd t ≤ enumOrd s := by sorry

/-- A characterization of `enumOrd`: it is the unique strict monotonic function with range `s`. -/
@[target]
theorem eq_enumOrd (f : Ordinal → Ordinal) (hs : ¬ BddAbove s) :
    enumOrd s = f ↔ StrictMono f ∧ range f = s := by sorry

theorem enumOrd_range {f : Ordinal → Ordinal} (hf : StrictMono f) : enumOrd (range f) = f :=
  (eq_enumOrd _ hf.not_bddAbove_range_of_wellFoundedLT).2 ⟨hf, rfl⟩

@[target, simp]
theorem enumOrd_univ : enumOrd Set.univ = id := by sorry

@[target, simp]
theorem enumOrd_zero : enumOrd s 0 = sInf s := by sorry

/-- An order isomorphism between an unbounded set of ordinals and the ordinals. -/
noncomputable def enumOrdOrderIso (s : Set Ordinal) (hs : ¬ BddAbove s) : Ordinal ≃o s :=
  StrictMono.orderIsoOfSurjective (fun o => ⟨_, enumOrd_mem hs o⟩) (enumOrd_strictMono hs) fun s =>
    let ⟨a, ha⟩ := enumOrd_surjective hs s.prop
    ⟨a, Subtype.eq ha⟩

end Ordinal
