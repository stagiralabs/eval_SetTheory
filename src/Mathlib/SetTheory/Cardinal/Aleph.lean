import VerifiedAgora.tagger
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.Order.Bounded
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.SetTheory.Ordinal.Enum

/-!
# Omega, aleph, and beth functions

* The function `Ordinal.preOmega` enumerates the initial ordinals, i.e. the smallest ordinals with
  any given cardinality. Thus `preOmega n = n`, `preOmega ω = ω`, `preOmega (ω + 1) = ω₁`, etc.
  `Ordinal.omega` is the more standard function which skips over finite ordinals.
* The function `Cardinal.preAleph` is an order isomorphism between ordinals and cardinals. Thus
  `preAleph n = n`, `preAleph ω = ℵ₀`, `preAleph (ω + 1) = ℵ₁`, etc. `Cardinal.aleph` is the more
  standard function which skips over finite ordinals.
* The function `Cardinal.beth` enumerates the Beth cardinals. `beth 0 = ℵ₀`,
  `beth (succ o) = 2 ^ beth o`, and for a limit ordinal `o`, `beth o` is the supremum of `beth a`
  for `a < o`.

## Notation

The following notations are scoped to the `Ordinal` namespace.

- `ω_ o` is notation for `Ordinal.omega o`. `ω₁` is notation for `ω_ 1`.

The following notations are scoped to the `Cardinal` namespace.

- `ℵ_ o` is notation for `aleph o`. `ℵ₁` is notation for `ℵ_ 1`.
- `ℶ_ o` is notation for `beth o`. The value `ℶ_ 1` equals the continuum `𝔠`, which is defined in
  `Mathlib.SetTheory.Cardinal.Continuum`.
-/

assert_not_exists Field Finsupp Module Cardinal.mul_eq_self

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

/-! ### Omega ordinals -/

namespace Ordinal

/-- An ordinal is initial when it is the first ordinal with a given cardinality.

This is written as `o.card.ord = o`, i.e. `o` is the smallest ordinal with cardinality `o.card`. -/
def IsInitial (o : Ordinal) : Prop :=
  o.card.ord = o

@[target]
theorem IsInitial.ord_card {o : Ordinal} (h : IsInitial o) : o.card.ord = o := by sorry

@[target]
theorem IsInitial.card_le_card {a b : Ordinal} (ha : IsInitial a) : a.card ≤ b.card ↔ a ≤ b := by sorry

@[target]
theorem IsInitial.card_lt_card {a b : Ordinal} (hb : IsInitial b) : a.card < b.card ↔ a < b := by sorry

@[target]
theorem isInitial_ord (c : Cardinal) : IsInitial c.ord := by sorry

@[target]
theorem isInitial_natCast (n : ℕ) : IsInitial n := by sorry

@[target]
theorem isInitial_zero : IsInitial 0 := by sorry

theorem isInitial_one : IsInitial 1 := by
  exact_mod_cast isInitial_natCast 1

@[target]
theorem isInitial_omega0 : IsInitial ω := by sorry

theorem not_bddAbove_isInitial : ¬ BddAbove {x | IsInitial x} := by
  rintro ⟨a, ha⟩
  have := ha (isInitial_ord (succ a.card))
  rw [ord_le] at this
  exact (lt_succ _).not_le this

/-- Initial ordinals are order-isomorphic to the cardinals. -/
@[simps!]
def isInitialIso : {x // IsInitial x} ≃o Cardinal where
  toFun x := x.1.card
  invFun x := ⟨x.ord, isInitial_ord _⟩
  left_inv x := Subtype.ext x.2.ord_card
  right_inv x := card_ord x
  map_rel_iff' {a _} := a.2.card_le_card

/-- The "pre-omega" function gives the initial ordinals listed by their ordinal index.
`preOmega n = n`, `preOmega ω = ω`, `preOmega (ω + 1) = ω₁`, etc.

For the more common omega function skipping over finite ordinals, see `Ordinal.omega`. -/
def preOmega : Ordinal.{u} ↪o Ordinal.{u} where
  toFun := enumOrd {x | IsInitial x}
  inj' _ _ h := enumOrd_injective not_bddAbove_isInitial h
  map_rel_iff' := enumOrd_le_enumOrd not_bddAbove_isInitial

@[target]
theorem coe_preOmega : preOmega = enumOrd {x | IsInitial x} := by sorry

@[target]
theorem preOmega_strictMono : StrictMono preOmega := by sorry

theorem preOmega_lt_preOmega {o₁ o₂ : Ordinal} : preOmega o₁ < preOmega o₂ ↔ o₁ < o₂ :=
  preOmega.lt_iff_lt

@[target]
theorem preOmega_le_preOmega {o₁ o₂ : Ordinal} : preOmega o₁ ≤ preOmega o₂ ↔ o₁ ≤ o₂ := by sorry

theorem preOmega_max (o₁ o₂ : Ordinal) : preOmega (max o₁ o₂) = max (preOmega o₁) (preOmega o₂) :=
  preOmega.monotone.map_max

theorem isInitial_preOmega (o : Ordinal) : IsInitial (preOmega o) :=
  enumOrd_mem not_bddAbove_isInitial o

@[target]
theorem le_preOmega_self (o : Ordinal) : o ≤ preOmega o := by sorry

@[target, simp]
theorem preOmega_zero : preOmega 0 = 0 := by sorry

@[target, simp]
theorem preOmega_natCast (n : ℕ) : preOmega n = n := by sorry

@[target, simp]
theorem preOmega_ofNat (n : ℕ) [n.AtLeastTwo] : preOmega ofNat(n) = n := by sorry

@[target]
theorem preOmega_le_of_forall_lt {o a : Ordinal} (ha : IsInitial a) (H : ∀ b < o, preOmega b < a) :
    preOmega o ≤ a := by sorry

theorem isNormal_preOmega : IsNormal preOmega := by
  rw [isNormal_iff_strictMono_limit]
  refine ⟨preOmega_strictMono, fun o ho a ha ↦
    (preOmega_le_of_forall_lt (isInitial_ord _) fun b hb ↦ ?_).trans (ord_card_le a)⟩
  rw [← (isInitial_ord _).card_lt_card, card_ord]
  apply lt_of_lt_of_le _ (card_le_card <| ha _ (ho.succ_lt hb))
  rw [(isInitial_preOmega _).card_lt_card, preOmega_lt_preOmega]
  exact lt_succ b

@[target, simp]
theorem range_preOmega : range preOmega = {x | IsInitial x} := by sorry

theorem mem_range_preOmega_iff {x : Ordinal} : x ∈ range preOmega ↔ IsInitial x := by
  rw [range_preOmega, mem_setOf]

alias ⟨_, IsInitial.mem_range_preOmega⟩ := mem_range_preOmega_iff

@[simp]
theorem preOmega_omega0 : preOmega ω = ω := by
  simp_rw [← isNormal_preOmega.apply_omega0, preOmega_natCast, iSup_natCast]

@[simp]
theorem omega0_le_preOmega_iff {x : Ordinal} : ω ≤ preOmega x ↔ ω ≤ x := by
  conv_lhs => rw [← preOmega_omega0, preOmega_le_preOmega]

@[target, simp]
theorem omega0_lt_preOmega_iff {x : Ordinal} : ω < preOmega x ↔ ω < x := by sorry

/-- The `omega` function gives the infinite initial ordinals listed by their ordinal index.
`omega 0 = ω`, `omega 1 = ω₁` is the first uncountable ordinal, and so on.

This is not to be confused with the first infinite ordinal `Ordinal.omega0`.

For a version including finite ordinals, see `Ordinal.preOmega`. -/
def omega : Ordinal ↪o Ordinal :=
  (OrderEmbedding.addLeft ω).trans preOmega

@[inherit_doc]
scoped notation "ω_ " => omega

/-- `ω₁` is the first uncountable ordinal. -/
scoped notation "ω₁" => ω_ 1

@[target]
theorem omega_eq_preOmega (o : Ordinal) : ω_ o = preOmega (ω + o) := by sorry

theorem omega_strictMono : StrictMono omega :=
  omega.strictMono

@[target]
theorem omega_lt_omega {o₁ o₂ : Ordinal} : ω_ o₁ < ω_ o₂ ↔ o₁ < o₂ := by sorry

@[target]
theorem omega_le_omega {o₁ o₂ : Ordinal} : ω_ o₁ ≤ ω_ o₂ ↔ o₁ ≤ o₂ := by sorry

@[target]
theorem omega_max (o₁ o₂ : Ordinal) : ω_ (max o₁ o₂) = max (ω_ o₁) (ω_ o₂) := by sorry

@[target]
theorem preOmega_le_omega (o : Ordinal) : preOmega o ≤ ω_ o := by sorry

@[target]
theorem isInitial_omega (o : Ordinal) : IsInitial (omega o) := by sorry

@[target]
theorem le_omega_self (o : Ordinal) : o ≤ omega o := by sorry

@[target, simp]
theorem omega_zero : ω_ 0 = ω := by sorry

@[target]
theorem omega0_le_omega (o : Ordinal) : ω ≤ ω_ o := by sorry

/-- For the theorem `0 < ω`, see `omega0_pos`. -/
theorem omega_pos (o : Ordinal) : 0 < ω_ o :=
  omega0_pos.trans_le (omega0_le_omega o)

@[target]
theorem omega0_lt_omega1 : ω < ω₁ := by sorry

@[deprecated omega0_lt_omega1 (since := "2024-10-11")]
alias omega_lt_omega1 := omega0_lt_omega1

@[target]
theorem isNormal_omega : IsNormal omega := by sorry

@[simp]
theorem range_omega : range omega = {x | ω ≤ x ∧ IsInitial x} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨omega0_le_omega a, isInitial_omega a⟩
  · rintro ⟨ha', ha⟩
    obtain ⟨a, rfl⟩ := ha.mem_range_preOmega
    use a - ω
    rw [omega0_le_preOmega_iff] at ha'
    rw [omega_eq_preOmega, Ordinal.add_sub_cancel_of_le ha']

@[target]
theorem mem_range_omega_iff {x : Ordinal} : x ∈ range omega ↔ ω ≤ x ∧ IsInitial x := by sorry

end Ordinal

/-! ### Aleph cardinals -/

namespace Cardinal

/-- The "pre-aleph" function gives the cardinals listed by their ordinal index. `preAleph n = n`,
`preAleph ω = ℵ₀`, `preAleph (ω + 1) = succ ℵ₀`, etc.

For the more common aleph function skipping over finite cardinals, see `Cardinal.aleph`. -/
def preAleph : Ordinal.{u} ≃o Cardinal.{u} :=
  (enumOrdOrderIso _ not_bddAbove_isInitial).trans isInitialIso

@[target, simp]
theorem _root_.Ordinal.card_preOmega (o : Ordinal) : (preOmega o).card = preAleph o := by sorry

@[target, simp]
theorem ord_preAleph (o : Ordinal) : (preAleph o).ord = preOmega o := by sorry

@[target, simp]
theorem type_cardinal : typeLT Cardinal = Ordinal.univ.{u, u + 1} := by sorry

@[target, simp]
theorem mk_cardinal : #Cardinal = univ.{u, u + 1} := by sorry

theorem preAleph_lt_preAleph {o₁ o₂ : Ordinal} : preAleph o₁ < preAleph o₂ ↔ o₁ < o₂ :=
  preAleph.lt_iff_lt

theorem preAleph_le_preAleph {o₁ o₂ : Ordinal} : preAleph o₁ ≤ preAleph o₂ ↔ o₁ ≤ o₂ :=
  preAleph.le_iff_le

@[target]
theorem preAleph_max (o₁ o₂ : Ordinal) : preAleph (max o₁ o₂) = max (preAleph o₁) (preAleph o₂) := by sorry

@[target, simp]
theorem preAleph_zero : preAleph 0 = 0 := by sorry

@[target, simp]
theorem preAleph_succ (o : Ordinal) : preAleph (succ o) = succ (preAleph o) := by sorry

@[target, simp]
theorem preAleph_nat (n : ℕ) : preAleph n = n := by sorry

@[target, simp]
theorem preAleph_omega0 : preAleph ω = ℵ₀ := by sorry

@[target, simp]
theorem preAleph_pos {o : Ordinal} : 0 < preAleph o ↔ 0 < o := by sorry

@[simp]
theorem aleph0_le_preAleph {o : Ordinal} : ℵ₀ ≤ preAleph o ↔ ω ≤ o := by
  rw [← preAleph_omega0, preAleph_le_preAleph]

@[target, simp]
theorem lift_preAleph (o : Ordinal.{u}) : lift.{v} (preAleph o) = preAleph (Ordinal.lift.{v} o) := by sorry

@[target, simp]
theorem _root_.Ordinal.lift_preOmega (o : Ordinal.{u}) :
    Ordinal.lift.{v} (preOmega o) = preOmega (Ordinal.lift.{v} o) := by sorry

@[target]
theorem preAleph_le_of_isLimit {o : Ordinal} (l : o.IsLimit) {c} :
    preAleph o ≤ c ↔ ∀ o' < o, preAleph o' ≤ c := by sorry

@[target]
theorem preAleph_limit {o : Ordinal} (ho : o.IsLimit) : preAleph o = ⨆ a : Iio o, preAleph a := by sorry

/-- The `aleph` function gives the infinite cardinals listed by their ordinal index. `aleph 0 = ℵ₀`,
`aleph 1 = succ ℵ₀` is the first uncountable cardinal, and so on.

For a version including finite cardinals, see `Cardinal.aleph'`. -/
def aleph : Ordinal ↪o Cardinal :=
  (OrderEmbedding.addLeft ω).trans preAleph.toOrderEmbedding

@[inherit_doc]
scoped notation "ℵ_ " => aleph

/-- `ℵ₁` is the first uncountable cardinal. -/
scoped notation "ℵ₁" => ℵ_ 1

@[target]
theorem aleph_eq_preAleph (o : Ordinal) : ℵ_ o = preAleph (ω + o) := by sorry

@[simp]
theorem _root_.Ordinal.card_omega (o : Ordinal) : (ω_ o).card = ℵ_ o :=
  rfl

@[target, simp]
theorem ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o := by sorry

@[target]
theorem aleph_lt_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ < ℵ_ o₂ ↔ o₁ < o₂ := by sorry

@[deprecated aleph_lt_aleph (since := "2024-10-22")]
alias aleph_lt := aleph_lt_aleph

@[target]
theorem aleph_le_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ ≤ ℵ_ o₂ ↔ o₁ ≤ o₂ := by sorry

@[deprecated aleph_le_aleph (since := "2024-10-22")]
alias aleph_le := aleph_le_aleph

@[target]
theorem aleph_max (o₁ o₂ : Ordinal) : ℵ_ (max o₁ o₂) = max (ℵ_ o₁) (ℵ_ o₂) := by sorry

@[target, deprecated aleph_max (since := "2024-08-28")]
theorem max_aleph_eq (o₁ o₂ : Ordinal) : max (ℵ_ o₁) (ℵ_ o₂) = ℵ_ (max o₁ o₂) := by sorry

@[target]
theorem preAleph_le_aleph (o : Ordinal) : preAleph o ≤ ℵ_ o := by sorry

@[target, simp]
theorem aleph_succ (o : Ordinal) : ℵ_ (succ o) = succ (ℵ_ o) := by sorry

@[target, simp]
theorem aleph_zero : ℵ_ 0 = ℵ₀ := by sorry

@[simp]
theorem lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) = aleph (Ordinal.lift.{v} o) := by
  simp [aleph_eq_preAleph]

/-- For the theorem `lift ω = ω`, see `lift_omega0`. -/
@[target, simp]
theorem _root_.Ordinal.lift_omega (o : Ordinal.{u}) :
    Ordinal.lift.{v} (ω_ o) = ω_ (Ordinal.lift.{v} o) := by sorry

@[target]
theorem aleph_limit {o : Ordinal} (ho : o.IsLimit) : ℵ_ o = ⨆ a : Iio o, ℵ_ a := by sorry

@[target]
theorem aleph0_le_aleph (o : Ordinal) : ℵ₀ ≤ ℵ_ o := by sorry

theorem aleph_pos (o : Ordinal) : 0 < ℵ_ o :=
  aleph0_pos.trans_le (aleph0_le_aleph o)

@[target, simp]
theorem aleph_toNat (o : Ordinal) : toNat (ℵ_ o) = 0 := by sorry

@[target, simp]
theorem aleph_toENat (o : Ordinal) : toENat (ℵ_ o) = ⊤ := by sorry

@[target]
theorem isLimit_omega (o : Ordinal) : Ordinal.IsLimit (ω_ o) := by sorry

@[deprecated isLimit_omega (since := "2024-10-24")]
theorem ord_aleph_isLimit (o : Ordinal) : (ℵ_ o).ord.IsLimit :=
  isLimit_ord <| aleph0_le_aleph _

@[target, simp]
theorem range_aleph : range aleph = Set.Ici ℵ₀ := by sorry

@[target]
theorem mem_range_aleph_iff {c : Cardinal} : c ∈ range aleph ↔ ℵ₀ ≤ c := by sorry

@[deprecated mem_range_aleph_iff (since := "2024-10-24")]
theorem exists_aleph {c : Cardinal} : ℵ₀ ≤ c ↔ ∃ o, c = ℵ_ o :=
  ⟨fun h =>
    ⟨preAleph.symm c - ω, by
      rw [aleph_eq_preAleph, Ordinal.add_sub_cancel_of_le, preAleph.apply_symm_apply]
      rwa [← aleph0_le_preAleph, preAleph.apply_symm_apply]⟩,
    fun ⟨o, e⟩ => e.symm ▸ aleph0_le_aleph _⟩

@[target, deprecated isNormal_preOmega (since := "2024-10-11")]
theorem preAleph_isNormal : IsNormal (ord ∘ preAleph) := by sorry

@[target, deprecated isNormal_omega (since := "2024-10-11")]
theorem aleph_isNormal : IsNormal (ord ∘ aleph) := by sorry

@[target, simp]
theorem succ_aleph0 : succ ℵ₀ = ℵ₁ := by sorry

@[target]
theorem aleph0_lt_aleph_one : ℵ₀ < ℵ₁ := by sorry

theorem countable_iff_lt_aleph_one {α : Type*} (s : Set α) : s.Countable ↔ #s < ℵ₁ := by
  rw [← succ_aleph0, lt_succ_iff, le_aleph0_iff_set_countable]

@[target, simp]
theorem aleph1_le_lift {c : Cardinal.{u}} : ℵ₁ ≤ lift.{v} c ↔ ℵ₁ ≤ c := by sorry

@[target, simp]
theorem lift_le_aleph1 {c : Cardinal.{u}} : lift.{v} c ≤ ℵ₁ ↔ c ≤ ℵ₁ := by sorry

@[simp]
theorem aleph1_lt_lift {c : Cardinal.{u}} : ℵ₁ < lift.{v} c ↔ ℵ₁ < c := by
  simpa using lift_lt (a := ℵ₁)

@[target, simp]
theorem lift_lt_aleph1 {c : Cardinal.{u}} : lift.{v} c < ℵ₁ ↔ c < ℵ₁ := by sorry

@[target, simp]
theorem aleph1_eq_lift {c : Cardinal.{u}} : ℵ₁ = lift.{v} c ↔ ℵ₁ = c := by sorry

@[target, simp]
theorem lift_eq_aleph1 {c : Cardinal.{u}} : lift.{v} c = ℵ₁ ↔ c = ℵ₁ := by sorry

theorem lt_omega_iff_card_lt {x o : Ordinal} : x < ω_ o ↔ x.card < ℵ_ o := by
  rw [← (isInitial_omega o).card_lt_card, card_omega]

section deprecated

set_option linter.docPrime false

@[deprecated preAleph (since := "2024-10-22")]
noncomputable alias aleph' := preAleph

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ω = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `alephIdx`.
  For an upgraded version stating that the range is everything, see `AlephIdx.rel_iso`. -/
@[deprecated preAleph (since := "2024-08-28")]
def alephIdx.initialSeg : @InitialSeg Cardinal Ordinal (· < ·) (· < ·) :=
  @RelEmbedding.collapse Cardinal Ordinal (· < ·) (· < ·) _ Cardinal.ord.orderEmbedding.ltEmbedding

set_option linter.deprecated false in
/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ℵ₀ = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `alephIdx`. -/
@[deprecated preAleph (since := "2024-08-28")]
def alephIdx.relIso : @RelIso Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) :=
  aleph'.symm.toRelIsoLT

set_option linter.deprecated false in
/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ω = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  For an upgraded version stating that the range is everything, see `AlephIdx.rel_iso`. -/
@[deprecated aleph' (since := "2024-08-28")]
def alephIdx : Cardinal → Ordinal :=
  aleph'.symm

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-08-28")]
theorem alephIdx.relIso_coe : (alephIdx.relIso : Cardinal → Ordinal) = alephIdx := by sorry

set_option linter.deprecated false in
/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
@[deprecated aleph' (since := "2024-08-28")]
def Aleph'.relIso :=
  aleph'

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided."  (since := "2024-08-28")]
theorem aleph'.relIso_coe : (Aleph'.relIso : Ordinal → Cardinal) = aleph' :=
  rfl

set_option linter.deprecated false in
@[target, deprecated preAleph_lt_preAleph (since := "2024-10-22")]
theorem aleph'_lt {o₁ o₂ : Ordinal} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ := by sorry

set_option linter.deprecated false in
@[target, deprecated preAleph_le_preAleph (since := "2024-10-22")]
theorem aleph'_le {o₁ o₂ : Ordinal} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ := by sorry

set_option linter.deprecated false in
@[target, deprecated preAleph_max (since := "2024-10-22")]
theorem aleph'_max (o₁ o₂ : Ordinal) : aleph' (max o₁ o₂) = max (aleph' o₁) (aleph' o₂) := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-08-28")]
theorem aleph'_alephIdx (c : Cardinal) : aleph' c.alephIdx = c := by sorry

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided."  (since := "2024-08-28")]
theorem alephIdx_aleph' (o : Ordinal) : (aleph' o).alephIdx = o :=
  Cardinal.alephIdx.relIso.toEquiv.apply_symm_apply o

set_option linter.deprecated false in
@[target, deprecated preAleph_zero (since := "2024-10-22")]
theorem aleph'_zero : aleph' 0 = 0 := by sorry

set_option linter.deprecated false in
@[target, deprecated preAleph_succ (since := "2024-10-22")]
theorem aleph'_succ (o : Ordinal) : aleph' (succ o) = succ (aleph' o) := by sorry

set_option linter.deprecated false in
@[target, deprecated preAleph_nat (since := "2024-10-22")]
theorem aleph'_nat : ∀ n : ℕ, aleph' n = n := by sorry

set_option linter.deprecated false in
@[deprecated lift_preAleph (since := "2024-10-22")]
theorem lift_aleph' (o : Ordinal.{u}) : lift.{v} (aleph' o) = aleph' (Ordinal.lift.{v} o) :=
  lift_preAleph o

set_option linter.deprecated false in
@[target, deprecated preAleph_le_of_isLimit (since := "2024-10-22")]
theorem aleph'_le_of_limit {o : Ordinal} (l : o.IsLimit) {c} :
    aleph' o ≤ c ↔ ∀ o' < o, aleph' o' ≤ c := by sorry

set_option linter.deprecated false in
@[target, deprecated preAleph_limit (since := "2024-10-22")]
theorem aleph'_limit {o : Ordinal} (ho : o.IsLimit) : aleph' o = ⨆ a : Iio o, aleph' a := by sorry

set_option linter.deprecated false in
@[target, deprecated preAleph_omega0 (since := "2024-10-22")]
theorem aleph'_omega0 : aleph' ω = ℵ₀ := by sorry

@[deprecated "No deprecation message was provided."  (since := "2024-09-30")]
alias aleph'_omega := aleph'_omega0

set_option linter.deprecated false in
/-- `aleph'` and `aleph_idx` form an equivalence between `Ordinal` and `Cardinal` -/
@[deprecated aleph' (since := "2024-08-28")]
def aleph'Equiv : Ordinal ≃ Cardinal :=
  ⟨aleph', alephIdx, alephIdx_aleph', aleph'_alephIdx⟩

@[target, deprecated aleph_eq_preAleph (since := "2024-10-22")]
theorem aleph_eq_aleph' (o : Ordinal) : ℵ_ o = preAleph (ω + o) := by sorry

set_option linter.deprecated false in
@[target, deprecated aleph0_le_preAleph (since := "2024-10-22")]
theorem aleph0_le_aleph' {o : Ordinal} : ℵ₀ ≤ aleph' o ↔ ω ≤ o := by sorry

set_option linter.deprecated false in
@[target, deprecated preAleph_pos (since := "2024-10-22")]
theorem aleph'_pos {o : Ordinal} (ho : 0 < o) : 0 < aleph' o := by sorry

set_option linter.deprecated false in
@[target, deprecated preAleph_isNormal (since := "2024-10-22")]
theorem aleph'_isNormal : IsNormal (ord ∘ aleph') := by sorry

/-- Ordinals that are cardinals are unbounded. -/
@[deprecated "No deprecation message was provided."  (since := "2024-09-24")]
theorem ord_card_unbounded : Unbounded (· < ·) { b : Ordinal | b.card.ord = b } :=
  unbounded_lt_iff.2 fun a =>
    ⟨_,
      ⟨by
        dsimp
        rw [card_ord], (lt_ord_succ_card a).le⟩⟩

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-24")]
theorem eq_aleph'_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) : ∃ a, (aleph' a).ord = o := by sorry

set_option linter.deprecated false in
/-- Infinite ordinals that are cardinals are unbounded. -/
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-24")]
theorem ord_card_unbounded' : Unbounded (· < ·) { b : Ordinal | b.card.ord = b ∧ ω ≤ b } := by sorry

set_option linter.deprecated false in
@[target, deprecated "No deprecation message was provided."  (since := "2024-09-24")]
theorem eq_aleph_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) (ho' : ω ≤ o) :
    ∃ a, (ℵ_ a).ord = o := by sorry

end deprecated

/-! ### Beth cardinals -/

/-- Beth numbers are defined so that `beth 0 = ℵ₀`, `beth (succ o) = 2 ^ beth o`, and when `o` is
a limit ordinal, `beth o` is the supremum of `beth o'` for `o' < o`.

Assuming the generalized continuum hypothesis, which is undecidable in ZFC, `beth o = aleph o` for
every `o`. -/
def beth (o : Ordinal.{u}) : Cardinal.{u} :=
  limitRecOn o ℵ₀ (fun _ x => 2 ^ x) fun a _ IH => ⨆ b : Iio a, IH b.1 b.2

@[inherit_doc]
scoped notation "ℶ_ " => beth

@[simp]
theorem beth_zero : ℶ_ 0 = ℵ₀ :=
  limitRecOn_zero _ _ _

@[target, simp]
theorem beth_succ (o : Ordinal) : ℶ_ (succ o) = 2 ^ beth o := by sorry

@[target]
theorem beth_limit {o : Ordinal} : o.IsLimit → ℶ_ o = ⨆ a : Iio o, ℶ_ a := by sorry

@[target]
theorem beth_strictMono : StrictMono beth := by sorry

@[target]
theorem beth_mono : Monotone beth := by sorry

@[target, simp]
theorem beth_lt {o₁ o₂ : Ordinal} : ℶ_ o₁ < ℶ_ o₂ ↔ o₁ < o₂ := by sorry

@[target, simp]
theorem beth_le {o₁ o₂ : Ordinal} : ℶ_ o₁ ≤ ℶ_ o₂ ↔ o₁ ≤ o₂ := by sorry

theorem aleph_le_beth (o : Ordinal) : ℵ_ o ≤ ℶ_ o := by
  induction o using limitRecOn with
  | H₁ => simp
  | H₂ o h =>
    rw [aleph_succ, beth_succ, succ_le_iff]
    exact (cantor _).trans_le (power_le_power_left two_ne_zero h)
  | H₃ o ho IH =>
    rw [aleph_limit ho, beth_limit ho]
    exact ciSup_mono (bddAbove_of_small _) fun x => IH x.1 x.2

@[target]
theorem aleph0_le_beth (o : Ordinal) : ℵ₀ ≤ ℶ_ o := by sorry

@[target]
theorem beth_pos (o : Ordinal) : 0 < ℶ_ o := by sorry

theorem beth_ne_zero (o : Ordinal) : ℶ_ o ≠ 0 :=
  (beth_pos o).ne'

@[target]
theorem isNormal_beth : IsNormal (ord ∘ beth) := by sorry

@[target, deprecated isNormal_beth (since := "2024-10-11")]
theorem beth_normal : IsNormal.{u} fun o => (beth o).ord := by sorry

end Cardinal
