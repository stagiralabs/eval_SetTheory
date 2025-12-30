import VerifiedAgora.tagger
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Countable.Small
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Equiv.Fin
import Mathlib.Logic.Small.Set
import Mathlib.Logic.UnivLE
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.InitialSeg
import Mathlib.Order.SuccPred.CompleteLinearOrder
import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-!
# Cardinal Numbers

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerity.

## Main definitions

* `Cardinal` is the type of cardinal numbers (in a given universe).
* `Cardinal.mk α` or `#α` is the cardinality of `α`. The notation `#` lives in the locale
  `Cardinal`.
* Addition `c₁ + c₂` is defined by `Cardinal.add_def α β : #α + #β = #(α ⊕ β)`.
* Multiplication `c₁ * c₂` is defined by `Cardinal.mul_def : #α * #β = #(α × β)`.
* The order `c₁ ≤ c₂` is defined by `Cardinal.le_def α β : #α ≤ #β ↔ Nonempty (α ↪ β)`.
* Exponentiation `c₁ ^ c₂` is defined by `Cardinal.power_def α β : #α ^ #β = #(β → α)`.
* `Order.IsSuccLimit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `Cardinal.aleph0` or `ℵ₀` is the cardinality of `ℕ`. This definition is universe polymorphic:
  `Cardinal.aleph0.{u} : Cardinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.
* `Cardinal.sum` is the sum of an indexed family of cardinals, i.e. the cardinality of the
  corresponding sigma type.
* `Cardinal.prod` is the product of an indexed family of cardinals, i.e. the cardinality of the
  corresponding pi type.
* `Cardinal.powerlt a b` or `a ^< b` is defined as the supremum of `a ^ c` for `c < b`.

## Main instances

* Cardinals form a `CanonicallyOrderedAdd` `OrderedCommSemiring` with the aforementioned sum and
  product.
* Cardinals form a `SuccOrder`. Use `Order.succ c` for the smallest cardinal greater than `c`.
* The less than relation on cardinals forms a well-order.
* Cardinals form a `ConditionallyCompleteLinearOrderBot`. Bounded sets for cardinals in universe
  `u` are precisely the sets indexed by some type in universe `u`, see
  `Cardinal.bddAbove_iff_small`. One can use `sSup` for the cardinal supremum, and `sInf` for the
  minimum of a set of cardinals.

## Main Statements

* Cantor's theorem: `Cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `Cardinal.sum_lt_prod`

## Implementation notes

* There is a type of cardinal numbers in every universe level:
  `Cardinal.{u} : Type (u + 1)` is the quotient of types in `Type u`.
  The operation `Cardinal.lift` lifts cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `Mathlib/SetTheory/Cardinal/Ordinal.lean`.
* There is an instance `Pow Cardinal`, but this will only fire if Lean already knows that both
  the base and the exponent live in the same universe. As a workaround, you can add
  ```
    local infixr:80 " ^' " => @HPow.hPow Cardinal Cardinal Cardinal _
  ```
  to a file. This notation will work even if Lean doesn't know yet that the base and the exponent
  live in the same universe (but no exponents in other types can be used).
  (Porting note: This last point might need to be updated.)

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

assert_not_exists Field

open List (Vector)
open Function Order Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

/-! ### Definition of cardinals -/

/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
instance Cardinal.isEquivalent : Setoid (Type u) where
  r α β := Nonempty (α ≃ β)
  iseqv := ⟨
    fun α => ⟨Equiv.refl α⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `Cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
@[pp_with_univ]
def Cardinal : Type (u + 1) :=
  Quotient Cardinal.isEquivalent

namespace Cardinal

/-- The cardinal number of a type -/
def mk : Type u → Cardinal :=
  Quotient.mk'

@[inherit_doc]
scoped prefix:max "#" => Cardinal.mk

instance canLiftCardinalType : CanLift Cardinal.{u} (Type u) mk fun _ => True :=
  ⟨fun c _ => Quot.inductionOn c fun α => ⟨α, rfl⟩⟩

@[target, elab_as_elim]
theorem inductionOn {p : Cardinal → Prop} (c : Cardinal) (h : ∀ α, p #α) : p c := by sorry

@[elab_as_elim]
theorem inductionOn₂ {p : Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal)
    (h : ∀ α β, p #α #β) : p c₁ c₂ :=
  Quotient.inductionOn₂ c₁ c₂ h

@[target, elab_as_elim]
theorem inductionOn₃ {p : Cardinal → Cardinal → Cardinal → Prop} (c₁ : Cardinal) (c₂ : Cardinal)
    (c₃ : Cardinal) (h : ∀ α β γ, p #α #β #γ) : p c₁ c₂ c₃ := by sorry

@[target]
theorem induction_on_pi {ι : Type u} {p : (ι → Cardinal.{v}) → Prop}
    (f : ι → Cardinal.{v}) (h : ∀ f : ι → Type v, p fun i ↦ #(f i)) : p f := by sorry

protected theorem eq : #α = #β ↔ Nonempty (α ≃ β) :=
  Quotient.eq'

/-- Avoid using `Quotient.mk` to construct a `Cardinal` directly -/
@[target, deprecated "No deprecation message was provided." (since := "2024-10-24")]
theorem mk'_def (α : Type u) : @Eq Cardinal ⟦α⟧ #α := by sorry

@[target, simp]
theorem mk_out (c : Cardinal) : #c.out = c := by sorry

/-- The representative of the cardinal of a type is equivalent to the original type. -/
def outMkEquiv {α : Type v} : (#α).out ≃ α :=
  Nonempty.some <| Cardinal.eq.mp (by simp)

@[target]
theorem mk_congr (e : α ≃ β) : #α = #β := by sorry

alias _root_.Equiv.cardinal_eq := mk_congr

/-- Lift a function between `Type*`s to a function between `Cardinal`s. -/
def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) : Cardinal.{u} → Cardinal.{v} :=
  Quotient.map f fun α β ⟨e⟩ => ⟨hf α β e⟩

@[target, simp]
theorem map_mk (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) (α : Type u) :
    map f hf #α = #(f α) := by sorry

/-- Lift a binary operation `Type* → Type* → Type*` to a binary operation on `Cardinal`s. -/
def map₂ (f : Type u → Type v → Type w) (hf : ∀ α β γ δ, α ≃ β → γ ≃ δ → f α γ ≃ f β δ) :
    Cardinal.{u} → Cardinal.{v} → Cardinal.{w} :=
  Quotient.map₂ f fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩

/-! ### Lifting cardinals to a higher universe -/

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : Cardinal.{v} → Cardinal.{max v u}` -/
@[pp_with_univ]
def lift (c : Cardinal.{v}) : Cardinal.{max v u} :=
  map ULift.{u, v} (fun _ _ e => Equiv.ulift.trans <| e.trans Equiv.ulift.symm) c

@[simp]
theorem mk_uLift (α) : #(ULift.{v, u} α) = lift.{v} #α :=
  rfl

/-- `lift.{max u v, u}` equals `lift.{v, u}`.

Unfortunately, the simp lemma doesn't work. -/
@[target]
theorem lift_umax : lift.{max u v, u} = lift.{v, u} := by sorry

/-- `lift.{max v u, u}` equals `lift.{v, u}`. -/
@[target, deprecated lift_umax (since := "2024-10-24")]
theorem lift_umax' : lift.{max v u, u} = lift.{v, u} := by sorry

/-- A cardinal lifted to a lower or equal universe equals itself.

Unfortunately, the simp lemma doesn't work. -/
theorem lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a :=
  inductionOn a fun _ => mk_congr Equiv.ulift

/-- A cardinal lifted to the same universe equals itself. -/
@[simp]
theorem lift_id (a : Cardinal) : lift.{u, u} a = a :=
  lift_id'.{u, u} a

/-- A cardinal lifted to the zero universe equals itself. -/
@[target, simp]
theorem lift_uzero (a : Cardinal.{u}) : lift.{0} a = a := by sorry

@[simp]
theorem lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lift.{v} a) = lift.{max v w} a := by
  sorry

@[target]
theorem out_lift_equiv (a : Cardinal.{u}) : Nonempty ((lift.{v} a).out ≃ a.out) := by sorry

@[target, simp]
lemma mk_preimage_down {s : Set α} : #(ULift.down.{v} ⁻¹' s) = lift.{v} (#s) := by sorry

@[target]
theorem lift_mk_eq {α : Type u} {β : Type v} :
    lift.{max v w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β) := by sorry

/-- A variant of `Cardinal.lift_mk_eq` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #α = lift.{u} #β ↔ Nonempty (α ≃ β) :=
  lift_mk_eq.{u, v, 0}

@[target]
theorem mk_congr_lift {α : Type u} {β : Type v} (e : α ≃ β) : lift.{v} #α = lift.{u} #β := by sorry

alias _root_.Equiv.lift_cardinal_eq := mk_congr_lift

@[target, simp, nolint simpNF]
theorem lift_mk_shrink (α : Type u) [Small.{v} α] :
    Cardinal.lift.{max u w} #(Shrink.{v} α) = Cardinal.lift.{max v w} #α := by sorry

@[simp]
theorem lift_mk_shrink' (α : Type u) [Small.{v} α] :
    Cardinal.lift.{u} #(Shrink.{v} α) = Cardinal.lift.{v} #α :=
  lift_mk_shrink.{u, v, 0} α

@[target, simp]
theorem lift_mk_shrink'' (α : Type max u v) [Small.{v} α] :
    Cardinal.lift.{u} #(Shrink.{v} α) = #α := by sorry

/-! ### Order on cardinals -/

/-- We define the order on cardinal numbers by `#α ≤ #β` if and only if
  there exists an embedding (injective function) from α to β. -/
instance : LE Cardinal.{u} :=
  ⟨fun q₁ q₂ =>
    Quotient.liftOn₂ q₁ q₂ (fun α β => Nonempty <| α ↪ β) fun _ _ _ _ ⟨e₁⟩ ⟨e₂⟩ =>
      propext ⟨fun ⟨e⟩ => ⟨e.congr e₁ e₂⟩, fun ⟨e⟩ => ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

instance partialOrder : PartialOrder Cardinal.{u} where
  le := (· ≤ ·)
  le_refl := by
    rintro ⟨α⟩
    exact ⟨Embedding.refl _⟩
  le_trans := by
    rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩
    exact ⟨e₁.trans e₂⟩
  le_antisymm := by
    rintro ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩
    exact Quotient.sound (e₁.antisymm e₂)

instance linearOrder : LinearOrder Cardinal.{u} :=
  { Cardinal.partialOrder with
    le_total := by
      rintro ⟨α⟩ ⟨β⟩
      apply Embedding.total
    decidableLE := Classical.decRel _ }

@[target]
theorem le_def (α β : Type u) : #α ≤ #β ↔ Nonempty (α ↪ β) := by sorry

theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : Injective f) : #α ≤ #β :=
  ⟨⟨f, hf⟩⟩

theorem _root_.Function.Embedding.cardinal_le {α β : Type u} (f : α ↪ β) : #α ≤ #β :=
  ⟨f⟩

@[target]
theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : Surjective f) : #β ≤ #α := by sorry

@[target]
theorem le_mk_iff_exists_set {c : Cardinal} {α : Type u} : c ≤ #α ↔ ∃ p : Set α, #p = c := by sorry

@[target]
theorem mk_subtype_le {α : Type u} (p : α → Prop) : #(Subtype p) ≤ #α := by sorry

@[target]
theorem mk_set_le (s : Set α) : #s ≤ #α := by sorry

@[target]
theorem out_embedding {c c' : Cardinal} : c ≤ c' ↔ Nonempty (c.out ↪ c'.out) := by sorry

@[target]
theorem lift_mk_le {α : Type v} {β : Type w} :
    lift.{max u w} #α ≤ lift.{max u v} #β ↔ Nonempty (α ↪ β) := by sorry

/-- A variant of `Cardinal.lift_mk_le` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
@[target]
theorem lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #α ≤ lift.{u} #β ↔ Nonempty (α ↪ β) := by sorry

/-! ### `lift` sends `Cardinal.{u}` to an initial segment of `Cardinal.{max u v}`. -/

/-- `Cardinal.lift` as an `InitialSeg`. -/
@[simps!]
def liftInitialSeg : Cardinal.{u} ≤i Cardinal.{max u v} := by
  refine ⟨(OrderEmbedding.ofMapLEIff lift ?_).ltEmbedding, ?_⟩ <;> intro a b
  · refine inductionOn₂ a b fun _ _ ↦ ?_
    rw [← lift_umax, lift_mk_le.{v, u, u}, le_def]
  · refine inductionOn₂ a b fun α β h ↦ ?_
    obtain ⟨e⟩ := h.le
    replace e := e.congr (Equiv.refl β) Equiv.ulift
    refine ⟨#(range e), mk_congr (Equiv.ulift.trans <| Equiv.symm ?_)⟩
    apply (e.codRestrict _ mem_range_self).equivOfSurjective
    rintro ⟨a, ⟨b, rfl⟩⟩
    exact ⟨b, rfl⟩

theorem mem_range_lift_of_le {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift.{v, u} a → b ∈ Set.range lift.{v, u} :=
  liftInitialSeg.mem_range_of_le

@[target, deprecated mem_range_lift_of_le (since := "2024-10-07")]
theorem lift_down {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift.{v, u} a → ∃ a', lift.{v, u} a' = b := by sorry

/-- `Cardinal.lift` as an `OrderEmbedding`. -/
@[deprecated Cardinal.liftInitialSeg (since := "2024-10-07")]
def liftOrderEmbedding : Cardinal.{v} ↪o Cardinal.{max v u} :=
  liftInitialSeg.toOrderEmbedding

theorem lift_injective : Injective lift.{u, v} :=
  liftInitialSeg.injective

@[simp]
theorem lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.{v, u} b ↔ a = b :=
  lift_injective.eq_iff

@[target, simp]
theorem lift_le {a b : Cardinal.{v}} : lift.{u} a ≤ lift.{u} b ↔ a ≤ b := by sorry

@[target, simp]
theorem lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v, u} b ↔ a < b := by sorry

@[target]
theorem lift_strictMono : StrictMono lift := by sorry

theorem lift_monotone : Monotone lift :=
  lift_strictMono.monotone

@[target, simp]
theorem lift_min {a b : Cardinal} : lift.{u, v} (min a b) = min (lift.{u, v} a) (lift.{u, v} b) := by sorry

@[target, simp]
theorem lift_max {a b : Cardinal} : lift.{u, v} (max a b) = max (lift.{u, v} a) (lift.{u, v} b) := by sorry

@[target, simp, nolint simpNF]
theorem lift_umax_eq {a : Cardinal.{u}} {b : Cardinal.{v}} :
    lift.{max v w} a = lift.{max u w} b ↔ lift.{v} a = lift.{u} b := by sorry

@[target]
theorem le_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift.{v, u} a ↔ ∃ a' ≤ a, lift.{v, u} a' = b := by sorry

@[target]
theorem lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b < lift.{v, u} a ↔ ∃ a' < a, lift.{v, u} a' = b := by sorry

/-! ### Basic cardinals -/

instance : Zero Cardinal.{u} :=
  -- `PEmpty` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 0)⟩

instance : Inhabited Cardinal.{u} :=
  ⟨0⟩

@[simp]
theorem mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0 := by
  sorry

@[target, simp]
theorem lift_zero : lift 0 = 0 := by sorry

@[target, simp]
theorem lift_eq_zero {a : Cardinal.{v}} : lift.{u} a = 0 ↔ a = 0 := by sorry

@[target]
theorem mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty α := by sorry

@[target]
theorem mk_ne_zero_iff {α : Type u} : #α ≠ 0 ↔ Nonempty α := by sorry

@[target, simp]
theorem mk_ne_zero (α : Type u) [Nonempty α] : #α ≠ 0 := by sorry

instance : One Cardinal.{u} :=
  -- `PUnit` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 1)⟩

instance : Nontrivial Cardinal.{u} :=
  ⟨⟨1, 0, mk_ne_zero _⟩⟩

@[target]
theorem mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α] : #α = 1 := by sorry

@[target]
theorem le_one_iff_subsingleton {α : Type u} : #α ≤ 1 ↔ Subsingleton α := by sorry

@[simp]
theorem mk_le_one_iff_set_subsingleton {s : Set α} : #s ≤ 1 ↔ s.Subsingleton :=
  le_one_iff_subsingleton.trans s.subsingleton_coe

alias ⟨_, _root_.Set.Subsingleton.cardinalMk_le_one⟩ := mk_le_one_iff_set_subsingleton

@[deprecated (since := "2024-11-10")]
alias _root_.Set.Subsingleton.cardinal_mk_le_one := Set.Subsingleton.cardinalMk_le_one

instance : Add Cardinal.{u} :=
  ⟨map₂ Sum fun _ _ _ _ => Equiv.sumCongr⟩

theorem add_def (α β : Type u) : #α + #β = #(α ⊕ β) :=
  rfl

instance : NatCast Cardinal.{u} :=
  ⟨fun n => lift #(Fin n)⟩

@[target, simp]
theorem mk_sum (α : Type u) (β : Type v) : #(α ⊕ β) = lift.{v, u} #α + lift.{u, v} #β := by sorry

@[target, simp]
theorem mk_option {α : Type u} : #(Option α) = #α + 1 := by sorry

@[target, simp]
theorem mk_psum (α : Type u) (β : Type v) : #(α ⊕' β) = lift.{v} #α + lift.{u} #β := by sorry

@[target, simp]
theorem mk_fintype (α : Type u) [h : Fintype α] : #α = Fintype.card α := by sorry

instance : Mul Cardinal.{u} :=
  ⟨map₂ Prod fun _ _ _ _ => Equiv.prodCongr⟩

@[target]
theorem mul_def (α β : Type u) : #α * #β = #(α × β) := by sorry

@[target, simp]
theorem mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v, u} #α * lift.{u, v} #β := by sorry

/-- The cardinal exponential. `#α ^ #β` is the cardinal of `β → α`. -/
instance instPowCardinal : Pow Cardinal.{u} Cardinal.{u} :=
  ⟨map₂ (fun α β => β → α) fun _ _ _ _ e₁ e₂ => e₂.arrowCongr e₁⟩

@[target]
theorem power_def (α β : Type u) : #α ^ #β = #(β → α) := by sorry

@[target]
theorem mk_arrow (α : Type u) (β : Type v) : #(α → β) = (lift.{u} #β^lift.{v} #α) := by sorry

@[simp]
theorem lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) = lift.{v} a ^ lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.ulift.arrowCongr Equiv.ulift).symm

@[simp]
theorem power_zero (a : Cardinal) : a ^ (0 : Cardinal) = 1 :=
  inductionOn a fun _ => mk_eq_one _

@[simp]
theorem power_one (a : Cardinal.{u}) : a ^ (1 : Cardinal) = a :=
  inductionOn a fun α => mk_congr (Equiv.funUnique (ULift.{u} (Fin 1)) α)

@[target]
theorem power_add (a b c : Cardinal) : a ^ (b + c) = a ^ b * a ^ c := by sorry

private theorem cast_succ (n : ℕ) : ((n + 1 : ℕ) : Cardinal.{u}) = n + 1 := by
  change #(ULift.{u} _) = #(ULift.{u} _) + 1
  rw [← mk_option]
  simp

instance commSemiring : CommSemiring Cardinal.{u} where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  zero_add a := inductionOn a fun α => mk_congr <| Equiv.emptySum _ α
  add_zero a := inductionOn a fun α => mk_congr <| Equiv.sumEmpty α _
  add_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumAssoc α β γ
  add_comm a b := inductionOn₂ a b fun α β => mk_congr <| Equiv.sumComm α β
  zero_mul a := inductionOn a fun _ => mk_eq_zero _
  mul_zero a := inductionOn a fun _ => mk_eq_zero _
  one_mul a := inductionOn a fun α => mk_congr <| Equiv.uniqueProd α _
  mul_one a := inductionOn a fun α => mk_congr <| Equiv.prodUnique α _
  mul_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.prodAssoc α β γ
  mul_comm a b := inductionOn₂ a b fun α β => mk_congr <| Equiv.prodComm α β
  left_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.prodSumDistrib α β γ
  right_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumProdDistrib α β γ
  nsmul := nsmulRec
  npow n c := c ^ (n : Cardinal)
  npow_zero := power_zero
  npow_succ n c := by dsimp; rw [cast_succ, power_add, power_one]
  natCast n := lift #(Fin n)
  natCast_zero := rfl
  natCast_succ n := cast_succ n

@[target, simp]
theorem one_power {a : Cardinal} : (1 : Cardinal) ^ a = 1 := by sorry

@[target]
theorem mk_bool : #Bool = 2 := by sorry

@[target]
theorem mk_Prop : #Prop = 2 := by sorry

@[target, simp]
theorem zero_power {a : Cardinal} : a ≠ 0 → (0 : Cardinal) ^ a = 0 := by sorry

@[target]
theorem power_ne_zero {a : Cardinal} (b : Cardinal) : a ≠ 0 → a ^ b ≠ 0 := by sorry

theorem mul_power {a b c : Cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
  inductionOn₃ a b c fun _ _ γ => mk_congr <| Equiv.arrowProdEquivProdArrow γ _ _

@[target]
theorem power_mul {a b c : Cardinal} : a ^ (b * c) = (a ^ b) ^ c := by sorry

@[target, simp, norm_cast]
theorem power_natCast (a : Cardinal.{u}) (n : ℕ) : a ^ (↑n : Cardinal.{u}) = a ^ n := by sorry

@[deprecated (since := "2024-10-16")]
alias power_cast_right := power_natCast

@[simp]
theorem lift_one : lift 1 = 1 := mk_eq_one _

@[simp]
theorem lift_eq_one {a : Cardinal.{v}} : lift.{u} a = 1 ↔ a = 1 :=
  lift_injective.eq_iff' lift_one

@[simp]
theorem lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = lift.{v} a + lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift).symm

@[simp]
theorem lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = lift.{v} a * lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.prodCongr Equiv.ulift Equiv.ulift).symm

@[target]
theorem lift_two : lift.{u, v} 2 = 2 := by sorry

@[simp]
theorem mk_set {α : Type u} : #(Set α) = 2 ^ #α := by simp [← one_add_one_eq_two, Set, mk_arrow]

/-- A variant of `Cardinal.mk_set` expressed in terms of a `Set` instead of a `Type`. -/
@[target, simp]
theorem mk_powerset {α : Type u} (s : Set α) : #(↥(𝒫 s)) = 2 ^ #(↥s) := by sorry

theorem lift_two_power (a : Cardinal) : lift.{v} (2 ^ a) = 2 ^ lift.{v} a := by
  simp [← one_add_one_eq_two]

/-! ### Order properties -/

protected theorem zero_le : ∀ a : Cardinal, 0 ≤ a := by
  rintro ⟨α⟩
  exact ⟨Embedding.ofIsEmpty⟩

private theorem add_le_add' : ∀ {a b c d : Cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.sumMap e₂⟩

instance addLeftMono : AddLeftMono Cardinal :=
  ⟨fun _ _ _ => add_le_add' le_rfl⟩

instance addRightMono : AddRightMono Cardinal :=
  ⟨fun _ _ _ h => add_le_add' h le_rfl⟩

instance canonicallyOrderedAdd : CanonicallyOrderedAdd Cardinal.{u} where
  exists_add_of_le {a b} :=
    inductionOn₂ a b fun α β ⟨⟨f, hf⟩⟩ =>
      have : α ⊕ ((range f)ᶜ : Set β) ≃ β := by
        classical
        exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans <|
          Equiv.Set.sumCompl (range f)
      ⟨#(↥(range f)ᶜ), mk_congr this.symm⟩
  le_self_add a _ := (add_zero a).ge.trans <| add_le_add_left (Cardinal.zero_le _) _

instance orderedCommSemiring : OrderedCommSemiring Cardinal.{u} :=
  CanonicallyOrderedAdd.toOrderedCommSemiring

instance : LinearOrderedAddCommMonoid Cardinal.{u} :=
  { Cardinal.orderedCommSemiring, Cardinal.linearOrder with }

instance orderBot : OrderBot Cardinal.{u} := inferInstance

instance noZeroDivisors : NoZeroDivisors Cardinal.{u} where
  eq_zero_or_eq_zero_of_mul_eq_zero := fun {a b} =>
    inductionOn₂ a b fun α β => by
      simpa only [mul_def, mk_eq_zero_iff, isEmpty_prod] using id

instance : LinearOrderedCommMonoidWithZero Cardinal.{u} :=
  { Cardinal.commSemiring,
    Cardinal.linearOrder with
    mul_le_mul_left := @mul_le_mul_left' _ _ _ _
    zero_le_one := zero_le _ }

-- Computable instance to prevent a non-computable one being found via the one above
instance : CommMonoidWithZero Cardinal.{u} :=
  { Cardinal.orderedCommSemiring with }

-- Porting note: new
-- Computable instance to prevent a non-computable one being found via the one above
instance : CommMonoid Cardinal.{u} :=
  { Cardinal.orderedCommSemiring with }

@[target]
theorem zero_power_le (c : Cardinal.{u}) : (0 : Cardinal.{u}) ^ c ≤ 1 := by sorry

@[target]
theorem power_le_power_left : ∀ {a b c : Cardinal}, a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c := by sorry

@[target]
theorem self_le_power (a : Cardinal) {b : Cardinal} (hb : 1 ≤ b) : a ≤ a ^ b := by sorry

/-- **Cantor's theorem** -/
@[target]
theorem cantor (a : Cardinal.{u}) : a < 2 ^ a := by sorry

instance : NoMaxOrder Cardinal.{u} where exists_gt a := ⟨_, cantor a⟩

-- short-circuit type class inference
instance : DistribLattice Cardinal.{u} := inferInstance

@[target]
theorem one_lt_iff_nontrivial {α : Type u} : 1 < #α ↔ Nontrivial α := by sorry

@[target]
theorem power_le_max_power_one {a b c : Cardinal} (h : b ≤ c) : a ^ b ≤ max (a ^ c) 1 := by sorry

@[target]
theorem power_le_power_right {a b c : Cardinal} : a ≤ b → a ^ c ≤ b ^ c := by sorry

@[target]
theorem power_pos {a : Cardinal} (b : Cardinal) (ha : 0 < a) : 0 < a ^ b := by sorry

protected theorem lt_wf : @WellFounded Cardinal.{u} (· < ·) :=
  ⟨fun a =>
    by_contradiction fun h => by
      let ι := { c : Cardinal // ¬Acc (· < ·) c }
      let f : ι → Cardinal := Subtype.val
      haveI hι : Nonempty ι := ⟨⟨_, h⟩⟩
      obtain ⟨⟨c : Cardinal, hc : ¬Acc (· < ·) c⟩, ⟨h_1 : ∀ j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
        Embedding.min_injective fun i => (f i).out
      refine hc (Acc.intro _ fun j h' => by_contradiction fun hj => h'.2 ?_)
      have : #_ ≤ #_ := ⟨h_1 ⟨j, hj⟩⟩
      simpa only [mk_out] using this⟩

instance : WellFoundedRelation Cardinal.{u} :=
  ⟨(· < ·), Cardinal.lt_wf⟩

-- Porting note: this no longer is automatically inferred.
instance : WellFoundedLT Cardinal.{u} :=
  ⟨Cardinal.lt_wf⟩

instance : ConditionallyCompleteLinearOrderBot Cardinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[target, simp]
theorem sInf_empty : sInf (∅ : Set Cardinal.{u}) = 0 := by sorry

lemma sInf_eq_zero_iff {s : Set Cardinal} : sInf s = 0 ↔ s = ∅ ∨ ∃ a ∈ s, a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨sInf s, csInf_mem hne, h⟩
  · rcases h with rfl | ⟨a, ha, rfl⟩
    · exact Cardinal.sInf_empty
    · exact eq_bot_iff.2 (csInf_le' ha)

@[target]
lemma iInf_eq_zero_iff {ι : Sort*} {f : ι → Cardinal} :
    (⨅ i, f i) = 0 ↔ IsEmpty ι ∨ ∃ i, f i = 0 := by sorry

/-- A variant of `ciSup_of_empty` but with `0` on the RHS for convenience -/
protected theorem iSup_of_empty {ι} (f : ι → Cardinal) [IsEmpty ι] : iSup f = 0 :=
  ciSup_of_empty f

@[target, simp]
theorem lift_sInf (s : Set Cardinal) : lift.{u, v} (sInf s) = sInf (lift.{u, v} '' s) := by sorry

@[target, simp]
theorem lift_iInf {ι} (f : ι → Cardinal) : lift.{u, v} (iInf f) = ⨅ i, lift.{u, v} (f i) := by sorry

/-- Note that the successor of `c` is not the same as `c + 1` except in the case of finite `c`. -/
instance : SuccOrder Cardinal := ConditionallyCompleteLinearOrder.toSuccOrder

@[target]
theorem succ_def (c : Cardinal) : succ c = sInf { c' | c < c' } := by sorry

@[target]
theorem succ_pos : ∀ c : Cardinal, 0 < succ c := by sorry

theorem succ_ne_zero (c : Cardinal) : succ c ≠ 0 :=
  (succ_pos _).ne'

@[target]
theorem add_one_le_succ (c : Cardinal.{u}) : c + 1 ≤ succ c := by sorry

@[target, simp]
theorem lift_succ (a) : lift.{v, u} (succ a) = succ (lift.{v, u} a) := by sorry

/-- A cardinal is a limit if it is not zero or a successor cardinal. Note that `ℵ₀` is a limit
  cardinal by this definition, but `0` isn't.
Deprecated. Use `Order.IsSuccLimit` instead. -/
@[deprecated IsSuccLimit (since := "2024-09-17")]
def IsLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ IsSuccPrelimit c

@[target]
theorem ne_zero_of_isSuccLimit {c} (h : IsSuccLimit c) : c ≠ 0 := by sorry

theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Cardinal) :=
  isSuccPrelimit_bot

protected theorem isSuccLimit_iff {c : Cardinal} : IsSuccLimit c ↔ c ≠ 0 ∧ IsSuccPrelimit c :=
  isSuccLimit_iff

section deprecated

set_option linter.deprecated false in
@[deprecated IsSuccLimit.isSuccPrelimit (since := "2024-09-17")]
protected theorem IsLimit.isSuccPrelimit {c} (h : IsLimit c) : IsSuccPrelimit c :=
  h.2

set_option linter.deprecated false in
@[deprecated ne_zero_of_isSuccLimit (since := "2024-09-17")]
protected theorem IsLimit.ne_zero {c} (h : IsLimit c) : c ≠ 0 :=
  h.1

set_option linter.deprecated false in
@[deprecated IsLimit.isSuccPrelimit (since := "2024-09-05")]
alias IsLimit.isSuccLimit := IsLimit.isSuccPrelimit

set_option linter.deprecated false in
@[target, deprecated IsSuccLimit.succ_lt (since := "2024-09-17")]
theorem IsLimit.succ_lt {x c} (h : IsLimit c) : x < c → succ x < c := by sorry

@[deprecated isSuccPrelimit_zero (since := "2024-09-05")]
alias isSuccLimit_zero := isSuccPrelimit_zero

end deprecated

/-! ### Indexed cardinal `sum` -/

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι} (f : ι → Cardinal) : Cardinal :=
  mk (Σ i, (f i).out)

@[target]
theorem le_sum {ι} (f : ι → Cardinal) (i) : f i ≤ sum f := by sorry

@[target]
theorem iSup_le_sum {ι} (f : ι → Cardinal) : iSup f ≤ sum f := by sorry

@[target, simp]
theorem mk_sigma {ι} (f : ι → Type*) : #(Σ i, f i) = sum fun i => #(f i) := by sorry

theorem mk_sigma_congr_lift {ι : Type v} {ι' : Type v'} {f : ι → Type w} {g : ι' → Type w'}
    (e : ι ≃ ι') (h : ∀ i, lift.{w'} #(f i) = lift.{w} #(g (e i))) :
    lift.{max v' w'} #(Σ i, f i) = lift.{max v w} #(Σ i, g i) :=
  Cardinal.lift_mk_eq'.2 ⟨.sigmaCongr e fun i ↦ Classical.choice <| Cardinal.lift_mk_eq'.1 (h i)⟩

@[target]
theorem mk_sigma_congr {ι ι' : Type u} {f : ι → Type v} {g : ι' → Type v} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Σ i, f i) = #(Σ i, g i) := by sorry

/-- Similar to `mk_sigma_congr` with indexing types in different universes. This is not a strict
generalization. -/
theorem mk_sigma_congr' {ι : Type u} {ι' : Type v} {f : ι → Type max w (max u v)}
    {g : ι' → Type max w (max u v)} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Σ i, f i) = #(Σ i, g i) :=
  mk_congr <| Equiv.sigmaCongr e fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)

@[target]
theorem mk_sigma_congrRight {ι : Type u} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Σ i, f i) = #(Σ i, g i) := by sorry

theorem mk_psigma_congrRight {ι : Type u} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Σ' i, f i) = #(Σ' i, g i) :=
  mk_congr <| .psigmaCongrRight fun i => Classical.choice <| Cardinal.eq.mp (h i)

theorem mk_psigma_congrRight_prop {ι : Prop} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Σ' i, f i) = #(Σ' i, g i) :=
  mk_congr <| .psigmaCongrRight fun i => Classical.choice <| Cardinal.eq.mp (h i)

theorem mk_sigma_arrow {ι} (α : Type*) (f : ι → Type*) :
    #(Sigma f → α) = #(Π i, f i → α) := mk_congr <| Equiv.piCurry fun _ _ ↦ α

@[target, simp]
theorem sum_const (ι : Type u) (a : Cardinal.{v}) :
    (sum fun _ : ι => a) = lift.{v} #ι * lift.{u} a := by sorry

theorem sum_const' (ι : Type u) (a : Cardinal.{u}) : (sum fun _ : ι => a) = #ι * a := by simp

@[target, simp]
theorem sum_add_distrib {ι} (f g : ι → Cardinal) : sum (f + g) = sum f + sum g := by sorry

@[target, simp]
theorem sum_add_distrib' {ι} (f g : ι → Cardinal) :
    (Cardinal.sum fun i => f i + g i) = sum f + sum g := by sorry

@[target, simp]
theorem lift_sum {ι : Type u} (f : ι → Cardinal.{v}) :
    Cardinal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i) := by sorry

theorem sum_le_sum {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
  ⟨(Embedding.refl _).sigmaMap fun i =>
      Classical.choice <| by have := H i; rwa [← Quot.out_eq (f i), ← Quot.out_eq (g i)] at this⟩

@[target]
theorem mk_le_mk_mul_of_mk_preimage_le {c : Cardinal} (f : α → β) (hf : ∀ b : β, #(f ⁻¹' {b}) ≤ c) :
    #α ≤ #β * c := by sorry

@[target]
theorem lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le {α : Type u} {β : Type v} {c : Cardinal}
    (f : α → β) (hf : ∀ b : β, lift.{v} #(f ⁻¹' {b}) ≤ c) : lift.{v} #α ≤ lift.{u} #β * c := by sorry

@[target]
theorem sum_nat_eq_add_sum_succ (f : ℕ → Cardinal.{u}) :
    Cardinal.sum f = f 0 + Cardinal.sum fun i => f (i + 1) := by sorry

end Cardinal

/-! ### Well-ordering theorem -/

open Cardinal in
@[target]
theorem nonempty_embedding_to_cardinal : Nonempty (α ↪ Cardinal.{u}) := by sorry

/-- An embedding of any type to the set of cardinals in its universe. -/
def embeddingToCardinal : α ↪ Cardinal.{u} :=
  Classical.choice nonempty_embedding_to_cardinal

/-- Any type can be endowed with a well order, obtained by pulling back the well order over
cardinals by some embedding. -/
def WellOrderingRel : α → α → Prop :=
  embeddingToCardinal ⁻¹'o (· < ·)

instance WellOrderingRel.isWellOrder : IsWellOrder α WellOrderingRel :=
  (RelEmbedding.preimage _ _).isWellOrder

instance IsWellOrder.subtype_nonempty : Nonempty { r // IsWellOrder α r } :=
  ⟨⟨WellOrderingRel, inferInstance⟩⟩

variable (α) in
/-- The **well-ordering theorem** (or **Zermelo's theorem**): every type has a well-order -/
@[target]
theorem exists_wellOrder : ∃ (_ : LinearOrder α), WellFoundedLT α := by sorry

/-! ### Small sets of cardinals -/

namespace Cardinal

instance small_Iic (a : Cardinal.{u}) : Small.{u} (Iic a) := by
  rw [← mk_out a]
  apply @small_of_surjective (Set a.out) (Iic #a.out) _ fun x => ⟨#x, mk_set_le x⟩
  rintro ⟨x, hx⟩
  simpa using le_mk_iff_exists_set.1 hx

instance small_Iio (a : Cardinal.{u}) : Small.{u} (Iio a) := small_subset Iio_subset_Iic_self
instance small_Icc (a b : Cardinal.{u}) : Small.{u} (Icc a b) := small_subset Icc_subset_Iic_self
instance small_Ico (a b : Cardinal.{u}) : Small.{u} (Ico a b) := small_subset Ico_subset_Iio_self
instance small_Ioc (a b : Cardinal.{u}) : Small.{u} (Ioc a b) := small_subset Ioc_subset_Iic_self
instance small_Ioo (a b : Cardinal.{u}) : Small.{u} (Ioo a b) := small_subset Ioo_subset_Iio_self

/-- A set of cardinals is bounded above iff it's small, i.e. it corresponds to a usual ZFC set. -/
@[target]
theorem bddAbove_iff_small {s : Set Cardinal.{u}} : BddAbove s ↔ Small.{u} s := by sorry

@[target]
theorem bddAbove_of_small (s : Set Cardinal.{u}) [h : Small.{u} s] : BddAbove s := by sorry

@[target]
theorem bddAbove_range {ι : Type*} [Small.{u} ι] (f : ι → Cardinal.{u}) : BddAbove (Set.range f) := by sorry

@[target]
theorem bddAbove_image (f : Cardinal.{u} → Cardinal.{max u v}) {s : Set Cardinal.{u}}
    (hs : BddAbove s) : BddAbove (f '' s) := by sorry

@[target]
theorem bddAbove_range_comp {ι : Type u} {f : ι → Cardinal.{v}} (hf : BddAbove (range f))
    (g : Cardinal.{v} → Cardinal.{max v w}) : BddAbove (range (g ∘ f)) := by sorry

/-- The type of cardinals in universe `u` is not `Small.{u}`. This is a version of the Burali-Forti
paradox. -/
@[target]
theorem _root_.not_small_cardinal : ¬ Small.{u} Cardinal.{max u v} := by sorry

instance uncountable : Uncountable Cardinal.{u} :=
  Uncountable.of_not_small not_small_cardinal.{u}

/-! ### Bounds on suprema -/

theorem sum_le_iSup_lift {ι : Type u}
    (f : ι → Cardinal.{max u v}) : sum f ≤ Cardinal.lift #ι * iSup f := by
  rw [← (iSup f).lift_id, ← lift_umax, lift_umax.{max u v, u}, ← sum_const]
  exact sum_le_sum _ _ (le_ciSup <| bddAbove_of_small _)

@[target]
theorem sum_le_iSup {ι : Type u} (f : ι → Cardinal.{u}) : sum f ≤ #ι * iSup f := by sorry

/-- The lift of a supremum is the supremum of the lifts. -/
@[target]
theorem lift_sSup {s : Set Cardinal} (hs : BddAbove s) :
    lift.{u} (sSup s) = sSup (lift.{u} '' s) := by sorry

/-- The lift of a supremum is the supremum of the lifts. -/
theorem lift_iSup {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f)) :
    lift.{u} (iSup f) = ⨆ i, lift.{u} (f i) := by
  rw [iSup, iSup, lift_sSup hf, ← range_comp]
  simp [Function.comp_def]

/-- To prove that the lift of a supremum is bounded by some cardinal `t`,
it suffices to show that the lift of each cardinal is bounded by `t`. -/
@[target]
theorem lift_iSup_le {ι : Type v} {f : ι → Cardinal.{w}} {t : Cardinal} (hf : BddAbove (range f))
    (w : ∀ i, lift.{u} (f i) ≤ t) : lift.{u} (iSup f) ≤ t := by sorry

@[target, simp]
theorem lift_iSup_le_iff {ι : Type v} {f : ι → Cardinal.{w}} (hf : BddAbove (range f))
    {t : Cardinal} : lift.{u} (iSup f) ≤ t ↔ ∀ i, lift.{u} (f i) ≤ t := by sorry

/-- To prove an inequality between the lifts to a common universe of two different supremums,
it suffices to show that the lift of each cardinal from the smaller supremum
if bounded by the lift of some cardinal from the larger supremum.
-/
@[target]
theorem lift_iSup_le_lift_iSup {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{w}}
    {f' : ι' → Cardinal.{w'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) {g : ι → ι'}
    (h : ∀ i, lift.{w'} (f i) ≤ lift.{w} (f' (g i))) : lift.{w'} (iSup f) ≤ lift.{w} (iSup f') := by sorry

/-- A variant of `lift_iSup_le_lift_iSup` with universes specialized via `w = v` and `w' = v'`.
This is sometimes necessary to avoid universe unification issues. -/
@[target]
theorem lift_iSup_le_lift_iSup' {ι : Type v} {ι' : Type v'} {f : ι → Cardinal.{v}}
    {f' : ι' → Cardinal.{v'}} (hf : BddAbove (range f)) (hf' : BddAbove (range f')) (g : ι → ι')
    (h : ∀ i, lift.{v'} (f i) ≤ lift.{v} (f' (g i))) : lift.{v'} (iSup f) ≤ lift.{v} (iSup f') := by sorry

@[target]
lemma exists_eq_of_iSup_eq_of_not_isSuccPrelimit
    {ι : Type u} (f : ι → Cardinal.{v}) (ω : Cardinal.{v})
    (hω : ¬ IsSuccPrelimit ω)
    (h : ⨆ i : ι, f i = ω) : ∃ i, f i = ω := by sorry

@[target]
lemma exists_eq_of_iSup_eq_of_not_isSuccLimit
    {ι : Type u} [hι : Nonempty ι] (f : ι → Cardinal.{v}) (hf : BddAbove (range f))
    {c : Cardinal.{v}} (hc : ¬ IsSuccLimit c)
    (h : ⨆ i, f i = c) : ∃ i, f i = c := by sorry

set_option linter.deprecated false in
@[target, deprecated exists_eq_of_iSup_eq_of_not_isSuccLimit (since := "2024-09-17")]
lemma exists_eq_of_iSup_eq_of_not_isLimit
    {ι : Type u} [hι : Nonempty ι] (f : ι → Cardinal.{v}) (hf : BddAbove (range f))
    (ω : Cardinal.{v}) (hω : ¬ ω.IsLimit)
    (h : ⨆ i : ι, f i = ω) : ∃ i, f i = ω := by sorry

/-! ### Indexed cardinal `prod` -/

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → Cardinal) : Cardinal :=
  #(Π i, (f i).out)

@[target, simp]
theorem mk_pi {ι : Type u} (α : ι → Type v) : #(Π i, α i) = prod fun i => #(α i) := by sorry

@[target]
theorem mk_pi_congr_lift {ι : Type v} {ι' : Type v'} {f : ι → Type w} {g : ι' → Type w'}
    (e : ι ≃ ι') (h : ∀ i, lift.{w'} #(f i) = lift.{w} #(g (e i))) :
    lift.{max v' w'} #(Π i, f i) = lift.{max v w} #(Π i, g i) := by sorry

@[target]
theorem mk_pi_congr {ι ι' : Type u} {f : ι → Type v} {g : ι' → Type v} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Π i, f i) = #(Π i, g i) := by sorry

@[target]
theorem mk_pi_congr_prop {ι ι' : Prop} {f : ι → Type v} {g : ι' → Type v} (e : ι ↔ ι')
    (h : ∀ i, #(f i) = #(g (e.mp i))) : #(Π i, f i) = #(Π i, g i) := by sorry

/-- Similar to `mk_pi_congr` with indexing types in different universes. This is not a strict
generalization. -/
theorem mk_pi_congr' {ι : Type u} {ι' : Type v} {f : ι → Type max w (max u v)}
    {g : ι' → Type max w (max u v)} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Π i, f i) = #(Π i, g i) :=
  mk_congr <| Equiv.piCongr e fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)

@[target]
theorem mk_pi_congrRight {ι : Type u} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Π i, f i) = #(Π i, g i) := by sorry

@[target]
theorem mk_pi_congrRight_prop {ι : Prop} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Π i, f i) = #(Π i, g i) := by sorry

@[target, simp]
theorem prod_const (ι : Type u) (a : Cardinal.{v}) :
    (prod fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι := by sorry

theorem prod_const' (ι : Type u) (a : Cardinal.{u}) : (prod fun _ : ι => a) = a ^ #ι :=
  inductionOn a fun _ => (mk_pi _).symm

theorem prod_le_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
  ⟨Embedding.piCongrRight fun i =>
      Classical.choice <| by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

@[target, simp]
theorem prod_eq_zero {ι} (f : ι → Cardinal.{u}) : prod f = 0 ↔ ∃ i, f i = 0 := by sorry

@[target]
theorem prod_ne_zero {ι} (f : ι → Cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 := by sorry

theorem power_sum {ι} (a : Cardinal) (f : ι → Cardinal) :
    a ^ sum f = prod fun i ↦ a ^ f i := by
  induction a using Cardinal.inductionOn with | _ α =>
  induction f using induction_on_pi with | _ f =>
  simp_rw [prod, sum, power_def]
  apply mk_congr
  refine (Equiv.piCurry fun _ _ => α).trans ?_
  refine Equiv.piCongrRight fun b => ?_
  refine (Equiv.arrowCongr outMkEquiv (Equiv.refl α)).trans ?_
  exact outMkEquiv.symm

@[target, simp]
theorem lift_prod {ι : Type u} (c : ι → Cardinal.{v}) :
    lift.{w} (prod c) = prod fun i => lift.{w} (c i) := by sorry

theorem prod_eq_of_fintype {α : Type u} [h : Fintype α] (f : α → Cardinal.{v}) :
    prod f = Cardinal.lift.{u} (∏ i, f i) := by
  revert f
  refine Fintype.induction_empty_option ?_ ?_ ?_ α (h_fintype := h)
  · intro α β hβ e h f
    letI := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp f, ← h]
    exact mk_congr (e.piCongrLeft _).symm
  · intro f
    rw [Fintype.univ_pempty, Finset.prod_empty, lift_one, Cardinal.prod, mk_eq_one]
  · intro α hα h f
    rw [Cardinal.prod, mk_congr Equiv.piOptionEquivProd, mk_prod, lift_umax.{v, u}, mk_out, ←
        Cardinal.prod, lift_prod, Fintype.prod_option, lift_mul, ← h fun a => f (some a)]
    simp only [lift_id]

/-- **König's theorem** -/
@[target]
theorem sum_lt_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i < g i) : sum f < prod g := by sorry

/-! ### The first infinite cardinal `aleph0` -/

/-- `ℵ₀` is the smallest infinite cardinal. -/
def aleph0 : Cardinal.{u} :=
  lift #ℕ

@[inherit_doc]
scoped notation "ℵ₀" => Cardinal.aleph0

@[target]
theorem mk_nat : #ℕ = ℵ₀ := by sorry

@[target]
theorem aleph0_ne_zero : ℵ₀ ≠ 0 := by sorry

@[target]
theorem aleph0_pos : 0 < ℵ₀ := by sorry

@[target, simp]
theorem lift_aleph0 : lift ℵ₀ = ℵ₀ := by sorry

@[target, simp]
theorem aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ ≤ lift.{v} c ↔ ℵ₀ ≤ c := by sorry

@[target, simp]
theorem lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c ≤ ℵ₀ ↔ c ≤ ℵ₀ := by sorry

@[target, simp]
theorem aleph0_lt_lift {c : Cardinal.{u}} : ℵ₀ < lift.{v} c ↔ ℵ₀ < c := by sorry

@[target, simp]
theorem lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c < ℵ₀ ↔ c < ℵ₀ := by sorry

@[target, simp]
theorem aleph0_eq_lift {c : Cardinal.{u}} : ℵ₀ = lift.{v} c ↔ ℵ₀ = c := by sorry

@[target, simp]
theorem lift_eq_aleph0 {c : Cardinal.{u}} : lift.{v} c = ℵ₀ ↔ c = ℵ₀ := by sorry

/-! ### Properties about the cast from `ℕ` -/

@[target]
theorem mk_fin (n : ℕ) : #(Fin n) = n := by sorry

@[target, simp]
theorem lift_natCast (n : ℕ) : lift.{u} (n : Cardinal.{v}) = n := by sorry

@[simp]
theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift.{u} (ofNat(n) : Cardinal.{v}) = OfNat.ofNat n :=
  lift_natCast n

@[simp]
theorem lift_eq_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a = n ↔ a = n :=
  lift_injective.eq_iff' (lift_natCast n)

@[target, simp]
theorem lift_eq_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a = ofNat(n) ↔ a = OfNat.ofNat n := by sorry

@[target, simp]
theorem nat_eq_lift_iff {n : ℕ} {a : Cardinal.{u}} :
    (n : Cardinal) = lift.{v} a ↔ (n : Cardinal) = a := by sorry

@[target, simp]
theorem zero_eq_lift_iff {a : Cardinal.{u}} :
    (0 : Cardinal) = lift.{v} a ↔ 0 = a := by sorry

@[target, simp]
theorem one_eq_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) = lift.{v} a ↔ 1 = a := by sorry

@[target, simp]
theorem ofNat_eq_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) = lift.{v} a ↔ (OfNat.ofNat n : Cardinal) = a := by sorry

@[target, simp]
theorem lift_le_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a ≤ n ↔ a ≤ n := by sorry

@[simp]
theorem lift_le_one_iff {a : Cardinal.{u}} :
    lift.{v} a ≤ 1 ↔ a ≤ 1 := by
  simpa using lift_le_nat_iff (n := 1)

@[target, simp]
theorem lift_le_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a ≤ ofNat(n) ↔ a ≤ OfNat.ofNat n := by sorry

@[target, simp]
theorem nat_le_lift_iff {n : ℕ} {a : Cardinal.{u}} : n ≤ lift.{v} a ↔ n ≤ a := by sorry

@[simp]
theorem one_le_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) ≤ lift.{v} a ↔ 1 ≤ a := by
  simpa using nat_le_lift_iff (n := 1)

@[target, simp]
theorem ofNat_le_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) ≤ lift.{v} a ↔ (OfNat.ofNat n : Cardinal) ≤ a := by sorry

@[target, simp]
theorem lift_lt_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a < n ↔ a < n := by sorry

@[simp]
theorem lift_lt_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a < ofNat(n) ↔ a < OfNat.ofNat n :=
  lift_lt_nat_iff

@[target, simp]
theorem nat_lt_lift_iff {n : ℕ} {a : Cardinal.{u}} : n < lift.{v} a ↔ n < a := by sorry

@[target, simp]
theorem zero_lt_lift_iff {a : Cardinal.{u}} :
    (0 : Cardinal) < lift.{v} a ↔ 0 < a := by sorry

@[target, simp]
theorem one_lt_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) < lift.{v} a ↔ 1 < a := by sorry

@[target, simp]
theorem ofNat_lt_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) < lift.{v} a ↔ (OfNat.ofNat n : Cardinal) < a := by sorry

theorem lift_mk_fin (n : ℕ) : lift #(Fin n) = n := rfl

@[target]
theorem mk_coe_finset {α : Type u} {s : Finset α} : #s = ↑(Finset.card s) := by sorry

@[target]
theorem mk_finset_of_fintype [Fintype α] : #(Finset α) = 2 ^ Fintype.card α := by sorry

@[target]
theorem card_le_of_finset {α} (s : Finset α) : (s.card : Cardinal) ≤ #α := by sorry

instance : CharZero Cardinal := by
  refine ⟨fun a b h ↦ ?_⟩
  rwa [← lift_mk_fin, ← lift_mk_fin, lift_inj, Cardinal.eq, ← Fintype.card_eq,
    Fintype.card_fin, Fintype.card_fin] at h

@[deprecated Nat.cast_le (since := "2024-10-16")]
theorem natCast_le {m n : ℕ} : (m : Cardinal) ≤ n ↔ m ≤ n := Nat.cast_le

@[target, deprecated Nat.cast_lt (since := "2024-10-16")]
theorem natCast_lt {m n : ℕ} : (m : Cardinal) < n ↔ m < n := by sorry

@[deprecated Nat.cast_inj (since := "2024-10-16")]
theorem natCast_inj {m n : ℕ} : (m : Cardinal) = n ↔ m = n := Nat.cast_inj

@[target, deprecated Nat.cast_injective (since := "2024-10-16")]
theorem natCast_injective : Injective ((↑) : ℕ → Cardinal) := by sorry

@[target, deprecated Nat.cast_pow (since := "2024-10-16")]
theorem natCast_pow {m n : ℕ} : (↑(m ^ n) : Cardinal) = (↑m : Cardinal) ^ (↑n : Cardinal) := by sorry

@[target, norm_cast]
theorem nat_succ (n : ℕ) : (n.succ : Cardinal) = succ ↑n := by sorry

lemma succ_natCast (n : ℕ) : Order.succ (n : Cardinal) = n + 1 := by
  rw [← Cardinal.nat_succ]
  norm_cast

lemma natCast_add_one_le_iff {n : ℕ} {c : Cardinal} : n + 1 ≤ c ↔ n < c := by
  rw [← Order.succ_le_iff, Cardinal.succ_natCast]

@[target]
lemma two_le_iff_one_lt {c : Cardinal} : 2 ≤ c ↔ 1 < c := by sorry

@[simp]
theorem succ_zero : succ (0 : Cardinal) = 1 := by norm_cast

-- This works generally to prove inequalities between numeric cardinals.
@[target]
theorem one_lt_two : (1 : Cardinal) < 2 := by sorry

@[target]
theorem exists_finset_le_card (α : Type*) (n : ℕ) (h : n ≤ #α) :
    ∃ s : Finset α, n ≤ s.card := by sorry

@[target]
theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : Finset α, s.card ≤ n) : #α ≤ n := by sorry

@[target]
theorem cantor' (a) {b : Cardinal} (hb : 1 < b) : a < b ^ a := by sorry

theorem one_le_iff_pos {c : Cardinal} : 1 ≤ c ↔ 0 < c := by
  rw [← succ_zero, succ_le_iff]

@[target]
theorem one_le_iff_ne_zero {c : Cardinal} : 1 ≤ c ↔ c ≠ 0 := by sorry

@[simp]
theorem lt_one_iff_zero {c : Cardinal} : c < 1 ↔ c = 0 := by
  simpa using lt_succ_bot_iff (a := c)

/-! ### Properties about `aleph0` -/

@[target]
theorem nat_lt_aleph0 (n : ℕ) : (n : Cardinal.{u}) < ℵ₀ := by sorry

@[target, simp]
theorem one_lt_aleph0 : 1 < ℵ₀ := by sorry

@[target, simp]
theorem one_le_aleph0 : 1 ≤ ℵ₀ := by sorry

@[target]
theorem lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ ∃ n : ℕ, c = n := by sorry

@[target]
lemma succ_eq_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : Order.succ c = c + 1 := by sorry

@[target]
theorem aleph0_le {c : Cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c := by sorry

@[target]
theorem isSuccPrelimit_aleph0 : IsSuccPrelimit ℵ₀ := by sorry

@[target]
theorem isSuccLimit_aleph0 : IsSuccLimit ℵ₀ := by sorry

@[target]
lemma not_isSuccLimit_natCast : (n : ℕ) → ¬ IsSuccLimit (n : Cardinal.{u}) := by sorry

theorem not_isSuccLimit_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ¬ IsSuccLimit c := by
  obtain ⟨n, rfl⟩ := lt_aleph0.1 h
  exact not_isSuccLimit_natCast n

theorem aleph0_le_of_isSuccLimit {c : Cardinal} (h : IsSuccLimit c) : ℵ₀ ≤ c := by
  contrapose! h
  exact not_isSuccLimit_of_lt_aleph0 h

section deprecated

set_option linter.deprecated false in
@[target, deprecated isSuccLimit_aleph0 (since := "2024-09-17")]
theorem isLimit_aleph0 : IsLimit ℵ₀ := by sorry

set_option linter.deprecated false in
@[target, deprecated not_isSuccLimit_natCast (since := "2024-09-17")]
lemma not_isLimit_natCast : (n : ℕ) → ¬ IsLimit (n : Cardinal.{u}) := by sorry

set_option linter.deprecated false in
@[target, deprecated aleph0_le_of_isSuccLimit (since := "2024-09-17")]
theorem IsLimit.aleph0_le {c : Cardinal} (h : IsLimit c) : ℵ₀ ≤ c := by sorry

end deprecated

@[target]
lemma exists_eq_natCast_of_iSup_eq {ι : Type u} [Nonempty ι] (f : ι → Cardinal.{v})
    (hf : BddAbove (range f)) (n : ℕ) (h : ⨆ i, f i = n) : ∃ i, f i = n := by sorry

@[simp]
theorem range_natCast : range ((↑) : ℕ → Cardinal) = Iio ℵ₀ :=
  ext fun x => by simp only [mem_Iio, mem_range, eq_comm, lt_aleph0]

@[target]
theorem mk_eq_nat_iff {α : Type u} {n : ℕ} : #α = n ↔ Nonempty (α ≃ Fin n) := by sorry

theorem lt_aleph0_iff_finite {α : Type u} : #α < ℵ₀ ↔ Finite α := by
  simp only [lt_aleph0, mk_eq_nat_iff, finite_iff_exists_equiv_fin]

@[target]
theorem lt_aleph0_iff_fintype {α : Type u} : #α < ℵ₀ ↔ Nonempty (Fintype α) := by sorry

theorem lt_aleph0_of_finite (α : Type u) [Finite α] : #α < ℵ₀ :=
  lt_aleph0_iff_finite.2 ‹_›

theorem lt_aleph0_iff_set_finite {S : Set α} : #S < ℵ₀ ↔ S.Finite :=
  lt_aleph0_iff_finite.trans finite_coe_iff

alias ⟨_, _root_.Set.Finite.lt_aleph0⟩ := lt_aleph0_iff_set_finite

@[target, simp]
theorem lt_aleph0_iff_subtype_finite {p : α → Prop} : #{ x // p x } < ℵ₀ ↔ { x | p x }.Finite := by sorry

theorem mk_le_aleph0_iff : #α ≤ ℵ₀ ↔ Countable α := by
  rw [countable_iff_nonempty_embedding, aleph0, ← lift_uzero #α, lift_mk_le']

@[target, simp]
theorem mk_le_aleph0 [Countable α] : #α ≤ ℵ₀ := by sorry

@[target]
theorem le_aleph0_iff_set_countable {s : Set α} : #s ≤ ℵ₀ ↔ s.Countable := by sorry

alias ⟨_, _root_.Set.Countable.le_aleph0⟩ := le_aleph0_iff_set_countable

@[simp]
theorem le_aleph0_iff_subtype_countable {p : α → Prop} :
    #{ x // p x } ≤ ℵ₀ ↔ { x | p x }.Countable :=
  le_aleph0_iff_set_countable

@[target]
theorem aleph0_lt_mk_iff : ℵ₀ < #α ↔ Uncountable α := by sorry

@[target, simp]
theorem aleph0_lt_mk [Uncountable α] : ℵ₀ < #α := by sorry

instance canLiftCardinalNat : CanLift Cardinal ℕ (↑) fun x => x < ℵ₀ :=
  ⟨fun _ hx =>
    let ⟨n, hn⟩ := lt_aleph0.mp hx
    ⟨n, hn.symm⟩⟩

@[target]
theorem add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a + b < ℵ₀ := by sorry

@[target]
theorem add_lt_aleph0_iff {a b : Cardinal} : a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ := by sorry

theorem aleph0_le_add_iff {a b : Cardinal} : ℵ₀ ≤ a + b ↔ ℵ₀ ≤ a ∨ ℵ₀ ≤ b := by
  simp only [← not_lt, add_lt_aleph0_iff, not_and_or]

/-- See also `Cardinal.nsmul_lt_aleph0_iff_of_ne_zero` if you already have `n ≠ 0`. -/
@[target]
theorem nsmul_lt_aleph0_iff {n : ℕ} {a : Cardinal} : n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀ := by sorry

/-- See also `Cardinal.nsmul_lt_aleph0_iff` for a hypothesis-free version. -/
@[target]
theorem nsmul_lt_aleph0_iff_of_ne_zero {n : ℕ} {a : Cardinal} (h : n ≠ 0) : n • a < ℵ₀ ↔ a < ℵ₀ := by sorry

@[target]
theorem mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a * b < ℵ₀ := by sorry

theorem mul_lt_aleph0_iff {a b : Cardinal} : a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀ := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_cases hb : b = 0
    · exact Or.inl hb
    right
    rw [← Ne, ← one_le_iff_ne_zero] at ha hb
    constructor
    · rw [← mul_one a]
      exact (mul_le_mul' le_rfl hb).trans_lt h
    · rw [← one_mul b]
      exact (mul_le_mul' ha le_rfl).trans_lt h
  rintro (rfl | rfl | ⟨ha, hb⟩) <;> simp only [*, mul_lt_aleph0, aleph0_pos, zero_mul, mul_zero]

/-- See also `Cardinal.aleph0_le_mul_iff`. -/
@[target]
theorem aleph0_le_mul_iff {a b : Cardinal} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (ℵ₀ ≤ a ∨ ℵ₀ ≤ b) := by sorry

/-- See also `Cardinal.aleph0_le_mul_iff'`. -/
theorem aleph0_le_mul_iff' {a b : Cardinal.{u}} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ ℵ₀ ≤ b ∨ ℵ₀ ≤ a ∧ b ≠ 0 := by
  have : ∀ {a : Cardinal.{u}}, ℵ₀ ≤ a → a ≠ 0 := fun a => ne_bot_of_le_ne_bot aleph0_ne_zero a
  simp only [aleph0_le_mul_iff, and_or_left, and_iff_right_of_imp this, @and_left_comm (a ≠ 0)]
  simp only [and_comm, or_comm]

@[target]
theorem mul_lt_aleph0_iff_of_ne_zero {a b : Cardinal} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ := by sorry

@[target]
theorem power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a ^ b < ℵ₀ := by sorry

theorem eq_one_iff_unique {α : Type*} : #α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  calc
    #α = 1 ↔ #α ≤ 1 ∧ 1 ≤ #α := le_antisymm_iff
    _ ↔ Subsingleton α ∧ Nonempty α :=
      le_one_iff_subsingleton.and (one_le_iff_ne_zero.trans mk_ne_zero_iff)

@[target]
theorem infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ ≤ #α := by sorry

@[target]
lemma aleph0_le_mk_iff : ℵ₀ ≤ #α ↔ Infinite α := by sorry

@[target]
lemma mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α := by sorry

@[simp] lemma mk_lt_aleph0 [Finite α] : #α < ℵ₀ := mk_lt_aleph0_iff.2 ‹_›

@[target, simp]
theorem aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ ≤ #α := by sorry

@[simp]
theorem mk_eq_aleph0 (α : Type*) [Countable α] [Infinite α] : #α = ℵ₀ :=
  mk_le_aleph0.antisymm <| aleph0_le_mk _

@[target]
theorem denumerable_iff {α : Type u} : Nonempty (Denumerable α) ↔ #α = ℵ₀ := by sorry

@[target]
theorem mk_denumerable (α : Type u) [Denumerable α] : #α = ℵ₀ := by sorry

@[target]
theorem _root_.Set.countable_infinite_iff_nonempty_denumerable {α : Type*} {s : Set α} :
    s.Countable ∧ s.Infinite ↔ Nonempty (Denumerable s) := by sorry

@[target, simp]
theorem aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀ := by sorry

@[target]
theorem aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀ := by sorry

@[target, simp]
theorem nat_mul_aleph0 {n : ℕ} (hn : n ≠ 0) : ↑n * ℵ₀ = ℵ₀ := by sorry

@[target, simp]
theorem aleph0_mul_nat {n : ℕ} (hn : n ≠ 0) : ℵ₀ * n = ℵ₀ := by sorry

@[target, simp]
theorem ofNat_mul_aleph0 {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) * ℵ₀ = ℵ₀ := by sorry

@[target, simp]
theorem aleph0_mul_ofNat {n : ℕ} [Nat.AtLeastTwo n] : ℵ₀ * ofNat(n) = ℵ₀ := by sorry

@[target, simp]
theorem add_le_aleph0 {c₁ c₂ : Cardinal} : c₁ + c₂ ≤ ℵ₀ ↔ c₁ ≤ ℵ₀ ∧ c₂ ≤ ℵ₀ := by sorry

@[target, simp]
theorem aleph0_add_nat (n : ℕ) : ℵ₀ + n = ℵ₀ := by sorry

@[simp]
theorem nat_add_aleph0 (n : ℕ) : ↑n + ℵ₀ = ℵ₀ := by rw [add_comm, aleph0_add_nat]

@[target, simp]
theorem ofNat_add_aleph0 {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) + ℵ₀ = ℵ₀ := by sorry

@[target, simp]
theorem aleph0_add_ofNat {n : ℕ} [Nat.AtLeastTwo n] : ℵ₀ + ofNat(n) = ℵ₀ := by sorry

@[target]
theorem exists_nat_eq_of_le_nat {c : Cardinal} {n : ℕ} (h : c ≤ n) : ∃ m, m ≤ n ∧ c = m := by sorry

@[target]
theorem mk_int : #ℤ = ℵ₀ := by sorry

@[target]
theorem mk_pNat : #ℕ+ = ℵ₀ := by sorry

/-! ### Cardinalities of basic sets and types -/

@[target]
theorem mk_empty : #Empty = 0 := by sorry

@[target]
theorem mk_pempty : #PEmpty = 0 := by sorry

@[target]
theorem mk_punit : #PUnit = 1 := by sorry

@[target]
theorem mk_unit : #Unit = 1 := by sorry

@[simp] theorem mk_additive : #(Additive α) = #α := rfl

@[simp] theorem mk_multiplicative : #(Multiplicative α) = #α := rfl

@[to_additive (attr := simp)] theorem mk_mulOpposite : #(MulOpposite α) = #α :=
  mk_congr MulOpposite.opEquiv.symm

@[target]
theorem mk_singleton {α : Type u} (x : α) : #({x} : Set α) = 1 := by sorry

@[target]
theorem mk_plift_true : #(PLift True) = 1 := by sorry

theorem mk_plift_false : #(PLift False) = 0 :=
  mk_eq_zero _

@[target, simp]
theorem mk_vector (α : Type u) (n : ℕ) : #(List.Vector α n) = #α ^ n := by sorry

@[target]
theorem mk_list_eq_sum_pow (α : Type u) : #(List α) = sum fun n : ℕ => #α ^ n := by sorry

theorem mk_quot_le {α : Type u} {r : α → α → Prop} : #(Quot r) ≤ #α :=
  mk_le_of_surjective Quot.exists_rep

theorem mk_quotient_le {α : Type u} {s : Setoid α} : #(Quotient s) ≤ #α :=
  mk_quot_le

@[target]
theorem mk_subtype_le_of_subset {α : Type u} {p q : α → Prop} (h : ∀ ⦃x⦄, p x → q x) :
    #(Subtype p) ≤ #(Subtype q) := by sorry

@[target]
theorem mk_emptyCollection (α : Type u) : #(∅ : Set α) = 0 := by sorry

@[target]
theorem mk_emptyCollection_iff {α : Type u} {s : Set α} : #s = 0 ↔ s = ∅ := by sorry

@[simp]
theorem mk_univ {α : Type u} : #(@univ α) = #α :=
  mk_congr (Equiv.Set.univ α)

@[simp] lemma mk_setProd {α β : Type u} (s : Set α) (t : Set β) : #(s ×ˢ t) = #s * #t := by
  rw [mul_def, mk_congr (Equiv.Set.prod ..)]

@[target]
theorem mk_image_le {α β : Type u} {f : α → β} {s : Set α} : #(f '' s) ≤ #s := by sorry

@[target]
lemma mk_image2_le {α β γ : Type u} {f : α → β → γ} {s : Set α} {t : Set β} :
    #(image2 f s t) ≤ #s * #t := by sorry

@[target]
theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : Set α} :
    lift.{u} #(f '' s) ≤ lift.{v} #s := by sorry

@[target]
theorem mk_range_le {α β : Type u} {f : α → β} : #(range f) ≤ #α := by sorry

theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α → β} :
    lift.{u} #(range f) ≤ lift.{v} #α :=
  lift_mk_le.{0}.mpr ⟨Embedding.ofSurjective _ surjective_onto_range⟩

@[target]
theorem mk_range_eq (f : α → β) (h : Injective f) : #(range f) = #α := by sorry

@[target]
theorem mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{max u w} #(range f) = lift.{max v w} #α := by sorry

@[target]
theorem mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    lift.{u} #(range f) = lift.{v} #α := by sorry

@[target]
lemma lift_mk_le_lift_mk_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : Injective f) :
    Cardinal.lift.{v} (#α) ≤ Cardinal.lift.{u} (#β) := by sorry

@[target]
lemma lift_mk_le_lift_mk_of_surjective {α : Type u} {β : Type v} {f : α → β} (hf : Surjective f) :
    Cardinal.lift.{u} (#β) ≤ Cardinal.lift.{v} (#α) := by sorry

theorem mk_image_eq_of_injOn {α β : Type u} (f : α → β) (s : Set α) (h : InjOn f s) :
    #(f '' s) = #s :=
  mk_congr (Equiv.Set.imageOfInjOn f s h).symm

@[target]
theorem mk_image_eq_of_injOn_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α)
    (h : InjOn f s) : lift.{u} #(f '' s) = lift.{v} #s := by sorry

@[target]
theorem mk_image_eq {α β : Type u} {f : α → β} {s : Set α} (hf : Injective f) : #(f '' s) = #s := by sorry

theorem mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : Set α) (h : Injective f) :
    lift.{u} #(f '' s) = lift.{v} #s :=
  mk_image_eq_of_injOn_lift _ _ h.injOn

@[simp]
theorem mk_image_embedding_lift {β : Type v} (f : α ↪ β) (s : Set α) :
    lift.{u} #(f '' s) = lift.{v} #s :=
  mk_image_eq_lift _ _ f.injective

@[target, simp]
theorem mk_image_embedding (f : α ↪ β) (s : Set α) : #(f '' s) = #s := by sorry

theorem mk_iUnion_le_sum_mk {α ι : Type u} {f : ι → Set α} : #(⋃ i, f i) ≤ sum fun i => #(f i) :=
  calc
    #(⋃ i, f i) ≤ #(Σi, f i) := mk_le_of_surjective (Set.sigmaToiUnion_surjective f)
    _ = sum fun i => #(f i) := mk_sigma _

@[target]
theorem mk_iUnion_le_sum_mk_lift {α : Type u} {ι : Type v} {f : ι → Set α} :
    lift.{v} #(⋃ i, f i) ≤ sum fun i => #(f i) := by sorry

@[target]
theorem mk_iUnion_eq_sum_mk {α ι : Type u} {f : ι → Set α}
    (h : Pairwise (Disjoint on f)) : #(⋃ i, f i) = sum fun i => #(f i) := by sorry

@[target]
theorem mk_iUnion_eq_sum_mk_lift {α : Type u} {ι : Type v} {f : ι → Set α}
    (h : Pairwise (Disjoint on f)) :
    lift.{v} #(⋃ i, f i) = sum fun i => #(f i) := by sorry

@[target]
theorem mk_iUnion_le {α ι : Type u} (f : ι → Set α) : #(⋃ i, f i) ≤ #ι * ⨆ i, #(f i) := by sorry

@[target]
theorem mk_iUnion_le_lift {α : Type u} {ι : Type v} (f : ι → Set α) :
    lift.{v} #(⋃ i, f i) ≤ lift.{u} #ι * ⨆ i, lift.{v} #(f i) := by sorry

@[target]
theorem mk_sUnion_le {α : Type u} (A : Set (Set α)) : #(⋃₀ A) ≤ #A * ⨆ s : A, #s := by sorry

@[target]
theorem mk_biUnion_le {ι α : Type u} (A : ι → Set α) (s : Set ι) :
    #(⋃ x ∈ s, A x) ≤ #s * ⨆ x : s, #(A x.1) := by sorry

theorem mk_biUnion_le_lift {α : Type u} {ι : Type v} (A : ι → Set α) (s : Set ι) :
    lift.{v} #(⋃ x ∈ s, A x) ≤ lift.{u} #s * ⨆ x : s, lift.{v} #(A x.1) := by
  rw [biUnion_eq_iUnion]
  apply mk_iUnion_le_lift

theorem finset_card_lt_aleph0 (s : Finset α) : #(↑s : Set α) < ℵ₀ :=
  lt_aleph0_of_finite _

@[target]
theorem mk_set_eq_nat_iff_finset {α} {s : Set α} {n : ℕ} :
    #s = n ↔ ∃ t : Finset α, (t : Set α) = s ∧ t.card = n := by sorry

theorem mk_eq_nat_iff_finset {n : ℕ} :
    #α = n ↔ ∃ t : Finset α, (t : Set α) = univ ∧ t.card = n := by
  rw [← mk_univ, mk_set_eq_nat_iff_finset]

@[target]
theorem mk_eq_nat_iff_fintype {n : ℕ} : #α = n ↔ ∃ h : Fintype α, @Fintype.card α h = n := by sorry

@[target]
theorem mk_union_add_mk_inter {α : Type u} {S T : Set α} :
    #(S ∪ T : Set α) + #(S ∩ T : Set α) = #S + #T := by sorry

/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
@[target]
theorem mk_union_le {α : Type u} (S T : Set α) : #(S ∪ T : Set α) ≤ #S + #T := by sorry

@[target]
theorem mk_union_of_disjoint {α : Type u} {S T : Set α} (H : Disjoint S T) :
    #(S ∪ T : Set α) = #S + #T := by sorry

@[target]
theorem mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ s) :
    #(insert a s : Set α) = #s + 1 := by sorry

@[target]
theorem mk_insert_le {α : Type u} {s : Set α} {a : α} : #(insert a s : Set α) ≤ #s + 1 := by sorry

theorem mk_sum_compl {α} (s : Set α) : #s + #(sᶜ : Set α) = #α := by
  classical
  exact mk_congr (Equiv.Set.sumCompl s)

@[target]
theorem mk_le_mk_of_subset {α} {s t : Set α} (h : s ⊆ t) : #s ≤ #t := by sorry

@[target]
theorem mk_le_iff_forall_finset_subset_card_le {α : Type u} {n : ℕ} {t : Set α} :
    #t ≤ n ↔ ∀ s : Finset α, (s : Set α) ⊆ t → s.card ≤ n := by sorry

theorem mk_subtype_mono {p q : α → Prop} (h : ∀ x, p x → q x) :
    #{ x // p x } ≤ #{ x // q x } :=
  ⟨embeddingOfSubset _ _ h⟩

@[target]
theorem le_mk_diff_add_mk (S T : Set α) : #S ≤ #(S \ T : Set α) + #T := by sorry

@[target]
theorem mk_diff_add_mk {S T : Set α} (h : T ⊆ S) : #(S \ T : Set α) + #T = #S := by sorry

@[target]
theorem mk_union_le_aleph0 {α} {P Q : Set α} :
    #(P ∪ Q : Set α) ≤ ℵ₀ ↔ #P ≤ ℵ₀ ∧ #Q ≤ ℵ₀ := by sorry

theorem mk_subtype_of_equiv {α β : Type u} (p : β → Prop) (e : α ≃ β) :
    #{ a : α // p (e a) } = #{ b : β // p b } :=
  mk_congr (Equiv.subtypeEquivOfSubtype e)

theorem mk_sep (s : Set α) (t : α → Prop) : #({ x ∈ s | t x } : Set α) = #{ x : s | t x.1 } :=
  mk_congr (Equiv.Set.sep s t)

@[target]
theorem mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) : lift.{v} #(f ⁻¹' s) ≤ lift.{u} #s := by sorry

theorem mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : Set β)
    (h : s ⊆ range f) : lift.{u} #s ≤ lift.{v} #(f ⁻¹' s) := by
  rw [← image_preimage_eq_iff] at h
  nth_rewrite 1 [← h]
  apply mk_image_le_lift

@[target]
theorem mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α → β) (s : Set β)
    (h : Injective f) (h2 : s ⊆ range f) : lift.{v} #(f ⁻¹' s) = lift.{u} #s := by sorry

@[target]
theorem mk_preimage_of_injective_of_subset_range (f : α → β) (s : Set β) (h : Injective f)
    (h2 : s ⊆ range f) : #(f ⁻¹' s) = #s := by sorry

@[simp]
theorem mk_preimage_equiv_lift {β : Type v} (f : α ≃ β) (s : Set β) :
    lift.{v} #(f ⁻¹' s) = lift.{u} #s := by
  apply mk_preimage_of_injective_of_subset_range_lift _ _ f.injective
  rw [f.range_eq_univ]
  exact fun _ _ ↦ ⟨⟩

@[target, simp]
theorem mk_preimage_equiv (f : α ≃ β) (s : Set β) : #(f ⁻¹' s) = #s := by sorry

theorem mk_preimage_of_injective (f : α → β) (s : Set β) (h : Injective f) :
    #(f ⁻¹' s) ≤ #s := by
  rw [← lift_id #(↑(f ⁻¹' s)), ← lift_id #(↑s)]
  exact mk_preimage_of_injective_lift f s h

@[target]
theorem mk_preimage_of_subset_range (f : α → β) (s : Set β) (h : s ⊆ range f) :
    #s ≤ #(f ⁻¹' s) := by sorry

theorem mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : Set α}
    {t : Set β} (h : t ⊆ f '' s) : lift.{u} #t ≤ lift.{v} #({ x ∈ s | f x ∈ t } : Set α) := by
  rw [image_eq_range] at h
  convert mk_preimage_of_subset_range_lift _ _ h using 1
  rw [mk_sep]
  rfl

@[target]
theorem mk_subset_ge_of_subset_image (f : α → β) {s : Set α} {t : Set β} (h : t ⊆ f '' s) :
    #t ≤ #({ x ∈ s | f x ∈ t } : Set α) := by sorry

theorem le_mk_iff_exists_subset {c : Cardinal} {α : Type u} {s : Set α} :
    c ≤ #s ↔ ∃ p : Set α, p ⊆ s ∧ #p = c := by
  rw [le_mk_iff_exists_set, ← Subtype.exists_set_subtype]
  apply exists_congr; intro t; rw [mk_image_eq]; apply Subtype.val_injective

@[simp]
theorem mk_range_inl {α : Type u} {β : Type v} : #(range (@Sum.inl α β)) = lift.{v} #α := by
  sorry

@[target, simp]
theorem mk_range_inr {α : Type u} {β : Type v} : #(range (@Sum.inr α β)) = lift.{u} #β := by sorry

@[target]
theorem two_le_iff : (2 : Cardinal) ≤ #α ↔ ∃ x y : α, x ≠ y := by sorry

@[target]
theorem two_le_iff' (x : α) : (2 : Cardinal) ≤ #α ↔ ∃ y : α, y ≠ x := by sorry

@[target]
theorem mk_eq_two_iff : #α = 2 ↔ ∃ x y : α, x ≠ y ∧ ({x, y} : Set α) = univ := by sorry

theorem mk_eq_two_iff' (x : α) : #α = 2 ↔ ∃! y, y ≠ x := by
  rw [mk_eq_two_iff]; constructor
  · rintro ⟨a, b, hne, h⟩
    simp only [eq_univ_iff_forall, mem_insert_iff, mem_singleton_iff] at h
    rcases h x with (rfl | rfl)
    exacts [⟨b, hne.symm, fun z => (h z).resolve_left⟩, ⟨a, hne, fun z => (h z).resolve_right⟩]
  · rintro ⟨y, hne, hy⟩
    exact ⟨x, y, hne.symm, eq_univ_of_forall fun z => or_iff_not_imp_left.2 (hy z)⟩

@[target]
theorem exists_not_mem_of_length_lt {α : Type*} (l : List α) (h : ↑l.length < #α) :
    ∃ z : α, z ∉ l := by sorry

@[target]
theorem three_le {α : Type*} (h : 3 ≤ #α) (x : α) (y : α) : ∃ z : α, z ≠ x ∧ z ≠ y := by sorry

/-! ### `powerlt` operation -/

/-- The function `a ^< b`, defined as the supremum of `a ^ c` for `c < b`. -/
def powerlt (a b : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ c : Iio b, a ^ (c : Cardinal)

@[inherit_doc]
infixl:80 " ^< " => powerlt

theorem le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (a^c) ≤ a ^< b := by
  refine le_ciSup (f := fun y : Iio b => a ^ (y : Cardinal)) ?_ ⟨c, h⟩
  rw [← image_eq_range]
  exact bddAbove_image.{u, u} _ bddAbove_Iio

@[target]
theorem powerlt_le {a b c : Cardinal.{u}} : a ^< b ≤ c ↔ ∀ x < b, a ^ x ≤ c := by sorry

@[target]
theorem powerlt_le_powerlt_left {a b c : Cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c := by sorry

theorem powerlt_mono_left (a) : Monotone fun c => a ^< c := fun _ _ => powerlt_le_powerlt_left

@[target]
theorem powerlt_succ {a b : Cardinal} (h : a ≠ 0) : a ^< succ b = a ^ b := by sorry

theorem powerlt_min {a b c : Cardinal} : a ^< min b c = min (a ^< b) (a ^< c) :=
  (powerlt_mono_left a).map_min

@[target]
theorem powerlt_max {a b c : Cardinal} : a ^< max b c = max (a ^< b) (a ^< c) := by sorry

@[target]
theorem zero_powerlt {a : Cardinal} (h : a ≠ 0) : 0 ^< a = 1 := by sorry

@[simp]
theorem powerlt_zero {a : Cardinal} : a ^< 0 = 0 := by
  convert Cardinal.iSup_of_empty _
  exact Subtype.isEmpty_of_false fun x => mem_Iio.not.mpr (Cardinal.zero_le x).not_lt

end Cardinal

-- namespace Tactic

-- open Cardinal Positivity

-- Porting note: Meta code, do not port directly
-- /-- Extension for the `positivity` tactic: The cardinal power of a positive cardinal is
--  positive. -/
-- @[positivity]
-- unsafe def positivity_cardinal_pow : expr → tactic strictness
--   | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => positive <$> mk_app `` power_pos [b, p]
--       | _ => failed
--   |-- We already know that `0 ≤ x` for all `x : Cardinal`
--     _ =>
--     failed

-- end Tactic

set_option linter.style.longFile 2300
