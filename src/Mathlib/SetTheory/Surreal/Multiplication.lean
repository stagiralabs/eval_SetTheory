import VerifiedAgora.tagger
/-
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Violeta Hernández Palacios, Junyan Xu, Theodore Hwa
-/
import Mathlib.Logic.Hydra
import Mathlib.SetTheory.Surreal.Basic

/-!
### Surreal multiplication

In this file, we show that multiplication of surreal numbers is well-defined, and thus the
surreal numbers form a linear ordered commutative ring.

An inductive argument proves the following three main theorems:
* P1: being numeric is closed under multiplication,
* P2: multiplying a numeric pregame by equivalent numeric pregames results in equivalent pregames,
* P3: the product of two positive numeric pregames is positive (`mul_pos`).

This is Theorem 8 in [Conway2001], or Theorem 3.8 in [SchleicherStoll]. P1 allows us to define
multiplication as an operation on numeric pregames, P2 says that this is well-defined as an
operation on the quotient by `PGame.Equiv`, namely the surreal numbers, and P3 is an axiom that
needs to be satisfied for the surreals to be a `OrderedRing`.

We follow the proof in [SchleicherStoll], except that we use the well-foundedness of
the hydra relation `CutExpand` on `Multiset PGame` instead of the argument based
on a depth function in the paper.

In the argument, P3 is stated with four variables `x₁`, `x₂`, `y₁`, `y₂` satisfying `x₁ < x₂` and
`y₁ < y₂`, and says that `x₁ * y₂ + x₂ * x₁ < x₁ * y₁ + x₂ * y₂`, which is equivalent to
`0 < x₂ - x₁ → 0 < y₂ - y₁ → 0 < (x₂ - x₁) * (y₂ - y₁)`, i.e.
`@mul_pos PGame _ (x₂ - x₁) (y₂ - y₁)`. It has to be stated in this form and not in terms of
`mul_pos` because we need to show P1, P2 and (a specialized form of) P3 simultaneously, and
for example `P1 x y` will be deduced from P3 with variables taking values simpler than `x` or `y`
(among other induction hypotheses), but if you subtract two pregames simpler than `x` or `y`,
the result may no longer be simpler.

The specialized version of P3 is called P4, which takes only three arguments `x₁`, `x₂`, `y` and
requires that `y₂ = y` or `-y` and that `y₁` is a left option of `y₂`. After P1, P2 and P4 are
shown, a further inductive argument (this time using the `GameAdd` relation) proves P3 in full.

Implementation strategy of the inductive argument: we
* extract specialized versions (`IH1`, `IH2`, `IH3`, `IH4` and `IH24`) of the induction hypothesis
  that are easier to apply (taking `IsOption` arguments directly), and
* show they are invariant under certain symmetries (permutation and negation of arguments) and that
  the induction hypothesis indeed implies the specialized versions.
* utilize the symmetries to minimize calculation.

The whole proof features a clear separation into lemmas of different roles:
* verification of symmetry properties of P and IH (`P3_comm`, `ih1_neg_left`, etc.),
* calculations that connect P1, P2, P3, and inequalities between the product of
  two surreals and its options (`mulOption_lt_iff_P1`, etc.),
* specializations of the induction hypothesis
  (`numeric_option_mul`, `ih1`, `ih1_swap`, `ih₁₂`, `ih4`, etc.),
* application of specialized induction hypothesis
  (`P1_of_ih`, `mul_right_le_of_equiv`, `P3_of_lt`, etc.).

## References

* [Conway, *On numbers and games*][Conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][SchleicherStoll]

-/

universe u

open SetTheory Game PGame WellFounded

namespace Surreal.Multiplication

/-- The nontrivial part of P1 in [SchleicherStoll] says that the left options of `x * y` are less
  than the right options, and this is the general form of these statements. -/
def P1 (x₁ x₂ x₃ y₁ y₂ y₃ : PGame) :=
  ⟦x₁ * y₁⟧ + ⟦x₂ * y₂⟧ - ⟦x₁ * y₂⟧ < ⟦x₃ * y₁⟧ + ⟦x₂ * y₃⟧ - (⟦x₃ * y₃⟧ : Game)

/-- The proposition P2, without numericity assumptions. -/
def P2 (x₁ x₂ y : PGame) := x₁ ≈ x₂ → ⟦x₁ * y⟧ = (⟦x₂ * y⟧ : Game)

/-- The proposition P3, without the `x₁ < x₂` and `y₁ < y₂` assumptions. -/
def P3 (x₁ x₂ y₁ y₂ : PGame) := ⟦x₁ * y₂⟧ + ⟦x₂ * y₁⟧ < ⟦x₁ * y₁⟧ + (⟦x₂ * y₂⟧ : Game)

/-- The proposition P4, without numericity assumptions. In the references, the second part of the
  conjunction is stated as `∀ j, P3 x₁ x₂ y (y.moveRight j)`, which is equivalent to our statement
  by `P3_comm` and `P3_neg`. We choose to state everything in terms of left options for uniform
  treatment. -/
def P4 (x₁ x₂ y : PGame) :=
  x₁ < x₂ → (∀ i, P3 x₁ x₂ (y.moveLeft i) y) ∧ ∀ j, P3 x₁ x₂ ((-y).moveLeft j) (-y)

/-- The conjunction of P2 and P4. -/
def P24 (x₁ x₂ y : PGame) : Prop := P2 x₁ x₂ y ∧ P4 x₁ x₂ y

variable {x x₁ x₂ x₃ x' y y₁ y₂ y₃ y' : PGame.{u}}

/-! #### Symmetry properties of P1, P2, P3, and P4 -/

@[target]
lemma P3_comm : P3 x₁ x₂ y₁ y₂ ↔ P3 y₁ y₂ x₁ x₂ := by sorry

lemma P3.trans (h₁ : P3 x₁ x₂ y₁ y₂) (h₂ : P3 x₂ x₃ y₁ y₂) : P3 x₁ x₃ y₁ y₂ := by
  rw [P3] at h₁ h₂
  rw [P3, ← add_lt_add_iff_left (⟦x₂ * y₁⟧ + ⟦x₂ * y₂⟧)]
  convert add_lt_add h₁ h₂ using 1 <;> abel

lemma P3_neg : P3 x₁ x₂ y₁ y₂ ↔ P3 (-x₂) (-x₁) y₁ y₂ := by
  simp_rw [P3, quot_neg_mul]
  rw [← _root_.neg_lt_neg_iff]
  abel_nf

@[target]
lemma P2_neg_left : P2 x₁ x₂ y ↔ P2 (-x₂) (-x₁) y := by sorry

lemma P2_neg_right : P2 x₁ x₂ y ↔ P2 x₁ x₂ (-y) := by
  rw [P2, P2, quot_mul_neg, quot_mul_neg, neg_inj]

@[target]
lemma P4_neg_left : P4 x₁ x₂ y ↔ P4 (-x₂) (-x₁) y := by sorry

lemma P4_neg_right : P4 x₁ x₂ y ↔ P4 x₁ x₂ (-y) := by
  rw [P4, P4, neg_neg, and_comm]

@[target]
lemma P24_neg_left : P24 x₁ x₂ y ↔ P24 (-x₂) (-x₁) y := by sorry

@[target]
lemma P24_neg_right : P24 x₁ x₂ y ↔ P24 x₁ x₂ (-y) := by sorry

/-! #### Explicit calculations necessary for the main proof -/

@[target]
lemma mulOption_lt_iff_P1 {i j k l} :
    (⟦mulOption x y i k⟧ : Game) < -⟦mulOption x (-y) j l⟧ ↔
    P1 (x.moveLeft i) x (x.moveLeft j) y (y.moveLeft k) (-(-y).moveLeft l) := by sorry

@[target]
lemma mulOption_lt_mul_iff_P3 {i j} :
    ⟦mulOption x y i j⟧ < (⟦x * y⟧ : Game) ↔ P3 (x.moveLeft i) x (y.moveLeft j) y := by sorry

lemma P1_of_eq (he : x₁ ≈ x₃) (h₁ : P2 x₁ x₃ y₁) (h₃ : P2 x₁ x₃ y₃) (h3 : P3 x₁ x₂ y₂ y₃) :
    P1 x₁ x₂ x₃ y₁ y₂ y₃ := by
  rw [P1, ← h₁ he, ← h₃ he, sub_lt_sub_iff]
  convert add_lt_add_left h3 ⟦x₁ * y₁⟧ using 1 <;> abel

lemma P1_of_lt (h₁ : P3 x₃ x₂ y₂ y₃) (h₂ : P3 x₁ x₃ y₂ y₁) : P1 x₁ x₂ x₃ y₁ y₂ y₃ := by
  rw [P1, sub_lt_sub_iff, ← add_lt_add_iff_left ⟦x₃ * y₂⟧]
  convert add_lt_add h₁ h₂ using 1 <;> abel

/-- The type of lists of arguments for P1, P2, and P4. -/
inductive Args : Type (u+1)
  | P1 (x y : PGame.{u}) : Args
  | P24 (x₁ x₂ y : PGame.{u}) : Args

/-- The multiset associated to a list of arguments. -/
def Args.toMultiset : Args → Multiset PGame
  | (Args.P1 x y) => {x, y}
  | (Args.P24 x₁ x₂ y) => {x₁, x₂, y}

/-- A list of arguments is numeric if all the arguments are. -/
def Args.Numeric (a : Args) := ∀ x ∈ a.toMultiset, SetTheory.PGame.Numeric x

lemma Args.numeric_P1 {x y} : (Args.P1 x y).Numeric ↔ x.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]

@[target]
lemma Args.numeric_P24 {x₁ x₂ y} :
    (Args.P24 x₁ x₂ y).Numeric ↔ x₁.Numeric ∧ x₂.Numeric ∧ y.Numeric := by sorry

open Relation

/-- The relation specifying when a list of (pregame) arguments is considered simpler than another:
  `ArgsRel a₁ a₂` is true if `a₁`, considered as a multiset, can be obtained from `a₂` by
  repeatedly removing a pregame from `a₂` and adding back one or two options of the pregame. -/
def ArgsRel := InvImage (TransGen <| CutExpand IsOption) Args.toMultiset

/-- `ArgsRel` is well-founded. -/
@[target]
theorem argsRel_wf : WellFounded ArgsRel := by sorry

/-- The statement that we will show by induction using the well-founded relation `ArgsRel`. -/
def P124 : Args → Prop
  | (Args.P1 x y) => Numeric (x * y)
  | (Args.P24 x₁ x₂ y) => P24 x₁ x₂ y

/-- The property that all arguments are numeric is leftward-closed under `ArgsRel`. -/
@[target]
lemma ArgsRel.numeric_closed {a' a} : ArgsRel a' a → a.Numeric → a'.Numeric := by sorry

/-- A specialized induction hypothesis used to prove P1. -/
def IH1 (x y : PGame) : Prop :=
  ∀ ⦃x₁ x₂ y'⦄, IsOption x₁ x → IsOption x₂ x → (y' = y ∨ IsOption y' y) → P24 x₁ x₂ y'

/-! #### Symmetry properties of `IH1` -/

lemma ih1_neg_left : IH1 x y → IH1 (-x) y :=
  fun h x₁ x₂ y' h₁ h₂ hy ↦ by
    rw [isOption_neg] at h₁ h₂
    exact P24_neg_left.2 (h h₂ h₁ hy)

@[target]
lemma ih1_neg_right : IH1 x y → IH1 x (-y) := by sorry

/-! #### Specialize `ih` to obtain specialized induction hypotheses for P1 -/

lemma numeric_option_mul (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (h : IsOption x' x) :
    (x' * y).Numeric :=
  ih (Args.P1 x' y) (TransGen.single <| cutExpand_pair_left h)

lemma numeric_mul_option (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (h : IsOption y' y) :
    (x * y').Numeric :=
  ih (Args.P1 x y') (TransGen.single <| cutExpand_pair_right h)

@[target]
lemma numeric_option_mul_option (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (hx : IsOption x' x)
    (hy : IsOption y' y) : (x' * y').Numeric := by sorry

@[target]
lemma ih1 (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 x y := by sorry

@[target]
lemma ih1_swap (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 y x := by sorry

@[target]
lemma P3_of_ih (hy : Numeric y) (ihyx : IH1 y x) (i k l) :
    P3 (x.moveLeft i) x (y.moveLeft k) (-(-y).moveLeft l) := by sorry

lemma P24_of_ih (ihxy : IH1 x y) (i j) : P24 (x.moveLeft i) (x.moveLeft j) y :=
  ihxy (IsOption.moveLeft i) (IsOption.moveLeft j) (Or.inl rfl)

section

@[target]
lemma mulOption_lt_of_lt (hy : y.Numeric) (ihxy : IH1 x y) (ihyx : IH1 y x) (i j k l)
    (h : x.moveLeft i < x.moveLeft j) :
    (⟦mulOption x y i k⟧ : Game) < -⟦mulOption x (-y) j l⟧ := by sorry

@[target]
lemma mulOption_lt (hx : x.Numeric) (hy : y.Numeric) (ihxy : IH1 x y) (ihyx : IH1 y x) (i j k l) :
    (⟦mulOption x y i k⟧ : Game) < -⟦mulOption x (-y) j l⟧ := by sorry

end

/-- P1 follows from the induction hypothesis. -/
@[target]
theorem P1_of_ih (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (hx : x.Numeric) (hy : y.Numeric) :
    (x * y).Numeric := by sorry

/-- A specialized induction hypothesis used to prove P2 and P4. -/
def IH24 (x₁ x₂ y : PGame) : Prop :=
  ∀ ⦃z⦄, (IsOption z x₁ → P24 z x₂ y) ∧ (IsOption z x₂ → P24 x₁ z y) ∧ (IsOption z y → P24 x₁ x₂ z)

/-- A specialized induction hypothesis used to prove P4. -/
def IH4 (x₁ x₂ y : PGame) : Prop :=
  ∀ ⦃z w⦄, IsOption w y → (IsOption z x₁ → P2 z x₂ w) ∧ (IsOption z x₂ → P2 x₁ z w)

/-! #### Specialize `ih'` to obtain specialized induction hypotheses for P2 and P4 -/

@[target]
lemma ih₁₂ (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₁ x₂ y := by sorry

lemma ih₂₁ (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₂ x₁ y := ih₁₂ <| by
  simp_rw [ArgsRel, InvImage, Args.toMultiset, Multiset.pair_comm] at ih' ⊢
  suffices {x₁, y, x₂} = {x₂, y, x₁} by rwa [← this]
  dsimp only [Multiset.insert_eq_cons, ← Multiset.singleton_add] at ih' ⊢
  abel

@[target]
lemma ih4 (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH4 x₁ x₂ y := by sorry

@[target]
lemma numeric_of_ih (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) :
    (x₁ * y).Numeric ∧ (x₂ * y).Numeric := by sorry

/-- Symmetry properties of `IH24`. -/
@[target]
lemma ih24_neg : IH24 x₁ x₂ y → IH24 (-x₂) (-x₁) y ∧ IH24 x₁ x₂ (-y) := by sorry

/-- Symmetry properties of `IH4`. -/
lemma ih4_neg : IH4 x₁ x₂ y → IH4 (-x₂) (-x₁) y ∧ IH4 x₁ x₂ (-y) := by
  simp_rw [IH4, isOption_neg]
  refine fun h ↦ ⟨fun z w h' ↦ ?_, fun z w h' ↦ ?_⟩
  · convert (h h').symm using 2 <;> rw [P2_neg_left, neg_neg]
  · convert h h' using 2 <;> rw [P2_neg_right]

@[target]
lemma mulOption_lt_mul_of_equiv (hn : x₁.Numeric) (h : IH24 x₁ x₂ y) (he : x₁ ≈ x₂) (i j) :
    ⟦mulOption x₁ y i j⟧ < (⟦x₂ * y⟧ : Game) := by sorry

/-- P2 follows from specialized induction hypotheses (one half of the equality). -/
@[target]
theorem mul_right_le_of_equiv (h₁ : x₁.Numeric) (h₂ : x₂.Numeric)
    (h₁₂ : IH24 x₁ x₂ y) (h₂₁ : IH24 x₂ x₁ y) (he : x₁ ≈ x₂) : x₁ * y ≤ x₂ * y := by sorry

/-- The statement that all left options of `x * y` of the first kind are less than itself. -/
def MulOptionsLTMul (x y : PGame) : Prop := ∀ ⦃i j⦄, ⟦mulOption x y i j⟧ < (⟦x * y⟧ : Game)

/-- That the left options of `x * y` are less than itself and the right options are greater, which
  is part of the condition that `x * y` is numeric, is equivalent to the conjunction of various
  `MulOptionsLTMul` statements for `x`, `y` and their negations. We only show the forward
  direction. -/
@[target]
lemma mulOptionsLTMul_of_numeric (hn : (x * y).Numeric) :
    (MulOptionsLTMul x y ∧ MulOptionsLTMul (-x) (-y)) ∧
    (MulOptionsLTMul x (-y) ∧ MulOptionsLTMul (-x) y) := by sorry

/-- A condition just enough to deduce P3, which will always be used with `x'` being a left
  option of `x₂`. When `y₁` is a left option of `y₂`, it can be deduced from induction hypotheses
  `IH24 x₁ x₂ y₂`, `IH4 x₁ x₂ y₂`, and `(x₂ * y₂).Numeric` (`ih3_of_ih`); when `y₁` is
  not necessarily an option of `y₂`, it follows from the induction hypothesis for P3 (with `x₂`
  replaced by a left option `x'`) after the `main` theorem (P124) is established, and is used to
  prove P3 in full (`P3_of_lt_of_lt`). -/
def IH3 (x₁ x' x₂ y₁ y₂ : PGame) : Prop :=
    P2 x₁ x' y₁ ∧ P2 x₁ x' y₂ ∧ P3 x' x₂ y₁ y₂ ∧ (x₁ < x' → P3 x₁ x' y₁ y₂)

@[target]
lemma ih3_of_ih (h24 : IH24 x₁ x₂ y) (h4 : IH4 x₁ x₂ y) (hl : MulOptionsLTMul x₂ y) (i j) :
    IH3 x₁ (x₂.moveLeft i) x₂ (y.moveLeft j) y := by sorry

@[target]
lemma P3_of_le_left {y₁ y₂} (i) (h : IH3 x₁ (x₂.moveLeft i) x₂ y₁ y₂) (hl : x₁ ≤ x₂.moveLeft i) :
    P3 x₁ x₂ y₁ y₂ := by sorry

/-- P3 follows from `IH3` (so P4 (with `y₁` a left option of `y₂`) follows from the induction
  hypothesis). -/
theorem P3_of_lt {y₁ y₂} (h : ∀ i, IH3 x₁ (x₂.moveLeft i) x₂ y₁ y₂)
    (hs : ∀ i, IH3 (-x₂) ((-x₁).moveLeft i) (-x₁) y₁ y₂) (hl : x₁ < x₂) :
    P3 x₁ x₂ y₁ y₂ := by
  obtain (⟨i,hi⟩|⟨i,hi⟩) := lf_iff_exists_le.1 (lf_of_lt hl)
  · exact P3_of_le_left i (h i) hi
  · apply P3_neg.2 <| P3_of_le_left _ (hs (toLeftMovesNeg i)) _
    simpa

/-- The main chunk of Theorem 8 in [Conway2001] / Theorem 3.8 in [SchleicherStoll]. -/
@[target]
theorem main (a : Args) : a.Numeric → P124 a := by sorry

end Surreal.Multiplication

namespace SetTheory.PGame
open Surreal.Multiplication

variable {x x₁ x₂ y y₁ y₂ : PGame.{u}}

@[target]
theorem Numeric.mul (hx : x.Numeric) (hy : y.Numeric) : Numeric (x * y) := by sorry

@[target]
theorem P24 (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hy : y.Numeric) : P24 x₁ x₂ y := by sorry

@[target]
theorem Equiv.mul_congr_left (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hy : y.Numeric)
    (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y := by sorry

@[target]
theorem Equiv.mul_congr_right (hx : x.Numeric) (hy₁ : y₁.Numeric) (hy₂ : y₂.Numeric)
    (he : y₁ ≈ y₂) : x * y₁ ≈ x * y₂ := by sorry

@[target]
theorem Equiv.mul_congr (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric)
    (hy₁ : y₁.Numeric) (hy₂ : y₂.Numeric) (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ := by sorry

open Prod.GameAdd

/-- One additional inductive argument that supplies the last missing part of Theorem 8. -/
theorem P3_of_lt_of_lt (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hy₁ : y₁.Numeric) (hy₂ : y₂.Numeric)
    (hx : x₁ < x₂) (hy : y₁ < y₂) : P3 x₁ x₂ y₁ y₂ := by
  revert x₁ x₂
  rw [← Prod.forall']
  refine (wf_isOption.prod_gameAdd wf_isOption).fix ?_
  rintro ⟨x₁, x₂⟩ ih hx₁ hx₂ hx
  refine P3_of_lt ?_ ?_ hx <;> intro i
  · have hi := hx₂.moveLeft i
    exact ⟨(P24 hx₁ hi hy₁).1, (P24 hx₁ hi hy₂).1,
      P3_comm.2 <| ((P24 hy₁ hy₂ hx₂).2 hy).1 _,
      ih _ (snd <| IsOption.moveLeft i) hx₁ hi⟩
  · have hi := hx₁.neg.moveLeft i
    exact ⟨(P24 hx₂.neg hi hy₁).1, (P24 hx₂.neg hi hy₂).1,
      P3_comm.2 <| ((P24 hy₁ hy₂ hx₁).2 hy).2 _, by
        rw [moveLeft_neg, ← P3_neg, neg_lt_neg_iff]
        exact ih _ (fst <| IsOption.moveRight _) (hx₁.moveRight _) hx₂⟩

@[target]
theorem Numeric.mul_pos (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hp₁ : 0 < x₁) (hp₂ : 0 < x₂) :
    0 < x₁ * x₂ := by sorry

end SetTheory.PGame

namespace Surreal

open SetTheory.PGame.Equiv

noncomputable instance : LinearOrderedCommRing Surreal where
  __ := Surreal.orderedAddCommGroup
  mul := Surreal.lift₂ (fun x y ox oy ↦ ⟦⟨x * y, ox.mul oy⟩⟧)
    (fun ox₁ oy₁ ox₂ oy₂ hx hy ↦ Quotient.sound <| mul_congr ox₁ ox₂ oy₁ oy₂ hx hy)
  mul_assoc := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (mul_assoc_equiv _ _ _)
  one := mk 1 numeric_one
  one_mul := by rintro ⟨_⟩; exact Quotient.sound (one_mul_equiv _)
  mul_one := by rintro ⟨_⟩; exact Quotient.sound (mul_one_equiv _)
  left_distrib := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (left_distrib_equiv _ _ _)
  right_distrib := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (right_distrib_equiv _ _ _)
  mul_comm := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound (mul_comm_equiv _ _)
  le := lift₂ (fun x y _ _ ↦ x ≤ y) (fun _ _ _ _ hx hy ↦ propext <| le_congr hx hy)
  lt := lift₂ (fun x y _ _ ↦ x < y) (fun _ _ _ _ hx hy ↦ propext <| lt_congr hx hy)
  le_refl := by rintro ⟨_⟩; apply @le_rfl PGame
  le_trans := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; apply @le_trans PGame
  lt_iff_le_not_le := by rintro ⟨_⟩ ⟨_⟩; exact lt_iff_le_not_le
  le_antisymm := by rintro ⟨_⟩ ⟨_⟩ h₁ h₂; exact Quotient.sound ⟨h₁, h₂⟩
  add_le_add_left := by rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩; exact add_le_add_left hx _
  zero_le_one := PGame.zero_lt_one.le
  zero_mul := by rintro ⟨_⟩; exact Quotient.sound (zero_mul_equiv _)
  mul_zero := by rintro ⟨_⟩; exact Quotient.sound (mul_zero_equiv _)
  exists_pair_ne := ⟨0, 1, ne_of_lt PGame.zero_lt_one⟩
  le_total := by rintro ⟨x⟩ ⟨y⟩; sorry
  mul_pos := by rintro ⟨x⟩ ⟨y⟩; exact x.2.mul_pos y.2
  decidableLE := Classical.decRel _

end Surreal
