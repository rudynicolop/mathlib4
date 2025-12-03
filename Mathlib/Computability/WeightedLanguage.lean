/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
module

public import Mathlib.Data.List.Perm.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Weigted Languages

A weighted language `f` over a semiring `W` for `κ` generalizes formal languages where, instead of
indicating whether a string `x` is in `f`, we assign every string `x ∈ List α` a weight
that is an element in `κ`. Thus a weighted formal language `f` is a function `List α → κ`
rather than a set `Set (List α)`.

A weighted language `f` may be thought of as a formal power series `∑ f(x) x` where we "sum" over
`x ∈ List α` with coefficients `f x`, i.e. the weights of `x` via `f`. This file does not
attempt to provide nor use a formal notion of formal power series, but it may provide a
high-level intuition.

The main result in this file is the construction of a semiring for weighted languages.

## References

* [Advanced Formal Language Theory: Regular Languages][weighted-regular-languages]
* [Handbook of Weighted Automata][Handbook-of-Weighted-Automata]
-/

@[expose] public section

open List

universe u k

/-- A weighted language is a map from strings `List α` over an alphabet `α` to elements of a
semiring `κ`. -/
def WeightedLanguage (α : Type u) (κ : Type k) : Type (max u k) :=
  List α → κ

namespace WeightedLanguage

variable {α : Type u} {κ : Type k}

@[ext]
lemma ext {f g : WeightedLanguage α κ} (h : ∀ (x : List α), f x = g x) : f = g :=
  funext h

instance : FunLike (WeightedLanguage α κ) (List α) κ where
  coe := id
  coe_injective' := Function.injective_id

/-- Compose a weighted language with some transformation. -/
@[simp]
def preimage {β : Type*} (f : WeightedLanguage β κ) (g : List α → List β) : WeightedLanguage α κ :=
  f ∘ g

/-- Reverse a weighted language. -/
def reverse (f : WeightedLanguage α κ) : WeightedLanguage α κ := f ∘ List.reverse

section zero

variable [Zero κ]

/-- The "zero" element of a weighted language: `0ₗ := x ↦ 0`. -/
instance instZero : Zero (WeightedLanguage α κ) :=
  ⟨fun _ ↦ 0⟩

lemma zero_def : (0 : WeightedLanguage α κ) = fun (_ : List α) ↦ (0 : κ) :=
  rfl

@[simp]
lemma zero_apply (x : List α) : (0 : WeightedLanguage α κ) x = (0 : κ) :=
  rfl

instance instInhabited : Inhabited (WeightedLanguage α κ) :=
  ⟨0⟩

end zero

section one

variable [Zero κ] [One κ]

/-- `onlyNil x` gives `1` when `x = []` and `0` otherwise.
This is the "one" element of a weighted language:
`1ₗ := x ↦ 1` if `x = ε`, and `1ₗ := x ↦ 0` otherwise. -/
def onlyNil : List α → κ
  | [] => 1
  | _  => 0

@[simp]
lemma onlyNil_nil : onlyNil ([] : List α) = (1 : κ) :=
  rfl

@[simp]
lemma onlyNil_cons (x : α) (xs : List α) : onlyNil (x :: xs) = (0 : κ) :=
  rfl

lemma onlyNil_gives_zero (x : List α) :
    0 < x.length →
    onlyNil x = (0 : κ) := by
  intros hx
  cases x <;> simp at *

lemma onlyNil_eq (xs : List α) :
    onlyNil xs = if xs.length > 0 then (0 : κ) else (1 : κ) := by
  cases xs <;> simp

instance instOne : One (WeightedLanguage α κ) :=
  ⟨onlyNil⟩

lemma one_def : (1 : WeightedLanguage α κ) = onlyNil :=
  rfl

@[simp]
lemma one_apply (x : List α) : (1 : WeightedLanguage α κ) x = onlyNil x :=
  rfl

lemma one_gives_zero (x : List α) :
    0 < x.length → (1 : WeightedLanguage α κ) x = 0 := by
  intros hx
  cases x <;> simp at *

end one

section add

variable [W : AddCommMonoid κ]

/-- The weighted language [f + g] assigns the pointwise sum `f x + g x` for all strings `x`.
`(f + g)(x) = f(x) + g(x)`. -/
instance instAdd : Add (WeightedLanguage α κ) where
  add f g := fun x ↦ f x + g x

lemma add_def (f g : WeightedLanguage α κ) : f + g = fun x ↦ f x + g x :=
  rfl

@[simp]
lemma add_apply (f g : WeightedLanguage α κ) (x : List α) : (f + g) x = f x + g x :=
  rfl

lemma add_comm (f g : WeightedLanguage α κ) : f + g = g + f := by
  ext x
  simp [W.add_comm (f _)]

lemma add_assoc (f g h : WeightedLanguage α κ) : (f + g) + h = f + (g + h) := by
  ext x
  simp [W.add_assoc]

@[simp]
lemma zero_add (f : WeightedLanguage α κ) : 0 + f = f := by
  ext x
  simp

@[simp]
lemma add_zero (f : WeightedLanguage α κ) : f + 0 = f := by
  ext x
  simp

end add

section cauchy

variable [W : Semiring κ]

/-- The weighted language [f.cauchy g] represents the multiplication of `f` and `g`.
`(f ×ₗ g)(x) = ∑ f(x₁) × g(x₂)` for all `x₁, x₂` such that `x = x₁ ++ x₂`. -/
def cauchy (f g : WeightedLanguage α κ) : WeightedLanguage α κ :=
  List.sum ∘ (List.map (fun x ↦ f x.1 * g x.2)) ∘ List.splits

@[simp]
lemma zero_cauchy (f : WeightedLanguage α κ) :
    (0 : WeightedLanguage α κ).cauchy f = 0 := by
  ext x
  simp [cauchy]

@[simp]
lemma cauchy_zero (f : WeightedLanguage α κ) : f.cauchy 0 = 0 := by
  ext x
  simp [cauchy]

@[simp]
lemma one_cauchy (f : WeightedLanguage α κ) :
    (1 : WeightedLanguage α κ).cauchy f = f := by
  ext x
  cases x <;>
  simp [cauchy, Function.comp_def, splits, range_succ_eq_map]

@[simp]
lemma cauchy_one (f : WeightedLanguage α κ) :
    f.cauchy (1 : WeightedLanguage α κ) = f := by
  ext x
  have hallzero : ∀ n ∈ range x.length,
      (if 0 < x.length - n then (0 : κ) else f (take n x)) = (0 : κ) := by
    simp only [mem_range, ite_eq_left_iff, not_lt, Nat.le_zero_eq]; omega
  simp [cauchy, Function.comp_def, onlyNil_eq, splits, List.range_add,
    List.map_eq_replicate_iff.mpr hallzero]

lemma cauchy_left_distrib (f g h : WeightedLanguage α κ) :
    f.cauchy (g + h) = f.cauchy g + f.cauchy h := by
  ext x
  simp [cauchy, splits, Function.comp_def, W.left_distrib]

lemma cauchy_right_distrib (f g h : WeightedLanguage α κ) :
    (g + h).cauchy f = g.cauchy f + h.cauchy f := by
  ext x
  simp [cauchy, splits, Function.comp_def, W.right_distrib]

/-- Left-associative cauchy product between three languages. -/
def cauchy₃Left (f g h : WeightedLanguage α κ) : WeightedLanguage α κ :=
  List.sum ∘ (List.map (fun x ↦ (f x.1 * g x.2.1) * h x.2.2)) ∘ List.splits₃Left

lemma cauchy₃Left_eq (f g h : WeightedLanguage α κ) :
    (f.cauchy g).cauchy h = cauchy₃Left f g h := by
  ext x
  simp [cauchy, cauchy₃Left, List.splits₃Left, splits, Function.comp_def,
    ←List.sum_map_mul_right, List.flatMap_def]

/-- Right-associative cauchy product between three languages. -/
def cauchy₃Right (f g h : WeightedLanguage α κ) : WeightedLanguage α κ :=
  List.sum ∘ (List.map (fun x ↦ f x.1 * (g x.2.1 * h x.2.2))) ∘ List.splits₃Right

lemma cauchy₃Right_eq (f g h : WeightedLanguage α κ) :
    f.cauchy (g.cauchy h) = cauchy₃Right f g h := by
  ext x
  simp [cauchy, cauchy₃Right, List.splits₃Right, splits, Function.comp_def,
    ←List.sum_map_mul_left, List.flatMap_def]

lemma cauchy₃LeftRight (f g h : WeightedLanguage α κ) :
    cauchy₃Left f g h = cauchy₃Right f g h := by
  ext l
  simp only [cauchy₃Left, cauchy₃Right, Function.comp_def, W.mul_assoc]
  apply_rules [List.Perm.sum_eq, List.Perm.map, Perm.splits₃LeftRight]

lemma cauchy_assoc (f g h : WeightedLanguage α κ) :
    (f.cauchy g).cauchy h = f.cauchy (g.cauchy h) := by
  rw [cauchy₃Left_eq, cauchy₃LeftRight, cauchy₃Right_eq]

instance instMul : Mul (WeightedLanguage α κ) where
  mul := cauchy

lemma mul_def (f g : WeightedLanguage α κ) : f * g = cauchy f g :=
  rfl

lemma mul_apply (f g : WeightedLanguage α κ) (x : List α) : (f * g) x = f.cauchy g x :=
  rfl

lemma mul_left_distrib (f g h : WeightedLanguage α κ) :
    f * (g + h) = f * g + f * h := by
  simp [mul_def, cauchy_left_distrib]

lemma mul_right_distrib (f g h : WeightedLanguage α κ) :
    (f + g) * h = f * h + g * h := by
  simp [mul_def, cauchy_right_distrib]

lemma mul_assoc (f g h : WeightedLanguage α κ) : (f * g) * h = f * (g * h) := by
  simp [mul_def, cauchy_assoc]

lemma mul_as_sum_over_prod [DecidableEq α] (f g : WeightedLanguage α κ) (x : List α) :
    (f * g) x = ∑ y ∈ x.splits.toFinset, f y.1 * g y.2 := by
  simp [mul_apply, cauchy, List.sum_toFinset _ <| List.Nodup.splits]

@[simp]
lemma mul_apply_nil (f g : WeightedLanguage α κ) : (f * g) [] = f [] * g [] := by
  simp [mul_apply, cauchy]

@[simp]
lemma mul_apply_cons (f g : WeightedLanguage α κ) (a : α) (x : List α) :
    (f * g) (a :: x)
    = f [] * g (a :: x)
    + (f.preimage (a :: ·) * g) x
    := by
  simp [mul_apply, cauchy, Function.comp_def, List.splits_cons]

end cauchy

section comm

variable [W : CommSemiring κ]

lemma cauchy_reverse (f g : WeightedLanguage α κ) :
    (f.cauchy g).reverse = g.reverse.cauchy f.reverse := by
  ext x
  simp [cauchy, reverse, List.splits_reverse, Function.comp_def, W.mul_comm (f _)]

lemma mul_reverse (f g : WeightedLanguage α κ) :
    (f * g).reverse = g.reverse * f.reverse := by
  simp [mul_def, cauchy_reverse]

end comm

section scalar

variable [Mul κ]

/-- `f.hadamard g` represents the Hadamard product of `f` and `g`. -/
def hadamard [Mul κ] (f g : WeightedLanguage α κ) : WeightedLanguage α κ :=
  fun x ↦ f x * g x

@[simp]
lemma hadamard_apply (f g : WeightedLanguage α κ) (x : List α) :
    (f.hadamard g) x = f x * g x := by
  rfl

/-- `w • f` is the left scalar product, assigns `w * f x` for all `x`. -/
instance : SMul κ (WeightedLanguage α κ) where
  smul w f := fun x ↦ w * f x

@[simp]
lemma smul_apply (w : κ) (f : WeightedLanguage α κ) (x : List α) :
    (w • f) x = w * f x :=
  rfl

/-- `scalarRight f w`: is the right scalar product, assigns `f x * w` for all `x`. -/
def scalarRight (f : WeightedLanguage α κ) (w : κ) : WeightedLanguage α κ :=
  fun x ↦ f x * w

@[simp]
lemma scalarRight_apply (f : WeightedLanguage α κ) (w : κ) (x : List α) :
     f.scalarRight w x = f x * w :=
  rfl

end scalar

section natCast

variable [AddCommMonoid κ] [One κ]

/-- `natCast n` assigns a weighted language for `n`. -/
def natCast : ℕ → WeightedLanguage α κ
  | 0 => 0
  | n + 1 => natCast n + 1

instance instNatCast : NatCast (WeightedLanguage α κ) where
  natCast := natCast

lemma natCast_zero (n : ℕ) : (↑ n : WeightedLanguage α κ) = natCast n :=
  rfl

lemma natCast_succ (n : ℕ) : ↑ ((n + 1) : ℕ) = (((↑ n) + 1) : WeightedLanguage α κ) :=
  rfl

end natCast

section npow

variable [Semiring κ]

/-- `npow n f` raises `f` to the `n`th power. -/
def npow (n : ℕ) (f : WeightedLanguage α κ) : WeightedLanguage α κ :=
  match n with
  | 0 => 1
  | n + 1 => npow n f * f

lemma npow_zero (f : WeightedLanguage α κ) : npow 0 f = 1 := by
  simp [npow]

lemma npow_succ (n : ℕ) (f : WeightedLanguage α κ) : npow (n + 1) f = npow n f * f := by
  rw (occs := [1]) [npow]

end npow

instance instSemiring [Semiring κ] : Semiring (WeightedLanguage α κ) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  left_distrib := mul_left_distrib
  right_distrib := mul_right_distrib
  zero_mul := zero_cauchy
  mul_zero := cauchy_zero
  mul_assoc := mul_assoc
  one_mul := one_cauchy
  mul_one := cauchy_one
  nsmul := nsmulRec

end WeightedLanguage
