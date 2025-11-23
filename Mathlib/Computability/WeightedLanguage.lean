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

TODO: fix naming conventions.

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

@[simp]
def preimage (f : WeightedLanguage α κ) (g : List α → List α) : WeightedLanguage α κ :=
  f ∘ g

section zero

variable [Zero κ]

/-- The "zero" element of a weighted language: `0ₗ := x ↦ 0`. -/
instance instZero : Zero (WeightedLanguage α κ) :=
  ⟨fun _ ↦ 0⟩

lemma zero_def_eq : (0 : WeightedLanguage α κ) = fun (_ : List α) ↦ (0 : κ) :=
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

lemma one_def_eq : (1 : WeightedLanguage α κ) = onlyNil :=
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

/-- The weighted language [f.add_def g] assigns the pointwise sum `f x + g x` for all strings `x`.
`(f +ₗ g)(x) = f(x) + g(x)`. -/
def add_def (f g : WeightedLanguage α κ) : WeightedLanguage α κ :=
  fun x ↦ f x + g x

instance instAdd : Add (WeightedLanguage α κ) where
  add := add_def

lemma add_def_eq (f g : WeightedLanguage α κ) : f + g = add_def f g :=
  rfl

@[simp]
lemma add_apply (f g : WeightedLanguage α κ) (x : List α) : (f + g) x = f x + g x :=
  rfl

lemma add_def_comm (f g : WeightedLanguage α κ) : f + g = g + f := by
  simp only [add_def_eq]
  ext x
  apply W.add_comm

lemma add_def_assoc (f g h : WeightedLanguage α κ) : (f + g) + h = f + (g + h) := by
  ext x
  simp [W.add_assoc]

@[simp]
lemma zero_add_def (f : WeightedLanguage α κ) : 0 + f = f := by
  ext x
  simp

@[simp]
lemma add_def_zero (f : WeightedLanguage α κ) : f + 0 = f := by
  ext x
  simp

end add

section cauchy

variable [W : Semiring κ]

/-- The weighted language [f.cauchy_prod g] represents the multiplication of `f` and `g`.
`(f ×ₗ g)(x) = ∑ f(x₁) × g(x₂)` for all `x₁, x₂` such that `x = x₁ ++ x₂`. -/
def cauchy_prod (f g : WeightedLanguage α κ) : WeightedLanguage α κ :=
  List.sum ∘ (List.map (fun x ↦ f x.1 * g x.2)) ∘ List.splits

@[simp]
lemma zero_cauchy_prod (f : WeightedLanguage α κ) :
    (0 : WeightedLanguage α κ).cauchy_prod f = 0 := by
  ext x
  simp [cauchy_prod]

@[simp]
lemma cauchy_prod_zero (f : WeightedLanguage α κ) : f.cauchy_prod 0 = 0 := by
  ext x
  simp [cauchy_prod]

@[simp]
lemma one_cauchy_prod (f : WeightedLanguage α κ) :
    (1 : WeightedLanguage α κ).cauchy_prod f = f := by
  ext x
  cases x <;>
  simp [cauchy_prod, Function.comp_def, splits, range_succ_eq_map]

@[simp]
lemma cauchy_prod_one (f : WeightedLanguage α κ) :
    f.cauchy_prod (1 : WeightedLanguage α κ) = f := by
  ext x
  have hallzero : ∀ n ∈ range x.length,
      (if 0 < x.length - n then (0 : κ) else f (take n x)) = (0 : κ) := by
    simp only [mem_range, ite_eq_left_iff, not_lt, Nat.le_zero_eq]; omega
  simp [cauchy_prod, Function.comp_def, onlyNil_eq, splits, List.range_add,
    List.map_eq_replicate_iff.mpr hallzero]

lemma cauchy_prod_left_distrib (f g h : WeightedLanguage α κ) :
    f.cauchy_prod (g + h) = f.cauchy_prod g + f.cauchy_prod h := by
  ext x
  simp [cauchy_prod, splits, Function.comp_def, W.left_distrib]

lemma cauchy_prod_right_distrib (f g h : WeightedLanguage α κ) :
    (g + h).cauchy_prod f = g.cauchy_prod f + h.cauchy_prod f := by
  ext x
  simp [cauchy_prod, splits, Function.comp_def, W.right_distrib]

/-- Left-associative cauchy product between three languages. -/
def cauchy_prod₃_left (f g h : WeightedLanguage α κ) : WeightedLanguage α κ :=
  List.sum ∘ (List.map (fun x ↦ (f x.1 * g x.2.1) * h x.2.2)) ∘ List.splits₃_left

lemma cauchy_prod₃_left_eq (f g h : WeightedLanguage α κ) :
    (f.cauchy_prod g).cauchy_prod h = cauchy_prod₃_left f g h := by
  ext x
  simp [cauchy_prod, cauchy_prod₃_left, List.splits₃_left, splits, Function.comp_def,
    ←List.sum_map_mul_right, List.flatMap_def]

/-- Right-associative cauchy product between three languages. -/
def cauchy_prod₃_right (f g h : WeightedLanguage α κ) : WeightedLanguage α κ :=
  List.sum ∘ (List.map (fun x ↦ f x.1 * (g x.2.1 * h x.2.2))) ∘ List.splits₃_right

lemma cauchy_prod₃_right_eq (f g h : WeightedLanguage α κ) :
    f.cauchy_prod (g.cauchy_prod h) = cauchy_prod₃_right f g h := by
  ext x
  simp [cauchy_prod, cauchy_prod₃_right, List.splits₃_right, splits, Function.comp_def,
    ←List.sum_map_mul_left, List.flatMap_def]

lemma cauchy_prod₃_left_right (f g h : WeightedLanguage α κ) :
    cauchy_prod₃_left f g h = cauchy_prod₃_right f g h := by
  ext l
  simp only [cauchy_prod₃_left, cauchy_prod₃_right, Function.comp_def, W.mul_assoc]
  apply_rules [List.Perm.sum_eq, List.Perm.map, Perm.splits₃_left_right_perm]

lemma cauchy_prod_assoc (f g h : WeightedLanguage α κ) :
    (f.cauchy_prod g).cauchy_prod h = f.cauchy_prod (g.cauchy_prod h) := by
  rw [cauchy_prod₃_left_eq, cauchy_prod₃_left_right, cauchy_prod₃_right_eq]

instance instMul : Mul (WeightedLanguage α κ) where
  mul := cauchy_prod

lemma mul_def_eq (f g : WeightedLanguage α κ) : f * g = cauchy_prod f g :=
  rfl

lemma mul_apply (f g : WeightedLanguage α κ) (x : List α) : (f * g) x = f.cauchy_prod g x :=
  rfl

lemma mul_def_left_distrib (f g h : WeightedLanguage α κ) :
    f * (g + h) = f * g + f * h := by
  simp [mul_def_eq, cauchy_prod_left_distrib]

lemma mul_def_right_distrib (f g h : WeightedLanguage α κ) :
    (f + g) * h = f * h + g * h := by
  simp [mul_def_eq, cauchy_prod_right_distrib]

lemma mul_def_assoc (f g h : WeightedLanguage α κ) : (f * g) * h = f * (g * h) := by
  simp [mul_def_eq, cauchy_prod_assoc]

lemma mul_as_sum_over_prod [DecidableEq α] (f g : WeightedLanguage α κ) (x : List α) :
    (f * g) x = ∑ y ∈ x.splits.toFinset, f y.1 * g y.2 := by
  simp [mul_apply, cauchy_prod, List.sum_toFinset _ <| List.Nodup.splits_nodup x]

@[simp]
lemma mul_apply_nil (f g : WeightedLanguage α κ) : (f * g) [] = f [] * g [] := by
  simp [mul_apply, cauchy_prod]

@[simp]
lemma mul_apply_cons (f g : WeightedLanguage α κ) (a : α) (x : List α) :
    (f * g) (a :: x)
    = f [] * g (a :: x)
    + (f.preimage (a :: ·) * g) x
    := by
  simp [mul_apply, cauchy_prod, Function.comp_def]

end cauchy

section scalar

variable [Mul κ]

/-- `f.pointwise_prod g` represents the Hadmard product of `f` and `g`. -/
def pointwise_prod [Mul κ] (f g : WeightedLanguage α κ) : WeightedLanguage α κ :=
  fun x ↦ f x * g x

@[simp]
lemma pointwise_prod_apply (f g : WeightedLanguage α κ) (x : List α) :
    (f.pointwise_prod g) x = f x * g x := by
  rfl

/-- `scalar_prodl w f` assigns `w * f x` for all `x`. -/
def scalar_prodl (w : κ) (f : WeightedLanguage α κ) : WeightedLanguage α κ :=
  fun x ↦ w * f x

@[simp]
lemma scalar_prodl_apply (w : κ) (f : WeightedLanguage α κ) (x : List α) :
    scalar_prodl w f x = w * f x :=
  rfl

/-- `scalar_prodr f w` assigns `f x * w` for all `x`. -/
def scalar_prodr (f : WeightedLanguage α κ) (w : κ) : WeightedLanguage α κ :=
  fun x ↦ f x * w

@[simp]
lemma scalar_prodr_apply (f : WeightedLanguage α κ) (w : κ) (x : List α) :
     f.scalar_prodr w x = f x * w :=
  rfl

end scalar

/-- `(x, w) ∈ f` when `f x = w`. -/
def mem_def (f : WeightedLanguage α κ) (xw : List α × κ) : Prop :=
  f xw.1 = xw.2

instance instMem : Membership (List α × κ) (WeightedLanguage α κ) where
  mem := mem_def

section natCast

variable [AddCommMonoid κ] [One κ]

/-- `natCast_def n` assigns a weighted language for `n`. -/
def natCast_def : ℕ → WeightedLanguage α κ
  | 0 => 0
  | n + 1 => natCast_def n + 1

instance instNatCast : NatCast (WeightedLanguage α κ) where
  natCast := natCast_def

lemma natCast_def_eq (n : ℕ) : (↑ n : WeightedLanguage α κ) = natCast_def n :=
  rfl

lemma natCast_def_succ (n : ℕ) : ↑ ((n + 1) : ℕ) = (((↑ n) + 1) : WeightedLanguage α κ) := by
  simp [natCast_def_eq, add_def_eq, one_def_eq, natCast_def, add_def_eq, one_def_eq]

end natCast

section npow

variable [Semiring κ]

/-- `npow_def n f` raises `f` to the `n`th power. -/
def npow_def (n : ℕ) (f : WeightedLanguage α κ) : WeightedLanguage α κ :=
  match n with
  | 0 => 1
  | n + 1 => npow_def n f * f

lemma npow_def_zero (f : WeightedLanguage α κ) : npow_def 0 f = 1 := by
  simp [npow_def]

lemma npow_def_succ (n : ℕ) (f : WeightedLanguage α κ) : npow_def (n + 1) f = npow_def n f * f := by
  rw (occs := [1]) [npow_def]

end npow

section nsmul

variable [AddCommMonoid κ]

/-- `nsmul_def n f` adds `f` with itself `n` times. -/
def nsmul_def (n : ℕ) (f : WeightedLanguage α κ) :=
  match n with
  | 0 => 0
  | n + 1 => nsmul_def n f + f

lemma nsmul_def_zero (f : WeightedLanguage α κ) : nsmul_def 0 f = 0 := by
  simp [nsmul_def]

lemma nsmul_def_succ (n : ℕ) (f : WeightedLanguage α κ) :
    nsmul_def (n + 1) f = nsmul_def n f + f := by
  rw (occs := [1]) [nsmul_def]

end nsmul

instance instSemiring [Semiring κ] : Semiring (WeightedLanguage α κ) where
  add_assoc := add_def_assoc
  zero_add := zero_add_def
  add_zero := add_def_zero
  add_comm := add_def_comm
  left_distrib := mul_def_left_distrib
  right_distrib := mul_def_right_distrib
  zero_mul := zero_cauchy_prod
  mul_zero := cauchy_prod_zero
  mul_assoc := mul_def_assoc
  one_mul := one_cauchy_prod
  mul_one := cauchy_prod_one
  nsmul := nsmul_def

end WeightedLanguage
