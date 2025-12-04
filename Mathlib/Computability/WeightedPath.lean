/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Weighted Paths

A path `π` is a finite sequence of transitions/arcs in a state machine. This file defines weighted
paths for weighted finite state machines (FSMs). A transition in a weighted state machine is
comprised of the incoming state `s₁ ∈ σ`, a character `a ∈ α`, a weight `w ∈ κ`, and the outgoing
state `s₂ ∈ σ`.

## Implementation details

`WPath α κ s₁ s₂` is a dependent type representing paths from `s₁ ∈ σ` to `s₂ ∈ σ`. The
indices ensure that the other constructions and operations (concatenation, reversal, etc.) are still
valid paths.

## References

* [Advanced Formal Language Theory: Regular Languages][weighted-regular-languages]
* [Handbook of Weighted Automata][Handbook-of-Weighted-Automata]
-/

@[expose] public section

universe k u v

/-- A weighted path `π : WPath α κ s₁ s₂` represents a sequence of transitions in a weighted
FSM starting from `s₁ ∈ σ` ending at `s₂ ∈ σ`. -/
inductive WPath (α : Type u) (κ : Type k) {σ : Type v} : σ → σ → Type (max u v k) where
  | nil (s : σ) : WPath α κ s s
  | cons (s₁ : σ) {s₂ s₃ : σ} (a : α) (w : κ) (π : WPath α κ s₂ s₃) : WPath α κ s₁ s₃

namespace WPath

variable {α : Type u} {σ : Type v} {κ : Type k}

/-- `π.length` is the number of transitions in `π`. -/
@[simp]
def length {s₁ s₃ : σ} : WPath α κ s₁ s₃ → Nat
  | nil _ => 0
  | cons _ _ _ π => 1 + π.length

/-- `π₁.concat π₂` is the sequence of transitions in `π₁` concatenated with `π₂`. -/
protected def concat {s₁ s₂ s₃ : σ} :
    WPath α κ s₁ s₂ → WPath α κ s₂ s₃ → WPath α κ s₁ s₃
  | nil _, π₂ => π₂
  | cons s₁ a w π₁, π₂ => cons s₁ a w (π₁.concat π₂)

instance {s₁ s₂ s₃ : σ} :
    HAppend (WPath α κ s₁ s₂) (WPath α κ s₂ s₃) (WPath α κ s₁ s₃) where
  hAppend := WPath.concat

lemma append_def {s₁ s₂ s₃ : σ} {π₁ : WPath α κ s₁ s₂} {π₂ : WPath α κ s₂ s₃} :
    π₁ ++ π₂ = π₁.concat π₂ :=
  rfl

@[simp]
lemma nil_append {s₁ s₂ : σ} {π : WPath α κ s₁ s₂} : nil (α:=α) (κ:=κ) s₁ ++ π = π :=
  rfl

@[simp]
lemma cons_append {s₁ s₂ s₃ s₄ : σ} {a : α} {w : κ} {π₁ : WPath α κ s₂ s₃} {π₂ : WPath α κ s₃ s₄} :
    cons s₁ a w π₁ ++ π₂ = cons s₁ a w (π₁ ++ π₂) :=
  rfl

/-- `π.reverse` reverses the sequence of transitions in `π`. -/
@[simp]
def reverse {s₁ s₃ : σ} : WPath α κ s₁ s₃ → WPath α κ s₃ s₁
  | nil _ => nil _
  | cons s₁ (s₂:=s₂) a w π => π.reverse ++ (cons s₂ a w (nil s₁))

/-- `π.yield` computes the string of the path `π`. -/
@[simp]
def yield {s₁ s₃ : σ} : WPath α κ s₁ s₃ → List α
  | nil _ => []
  | cons _ a _ π => a :: π.yield

lemma append_assoc {s₁ s₂ s₃ s₄ : σ}
  (π₁ : WPath α κ s₁ s₂) (π₂ : WPath α κ s₂ s₃) (π₃ : WPath α κ s₃ s₄) :
    (π₁ ++ π₂) ++ π₃ = π₁ ++ (π₂ ++ π₃) := by
  induction π₁
  case nil _ =>
    simp
  case cons s a w π₁ ih =>
    simp [ih]

lemma append_nil {s₁ s₃ : σ} (π : WPath α κ s₁ s₃) : π ++ (nil (α:=α) (κ:=κ) s₃) = π := by
  induction π
  case nil _ =>
    simp
  case cons _ a w π ih =>
    simp [ih]

lemma length_append {s₁ s₂ s₃ : σ} (π₁ : WPath α κ s₁ s₂) (π₂ : WPath α κ s₂ s₃) :
    (π₁ ++ π₂).length = π₁.length + π₂.length := by
  revert π₂
  induction π₁ <;> intro π₂
  case nil _ =>
    simp
  case cons s a w π₁ ih =>
    simp [ih, Nat.add_assoc]

lemma length_reverse {s₁ s₃ : σ} (π : WPath α κ s₁ s₃) : π.reverse.length = π.length := by
  induction π
  case nil _ =>
    simp
  case cons _ s₂ _ a w π ih =>
    simp [length_append, ih, Nat.add_comm 1]

lemma reverse_append {s₁ s₂ s₃ : σ} (π₁ : WPath α κ s₁ s₂) (π₂ : WPath α κ s₂ s₃) :
    (π₁ ++ π₂).reverse = π₂.reverse ++ π₁.reverse := by
  induction π₁
  case nil _ =>
    simp [append_nil]
  case cons s a w π₁ ih =>
    simp [ih, append_assoc]

lemma reverse_involutive {s₁ s₃ : σ} (π : WPath α κ s₁ s₃) : π.reverse.reverse = π := by
  induction π
  case nil _ =>
    simp
  case cons s1 a w π ih =>
    simp [reverse_append, ih]

lemma yield_append {s₁ s₂ s₃ : σ} (π₁ : WPath α κ s₁ s₂) (π₂ : WPath α κ s₂ s₃) :
    (π₁ ++ π₂).yield = π₁.yield ++ π₂.yield := by
  induction π₁
  case nil _ =>
    simp
  case cons s a w ih =>
    simp [ih]

lemma yield_reverse {s₁ s₃ : σ} (π : WPath α κ s₁ s₃) :
    π.reverse.yield = π.yield.reverse := by
  induction π
  case nil _ =>
    simp
  case cons _ a w π ih =>
    simp [yield_append, ih]

/-- `π.innerWeight` multiplies the weights in order of all transitions in `π`. -/
@[simp]
def innerWeight [W : Monoid κ] {s₁ s₃ : σ} : WPath α κ s₁ s₃ → κ
  | nil _ => 1
  | cons _ _ w π => w * π.innerWeight

lemma innerWeight_append [W : Monoid κ] {s₁ s₂ s₃ : σ}
  (π₁ : WPath α κ s₁ s₂) (π₂ : WPath α κ s₂ s₃) :
    (π₁ ++ π₂).innerWeight = π₁.innerWeight * π₂.innerWeight := by
  induction π₁
  case nil _ =>
    simp
  case cons _ a w π₁ ih =>
    simp [ih, W.mul_assoc]

lemma innerWeight_reverse [W : CommMonoid κ] {s₁ s₃ : σ} (π : WPath α κ s₁ s₃) :
    π.reverse.innerWeight = π.innerWeight := by
  induction π
  case nil _ =>
    simp
  case cons _ a w π ih =>
    simp [innerWeight_append, ih, W.mul_comm]

section foldr

universe b

variable {β : Type b} (f : σ → α → κ → σ → β → β) (init : β)

/-- `foldr f init π` folds `f` over `π` right-associatively. -/
@[simp]
def foldr {s₁ s₃ : σ} : WPath α κ s₁ s₃ → β
  | nil _ => init
  | cons _ (s₂:=s₂) a w π => f s₁ a w s₂ π.foldr

end foldr

lemma foldr_length {s₁ s₃ : σ} (π : WPath α κ s₁ s₃) :
    foldr (fun _ _ _ _ ↦ Nat.succ) 0 π = π.length := by
  induction π
  case nil _ =>
    simp
  case cons _ s₂ _ a w π ih =>
    simp [ih, Nat.add_comm 1]

lemma foldr_yield {s₁ s₃ : σ} (π : WPath α κ s₁ s₃) :
    foldr (fun _ a _ _ ↦ List.cons a) [] π = π.yield := by
  induction π
  case nil _ =>
    simp
  case cons _ s₂ _ a w π ih =>
    simp [ih]

lemma foldr_innerWeight [W : Monoid κ] {s₁ s₃ : σ} (π : WPath α κ s₁ s₃) :
    foldr (fun _ _ w _ ↦ W.mul w) 1 π = π.innerWeight := by
  induction π
  case nil _ =>
    simp
  case cons _ s₂ _ a w π ih =>
    simp [ih, (· * ·)]

section All

variable (P : σ → α → κ → σ → Prop)

/-- `All P π` holds when `P` holds for every transition in `π`. -/
@[simp]
def All {s₁ s₂ : σ} : WPath α κ s₁ s₂ → Prop
  | nil _ => True
  | cons s₁ (s₂:=s₂) a w π => P s₁ a w s₂ ∧ All π

end All

section AllLemmas

variable (P : σ → α → κ → σ → Prop)

lemma All_append {s₁ s₂ s₃ : σ}
  (π₁ : WPath α κ s₁ s₂) (π₂ : WPath α κ s₂ s₃) :
    All P (π₁ ++ π₂) ↔ All P π₁ ∧ All P π₂ := by
  induction π₁
  case nil _ =>
    simp
  case cons _ a w π₁ ih =>
    simp [ih, and_assoc]

lemma All_reverse {s₁ s₂ : σ} (π : WPath α κ s₁ s₂) :
    All P π.reverse ↔ All (fun s₂ a w s₁ => P s₁ a w s₂) π := by
  induction π
  case nil _ =>
    simp
  case cons _ a w π ih =>
    simp [All_append, ih, and_comm]

end AllLemmas

end WPath
