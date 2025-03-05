/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
import Mathlib.Computability.Language
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# Weighted Paths

TODO: explain stuff.
-/

universe k u v

open Computability

/-- A weighted path (`π`) represents a list of transitions in a FSM.
-/
inductive Path (α : Type u) (κ : Type k) {σ : Type v} : σ → σ → Type (max u v k) where
  | last (s : σ) : Path α κ s s
  | arc (s₁ s₂ s₃ : σ) (a : α) (w : κ) (π : Path α κ s₂ s₃) : Path α κ s₁ s₃

namespace Path

variable {α : Type u} {σ : Type v} {κ : Type k}

@[simp]
def length {s₁ s₃ : σ} : Path α κ s₁ s₃ → Nat
  | last _ => 0
  | arc _ _ _ _ _ π => 1 + π.length

@[simp]
def concat {s₁ s₂ s₃ : σ} : Path α κ s₁ s₂ → Path α κ s₂ s₃ → Path α κ s₁ s₃
  | last _, π₂ => π₂
  | arc s₁ s s₂ a w π₁, π₂ => arc s₁ s s₃ a w (π₁.concat π₂)

@[simp]
def reverse {s₁ s₃ : σ} : Path α κ s₁ s₃ → Path α κ s₃ s₁
  | last _ => last _
  | arc s₁ s₂ s₃ a w π => concat π.reverse (arc s₂ s₁ s₁ a w (last s₁))

@[simp]
def string {s₁ s₃ : σ} : Path α κ s₁ s₃ → List α
  | last _ => []
  | arc _ _ _ a _ π => a :: π.string

lemma concat_assoc {s₁ s₂ s₃ s₄ : σ}
  (π₁ : Path α κ s₁ s₂) (π₂ : Path α κ s₂ s₃) (π₃ : Path α κ s₃ s₄) :
  (π₁.concat π₂).concat π₃ = π₁.concat (π₂.concat π₃) := by
  revert s₃ s₄ π₂ π₃
  induction π₁ <;> intros s₃ s₄ π₂ π₃
  case last _ =>
    simp
  case arc _ s _ a w π₁ ih =>
    simp [ih]

lemma concat_last {s₁ s₃ : σ} (π : Path α κ s₁ s₃) :
  π.concat (last _) = π := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [ih]

lemma length_concat {s₁ s₂ s₃ : σ} (π₁ : Path α κ s₁ s₂) (π₂ : Path α κ s₂ s₃) :
  (π₁.concat π₂).length = π₁.length + π₂.length := by
  revert π₂
  induction π₁ <;> intro π₂
  case last _ =>
    simp
  case arc _ s _ a w π₁ ih =>
    simp [ih]
    ring

lemma length_reverse {s₁ s₃ : σ} (π : Path α κ s₁ s₃) :
  π.reverse.length = π.length := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [length_concat, ih]
    ring

lemma reverse_concat {s₁ s₂ s₃ : σ} (π₁ : Path α κ s₁ s₂) (π₂ : Path α κ s₂ s₃) :
  (π₁.concat π₂).reverse = π₂.reverse.concat π₁.reverse := by
  revert s₃ π₂
  induction π₁ <;> intros s₃ π₂
  case last _ =>
    simp [concat_last]
  case arc _ s _ a w π₁ ih =>
    simp [ih, concat_assoc]

lemma reverse_involutive {s₁ s₃ : σ} (π : Path α κ s₁ s₃) :
  π.reverse.reverse = π := by
  induction π
  case last _ =>
    simp
  case arc s1 s₂ s3 a w π ih =>
    simp
    have h : arc s₂ s1 _ a w (last _) = (arc s1 _ s₂ a w (last _)).reverse := by simp
    rw [h]
    simp [reverse_concat, ih]

lemma string_concat {s₁ s₂ s₃ : σ} (π₁ : Path α κ s₁ s₂) (π₂ : Path α κ s₂ s₃) :
  (π₁.concat π₂).string = π₁.string ++ π₂.string := by
  revert π₂
  induction π₁ <;> intros π₂
  case last _ =>
    simp
  case arc _ s _ a w ih =>
    simp [ih]

lemma string_reverse {s₁ s₃ : σ} (π : Path α κ s₁ s₃) :
  π.reverse.string = π.string.reverse := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [string_concat, ih]

@[simp]
def innerWeight [W : Semiring κ] {s₁ s₃ : σ} : Path α κ s₁ s₃ → κ
  | last _ => 1
  | arc _ _ _ _ w π => w * π.innerWeight

lemma innerWeight_concat [W : Semiring κ] {s₁ s₂ s₃ : σ}
  (π₁ : Path α κ s₁ s₂) (π₂ : Path α κ s₂ s₃) :
  (π₁.concat π₂).innerWeight = π₁.innerWeight * π₂.innerWeight := by
  revert π₂
  induction π₁ <;> intro π₂
  case last _ =>
    simp
  case arc _ s _ a w π₁ ih =>
    simp [ih, W.mul_assoc]

lemma innerWeight_reverse [W : CommSemiring κ] {s₁ s₃ : σ} (π : Path α κ s₁ s₃) :
  π.reverse.innerWeight = π.innerWeight := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [innerWeight_concat, ih, W.mul_comm]

section foldr

universe b

variable {β : Type b} (f : σ → α → κ → σ → β → β) (init : β)

@[simp]
def foldr {s₁ s₃ : σ} : Path α κ s₁ s₃ → β
  | last _ => init
  | arc _ s₂ _ a w π => f s₁ a w s₂ π.foldr

end foldr

lemma foldr_length {s₁ s₃ : σ} (π : Path α κ s₁ s₃) :
  foldr (fun _ _ _ _ ↦ Nat.succ) 0 π = π.length := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [ih]
    ring

lemma foldr_string {s₁ s₃ : σ} (π : Path α κ s₁ s₃) :
  foldr (fun _ a _ _ ↦ List.cons a) [] π = π.string := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [ih]

lemma foldr_innerWeight [W : Semiring κ] {s₁ s₃ : σ} (π : Path α κ s₁ s₃) :
  foldr (fun _ _ w _ ↦ W.mul w) 1 π = π.innerWeight := by
  induction π
  case last _ =>
    simp
  case arc _ s₂ _ a w π ih =>
    simp [ih]
    rfl

end Path
