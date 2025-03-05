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
def rev {s₁ s₃ : σ} : Path α κ s₁ s₃ → Path α κ s₃ s₁
  | last _ => last _
  | arc s₁ s₂ s₃ a w π => concat π.rev (arc s₂ s₁ s₁ a w (last s₁))

lemma length_concat {s₁ s₂ s₃ : σ} (π₁ : Path α κ s₁ s₂) (π₂ : Path α κ s₂ s₃) :
  (π₁.concat π₂).length = π₁.length + π₂.length := by
  revert π₂
  induction π₁ <;> intro π₂
  case last _ =>
    simp
  case arc _ s _ a w π₁ ih =>
    simp [ih]
    ring

section weight

variable [W : Semiring κ]

@[simp]
def innerWeight {s₁ s₃ : σ} : Path α κ s₁ s₃ → κ
  | last _ => 1
  | arc _ _ _ _ w π => w * π.innerWeight

lemma innerWeight_concat {s₁ s₂ s₃ : σ} (π₁ : Path α κ s₁ s₂) (π₂ : Path α κ s₂ s₃) :
  (π₁.concat π₂).innerWeight = π₁.innerWeight * π₂.innerWeight := by
  revert π₂
  induction π₁ <;> intro π₂
  case last _ =>
    simp
  case arc _ s _ a w π₁ ih =>
    simp [ih, W.mul_assoc]

end weight

end Path
