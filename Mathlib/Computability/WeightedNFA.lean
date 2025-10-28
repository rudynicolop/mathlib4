/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
import Mathlib.Computability.WeightedDFA
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Weighted Nondeterministic Finite Automata

TODO
-/

universe u v k

structure WNFA (α : Type u) (σ : Type v) (κ : Type k) where
  /-- The NFA's transition function -/
  step : σ → α → Finset (σ × κ)
  /-- Initial weights. -/
  start : Finset (σ × κ)
  /-- Final weights. -/
  final : σ → κ

namespace WNFA

variable {α : Type u} {κ : Type k}

section basic

variable {σ : Type v} [W : Semiring κ]

instance : Inhabited (WNFA α σ κ) :=
  ⟨WNFA.mk (fun _ _ ↦ ∅) ∅ (fun _ ↦ 0)⟩

variable (M : WNFA α σ κ)

-- `Finset.image` requies this.
variable [DecidableEq σ] [DecidableEq κ]

def stepSet (S : Finset (σ × κ)) (a : α) : Finset (σ × κ) :=
  S.biUnion (fun sw ↦ Finset.image (Prod.map id (sw.2 * ·)) (M.step sw.1 a))

theorem mem_stepSet {sw : σ × κ} {S : Finset (σ × κ)} {a : α} :
    sw ∈ M.stepSet S a ↔ ∃ tw ∈ S, sw ∈ Finset.image (Prod.map id (tw.2 * ·)) (M.step tw.1 a) := by
  simp [stepSet]

@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp [stepSet]

@[simp]
theorem stepSet_singleton (sw : σ × κ) (a : α) :
    M.stepSet {sw} a = Finset.image (Prod.map id (sw.2 * ·)) (M.step sw.1 a) := by
  simp [stepSet]

def evalFrom (S : Finset (σ × κ)) : List α → Finset (σ × κ) :=
  List.foldl M.stepSet S

@[simp]
theorem evalFrom_nil (S : Finset (σ × κ)) : M.evalFrom S [] = S :=
  rfl

@[simp]
theorem evalFrom_singleton (S : Finset (σ × κ)) (a : α) : M.evalFrom S [a] = M.stepSet S a :=
  rfl

@[simp]
theorem evalFrom_cons (S : Finset (σ × κ)) (a : α) (x : List α) :
    M.evalFrom S (a :: x) = M.evalFrom (M.stepSet S a) x :=
  rfl

theorem evalFrom_append_singleton (S : Finset (σ × κ)) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem evalFrom_append (S : Finset (σ × κ)) (x y : List α) :
    M.evalFrom S (x ++ y) = M.evalFrom (M.evalFrom S x) y := by
  simp only [evalFrom, List.foldl_append]

def eval : List α → Finset (σ × κ) :=
  M.evalFrom M.start

@[simp]
theorem eval_nil : M.eval [] = M.start :=
  rfl

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet M.start a :=
  rfl

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton ..

def acceptsFrom (S : Finset (σ × κ)) : WeightedLanguage α κ :=
  fun x ↦ ∑ sw ∈ M.evalFrom S x, sw.2

def accepts : WeightedLanguage α κ := M.acceptsFrom M.start

end basic

end WNFA
