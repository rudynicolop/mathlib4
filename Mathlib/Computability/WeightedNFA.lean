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
  fun x ↦ ∑ sw ∈ M.evalFrom S x, sw.2 * M.final sw.1

@[simp]
theorem acceptsFrom_nil (S : Finset (σ × κ)) :
    M.acceptsFrom S [] = ∑ sw ∈ S, sw.2 * M.final sw.1 :=
  rfl

@[simp]
theorem acceptsFrom_cons (S : Finset (σ × κ)) (a : α) (x : List α) :
    M.acceptsFrom S (a :: x) = M.acceptsFrom (M.stepSet S a) x := rfl

def accepts : WeightedLanguage α κ := M.acceptsFrom M.start

end basic

section union

variable {σ1 σ2 : Type v}

def embed_prodl : σ1 × κ ↪ (σ1 ⊕ σ2) × κ :=
  open Function.Embedding in prodMap inl (Function.Embedding.refl κ)

def embed_prodr : σ2 × κ ↪ (σ1 ⊕ σ2) × κ :=
  open Function.Embedding in prodMap inr (Function.Embedding.refl κ)

lemma disjoint_injlr {S1 : Finset (σ1 × κ)} {S2 : Finset (σ2 × κ)} :
    Disjoint (Finset.map embed_prodl S1) (Finset.map embed_prodr S2) := by
  simp [←Finset.disjoint_val, Multiset.disjoint_map_map]
  simp [embed_prodl, embed_prodr]

variable [DecidableEq σ1] [DecidableEq σ2] [DecidableEq κ]

@[simp]
def union_start (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) : Finset ((σ1 ⊕ σ2) × κ) :=
  (Finset.map embed_prodl M1.start) ∪ (Finset.map embed_prodr M2.start)

@[simp]
def union_final (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) (s : σ1 ⊕ σ2) : κ :=
  s.casesOn M1.final M2.final

@[simp]
def union_step (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ)
  (s : σ1 ⊕ σ2) (a : α) : Finset ((σ1 ⊕ σ2) × κ) :=
  s.casesOn
    (fun s1 ↦ Finset.map embed_prodl (M1.step s1 a))
    (fun s2 ↦ Finset.map embed_prodr (M2.step s2 a))

def union (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) : WNFA α (σ1 ⊕ σ2) κ where
  step := union_step M1 M2
  start := union_start M1 M2
  final := union_final M1 M2

instance : HAdd (WNFA α σ1 κ) (WNFA α σ2 κ) (WNFA α (σ1 ⊕ σ2) κ) :=
  ⟨union⟩

lemma union_eq_hadd {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
    M1 + M2 = M1.union M2 := rfl

@[simp]
lemma union_start_proj {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
    (M1 + M2).start = M1.union_start M2 := rfl

@[simp]
lemma union_final_proj {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
    (M1 + M2).final = M1.union_final M2 := rfl

@[simp]
lemma union_step_proj {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
    (M1 + M2).step = M1.union_step M2 := rfl

variable [W : Semiring κ]

lemma acceptsFrom_union {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ}
  {S1 : Finset (σ1 × κ)} {S2 : Finset (σ2 × κ)} :
    (M1 + M2).acceptsFrom ((Finset.map embed_prodl S1) ∪ (Finset.map embed_prodr S2))
    = M1.acceptsFrom S1 + M2.acceptsFrom S2 := by
  funext x
  induction x generalizing S1 S2
  case nil =>
    simp [WeightedLanguage.add_def_eq, WeightedLanguage.add_def]
    simp [Finset.sum_union disjoint_injlr]
    congr
  case cons a x ih =>
    simp [WeightedLanguage.add_def_eq, WeightedLanguage.add_def] at *
    simp [←ih]
    clear ih
    congr 1
    simp [stepSet, Finset.map_eq_image, Finset.biUnion_image]
    simp [Finset.image_image]
    apply Finset.ext
    rintro ⟨s1' | s2', w⟩ <;> simp [embed_prodl, embed_prodr]

lemma accepts_union {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
    (M1 + M2).accepts = M1.accepts + M2.accepts := by
  simp [accepts, acceptsFrom_union]

end union

end WNFA
