/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
import Mathlib.Computability.NFA
import Mathlib.Computability.WeightedDFA
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Functor
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Notation

/-!
# Weighted Nondeterministic Finite Automata

TODO
-/

section helper

universe u v

variable {α : Type u} {β : Type v}

lemma distr_fun_ite (c : Prop) [Decidable c] (f : α → β) (t e : α) :
    f (if c then t else e) = if c then f t else f e := by
  by_cases h : c
  · simp [if_pos h]
  · simp [if_neg h]

end helper

universe u v k

structure WNFA (α : Type u) (σ : Type v) (κ : Type k) where
  /-- The NFA's transition function -/
  step : σ → α → Multiset (σ × κ)
  /-- Initial weights. -/
  start : Multiset (σ × κ)
  /-- Final weights. -/
  final : σ → κ

namespace WNFA

variable {α : Type u}

section basic

variable {κ : Type k} {σ : Type v} [W : Semiring κ]

instance : Inhabited (WNFA α σ κ) :=
  ⟨WNFA.mk (fun _ _ ↦ ∅) ∅ (fun _ ↦ 0)⟩

variable (M : WNFA α σ κ)

def stepSet (S : Multiset (σ × κ)) (a : α) : Multiset (σ × κ) :=
  S.bind (fun sw ↦ (Prod.map id (sw.2 * ·)) <$> (M.step sw.1 a))

theorem mem_stepSet {sw : σ × κ} {S : Multiset (σ × κ)} {a : α} :
    sw ∈ M.stepSet S a ↔ ∃ tw ∈ S, sw ∈ (Prod.map id (tw.2 * ·)) <$> (M.step tw.1 a) := by
  simp [stepSet]

@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp [stepSet]

@[simp]
theorem stepSet_singleton (sw : σ × κ) (a : α) :
    M.stepSet {sw} a = (Prod.map id (sw.2 * ·)) <$> (M.step sw.1 a) := by
  simp [stepSet]

def evalFrom (S : Multiset (σ × κ)) : List α → Multiset (σ × κ) :=
  List.foldl M.stepSet S

@[simp]
theorem evalFrom_nil (S : Multiset (σ × κ)) : M.evalFrom S [] = S :=
  rfl

@[simp]
theorem evalFrom_singleton (S : Multiset (σ × κ)) (a : α) : M.evalFrom S [a] = M.stepSet S a :=
  rfl

@[simp]
theorem evalFrom_cons (S : Multiset (σ × κ)) (a : α) (x : List α) :
    M.evalFrom S (a :: x) = M.evalFrom (M.stepSet S a) x :=
  rfl

theorem evalFrom_append_singleton (S : Multiset (σ × κ)) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp]
theorem evalFrom_append (S : Multiset (σ × κ)) (x y : List α) :
    M.evalFrom S (x ++ y) = M.evalFrom (M.evalFrom S x) y := by
  simp only [evalFrom, List.foldl_append]

def eval : List α → Multiset (σ × κ) :=
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

def acceptsFrom (S : Multiset (σ × κ)) : WeightedLanguage α κ :=
  fun x ↦ (Multiset.map (fun sw ↦ sw.2 * (M.final sw.1)) (M.evalFrom S x)).sum

@[simp]
theorem acceptsFrom_nil (S : Multiset (σ × κ)) :
    M.acceptsFrom S [] = (Multiset.map (fun sw ↦ sw.2 * (M.final sw.1)) S).sum :=
  rfl

@[simp]
theorem acceptsFrom_cons (S : Multiset (σ × κ)) (a : α) (x : List α) :
    M.acceptsFrom S (a :: x) = M.acceptsFrom (M.stepSet S a) x := rfl

def accepts : WeightedLanguage α κ := M.acceptsFrom M.start

end basic

section toNFA

/- ### Weighted to unweighted NFA

We cannot use `Bool` for the weight type, since the Mathlib instance for `Add Bool` uses `xor`, not
`or`. Instead we use a type isomorphic to `Bool`.

-/

variable {σ : Type} (M : WNFA α σ (WithZero Unit)) [DecidableEq σ]

@[simp]
private def getSet (S : Multiset (σ × WithZero Unit)) : Set σ :=
  { s | (Multiset.map Prod.snd (Multiset.filter (fun sw ↦ sw.1 = s) S)).sum = 1 }

@[simp]
def toNFAStart : Set σ := getSet M.start

@[simp]
def toNFAAccept : Set σ := { s | M.final s = 1 }

@[simp]
def toNFAStep (s : σ) (a : α) : Set σ := getSet <| M.step s a

@[simps]
def toNFA : NFA α σ where
  step := M.toNFAStep
  start := M.toNFAStart
  accept := M.toNFAAccept

@[simp]
lemma wzu_add_eq_one (x y : WithZero Unit) :
    x + y = 1 ↔ (x = 1 ∨ y = 1) := by
  rcases (WDFA.wzu_zero_or_one x) with rfl | rfl <;>
  rcases (WDFA.wzu_zero_or_one y) with rfl | rfl <;> tauto

lemma toNFA_acceptsFrom {x : List α} {S : Multiset (σ × WithZero Unit)} :
    x ∈ M.toNFA.acceptsFrom (getSet S) ↔ M.acceptsFrom S x = 1 := by
  induction x generalizing S
  case nil =>
    simp
    induction S using Multiset.induction
    case empty => simp
    case cons sw S ih =>
      rcases sw with ⟨s, w⟩
      simp [Multiset.filter_cons, Multiset.map_add, distr_fun_ite]
      rcases (WDFA.wzu_zero_or_one w) with rfl | rfl
      · simpa
      · simp [←ih]; clear ih
        constructor
        · rintro ⟨s', hs' | hsum, hfinal'⟩
          · by_cases hss' : s = s'
            · subst s'; tauto
            · simp [hss'] at hs'
          · tauto
        · rintro (hfinal | ⟨s', hs', hfinal'⟩)
          · exists s; simpa
          · exists s'; tauto
  case cons a x ih =>
    sorry

end toNFA

section union

variable {κ : Type k} {σ1 σ2 : Type v}

lemma disjoint_injlr {S1 : Multiset (σ1 × κ)} {S2 : Multiset (σ2 × κ)} :
    Disjoint (Prod.map Sum.inl id <$> S1) (Prod.map Sum.inr id <$> S2) := by
  simp [Multiset.disjoint_map_map]

variable [DecidableEq σ1] [DecidableEq σ2] [DecidableEq κ]

@[simp]
def union_start (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) : Multiset ((σ1 ⊕ σ2) × κ) :=
  (Prod.map Sum.inl id <$> M1.start) ∪ (Prod.map Sum.inr id <$> M2.start)

@[simp]
def union_final (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) (s : σ1 ⊕ σ2) : κ :=
  s.casesOn M1.final M2.final

@[simp]
def union_step (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ)
  (s : σ1 ⊕ σ2) (a : α) : Multiset ((σ1 ⊕ σ2) × κ) :=
  s.casesOn
    (fun s1 ↦ Prod.map Sum.inl id <$> M1.step s1 a)
    (fun s2 ↦ Prod.map Sum.inr id <$> M2.step s2 a)

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
  {S1 : Multiset (σ1 × κ)} {S2 : Multiset (σ2 × κ)} :
    (M1 + M2).acceptsFrom ((Prod.map Sum.inl id <$> S1) ∪ (Prod.map Sum.inr id <$> S2))
    = M1.acceptsFrom S1 + M2.acceptsFrom S2 := by
  funext x
  induction x generalizing S1 S2
  case nil =>
    simp [WeightedLanguage.add_def_eq, WeightedLanguage.add_def]
    simp [←Multiset.fmap_def, ←Multiset.add_eq_union_iff_disjoint.mpr disjoint_injlr]
    simp [Multiset.fmap_def]
  case cons a x ih =>
    simp [WeightedLanguage.add_def_eq, WeightedLanguage.add_def] at *
    simp [←ih]
    clear ih
    congr 1
    simp [stepSet, ←Multiset.fmap_def, ←Multiset.add_eq_union_iff_disjoint.mpr disjoint_injlr]
    simp [Multiset.fmap_def, Multiset.bind_map, Multiset.map_bind, Prod.map_map]

lemma accepts_union {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
    (M1 + M2).accepts = M1.accepts + M2.accepts := by
  simp [accepts, ←acceptsFrom_union]

end union

section inter

variable {κ : Type k} {σ1 σ2 : Type v} [W : CommSemiring κ]

-- TODO: Maybe we go back to Finset for WNFA in general, but before the cauchy prod this goes to multiset then condenses?

@[simp]
def combine (sw : (σ1 × κ) × (σ2 × κ)) : (σ1 × σ2) × κ :=
  ((sw.1.1, sw.2.1,), sw.1.2 * sw.2.2)

@[simp]
def inter_start (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) : Multiset ((σ1 × σ2) × κ) :=
  combine <$> (M1.start ×ˢ M2.start)

@[simp]
def inter_final (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) (s : σ1 × σ2) : κ :=
  M1.final s.1 * M2.final s.2

@[simp]
def inter_step (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ)
  (s : σ1 × σ2) (a : α) : Multiset ((σ1 × σ2) × κ) :=
  combine <$> (M1.step s.1 a ×ˢ M2.step s.2 a)

def inter (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) : WNFA α (σ1 × σ2) κ where
  step := inter_step M1 M2
  start := inter_start M1 M2
  final := inter_final M1 M2

instance : HMul (WNFA α σ1 κ) (WNFA α σ2 κ) (WNFA α (σ1 × σ2) κ) := ⟨inter⟩

lemma inter_eq_hmul {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} : M1 * M2 = M1.inter M2 := rfl

@[simp]
lemma inter_start_proj {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
  (M1 * M2).start = inter_start M1 M2 := rfl

@[simp]
lemma inter_final_proj {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
  (M1 * M2).final = inter_final M1 M2 := rfl

@[simp]
lemma inter_step_proj {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
  (M1 * M2).step = inter_step M1 M2 := rfl

lemma acceptsFrom_inter {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ}
  {S1 : Multiset (σ1 × κ)} {S2 : Multiset (σ2 × κ)} :
    (M1 * M2).acceptsFrom (combine <$> (S1 ×ˢ S2))
    = (M1.acceptsFrom S1).pointwise_prod (M2.acceptsFrom S2) := by
  funext x
  simp [WeightedLanguage.pointwise_prod]
  induction x generalizing S1 S2
  case nil =>
    rw [mul_comm (M1.acceptsFrom S1 [])]
    simp [←Multiset.sum_map_mul_left, ←Multiset.sum_map_mul_right]
    simp [Multiset.instSProd, Multiset.product.eq_1, Multiset.map_bind]
    congr; funext ⟨s1, w1⟩
    congr; funext ⟨s2, w2⟩
    simp [←mul_comm (w1 * M1.final s1), mul_assoc]
    congr 1
    simp [←mul_assoc (M1.final s1), mul_comm (M1.final s1) w2, mul_assoc]
  case cons a x ih =>
    simp [←ih]
    clear ih
    simp [stepSet]
    congr
    simp [Multiset.instSProd, Multiset.product.eq_1, Multiset.bind_map]
    simp [Multiset.map_bind, Multiset.bind_assoc, Multiset.bind_map, ←Multiset.bind_bind S2]
    congr; funext ⟨s2, w2⟩
    congr; funext ⟨s1, w1⟩
    congr; funext ⟨s1', w1'⟩
    congr; funext ⟨s2', w2'⟩
    simp [mul_assoc w1 w1', ←mul_assoc w1' w2 w2', mul_comm w1' w2, mul_assoc]

theorem accepts_inter {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
    (M1 * M2).accepts = M1.accepts.pointwise_prod M2.accepts := by
  simp [accepts, ←acceptsFrom_inter]

end inter

end WNFA

namespace WDFA

variable {α : Type u} {κ : Type k} {σ : Type v} [W : Semiring κ]

@[simp] def toWNFA (M : WDFA α σ κ) : WNFA α σ κ where
  step s a := {M.step s a}
  start := {M.start}
  final := M.final

theorem acceptsFrom_toWNFA (M : WDFA α σ κ) (sw : σ × κ) :
    M.acceptsFrom sw = M.toWNFA.acceptsFrom {sw} := by
  funext x
  induction x generalizing sw
  case nil =>
    simp
  case cons a x ih =>
    simp [ih, Prod.map_def]

theorem accepts_toWNFA (M : WDFA α σ κ) : M.accepts = M.toWNFA.accepts := by
  simp [WDFA.accepts, WNFA.accepts, acceptsFrom_toWNFA]

end WDFA

-- `Finsupp` version.
structure WNFA₂ (α : Type u) (σ : Type v) (κ : Type k) [W : Zero κ] where
  /-- The NFA's transition function -/
  step : σ → α → σ →₀ κ
  /-- Initial weights. -/
  start : σ →₀ κ
  /-- Final weights. -/
  final : σ →₀ κ

namespace WFA₂

variable {α : Type u} {κ : Type k}

section basic

variable {σ : Type v} [W : Semiring κ]

instance : Inhabited (WNFA₂ α σ κ) :=
  ⟨WNFA₂.mk (fun _ _ ↦ 0) 0 0⟩

noncomputable section stepSet

variable (M : WNFA₂ α σ κ)

def stepSet (S : σ →₀ κ) (a : α) : σ →₀ κ :=
  (S.support.val.map
    (fun s : σ ↦
      Finsupp.mapRange (S s * ·) (W.mul_zero (S s)) (M.step s a))
   ).sum

@[simp]
theorem stepSet_empty (a : α) : stepSet M 0 a = 0 := by simp [stepSet]

def evalFrom (S : σ →₀ κ) : List α → σ →₀ κ :=
  List.foldl (stepSet M) S

@[simp]
theorem evalFrom_nil (S : σ →₀ κ) : evalFrom M S [] = S :=
  rfl

@[simp]
theorem evalFrom_singleton (S : σ →₀ κ) (a : α) : evalFrom M S [a] = stepSet M S a :=
  rfl

@[simp]
theorem evalFrom_cons (S : σ →₀ κ) (a : α) (x : List α) :
    evalFrom M S (a :: x) = evalFrom M (stepSet M S a) x :=
  rfl

@[simp]
theorem evalFrom_append (S : σ →₀ κ) (x y : List α) :
    evalFrom M S (x ++ y) = evalFrom M (evalFrom M S x) y := by
  simp only [evalFrom, List.foldl_append]

def acceptsFrom (S : σ →₀ κ) : WeightedLanguage α κ :=
  Finsupp.weight M.final ∘ (evalFrom M S)

@[simp]
theorem acceptsFrom_nil (S : σ →₀ κ) :
    acceptsFrom M S [] = Finsupp.weight M.final S :=
  rfl

@[simp]
theorem acceptsFrom_cons (S : σ →₀ κ) (a : α) (x : List α) :
    acceptsFrom M S (a :: x) = acceptsFrom M (stepSet M S a) x := rfl

def accepts : WeightedLanguage α κ := acceptsFrom M M.start

end stepSet

end basic

noncomputable section union

variable {σ1 σ2 : Type v} [W : Semiring κ]

@[simp]
def combineSum (S1 : σ1 →₀ κ) (S2 : σ2 →₀ κ) : σ1 ⊕ σ2 →₀ κ :=
  S1.embDomain Function.Embedding.inl + S2.embDomain Function.Embedding.inr

lemma combineSum_disjoint {S1 : σ1 →₀ κ} {S2 : σ2 →₀ κ} :
    Disjoint
      (Finset.map Function.Embedding.inl S1.support)
      (Finset.map Function.Embedding.inr S2.support) := by
    simp [Finset.disjoint_map_inl_map_inr]

@[simp]
def union_start (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) : σ1 ⊕ σ2 →₀ κ :=
  combineSum M1.start M2.start

@[simp]
def union_final (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) : σ1 ⊕ σ2 →₀ κ :=
  combineSum M1.final M2.final

@[simp]
def union_step (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ)
  (s : σ1 ⊕ σ2) (a : α) : σ1 ⊕ σ2 →₀ κ :=
  s.casesOn
    (fun s1 ↦ (M1.step s1 a).embDomain Function.Embedding.inl)
    (fun s2 ↦ (M2.step s2 a).embDomain Function.Embedding.inr)

def union (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) : WNFA₂ α (σ1 ⊕ σ2) κ where
  step := union_step M1 M2
  start := union_start M1 M2
  final := union_final M1 M2

instance : HAdd (WNFA₂ α σ1 κ) (WNFA₂ α σ2 κ) (WNFA₂ α (σ1 ⊕ σ2) κ) :=
  ⟨union⟩

lemma union_eq_hadd {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} :
    M1 + M2 = union M1 M2 := rfl

@[simp]
lemma union_start_proj {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} :
    (M1 + M2).start = union_start M1 M2 := rfl

@[simp]
lemma union_final_proj {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} :
    (M1 + M2).final = union_final M1 M2 := rfl

@[simp]
lemma union_step_proj {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} :
    (M1 + M2).step = union_step M1 M2 := rfl

variable [DecidableEq σ1] [DecidableEq σ2]

lemma acceptsFrom_union {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} {S1 : σ1 →₀ κ} {S2 : σ2 →₀ κ} :
    acceptsFrom (M1 + M2) (combineSum S1 S2) = acceptsFrom M1 S1 + acceptsFrom M2 S2 := by
  funext x
  induction x generalizing S1 S2
  case nil =>
    simp [WeightedLanguage.add_def_eq, WeightedLanguage.add_def]
    simp [Finsupp.weight_apply, Finsupp.sum_embDomain]
    simp [←Function.Embedding.inl_apply, ←Function.Embedding.inr_apply]
    simp [Finsupp.embDomain_notin_range]
  case cons a x ih =>
    simp [WeightedLanguage.add_def_eq, WeightedLanguage.add_def] at *
    simp [←ih]
    clear ih
    congr 1
    simp [stepSet]
    rw [Finsupp.support_add_eq combineSum_disjoint]
    simp [Finsupp.support_embDomain, Finset.sum_union combineSum_disjoint]
    simp [←Function.Embedding.inl_apply, ←Function.Embedding.inr_apply]
    simp [Finsupp.embDomain_notin_range]
    simp [←Finsupp.embDomain_mapRange]
    apply Finsupp.ext_iff.mpr
    rintro (s1 | s2)
    · simp [←Function.Embedding.inl_apply]
      simp [Finsupp.embDomain_notin_range]
    · simp [←Function.Embedding.inr_apply]
      simp [Finsupp.embDomain_notin_range]

lemma accepts_union {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} :
    accepts (M1 + M2) = accepts M1 + accepts M2 := by
  simp [accepts, ←acceptsFrom_union]

end union

noncomputable section inter

variable {σ1 σ2 : Type v} [W : CommSemiring κ]

-- This is unfortunate.
variable [NoZeroDivisors κ]

@[simp]
def combineProd (S1 : σ1 →₀ κ) (S2 : σ2 →₀ κ) (s : σ1 × σ2) : κ := S1 s.1 * S2 s.2

lemma combineProd_mem (S1 : σ1 →₀ κ) (S2 : σ2 →₀ κ) (s : σ1 × σ2) :
    combineProd S1 S2 s ≠ 0 →
    s ∈ S1.support ×ˢ S2.support := by
  simp

@[simp]
def combineProd₀ (S1 : σ1 →₀ κ) (S2 : σ2 →₀ κ) : σ1 × σ2 →₀ κ :=
  Finsupp.onFinset
    (S1.support ×ˢ S2.support)
    (combineProd S1 S2)
    (combineProd_mem S1 S2)

@[simp]
lemma combineProd₀_support (S1 : σ1 →₀ κ) (S2 : σ2 →₀ κ) :
    (combineProd₀ S1 S2).support = S1.support ×ˢ S2.support := by
  simp
  ext ⟨s1, s2⟩
  simp

@[simp]
def inter_start (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) : σ1 × σ2 →₀ κ :=
  combineProd₀ M1.start M2.start

@[simp]
def inter_final (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) : σ1 × σ2 →₀ κ :=
  combineProd₀ M1.final M2.final

@[simp]
def inter_step (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) (s : σ1 × σ2) (a : α) : σ1 × σ2 →₀ κ :=
  combineProd₀ (M1.step s.1 a) (M2.step s.2 a)

def inter (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) : WNFA₂ α (σ1 × σ2) κ where
  step := inter_step M1 M2
  start := inter_start M1 M2
  final := inter_final M1 M2

instance : HMul (WNFA₂ α σ1 κ) (WNFA₂ α σ2 κ) (WNFA₂ α (σ1 × σ2) κ) := ⟨inter⟩

lemma inter_eq_hmul {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} : M1 * M2 = inter M1 M2 := rfl

@[simp]
lemma inter_start_proj {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} :
  (M1 * M2).start = inter_start M1 M2 := rfl

@[simp]
lemma inter_final_proj {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} :
  (M1 * M2).final = inter_final M1 M2 := rfl

@[simp]
lemma inter_step_proj {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} :
  (M1 * M2).step = inter_step M1 M2 := rfl

lemma acceptsFrom_inter {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} {S1 : σ1 →₀ κ} {S2 : σ2 →₀ κ} :
    (acceptsFrom (M1 * M2)) (combineProd₀ S1 S2)
    = (acceptsFrom M1 S1).pointwise_prod (acceptsFrom M2 S2) := by
  funext x
  simp [WeightedLanguage.pointwise_prod]
  induction x generalizing S1 S2
  case nil =>
    simp [Finsupp.weight_apply, Finsupp.onFinset_sum]
    simp [Finset.sum_product, Finsupp.sum.eq_1, Finset.sum_mul_sum]
    congr; funext s1
    congr; funext s2
    rw [mul_assoc (S1 s1) (M1.final s1), ←mul_assoc (M1.final s1), mul_comm (M1.final s1) (S2 s2)]
    simp [mul_assoc]
  case cons a x ih =>
    simp [←ih]; clear ih
    simp [stepSet]
    congr; apply Finsupp.ext_iff.mpr; rintro ⟨s1', s2'⟩
    have h := combineProd₀_support S1 S2
    simp at h
    simp [h]; clear h
    simp [Finset.sum_product, Finset.sum_mul_sum]
    congr; funext s1
    congr; funext s2
    rw [mul_assoc (S1 s1) ((M1.step s1 a) s1'),
        ←mul_assoc ((M1.step s1 a) s1') (S2 s2),
        mul_comm ((M1.step s1 a) s1') (S2 s2)]
    simp [mul_assoc]

theorem accepts_inter {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} :
    accepts (M1 * M2) = (accepts M1).pointwise_prod (accepts M2) := by
  simp [accepts, ←acceptsFrom_inter]

end inter

noncomputable section reverse

variable {σ : Type v} [W : CommSemiring κ]

@[simp]
def reverse_step (M : WNFA₂ α σ κ) (s' : σ) (a : α) : σ →₀ κ :=
  Finsupp.ofSupportFinite
    (fun s ↦ M.step s a s')
    sorry

end reverse

end WFA₂
