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

-- Maybe someday this will be merged into Mathlib...
theorem Multiset.filter_eq_bind (m : Multiset α) (p : α → Prop) [DecidablePred p] :
    filter p m = bind m (fun a => if p a then {a} else 0) := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [filter_cons, ih]

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
  S.bind (fun sw ↦ (M.step sw.1 a).map (Prod.map id (sw.2 * ·)))

theorem mem_stepSet {sw : σ × κ} {S : Multiset (σ × κ)} {a : α} :
    sw ∈ M.stepSet S a ↔ ∃ tw ∈ S, sw ∈ (M.step tw.1 a).map (Prod.map id (tw.2 * ·)):= by
  simp [stepSet]

theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp [stepSet]

@[simp]
theorem stepSet_zero (a : α) : M.stepSet 0 a = ∅ := M.stepSet_empty a

@[simp]
theorem stepSet_cons (a : α) (sw : σ × κ) (S : Multiset (σ × κ)) :
    M.stepSet (sw ::ₘ S) a = (M.step sw.1 a).map (Prod.map id (sw.2 * ·)) + M.stepSet S a := by
  simp [stepSet]

@[simp]
theorem stepSet_add (a : α) (S1 S2 : Multiset (σ × κ)) :
    M.stepSet (S1 + S2) a = M.stepSet S1 a + M.stepSet S2 a := by
  simp [stepSet]

@[simp]
theorem stepSet_singleton (sw : σ × κ) (a : α) :
    M.stepSet {sw} a = (M.step sw.1 a).map (Prod.map id (sw.2 * ·)) := by
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

theorem eval_singleton (a : α) : M.eval [a] = M.stepSet M.start a :=
  rfl

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
lemma wzu_add_eq_one (x y : WithZero Unit) :
    x + y = 1 ↔ (x = 1 ∨ y = 1) := by
  rcases (WDFA.wzu_zero_or_one x) with rfl | rfl <;>
  rcases (WDFA.wzu_zero_or_one y) with rfl | rfl <;> tauto

@[simp]
lemma wzu_mul_eq_one (x y : WithZero Unit) :
    x * y = 1 ↔ (x = 1 ∧ y = 1) := by
  rcases (WDFA.wzu_zero_or_one x) with rfl | rfl <;>
  rcases (WDFA.wzu_zero_or_one y) with rfl | rfl <;> tauto

private def getSet (S : Multiset (σ × WithZero Unit)) : Set σ :=
  { s | (Multiset.map Prod.snd (Multiset.filter (fun sw ↦ sw.1 = s) S)).sum = 1 }

@[simp]
private theorem getSet_zero : getSet (0 : Multiset (σ × WithZero Unit)) = ∅ := by
  simp [getSet]

@[simp]
private theorem getSet_cons (sw : σ × WithZero Unit) (S : Multiset (σ × WithZero Unit)) :
    getSet (sw ::ₘ S) = (if sw.2 = 1 then {sw.1} else ∅) ∪ getSet S := by
  obtain ⟨s, w⟩ := sw
  ext q
  simp [getSet, Multiset.filter_cons]
  by_cases hsq : s = q
  · subst q
    simp
  · simp [if_neg hsq]
    rintro rfl rfl
    contradiction

@[simp]
private theorem getSet_add (S1 S2 : Multiset (σ × WithZero Unit)) :
    getSet (S1 + S2) = getSet S1 ∪ getSet S2 := by
  ext q
  simp [getSet]

private theorem getSet_map_zero (S : Multiset (σ × WithZero Unit)) :
    getSet (Multiset.map (fun sw ↦ Prod.map id (fun _ ↦ 0) sw) S) = ∅ := by
  induction S using Multiset.induction with
  | empty => simp
  | cons sw S ih => simp [ih]

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

lemma toNFA_stepSet {S : Multiset (σ × WithZero Unit)} {a : α} :
    M.toNFA.stepSet (getSet S) a = getSet (M.stepSet S a) := by
  induction S using Multiset.induction with
  | empty =>
    simp
  | cons sw S ih =>
    obtain ⟨s, w⟩ := sw
    simp [NFA.stepSet_union, ih]
    rcases (WDFA.wzu_zero_or_one w) with rfl | rfl
    · simp [getSet_map_zero]
    · simp [←Function.id_def, Prod.map_id]

theorem getSet_final_exists {S : Multiset (σ × WithZero Unit)} :
    (∃ s ∈ getSet S, M.final s = 1) ↔ (Multiset.map (fun sw ↦ sw.2 * M.final sw.1) S).sum = 1 := by
  induction S using Multiset.induction with
  | empty => simp
  | cons sw S ih =>
    obtain ⟨s, w⟩ := sw
    simp [←ih]; clear ih
    constructor
    · rintro ⟨q, (⟨rfl, rfl⟩ | h), hq⟩
      · simp
        tauto
      · tauto
    · rintro (⟨rfl, h⟩ | ⟨q, h, hq⟩)
      · exists s
        tauto
      · exists q
        tauto

lemma toNFA_acceptsFrom {x : List α} {S : Multiset (σ × WithZero Unit)} :
    x ∈ M.toNFA.acceptsFrom (getSet S) ↔ M.acceptsFrom S x = 1 := by
  induction x generalizing S
  case nil =>
    simp [getSet_final_exists]
  case cons a x ih =>
    simp only [NFA.cons_mem_acceptsFrom, toNFA_stepSet, ih]
    rfl

theorem toNFA_accepts {x : List α} : x ∈ M.toNFA.accepts ↔ M.accepts x = 1 := by
  apply toNFA_acceptsFrom

end toNFA

section union

variable {κ : Type k} {σ1 σ2 : Type v}

lemma disjoint_injlr {S1 : Multiset (σ1 × κ)} {S2 : Multiset (σ2 × κ)} :
    Disjoint (Prod.map Sum.inl id <$> S1) (Prod.map Sum.inr id <$> S2) := by
  simp [Multiset.disjoint_map_map]

@[simp]
def union_start (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) : Multiset ((σ1 ⊕ σ2) × κ) :=
  (Prod.map Sum.inl id <$> M1.start) + (Prod.map Sum.inr id <$> M2.start)

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
    (M1 + M2).acceptsFrom ((Prod.map Sum.inl id <$> S1) + (Prod.map Sum.inr id <$> S2))
    = M1.acceptsFrom S1 + M2.acceptsFrom S2 := by
  funext x
  induction x generalizing S1 S2
  case nil =>
    simp [WeightedLanguage.add_def_eq, WeightedLanguage.add_def]
  case cons a x ih =>
    simp [WeightedLanguage.add_def_eq, WeightedLanguage.add_def] at *
    simp [←ih]
    clear ih
    congr 1
    simp [stepSet, Multiset.bind_map, Multiset.map_bind, Prod.map_map]

lemma accepts_union {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
    (M1 + M2).accepts = M1.accepts + M2.accepts := by
  simp [accepts, ←acceptsFrom_union]

end union

section inter

variable {κ : Type k} {σ1 σ2 : Type v} [W : CommSemiring κ]

/- TODO: Maybe we go back to Finset for WNFA in general, but before the cauchy prod this goes to
multiset then condenses? -/

@[simp]
def combine (sw : (σ1 × κ) × (σ2 × κ)) : (σ1 × σ2) × κ :=
  ((sw.1.1, sw.2.1,), sw.1.2 * sw.2.2)

@[simp]
def interStart (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) : Multiset ((σ1 × σ2) × κ) :=
  combine <$> (M1.start ×ˢ M2.start)

@[simp]
def interFinal (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) (s : σ1 × σ2) : κ :=
  M1.final s.1 * M2.final s.2

@[simp]
def interStep (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ)
  (s : σ1 × σ2) (a : α) : Multiset ((σ1 × σ2) × κ) :=
  combine <$> (M1.step s.1 a ×ˢ M2.step s.2 a)

@[simps]
def inter (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ) : WNFA α (σ1 × σ2) κ where
  step := interStep M1 M2
  start := interStart M1 M2
  final := interFinal M1 M2

lemma acceptsFrom_inter {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ}
  {S1 : Multiset (σ1 × κ)} {S2 : Multiset (σ2 × κ)} :
    (M1.inter M2).acceptsFrom (combine <$> (S1 ×ˢ S2))
    = (M1.acceptsFrom S1).pointwise_prod (M2.acceptsFrom S2) := by
  funext x
  rw [WeightedLanguage.pointwise_prod]
  induction x generalizing S1 S2
  case nil =>
    rw [mul_comm (M1.acceptsFrom S1 [])]
    simp [←Multiset.sum_map_mul_left, ←Multiset.sum_map_mul_right]
    simp [Multiset.instSProd, Multiset.product.eq_1, Multiset.map_bind]
    ac_nf
  case cons a x ih =>
    simp [←ih]
    clear ih
    simp [stepSet]
    congr
    simp [Multiset.instSProd, Multiset.product.eq_1, Multiset.bind_map]
    simp [Multiset.map_bind, Multiset.bind_assoc, Multiset.bind_map, ←Multiset.bind_bind S2]
    ac_nf

theorem accepts_inter {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ} :
    (M1.inter M2).accepts = M1.accepts.pointwise_prod M2.accepts := by
  simp [accepts, ←acceptsFrom_inter]

end inter

section concat

variable {α : Type u} {κ : Type k} {σ1 σ2 : Type v} [W : Semiring κ]

variable (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ)

@[simp]
def concatStart : Multiset ((σ1 ⊕ σ2) × κ) := M1.start.map (Prod.map Sum.inl id)

end concat

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
  ∑ s ∈ S.support, (M.step s a).mapRange (S s * ·) (W.mul_zero (S s))

@[simp]
theorem stepSet_empty (a : α) : stepSet M 0 a = 0 := by simp [stepSet]

theorem stepSet_single (s : σ) {w : κ} (a : α) (hw : w ≠ 0) :
    stepSet M (fun₀ | s => w) a = (M.step s a).mapRange (w * ·) (W.mul_zero w) := by
  simp [stepSet, Finsupp.support_single_ne_zero _ hw]

theorem stepSet_disjoint_add [DecidableEq σ] {S1 S2 : σ →₀ κ} (a : α)
  (h : Disjoint S1.support S2.support) :
    stepSet M (S1 + S2) a = stepSet M S1 a + stepSet M S2 a := by
  ext s
  simp [stepSet, W.right_distrib]
  rw [Finsupp.support_add_eq h, ←Finset.disjUnion_eq_union _ _ h, Finset.sum_disjUnion]
  congr 1 <;> apply Finset.sum_congr rfl
  · intro s hs1
    have hs2 := Disjoint.notMem_of_mem_left_finset h hs1
    simp [Finsupp.notMem_support_iff.mp hs2]
  · intro s hs2
    have hs1 := Disjoint.notMem_of_mem_right_finset h hs2
    simp [Finsupp.notMem_support_iff.mp hs1]

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
def interStart (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) : σ1 × σ2 →₀ κ :=
  combineProd₀ M1.start M2.start

@[simp]
def interFinal (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) : σ1 × σ2 →₀ κ :=
  combineProd₀ M1.final M2.final

@[simp]
def interStep (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) (s : σ1 × σ2) (a : α) : σ1 × σ2 →₀ κ :=
  combineProd₀ (M1.step s.1 a) (M2.step s.2 a)

@[simps]
def inter (M1 : WNFA₂ α σ1 κ) (M2 : WNFA₂ α σ2 κ) : WNFA₂ α (σ1 × σ2) κ where
  step := interStep M1 M2
  start := interStart M1 M2
  final := interFinal M1 M2

lemma acceptsFrom_inter {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} {S1 : σ1 →₀ κ} {S2 : σ2 →₀ κ} :
    (acceptsFrom (inter M1 M2)) (combineProd₀ S1 S2)
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
    ac_nf
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
    rw [mul_assoc (S1 s1) ((M1.step s1 a) s1')]
    ac_nf

theorem accepts_inter {M1 : WNFA₂ α σ1 κ} {M2 : WNFA₂ α σ2 κ} :
    accepts (inter M1 M2) = (accepts M1).pointwise_prod (accepts M2) := by
  simp [accepts, ←acceptsFrom_inter]

end inter

noncomputable section toWNFA

variable {σ : Type v} [W : CommSemiring κ] (M : WNFA₂ α σ κ)

-- consider goint back to converting to multiset first
def getMultiset (S : σ →₀ κ) : Multiset (σ × κ) :=
  S.support.val.map (fun s ↦ (s, S s))

@[simp]
theorem getMultiset_zero : getMultiset (0 : σ →₀ κ) = 0 := by
  simp [getMultiset]

@[simp]
theorem getMultiset_single [DecidableEq κ] (s : σ) (w : κ) :
    getMultiset (fun₀ | s => w) = if w = 0 then 0 else {(s, w)} := by
  by_cases hw : w = 0
  · subst w
    simp [getMultiset]
  · simpa [getMultiset, Finsupp.support_single_ne_zero s hw]

variable [DecidableEq σ]

theorem getMultiset_disjoint_add {S1 S2 : σ →₀ κ} (h : Disjoint S1.support S2.support) :
    getMultiset (S1 + S2) = getMultiset S1 + getMultiset S2 := by
  simp [getMultiset, Finsupp.support_add_eq h]
  rw [←Multiset.add_eq_union_iff_disjoint.mpr <| Finset.disjoint_val.mpr h]
  simp [Multiset.map_add]
  congr 1 <;> apply Multiset.map_congr rfl
  · intro s hs1
    have hs2 := Disjoint.notMem_of_mem_left_finset h hs1
    simp [Finsupp.notMem_support_iff.mp hs2]
  · intro s hs2
    have hs1 := Disjoint.notMem_of_mem_right_finset h hs2
    simp [Finsupp.notMem_support_iff.mp hs1]

variable [DecidableEq κ]

theorem Nodup_getMultisetSet (S : σ →₀ κ) : (getMultiset S).Nodup := by
  induction S using Finsupp.induction with
  | zero =>
    simp
  | single_add s w S hdom hw ih =>
    rw [getMultiset_disjoint_add
      (by rwa [Finsupp.support_single_ne_zero s hw, Finset.disjoint_singleton_left])]
    simp [if_neg hw]
    refine ⟨?_ , ih⟩
    simp [getMultiset]
    intro hSs
    have hcontra := Finsupp.notMem_support_iff.mp hdom
    contradiction

theorem dedup_getMultiset (S : σ →₀ κ) :
    (getMultiset S).dedup = getMultiset S :=
  Multiset.dedup_eq_self.mpr (Nodup_getMultisetSet S)

@[simp]
def toWNFAstart : Multiset (σ × κ) :=
  getMultiset M.start

@[simp]
def toWNFAfinal : σ → κ := M.final.toFun

@[simp]
def toWNFAstep (s : σ) (a : α) : Multiset (σ × κ) :=
  getMultiset <| M.step s a

@[simps]
def toWNFA : WNFA α σ κ where
  step := toWNFAstep M
  start := toWNFAstart M
  final := toWNFAfinal M

theorem stepSet_getMultiset {S : σ →₀ κ} {a : α} :
    (toWNFA M).stepSet (getMultiset S) a = getMultiset (stepSet M S a) := by
  induction S using Finsupp.induction with
  | zero =>
    simp
  | single_add s w S hdom hw ih =>
    have hdisj : Disjoint (fun₀ | s => w).support S.support := by
      rwa [Finsupp.support_single_ne_zero s hw, Finset.disjoint_singleton_left]
    rw [getMultiset_disjoint_add hdisj]
    simp [if_neg hw, ih]; clear ih
    rw [stepSet_disjoint_add _ _ hdisj]
    rw [stepSet_single _ _ _ hw]
    simp only [getMultiset, stepSet]
    simp
    sorry

theorem acceptsFrom_toWNFA {S : σ →₀ κ} :
    (toWNFA M).acceptsFrom (getMultiset S) = acceptsFrom M S := by
  funext x
  induction x generalizing S with
  | nil =>
    rw [getMultiset]
    simp [getMultiset, Finsupp.weight_apply]
    rfl
  | cons a x ih =>
    simp [ih]
    simp [stepSet, WNFA.stepSet]
    sorry

end toWNFA

noncomputable section reverse

variable {σ : Type v} [W : CommSemiring κ]

@[simp]
def reverse_step (M : WNFA₂ α σ κ) (s' : σ) (a : α) : σ →₀ κ :=
  Finsupp.ofSupportFinite
    (fun s ↦ M.step s a s')
    sorry

end reverse

end WFA₂

-- Full function version.
structure WNFA₃ (α : Type u) (σ : Type v) (κ : Type k) where
  /-- The NFA's transition function -/
  step : σ → α → σ → κ
  /-- Initial weights. -/
  start : σ → κ
  /-- Final weights. -/
  final : σ → κ

namespace WNFA₃

variable {α : Type u} {κ : Type k}

section basic

variable {σ : Type v} [W : Semiring κ]

instance : Inhabited (WNFA₃ α σ κ) :=
  ⟨WNFA₃.mk (fun _ _ ↦ 0) 0 0⟩

variable (M : WNFA₃ α σ κ) [Fintype σ]

def stepSet (S : σ → κ) (a : α) : σ → κ :=
  ∑ s : σ, (S s * ·) ∘ M.step s a

@[simp]
theorem stepSet_add (S1 S2 : σ → κ) (a : α) :
    M.stepSet (S1 + S2) a = M.stepSet S1 a + M.stepSet S2 a := by
  ext s
  simp [stepSet, W.right_distrib, Finset.sum_add_distrib]

@[simp]
theorem stepSet_const_zero {a : α} : M.stepSet 0 a = 0 := by
  ext s
  simp [stepSet]

def evalFrom (S : σ → κ) : List α → σ → κ :=
  List.foldl M.stepSet S

@[simp]
theorem evalFrom_nil (S : σ → κ) : M.evalFrom S [] = S :=
  rfl

@[simp]
theorem evalFrom_cons (S : σ → κ) (a : α) (x : List α) :
    M.evalFrom S (a :: x) = M.evalFrom (M.stepSet S a) x :=
  rfl

@[simp]
theorem evalFrom_append (S : σ → κ) (x y : List α) :
    M.evalFrom S (x ++ y) = M.evalFrom (M.evalFrom S x) y := by
  simp only [evalFrom, List.foldl_append]

@[simp]
theorem evalFrom_add (S1 S2 : σ → κ) (x : List α) :
    M.evalFrom (S1 + S2) x = M.evalFrom S1 x + M.evalFrom S2 x := by
  induction x generalizing S1 S2 with
  | nil => simp
  | cons a x ih => simp [ih]

def acceptsFrom (S : σ → κ) : WeightedLanguage α κ :=
  fun x ↦ ∑ s : σ, M.evalFrom S x s * M.final s

@[simp]
theorem acceptsFrom_nil (S : σ → κ) : M.acceptsFrom S [] = ∑ s : σ, S s * M.final s :=
  rfl

@[simp]
theorem acceptsFrom_cons (S : σ → κ) (a : α) (x : List α) :
    M.acceptsFrom S (a :: x) = M.acceptsFrom (M.stepSet S a) x :=
  rfl

@[simp]
theorem acceptsFrom_add (S1 S2 : σ → κ) (x : List α) :
    M.acceptsFrom (S1 + S2) x = M.acceptsFrom S1 x + M.acceptsFrom S2 x := by
  simp [acceptsFrom, W.right_distrib, Finset.sum_add_distrib]

@[simp]
theorem acceptsFrom_const_zero :
    M.acceptsFrom 0 = 0 := by
  funext x
  simp only [WeightedLanguage.zero_def_eq]
  induction x with
  | nil => simp
  | cons a x ih => simp [M.stepSet_const_zero, ih]

def accepts : WeightedLanguage α κ := M.acceptsFrom M.start

end basic

section toNFA

/- ### Weighted to unweighted NFA

We cannot use `Bool` for the weight type, since the Mathlib instance for `Add Bool` uses `xor`, not
`or`. Instead we use a type isomorphic to `Bool`.

-/

variable {σ : Type} (M : WNFA₃ α σ (WithZero Unit))

-- TODO: factor out
@[simp]
lemma wzu_add_eq_one (x y : WithZero Unit) :
    x + y = 1 ↔ (x = 1 ∨ y = 1) := by
  rcases (WDFA.wzu_zero_or_one x) with rfl | rfl <;>
  rcases (WDFA.wzu_zero_or_one y) with rfl | rfl <;> tauto

-- TODO: factor out
@[simp]
lemma wzu_mul_eq_one (x y : WithZero Unit) :
    x * y = 1 ↔ (x = 1 ∧ y = 1) := by
  rcases (WDFA.wzu_zero_or_one x) with rfl | rfl <;>
  rcases (WDFA.wzu_zero_or_one y) with rfl | rfl <;> tauto

private def getSet (S : σ → WithZero Unit) : Set σ :=
  { s | S s = 1 }

@[simp]
private theorem getSet_zero : getSet (0 : σ → WithZero Unit) = ∅ := by
  simp [getSet]

@[simp]
private theorem getSet_add (S1 S2 : σ → WithZero Unit) :
    getSet (S1 + S2) = getSet S1 ∪ getSet S2 := by
  ext q
  simp [getSet]

@[simp]
def toNFAStart : Set σ := getSet M.start

@[simp]
def toNFAAccept : Set σ := getSet M.final

@[simp]
def toNFAStep (s : σ) (a : α) : Set σ := getSet <| M.step s a

@[simps]
def toNFA : NFA α σ where
  step := M.toNFAStep
  start := M.toNFAStart
  accept := M.toNFAAccept

variable [DecidableEq σ]

theorem exists_sum_Finset_eq_one {S : Finset σ} {f : σ → WithZero Unit} :
    (∃ s ∈ S, f s = 1) ↔ ∑ s ∈ S, f s = 1 := by
  induction S using Finset.induction with
  | empty => simp
  | insert q S hq ih => simp [Finset.sum_insert hq, ih]

variable [Fintype σ]

theorem exists_sum_Fintype_eq_one {f : σ → WithZero Unit} :
    (∃ s, f s = 1) ↔ ∑ s : σ, f s = 1 := by
  simp [←exists_sum_Finset_eq_one]

lemma toNFA_stepSet {S : σ → WithZero Unit} {a : α} :
    M.toNFA.stepSet (getSet S) a = getSet (M.stepSet S a) := by
  ext s
  simp [NFA.stepSet, stepSet, getSet, ←exists_sum_Fintype_eq_one]

lemma toNFA_acceptsFrom {x : List α} {S : σ → WithZero Unit} :
    x ∈ M.toNFA.acceptsFrom (getSet S) ↔ M.acceptsFrom S x = 1 := by
  induction x generalizing S
  case nil => simp [getSet, ←exists_sum_Fintype_eq_one]
  case cons a x ih =>
    simp only [NFA.cons_mem_acceptsFrom, toNFA_stepSet, ih]
    rfl

theorem toNFA_accepts {x : List α} : x ∈ M.toNFA.accepts ↔ M.accepts x = 1 := by
  apply toNFA_acceptsFrom

end toNFA

section empty

variable (w : κ) [W : Semiring κ]

def empty : WNFA₃ α Unit κ where
  step := fun _ _ _ ↦ 0
  start := Function.const Unit w
  final := Function.const Unit 1

@[simp]
theorem empty_step : (empty (α:=α) w).step = fun _ (_ : α) _ ↦ 0 :=
  rfl

@[simp]
theorem empty_start : (empty (α:=α) w).start = Function.const Unit w :=
  rfl

@[simp]
theorem empty_final : (empty (α:=α) w).final = Function.const Unit 1 :=
  rfl

@[simp]
theorem stepSet_empty {S : Unit → κ} {a : α} : (empty (α:=α) w).stepSet S a = 0 := by
  ext ⟨⟩
  simp [stepSet]

theorem accepts_empty : (empty (α:=α) w).accepts = WeightedLanguage.scalar_prodl (α:=α) w 1 := by
  funext x
  simp [accepts, WeightedLanguage.scalar_prodl, WeightedLanguage.one_def_eq]
  cases x with
  | nil => simp
  | cons a x => simp [WeightedLanguage.zero_def_eq]

end empty

section char

variable (a : α) [DecidableEq α] [W : Semiring κ]

@[simp]
def charStart (s : Bool) : κ :=
  if s then 0 else 1

@[simp]
def charFinal (s : Bool) : κ :=
  if s then 1 else 0

@[simp]
def charStep : Bool → α → Bool → κ
| false, b, true => if decide (b = a) then 1 else 0
| _, _, _ => 0

def char : WNFA₃ α Bool κ where
  step := charStep a
  start := charStart
  final := charFinal

@[simp]
theorem char_step : (char (κ:=κ) a).step = charStep (κ:=κ) a :=
  rfl

@[simp]
theorem char_start : (char (κ:=κ) a).start = charStart (κ:=κ) :=
  rfl

@[simp]
theorem char_final : (char (κ:=κ) a).final = charFinal (κ:=κ) :=
  rfl

@[simp]
theorem charStep_zero :
    charStep (κ:=κ) a true = Function.const α (Function.const Bool (0 : κ)) := by
  ext b s
  simp

theorem accepts_char : (char (κ:=κ) a).accepts = fun x ↦ if x = [a] then (1 : κ) else (0 : κ) := by
  funext x
  rw [accepts]
  cases x with
  | nil =>
    simp
  | cons b x =>
    cases x with
    | nil =>
      by_cases h : b = a <;>
      simp [stepSet, show (fun x ↦ x) = id by rfl]
    | cons c x =>
      by_cases hba : b = a <;>
      suffices h : (0 : List α → κ) x = (0 : κ) by
        { simpa [stepSet, show (fun x ↦ x) = id by rfl,
          show (fun x ↦ (0 : κ)) = Function.const κ 0 by rfl] } <;>
      rfl

end char

section union

variable {σ1 σ2 : Type v} [W : Semiring κ]

def combineSum (S1 : σ1 → κ) (S2 : σ2 → κ) : σ1 ⊕ σ2 → κ
| .inl s1 => S1 s1
| .inr s2 => S2 s2

section unionDef

variable (M1 : WNFA₃ α σ1 κ) (M2 : WNFA₃ α σ2 κ)

@[simp]
def unionStart : σ1 ⊕ σ2 → κ := combineSum M1.start M2.start

@[simp]
def unionFinal : σ1 ⊕ σ2 → κ := combineSum M1.final M2.final

@[simp]
def unionStep : σ1 ⊕ σ2 → α → σ1 ⊕ σ2 → κ
| .inl s1, a => combineSum (M1.step s1 a) (fun _ ↦ 0)
| .inr s2, a => combineSum (fun _ ↦ 0) (M2.step s2 a)

def union : WNFA₃ α (σ1 ⊕ σ2) κ where
  step := unionStep M1 M2
  start := unionStart M1 M2
  final := unionFinal M1 M2

end unionDef

instance : HAdd (WNFA₃ α σ1 κ) (WNFA₃ α σ2 κ) (WNFA₃ α (σ1 ⊕ σ2) κ) :=
  ⟨union⟩

variable {M1 : WNFA₃ α σ1 κ} {M2 : WNFA₃ α σ2 κ}

theorem hadd_eq_union : M1 + M2 = M1.union M2 :=
  rfl

@[simp]
theorem unionStart_proj : (M1 + M2).start = M1.unionStart M2 :=
  rfl

@[simp]
theorem unionFinal_proj : (M1 + M2).final = M1.unionFinal M2 :=
  rfl

@[simp]
theorem unionStep_proj : (M1 + M2).step = M1.unionStep M2 :=
  rfl

variable [Fintype σ1] [Fintype σ2]

theorem stepSet_hadd {S1 : σ1 → κ} {S2 : σ2 → κ} {a : α} :
    (M1 + M2).stepSet (combineSum S1 S2) a = combineSum (M1.stepSet S1 a) (M2.stepSet S2 a) := by
  ext (s1 | s2) <;> simp [stepSet, combineSum]

theorem acceptsFrom_hadd {S1 : σ1 → κ} {S2 : σ2 → κ} :
    (M1 + M2).acceptsFrom (combineSum S1 S2) = M1.acceptsFrom S1 + M2.acceptsFrom S2 := by
  funext x
  rw [WeightedLanguage.add_def_eq, WeightedLanguage.add_def]
  induction x generalizing S1 S2 with
  | nil => simp [combineSum]
  | cons a x ih => simp [stepSet_hadd, ih]

theorem accepts_hadd : (M1 + M2).accepts = M1.accepts + M2.accepts := by
  simp [accepts, acceptsFrom_hadd]

end union

section inter

variable {σ1 σ2 : Type v} [W : CommSemiring κ]

def combineProd (S1 : σ1 → κ) (S2 : σ2 → κ) (s : σ1 × σ2) : κ := S1 s.1 * S2 s.2

variable (M1 : WNFA₃ α σ1 κ) (M2 : WNFA₃ α σ2 κ)

@[simp]
def interStart : σ1 × σ2 → κ := combineProd M1.start M2.start

@[simp]
def interFinal : σ1 × σ2 → κ := combineProd M1.final M2.final

@[simp]
def interStep (s : σ1 × σ2) (a : α) : σ1 × σ2 → κ :=
  combineProd (M1.step s.1 a) (M2.step s.2 a)

@[simps]
def inter : WNFA₃ α (σ1 × σ2) κ where
  step := M1.interStep M2
  start := M1.interStart M2
  final := M1.interFinal M2

@[simp]
theorem inter_start_eq_interStart : (M1.inter M2).start = M1.interStart M2 :=
  rfl

@[simp]
theorem inter_final_eq_interFinal : (M1.inter M2).final = M1.interFinal M2 :=
  rfl

@[simp]
theorem inter_step_eq_interStep : (M1.inter M2).step = M1.interStep M2 :=
  rfl

variable [Fintype σ1] [Fintype σ2]

theorem stepSet_inter {S1 : σ1 → κ} {S2 : σ2 → κ} {a : α} :
    (M1.inter M2).stepSet (combineProd S1 S2) a
    = combineProd (M1.stepSet S1 a) (M2.stepSet S2 a) := by
  ext ⟨s1, s2⟩
  simp [stepSet, combineProd]
  simp [Fintype.sum_mul_sum, Fintype.sum_prod_type]
  ac_nf

theorem acceptsFrom_inter {S1 : σ1 → κ} {S2 : σ2 → κ} :
    (M1.inter M2).acceptsFrom (combineProd S1 S2)
    = (M1.acceptsFrom S1).pointwise_prod (M2.acceptsFrom S2) := by
  funext x
  rw [WeightedLanguage.pointwise_prod]
  induction x generalizing S1 S2 with
  | nil =>
    simp [combineProd, Fintype.sum_mul_sum, Fintype.sum_prod_type]
    ac_nf
  | cons a x ih =>
    simp [stepSet_inter, ih]

theorem accepts_inter : (M1.inter M2).accepts = M1.accepts.pointwise_prod M2.accepts := by
  simp [accepts, acceptsFrom_inter]

end inter

end WNFA₃
