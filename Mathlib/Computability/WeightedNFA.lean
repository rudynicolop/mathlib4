/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
module

public import Mathlib.Computability.NFA
public import Mathlib.Computability.WeightedDFA
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.Functor
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Finsupp.Notation

/-!
# Weighted Nondeterministic Finite Automata

TODO
-/

@[expose] public section

universe u v k

-- Full function version.
structure WNFA (α : Type u) (σ : Type v) (κ : Type k) where
  /-- The NFA's transition function -/
  step : σ → α → σ → κ
  /-- Initial weights. -/
  start : σ → κ
  /-- Final weights. -/
  final : σ → κ

namespace WNFA

variable {α : Type u} {κ : Type k}

section basic

variable {σ : Type v} [W : Semiring κ]

@[simp]
theorem finset_sum_apply (S : Finset σ) (f : σ → WeightedLanguage α κ) (x : List α) :
    (∑ s ∈ S, f s) x = ∑ s ∈ S, f s x := by
  apply Finset.sum_apply

instance : Inhabited (WNFA α σ κ) :=
  ⟨WNFA.mk (fun _ _ ↦ 0) 0 0⟩

variable (M : WNFA α σ κ) [Fintype σ]

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

theorem stepSet_compose_mul (w : κ) (S : σ → κ) (a : α) :
    M.stepSet ((w * ·) ∘ S) a = (w * ·) ∘ M.stepSet S a := by
  ext s
  simp [stepSet, Finset.mul_sum, W.mul_assoc]

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
theorem acceptsFrom_add (S1 S2 : σ → κ) :
    M.acceptsFrom (S1 + S2) = M.acceptsFrom S1 + M.acceptsFrom S2 := by
  ext x
  simp [acceptsFrom, W.right_distrib, Finset.sum_add_distrib]

@[simp]
theorem acceptsFrom_const_zero :
    M.acceptsFrom 0 = 0 := by
  ext x
  simp only [WeightedLanguage.zero_def]
  induction x with
  | nil => simp
  | cons a x ih => simp [M.stepSet_const_zero, ih]

theorem acceptsFrom_sum {ι : Type*} (I : Finset ι) (f : ι → σ → κ) :
    M.acceptsFrom (∑ i ∈ I, f i) = ∑ i ∈ I, M.acceptsFrom (f i) := by
  open scoped Classical in
  ext x
  induction I using Finset.induction with
  | empty => simp [show (0 : List α → κ) x = (0 : κ) by rfl]
  | insert i I hi ih => simp [Finset.sum_insert hi, ih]

theorem acceptsFrom_sum_Fintype {ι : Type*} [Fintype ι] (f : ι → σ → κ) :
    M.acceptsFrom (∑ i : ι, f i) = ∑ i : ι, M.acceptsFrom (f i) := by
  rw [acceptsFrom_sum]

theorem acceptsFrom_compose_mul (w : κ) (S : σ → κ) :
    M.acceptsFrom ((w * ·) ∘ S) = (w * ·) ∘ M.acceptsFrom S := by
  ext x
  induction x generalizing w S with
  | nil => simp [Finset.mul_sum, W.mul_assoc]
  | cons a x ih => simp [stepSet_compose_mul, ih]

@[simp]
theorem acceptsFrom_compose_cons (S : σ → κ) (a : α) :
    M.acceptsFrom S ∘ (a :: ·) = M.acceptsFrom (M.stepSet S a) :=
  rfl

def accepts : WeightedLanguage α κ := M.acceptsFrom M.start

end basic

section toNFA

/- ### Weighted to unweighted NFA

We cannot use `Bool` for the weight type, since the Mathlib instance for `Add Bool` uses `xor`, not
`or`. Instead we use a type isomorphic to `Bool`.

-/

variable {σ : Type} (M : WNFA α σ (WithZero Unit))

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

theorem exists_sum_Finset_eq_one {S : Finset σ} {f : σ → WithZero Unit} :
    (∃ s ∈ S, f s = 1) ↔ ∑ s ∈ S, f s = 1 := by
  open scoped Classical in
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

def empty : WNFA α Unit κ where
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

theorem accepts_empty : (empty (α:=α) w).accepts = w • 1 := by
  ext x
  rw [accepts]
  cases x with
  | nil => simp
  | cons a x => simp

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

def char : WNFA α Bool κ where
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
  ext x
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
        { simp [stepSet, show (fun x ↦ x) = id by rfl,
            show (fun x ↦ (0 : κ)) = Function.const κ 0 by rfl] } <;>
      rfl

end char

section union

variable {σ1 σ2 : Type v} [W : Semiring κ]

def combineSum (S1 : σ1 → κ) (S2 : σ2 → κ) : σ1 ⊕ σ2 → κ
| .inl s1 => S1 s1
| .inr s2 => S2 s2

section unionDef

variable (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ)

@[simp]
def unionStart : σ1 ⊕ σ2 → κ := combineSum M1.start M2.start

@[simp]
def unionFinal : σ1 ⊕ σ2 → κ := combineSum M1.final M2.final

@[simp]
def unionStep : σ1 ⊕ σ2 → α → σ1 ⊕ σ2 → κ
| .inl s1, a => combineSum (M1.step s1 a) (fun _ ↦ 0)
| .inr s2, a => combineSum (fun _ ↦ 0) (M2.step s2 a)

def union : WNFA α (σ1 ⊕ σ2) κ where
  step := unionStep M1 M2
  start := unionStart M1 M2
  final := unionFinal M1 M2

end unionDef

instance : HAdd (WNFA α σ1 κ) (WNFA α σ2 κ) (WNFA α (σ1 ⊕ σ2) κ) :=
  ⟨union⟩

variable {M1 : WNFA α σ1 κ} {M2 : WNFA α σ2 κ}

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
  ext x
  rw [WeightedLanguage.add_apply]
  induction x generalizing S1 S2 with
  | nil => simp [combineSum]
  | cons a x ih => simp [stepSet_hadd, ih]

theorem accepts_hadd : (M1 + M2).accepts = M1.accepts + M2.accepts := by
  simp [accepts, acceptsFrom_hadd]

end union

section inter

variable {σ1 σ2 : Type v} [W : CommSemiring κ]

def combineProd (S1 : σ1 → κ) (S2 : σ2 → κ) (s : σ1 × σ2) : κ := S1 s.1 * S2 s.2

variable (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ)

@[simp]
def interStart : σ1 × σ2 → κ := combineProd M1.start M2.start

@[simp]
def interFinal : σ1 × σ2 → κ := combineProd M1.final M2.final

@[simp]
def interStep (s : σ1 × σ2) (a : α) : σ1 × σ2 → κ :=
  combineProd (M1.step s.1 a) (M2.step s.2 a)

@[simps]
def inter : WNFA α (σ1 × σ2) κ where
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
  suffices h :
    ∑ i, ∑ j, S1 i * S2 j * (M1.step i a s1 * M2.step j a s2) =
    ∑ i, ∑ j, S1 i * M1.step i a s1 * (S2 j * M2.step j a s2) by
    simpa [stepSet, combineProd, Fintype.sum_mul_sum, Fintype.sum_prod_type]
  ac_nf

theorem acceptsFrom_inter {S1 : σ1 → κ} {S2 : σ2 → κ} :
    (M1.inter M2).acceptsFrom (combineProd S1 S2)
    = (M1.acceptsFrom S1).hadamard (M2.acceptsFrom S2) := by
  ext x
  rw [WeightedLanguage.hadamard]
  induction x generalizing S1 S2 with
  | nil =>
    suffices h :
      ∑ i, ∑ j, S1 i * S2 j * (M1.final i * M2.final j) =
      ∑ i, ∑ j, S1 i * M1.final i * (S2 j * M2.final j) by
      simpa [combineProd, Fintype.sum_mul_sum, Fintype.sum_prod_type]
    ac_nf
  | cons a x ih =>
    simp [stepSet_inter, ih]

theorem accepts_inter : (M1.inter M2).accepts = M1.accepts.hadamard M2.accepts := by
  simp [accepts, acceptsFrom_inter]

end inter

section concat

variable {σ1 σ2 : Type v}

@[simp]
theorem combineSum_apply_inl {S1 : σ1 → κ} {S2 : σ2 → κ} {s : σ1} :
    combineSum S1 S2 (Sum.inl s) = S1 s :=
  rfl

@[simp]
theorem combineSum_apply_inr {S1 : σ1 → κ} {S2 : σ2 → κ} {s : σ2} :
    combineSum S1 S2 (Sum.inr s) = S2 s :=
  rfl

variable [W : Semiring κ]

theorem combineSum_separate {S1 : σ1 → κ} {S2 : σ2 → κ} :
    combineSum S1 S2 = combineSum S1 0 + combineSum 0 S2 := by
  ext (s1 | s2) <;> simp

variable (M1 : WNFA α σ1 κ) (M2 : WNFA α σ2 κ)

@[simp]
def concatStart : σ1 ⊕ σ2 → κ :=
  combineSum M1.start 0

variable [Fintype σ2]

@[simp]
def concatFinal : σ1 ⊕ σ2 → κ :=
  combineSum ((· * M2.accepts []) ∘ M1.final) M2.final

@[simp]
def concatStep : σ1 ⊕ σ2 → α → σ1 ⊕ σ2 → κ
| .inl s1, a =>
  combineSum (M1.step s1 a) ((M1.final s1 * ·) ∘ ∑ s2 : σ2, (M2.start s2 * ·) ∘ M2.step s2 a)
| .inr s2, a =>
  combineSum 0 (M2.step s2 a)

def concat : WNFA α (σ1 ⊕ σ2) κ where
  step := M1.concatStep M2
  start := M1.concatStart
  final := M1.concatFinal M2

instance : HMul (WNFA α σ1 κ) (WNFA α σ2 κ) (WNFA α (σ1 ⊕ σ2) κ) where
  hMul M1 M2 := M1.concat M2

theorem hmul_eq_concat : M1 * M2 = M1.concat M2 := by
  rfl

@[simp]
theorem hmul_concat_step : (M1 * M2).step = M1.concatStep M2 := by
  rfl

@[simp]
theorem hmul_concat_start : (M1 * M2).start = M1.concatStart := by
  rfl

@[simp]
theorem hmul_concat_final : (M1 * M2).final = M1.concatFinal M2 := by
  rfl

variable [Fintype σ1]

theorem stepSet_hmul_inr {S2 : σ2 → κ} {a : α} :
    (M1 * M2).stepSet (combineSum 0 S2) a = combineSum 0 (M2.stepSet S2 a) := by
  ext (s1 | s2) <;> simp [stepSet, combineSum]

theorem acceptsFrom_hmul_inr {S2 : σ2 → κ} :
    (M1 * M2).acceptsFrom (combineSum 0 S2) = M2.acceptsFrom S2 := by
  ext y
  induction y generalizing S2 with
  | nil => simp [combineSum]
  | cons a y ih => simp [stepSet_hmul_inr, ih]

theorem acceptsFrom_hmul {S1 : σ1 → κ} :
    (M1 * M2).acceptsFrom (combineSum S1 0) = M1.acceptsFrom S1 * M2.accepts := by
  ext z
  induction z generalizing S1 with
  | nil =>
    simp [Finset.sum_mul, W.mul_assoc]
  | cons a z ih =>
    suffices h :
      ∑ s1 : σ1,
        S1 s1 *
        (M1 * M2).acceptsFrom
          (combineSum (M1.step s1 a)
            ((M1.final s1 * ·) ∘ ∑ s2 : σ2, (M2.start s2 * ·) ∘ M2.step s2 a)) z =
      (∑ s1 : σ1, S1 s1 * M1.final s1) * M2.accepts (a :: z) +
      (((∑ s1 : σ1, (S1 s1 * ·) ∘ M1.acceptsFrom (M1.step s1 a)) : WeightedLanguage α κ)
       * M2.accepts) z by
      simpa [stepSet, acceptsFrom_sum, acceptsFrom_compose_mul,
        Function.comp_def (fun x : κ ↦ (0 : κ)),
        show (↑(Fintype.card σ2) * fun x ↦ 0) = (0 : σ1 ⊕ σ2 → κ) by (ext (s1 | s2) <;> simp)]
    conv_lhs => {
      arg 2
      ext s
      rw [combineSum_separate, acceptsFrom_add, WeightedLanguage.add_apply, ih,
        acceptsFrom_hmul_inr]
    }
    open scoped Classical in
    simp [W.left_distrib, Finset.sum_add_distrib,
      acceptsFrom_compose_mul, acceptsFrom_sum, accepts, stepSet, Finset.sum_mul,
      Finset.mul_sum, WeightedLanguage.mul_as_sum_over_prod,
      W.add_comm (∑ s : σ1, ∑ y ∈ z.splits.toFinset, _), W.mul_assoc,
      Finset.sum_comm (f:=fun x y ↦ S1 y * _)]

theorem accepts_hmul : (M1 * M2).accepts = M1.accepts * M2.accepts := by
  simp [accepts, acceptsFrom_hmul]

end concat

section reverse

variable {σ : Type v} (M : WNFA α σ κ)

@[simp]
def revStart : σ → κ := M.final

@[simp]
def revFinal : σ → κ := M.start

@[simp]
def revStep (s : σ) (a : α) (s' : σ) : κ := M.step s' a s

def rev : WNFA α σ κ where
  step := M.revStep
  start := M.revStart
  final := M.revFinal

@[simp]
theorem rev_step_eq_revStep : M.rev.step = M.revStep :=
  rfl

@[simp]
theorem rev_start_eq_revStart : M.rev.start = M.revStart :=
  rfl

@[simp]
theorem rev_final_eq_revFinal : M.rev.final = M.revFinal :=
  rfl

variable [W : CommSemiring κ] [Fintype σ]

theorem rev_evalFrom_eq_evalFrom_reverse {S1 S2 : σ → κ} {x : List α} :
    ∑ s : σ, M.rev.evalFrom S2 x s * S1 s = ∑ s : σ, M.evalFrom S1 x.reverse s * S2 s := by
  induction x generalizing S1 S2 with
  | nil => simp [W.mul_comm (S1 _) (S2 _)]
  | cons a x ih =>
    suffices h :
      ∑ i, ∑ j, M.evalFrom S1 x.reverse i * (S2 j * M.step i a j) =
      ∑ j, ∑ i, M.evalFrom S1 x.reverse i * M.step i a j * S2 j by
      simpa [stepSet, ih, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    ac_nf

theorem accepts_rev : M.rev.accepts = M.accepts.rev := by
  ext x
  simp [accepts, acceptsFrom, rev_evalFrom_eq_evalFrom_reverse]

end reverse

end WNFA

namespace WDFA

variable {α : Type u} {κ : Type k} {σ : Type v} [W : Semiring κ] [DecidableEq σ]

@[simp]
def funOfPair (sw : σ × κ) (s : σ) : κ :=
  if s = sw.1 then sw.2 else 0

@[simps]
def toWNFA (M : WDFA α σ κ) : WNFA α σ κ where
  step s a := funOfPair (M.step s a)
  start := funOfPair M.start
  final := M.final

variable [Fintype σ]

theorem acceptsFrom_toWNFA (M : WDFA α σ κ) (sw : σ × κ) :
    M.acceptsFrom sw = M.toWNFA.acceptsFrom (funOfPair sw) := by
  ext x
  induction x generalizing sw
  case nil => simp
  case cons a x ih =>
    obtain ⟨s, w⟩ := sw
    rcases hstep : M.step s a with ⟨s', w'⟩
    simp only [acceptsFrom_cons, ih, WNFA.acceptsFrom_cons, WNFA.stepSet]
    congr 1
    ext q
    simp [hstep]

theorem accepts_toWNFA (M : WDFA α σ κ) : M.toWNFA.accepts = M.accepts := by
  simp only [WDFA.accepts, WNFA.accepts, acceptsFrom_toWNFA]
  rfl

end WDFA
