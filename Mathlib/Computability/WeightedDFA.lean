/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Computability.WeightedPath
import Mathlib.Computability.WeightedLanguage
import Mathlib.Computability.DFA

/-!
# Weighted Deterministic Finite Automata

A Weighted Deterministic Finite Automata (WDFA) is a state machine that describes a weighted
language by assinging an input string a weight. The weight of the string is determined by
the path it takes through the state machine.

Every transition in a WDFA produces a weight, which is an element of a semiring.
The weight of a path, a sequence of transitions, is the in-order multiplication of all of its
constituent transitions.

Note that this definition allows for automata with infinite states,
a `Fintype` instance must be supplied for true DFAs.

TODO: explain stuff.
-/

universe k u v

/-- A Weighted DFA (`𝓐`) over a semiring (`𝓦 = (κ, ⊕, ⊗, 0, 1)`)
is a 5-tuple (`(α, σ, step, start, final)`) where
* (`α`) is a (finite) alphabet.
* (`σ`) is a (finite) set of states.
* (`step : σ → α → σ × κ`) is a (finite) set of transitions.
* (`start : σ × κ`) the start state and its weight.
* (`final : σ → κ`) is a weighting function assigning states their final values.
-/
structure WDFA (α : Type u) (σ : Type v) (κ : Type k) where
  /-- A transition function from state to state labelled by the alphabet producing a weight. -/
  step : σ → α → σ × κ
  /-- Starting state and weight. -/
  start : σ × κ
  /-- Final weights. -/
  final : σ → κ

namespace WDFA

variable {α : Type u} {κ : Type k}

section basic

variable {σ : Type v} (M : WDFA α σ κ) [W : Semiring κ]

instance [Inhabited σ] [Inhabited κ] : Inhabited (WDFA α σ κ) :=
  ⟨WDFA.mk (fun _ _ => ⟨default, default⟩) ⟨default, default⟩ (fun _ ↦ 0)⟩

/-- `M.PathInWDFA π` holds when `π` is a valid sequence of transitions in `M`. -/
def PathInWDFA {s₁ s₃ : σ} : WeightedPath α κ s₁ s₃ → Prop :=
  WeightedPath.All (fun q₁ a w q₂ ↦ M.step q₁ a = (q₂, w))

/-- `M.AcceptingPathInWDFA π` holds when `π` is a valid path in `M` from a start state to a final
state yielding weight `w`. -/
def AcceptingPathInWDFA {s₁ s₂ : σ} (π : WeightedPath α κ s₁ s₂) (w : κ) : Prop :=
  s₁ = M.start.1 ∧
  M.PathInWDFA π ∧
  w = M.start.2 * π.innerWeight * M.final s₂

/--
`M.evalFromL s x` evaluates `M` with input `x` starting from
the state `s` left-associatively. -/
def evalFromL : σ × κ → List α → σ × κ :=
  List.foldl (fun sw a ↦ Prod.map id (W.mul sw.2) (M.step sw.1 a))

@[simp]
lemma evalFromL_nil (sw : σ × κ) : M.evalFromL sw [] = sw := rfl

@[simp]
lemma evalFromL_singleton (sw : σ × κ) (a : α) :
    M.evalFromL sw [a] = Prod.map id (sw.2 * ·) (M.step sw.1 a) := rfl

@[simp]
lemma evalFromL_append_singleton (sw : σ × κ) (x : List α) (a : α) :
    M.evalFromL sw (x ++ [a]) =
    Prod.map id ((M.evalFromL sw x).2 * ·) (M.step (M.evalFromL sw x).1 a) := by
  simp only [evalFromL, List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr

@[simp]
lemma evalFromL_cons (sw : σ × κ) (a : α) (x : List α) :
    M.evalFromL sw (a :: x) = M.evalFromL (Prod.map id (sw.2 * ·) (M.step sw.1 a)) x := by
  simp only [evalFromL, List.foldl_cons]
  congr

lemma evalFromL_append (sw : σ × κ) (x y : List α) :
    M.evalFromL sw (x ++ y) = M.evalFromL (M.evalFromL sw x) y := by
  simp only [evalFromL, List.foldl_append]

lemma evalFromL_prod (s : σ) (w1 w2 : κ) (x : List α) :
    M.evalFromL (s, w1 * w2) x =
    Prod.map id (w1 * ·) (M.evalFromL (s, w2) x) := by
  induction x generalizing s w1 w2
  case nil =>
    simp
  case cons a x ih =>
    simp [evalFromL_cons, ←ih]
    rcases (M.step s a) with ⟨s', w'⟩
    simp [mul_assoc]

lemma evalFromL_prod_one (s : σ) (w : κ) (x : List α) :
    M.evalFromL (s, w) x =
    Prod.map id (w * ·) (M.evalFromL (s, 1) x) := by
  simp [←evalFromL_prod, W.mul_one]

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval : List α → σ × κ := M.evalFromL M.start

/-- `M.evalWeight x` evaluates `M` with input `x` starting from the state `M.start` producing the
final weight. -/
def evalWeight : WeightedLanguage α κ :=
  fun x ↦
    let (s, w) := M.eval x;
    w * M.final s

@[simp]
lemma eval_nil : M.eval [] = M.start := rfl

@[simp]
lemma eval_singleton (a : α) : M.eval [a] = Prod.map id (M.start.2 * ·) (M.step M.start.1 a) := by
  simp only [eval, evalFromL_singleton]

@[simp]
lemma eval_append_singleton (x : List α) (a : α) :
    M.eval (x ++ [a]) = Prod.map id ((M.eval x).2 * ·) (M.step (M.eval x).1 a) := by
  simp only [eval, evalFromL_append_singleton]

/-- `M.acceptsFrom sw x` is the weighted lenaguage of `x` such that `(M.evalFromL sw x).1` is an
accept state. -/
def acceptsFrom (sw : σ × κ) : WeightedLanguage α κ :=
  fun x ↦
    let (s₂, w) := (M.evalFromL sw x);
    w * M.final s₂

@[simp]
lemma acceptsFrom_nil (sw : σ × κ) : M.acceptsFrom sw [] = sw.2 * M.final sw.1 :=
  rfl

@[simp]
lemma acceptsFrom_cons (sw : σ × κ) (a : α) (x : List α) :
    M.acceptsFrom sw (a :: x) = M.acceptsFrom ((M.step sw.1 a).1, (sw.2 * (M.step sw.1 a).2)) x :=
  rfl

lemma acceptsFrom_prod (s : σ) (w1 w2 : κ) (x : List α) :
    M.acceptsFrom (s, w1 * w2) x =
    w1 * M.acceptsFrom (s, w2) x := by
  simp [acceptsFrom, evalFromL_prod, mul_assoc]

lemma acceptsFrom_prod_one (s : σ) (w : κ) (x : List α) :
    M.acceptsFrom (s, w) x =
    w * M.acceptsFrom (s, 1) x := by
  simp [←acceptsFrom_prod]

/-- `M.accepts x` is the weighted lenaguage of `x` such that `(M.evalFromL M.start x).1` is an
accept state. -/
def accepts : WeightedLanguage α κ := M.acceptsFrom M.start

theorem weight_accepts (x : List α) : M.accepts x = M.evalWeight x :=
  rfl

-- TODO: fix final states
def ofDFA (M : DFA α σ) : WDFA α σ κ :=
  ⟨(fun s a ↦ (M.step s a, 1)), (M.start, 1), (fun s ↦ 0)⟩
end basic

section inter

variable {σ1 σ2 : Type v} [W : CommSemiring κ]

@[simp]
def inter_start (M1 : WDFA α σ1 κ) (M2 : WDFA α σ2 κ) : ((σ1 × σ2) × κ) :=
  ((M1.start.1, M2.start.1), M1.start.2 * M2.start.2)

@[simp]
def inter_final (M1 : WDFA α σ1 κ) (M2 : WDFA α σ2 κ) (s : σ1 × σ2) : κ :=
  M1.final s.1 * M2.final s.2

@[simp]
def inter_step (M1 : WDFA α σ1 κ) (M2 : WDFA α σ2 κ) (s : σ1 × σ2) (a : α) : (σ1 × σ2) × κ :=
  let sw1 := M1.step s.1 a;
  let sw2 := M2.step s.2 a;
  ((sw1.1, sw2.1), sw1.2 * sw2.2)

def inter (M1 : WDFA α σ1 κ) (M2 : WDFA α σ2 κ) : WDFA α (σ1 × σ2) κ where
  start := inter_start M1 M2
  final := inter_final M1 M2
  step := inter_step M1 M2

instance : HMul (WDFA α σ1 κ) (WDFA α σ2 κ) (WDFA α (σ1 × σ2) κ) := ⟨inter⟩

lemma inter_eq_hmul {M1 : WDFA α σ1 κ} {M2 : WDFA α σ2 κ} : M1 * M2 = M1.inter M2 := rfl

@[simp]
lemma inter_start_proj {M1 : WDFA α σ1 κ} {M2 : WDFA α σ2 κ} :
  (M1 * M2).start = inter_start M1 M2 := rfl

@[simp]
lemma inter_final_proj {M1 : WDFA α σ1 κ} {M2 : WDFA α σ2 κ} :
  (M1 * M2).final = inter_final M1 M2 := rfl

@[simp]
lemma inter_step_proj {M1 : WDFA α σ1 κ} {M2 : WDFA α σ2 κ} :
  (M1 * M2).step = inter_step M1 M2 := rfl

lemma acceptsFrom_inter {M1 : WDFA α σ1 κ} {M2 : WDFA α σ2 κ}
  {x : List α} {s1 : σ1} {s2 : σ2} {w1 w2 : κ} :
    (M1 * M2).acceptsFrom ((s1, s2), w1 * w2) x
    = M1.acceptsFrom (s1, w1) x * M2.acceptsFrom (s2, w2) x := by
  induction x generalizing s1 s2 w1 w2
  case nil =>
    simp
    exact mul_mul_mul_comm w1 w2 (M1.final s1) (M2.final s2)
  case cons a x ih =>
    simp [ih]
    rcases (M1.step s1 a) with ⟨s1', w1'⟩
    rcases (M2.step s2 a) with ⟨s2', w2'⟩
    simp [acceptsFrom_prod]
    rw [acceptsFrom_prod_one M1 s1' w2,
        acceptsFrom_prod_one M1 s1' w1',
        acceptsFrom_prod_one M2 s2' w2']
    simp [W.mul_assoc]
    congr 1
    simp [←W.mul_assoc]
    congr 1
    congr 1
    rw [W.mul_comm _ w2, W.mul_assoc, W.mul_comm w1']

theorem accepts_inter {M1 : WDFA α σ1 κ} {M2 : WDFA α σ2 κ} :
    (M1 * M2).accepts = M1.accepts.pointwise_prod M2.accepts := by
  funext x
  simp [accepts, WeightedLanguage.pointwise_prod, acceptsFrom_inter]

end inter

section boolean

variable {σ : Type v}

-- TODO: fix false transitions in step
def toDFA (M : WDFA α σ Bool) : DFA α σ :=
  ⟨(fun s a ↦ (M.step s a).1), M.start.1, { s | M.final s } ⟩

end boolean

end WDFA
