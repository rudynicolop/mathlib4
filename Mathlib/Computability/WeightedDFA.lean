/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Computability.WeightedPath
public import Mathlib.Computability.WeightedLanguage
public import Mathlib.Computability.DFA
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.Algebra.Ring.WithZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical

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

Note that since WDFA only use multiplication, we only require a monoid for multiplication, not a
full semiring.

TODO: explain stuff.
-/

@[expose] public section

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

variable {α : Type u}

section basic

variable {κ : Type k} {σ : Type v} (M : WDFA α σ κ) [W : MonoidWithZero κ]

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
lemma evalFromL_cons (sw : σ × κ) (a : α) (x : List α) :
    M.evalFromL sw (a :: x) = M.evalFromL (Prod.map id (sw.2 * ·) (M.step sw.1 a)) x := by
  simp only [evalFromL, List.foldl_cons]
  congr

@[simp]
lemma evalFromL_append (sw : σ × κ) (x y : List α) :
    M.evalFromL sw (x ++ y) = M.evalFromL (M.evalFromL sw x) y := by
  simp only [evalFromL, List.foldl_append]

lemma evalFromL_singleton (sw : σ × κ) (a : α) :
    M.evalFromL sw [a] = Prod.map id (sw.2 * ·) (M.step sw.1 a) := rfl

lemma evalFromL_append_singleton (sw : σ × κ) (x : List α) (a : α) :
    M.evalFromL sw (x ++ [a]) =
    Prod.map id ((M.evalFromL sw x).2 * ·) (M.step (M.evalFromL sw x).1 a) := by
  simp

lemma evalFromL_prod (s : σ) (w1 w2 : κ) (x : List α) :
    M.evalFromL (s, w1 * w2) x =
    Prod.map id (w1 * ·) (M.evalFromL (s, w2) x) := by
  induction x generalizing s w1 w2
  case nil =>
    simp
  case cons a x ih =>
    rcases hstep : (M.step s a) with ⟨s', w'⟩
    simp only [evalFromL_cons, hstep, Prod.map_apply, id_eq, ← ih]
    ac_nf

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

@[simp]
lemma acceptsFrom_zero (s : σ) (x : List α) : M.acceptsFrom (s, 0) x = 0 := by
  induction x generalizing s
  case nil => simp
  case cons a x ih => simp [ih]

/-- `M.accepts x` is the weighted lenaguage of `x` such that `(M.evalFromL M.start x).1` is an
accept state. -/
def accepts : WeightedLanguage α κ := M.acceptsFrom M.start

theorem weight_accepts (x : List α) : M.accepts x = M.evalWeight x :=
  rfl

end basic

section inter

variable {κ : Type k} {σ1 σ2 : Type v} [W : CommMonoidWithZero κ]

@[simp]
def interStart (M1 : WDFA α σ1 κ) (M2 : WDFA α σ2 κ) : ((σ1 × σ2) × κ) :=
  ((M1.start.1, M2.start.1), M1.start.2 * M2.start.2)

@[simp]
def interFinal (M1 : WDFA α σ1 κ) (M2 : WDFA α σ2 κ) (s : σ1 × σ2) : κ :=
  M1.final s.1 * M2.final s.2

@[simp]
def interStep (M1 : WDFA α σ1 κ) (M2 : WDFA α σ2 κ) (s : σ1 × σ2) (a : α) : (σ1 × σ2) × κ :=
  let sw1 := M1.step s.1 a;
  let sw2 := M2.step s.2 a;
  ((sw1.1, sw2.1), sw1.2 * sw2.2)

@[simps]
def inter (M1 : WDFA α σ1 κ) (M2 : WDFA α σ2 κ) : WDFA α (σ1 × σ2) κ where
  start := interStart M1 M2
  final := interFinal M1 M2
  step := interStep M1 M2

lemma acceptsFrom_inter {M1 : WDFA α σ1 κ} {M2 : WDFA α σ2 κ}
  {s1 : σ1} {s2 : σ2} {w1 w2 : κ} :
    (M1.inter M2).acceptsFrom ((s1, s2), w1 * w2)
    = (M1.acceptsFrom (s1, w1)).pointwise_prod (M2.acceptsFrom (s2, w2)) := by
  ext x
  rw [WeightedLanguage.pointwise_prod_apply]
  induction x generalizing s1 s2 w1 w2
  case nil =>
    simp only [acceptsFrom_nil, inter_final, interFinal]
    ac_nf
  case cons a x ih =>
    simp only [acceptsFrom_cons, inter_step, interStep, ih]
    rcases (M1.step s1 a) with ⟨s1', w1'⟩
    rcases (M2.step s2 a) with ⟨s2', w2'⟩
    simp only [acceptsFrom_prod]
    rw [acceptsFrom_prod_one M1 s1' w2,
        acceptsFrom_prod_one M1 s1' w1',
        acceptsFrom_prod_one M2 s2' w2']
    ac_nf

theorem accepts_inter {M1 : WDFA α σ1 κ} {M2 : WDFA α σ2 κ} :
    (M1.inter M2).accepts = M1.accepts.pointwise_prod M2.accepts := by
  simp [accepts, acceptsFrom_inter]

end inter

section toDFA

/- ### Weighted to unweighted DFA

We cannot use `Bool` for the weight type, since the Mathlib instance for `Add Bool` uses `xor`, not
`or`. Instead we use a type isomorphic to `Bool`.

-/

variable {σ : Type v} (M : WDFA α σ (WithZero Unit))

@[simp]
def toDFAStart : Option σ :=
  if M.start.2 = 1 then .some M.start.1 else .none

@[simp]
def toDFAAccept : Set (Option σ) :=
  { so | ∃ s, M.final s = 1 ∧ so = .some s }

@[simp]
def toDFAStep : Option σ → α → Option σ
| .none, _ => .none
| .some s, a =>
  let ⟨s', w⟩ := M.step s a;
  if w = 1 then .some s' else none

@[simps]
def toDFA : DFA α (Option σ) where
  step := M.toDFAStep
  start := M.toDFAStart
  accept := M.toDFAAccept

lemma toDFA_acceptsFrom_none {x : List α} : x ∉ M.toDFA.acceptsFrom .none := by
  induction x
  case nil => simp
  case cons a x ih => simpa

lemma wzu_zero_or_one (w : WithZero Unit) : w = 0 ∨ w = 1 :=
  match w with
  | .none => by tauto
  | .some .unit => by tauto

lemma toDFA_acceptsFrom {s : σ} {x : List α} :
    x ∈ M.toDFA.acceptsFrom (.some s) ↔ M.acceptsFrom (s, 1) x = 1 := by
  induction x generalizing s
  case nil => simp
  case cons a x ih =>
    rcases hstep : M.step s a with ⟨s', w⟩
    simp [hstep]
    rcases (wzu_zero_or_one w) with rfl | rfl
    · simp [toDFA_acceptsFrom_none]
    · simp [ih]

theorem toDFA_accepts {x : List α} :
    x ∈ M.toDFA.accepts ↔ M.accepts x = 1 := by
  simp [accepts, DFA.accepts]
  rcases M.start with ⟨s, w⟩
  rcases (wzu_zero_or_one w) with rfl | rfl
  · simp [toDFA_acceptsFrom_none]
  · simp [toDFA_acceptsFrom]

end toDFA

end WDFA

namespace DFA

variable {α : Type u} {κ : Type k} {σ : Type v} (M : DFA α σ) [W : CommMonoidWithZero κ]

/- We need to assume that the set of final states is finite. -/
variable [Fintype M.accept] [DecidableEq σ]
attribute [local instance] Set.decidableMemOfFintype

@[simp]
def toWDFAStart : σ × κ := (M.start, 1)

@[simp]
def toWDFAFinal (s : σ) : κ :=
  if s ∈ M.accept then 1 else 0

@[simp]
def toWDFAStep (s : σ) (a : α) : σ × κ := (M.step s a, 1)

@[simps]
def toWDFA : WDFA α σ κ where
  step := M.toWDFAStep
  start := M.toWDFAStart
  final := M.toWDFAFinal

lemma toWDFA_acceptsFrom {x : List α} {s : σ} {w : κ} (hw₀ : w ≠ 0) :
    M.toWDFA.acceptsFrom (s, w) x = w ↔ x ∈ M.acceptsFrom s := by
  induction x generalizing s w
  case nil => simp; tauto
  case cons a x ih => simp [ih hw₀]

lemma toWDFA_accetps {x : List α} : M.toWDFA.accepts x = 1 ↔ x ∈ M.accepts := by
  simp [WDFA.accepts, accepts, toWDFA_acceptsFrom]

end DFA
