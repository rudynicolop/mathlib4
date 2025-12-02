/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
module

public import Mathlib.Computability.WeightedLanguage
public import Mathlib.Computability.WeightedNFA

/-!
# Weighted Regular Expressions

This file contains the formal definition for *semiring-weighted* regular expressions and basic
lemmas.

TODO: more explanation
-/

@[expose] public section

open List

universe u k

namespace List

variable {α : Type u}

theorem splits_append_singleton {x : List α} (a : α) :
    (x ++ [a]).splits = x.splits.map (fun td ↦ (td.1, td.2 ++ [a])) ++ [(x ++ [a], [])] := by
  induction x generalizing a with
  | nil => simp [List.splits_cons]
  | cons b x ih => simp [List.splits_cons, ih]

theorem splits_reverse {l : List α} :
    l.reverse.splits = (l.splits.map (fun td ↦ (td.2.reverse, td.1.reverse))).reverse := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.splits_cons, splits_append_singleton, ih]

end List

/-- This is the definition of *semiring-weighted* regular expressions. We mirror uniweghted
`RegularExpression` data type.
* `w` matchs the empty string with weight `w`
* `char a` matches only the string 'a' with weight `1`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q` and adds the weights
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q` and multiples the
  weights

NOTE: We do not yet support kleene stars for weighted languages, which naively would involve an
infinite computation.
-/
inductive WRegExp (α : Type u) (κ : Type k) where
  | weight : κ → WRegExp α κ
  | char : α → WRegExp α κ
  | plus : WRegExp α κ → WRegExp α κ → WRegExp α κ
  | comp : WRegExp α κ → WRegExp α κ → WRegExp α κ

namespace WRegExp

variable {α : Type u} {κ : Type k}

instance [Inhabited κ] : Inhabited (WRegExp α κ) :=
  ⟨weight default⟩

instance : Add (WRegExp α κ) :=
  ⟨plus⟩

instance : Mul (WRegExp α κ) :=
  ⟨comp⟩

instance [One κ] : One (WRegExp α κ) :=
  ⟨weight 1⟩

instance [Zero κ] : Zero (WRegExp α κ) :=
  ⟨weight 0⟩

instance [One κ] : Pow (WRegExp α κ) ℕ :=
  ⟨fun P n => npowRec n P⟩

@[simp]
theorem zero_def [Zero κ] : weight 0 = (0 : WRegExp α κ) :=
  rfl

@[simp]
theorem one_def [One κ] : weight 1 = (1 : WRegExp α κ) :=
  rfl

@[simp]
theorem plus_def (P Q : WRegExp α κ) : plus P Q = P + Q :=
  rfl

@[simp]
theorem comp_def (P Q : WRegExp α κ) : comp P Q = P * Q :=
  rfl

@[simp]
theorem pow_def [One κ] (P : WRegExp α κ) (n : Nat) : npowRec n P = P ^ n :=
  rfl

section matches'

variable [DecidableEq α] [W : Semiring κ]

/-- `macthes' P` provides a *weighted* language for all strings that `P` macthes.

Not named `matches` since that is a reserved word.
-/
@[simp]
def matches' : WRegExp α κ → WeightedLanguage α κ
  | weight w => WeightedLanguage.scalar_prodl w 1
  | char a => fun x ↦ if x = [a] then 1 else 0
  | P + Q => P.matches' + Q.matches'
  | P * Q => P.matches' * Q.matches'

theorem matches'_char (a : α) : (char a).matches' = (fun x ↦ if x = [a] then W.one else 0) :=
  rfl

theorem matches'_add (P Q : WRegExp α κ) : (P + Q).matches' = P.matches' + Q.matches' :=
  rfl

theorem matches'_mul (P Q : WRegExp α κ) : (P * Q).matches' = P.matches' * Q.matches' :=
  rfl

@[simp]
theorem matches'_pow (P : WRegExp α κ) (n : ℕ) : (P ^ n).matches' = P.matches' ^ n := by
  induction n generalizing P
  case zero =>
    funext x
    simp [pow_zero, ←pow_def, npowRec.eq_def, WeightedLanguage.scalar_prodl]
  case succ n ih =>
    simp only [pow_succ, ←ih]
    rfl

end matches'

section rev

@[simp]
def rev : WRegExp α κ → WRegExp α κ
| weight w => weight w
| char a => char a
| P + Q => P.rev + Q.rev
| P * Q => Q.rev * P.rev

variable [DecidableEq α] [W : CommSemiring κ]

theorem rev_matches' (P : WRegExp α κ) : P.rev.matches' = P.matches'.rev := by
  ext x
  rw [WeightedLanguage.rev, Function.comp_apply]
  induction P generalizing x with
  | weight w => cases x <;> simp [WeightedLanguage.onlyNil_gives_zero]
  | char a => simp
  | plus P Q ihp ihq => simp [ihp, ihq]
  | comp P Q ihp ihq =>
    simp [WeightedLanguage.mul_apply, WeightedLanguage.cauchy_prod, List.splits_reverse,
      Function.comp_def, ihp, ihq, W.mul_comm (P.matches' _)]

end rev

section toWNFA

@[simp]
def states : WRegExp α κ → Type
| weight _ => Unit
| char _ => Bool
| P + Q
| P * Q => P.states ⊕ Q.states

@[simp]
theorem states_weight_unit (w : κ) : (weight (α:=α) w).states = Unit :=
  rfl

@[simp]
theorem states_char_bool (a : α) : (char (κ:=κ) a).states = Bool :=
  rfl

@[simp]
theorem states_plus_sum (P Q : WRegExp α κ) : (P + Q).states = (P.states ⊕ Q.states) :=
  rfl

@[simp]
theorem states_comp_sum (P Q : WRegExp α κ) : (P * Q).states = (P.states ⊕ Q.states) :=
  rfl

def statesDecEq : ∀ (r : WRegExp α κ) (s1 s2 : r.states), Decidable (s1 = s2)
| weight w =>
  cast (α:=∀ (s1 s2 : Unit), Decidable (s1 = s2)) (by simp) inferInstance
| char a =>
  cast (α:=∀ (s1 s2 : Bool), Decidable (s1 = s2)) (by simp) Bool.decEq
| P + Q | P * Q =>
  cast (α:=∀ (s1 s2 : P.states ⊕ Q.states), Decidable (s1 = s2)) (by simp) <|
    fun | .inl s1, .inl s2 =>
          match P.statesDecEq s1 s2 with
          | isTrue rfl => isTrue rfl
          | isFalse h => isFalse <| fun hinl ↦ h <| Sum.inl_injective hinl
        | .inr s1, .inr s2 =>
          match Q.statesDecEq s1 s2 with
          | isTrue rfl => isTrue rfl
          | isFalse h => isFalse <| fun hinr ↦ h <| Sum.inr_injective hinr
        | .inl _, .inr _ | .inr _, .inl _ => isFalse (by rintro ⟨⟩)

instance instDeciableEqStates {r : WRegExp α κ} : DecidableEq r.states := r.statesDecEq

@[simp]
def statesElems : ∀ (r : WRegExp α κ), Finset r.states
| weight w => cast (α:=Finset Unit) (by simp) Finset.univ
| char a => cast (α:=Finset Bool) (by simp) Finset.univ
| P + Q | P * Q =>
  cast (α:= Finset (P.states ⊕ Q.states)) (by simp) <|
    P.statesElems.disjSum Q.statesElems

theorem statesElems_complete (r : WRegExp α κ) (s : r.states) : s ∈ r.statesElems := by
  revert s
  induction r with
  | weight w => simp
  | char a => simp
  | plus P Q ihp ihq
  | comp P Q ihp ihq =>
    suffices h : (∀ (s : P.states), s ∈ P.statesElems) ∧ ∀ (s : Q.states), s ∈ Q.statesElems by
      simpa
    constructor <;> assumption

instance instFintypeStates {r : WRegExp α κ} : Fintype r.states where
  elems := r.statesElems
  complete := r.statesElems_complete

variable [DecidableEq α] [W : Semiring κ]

@[simp]
def toWNFA : ∀ (r : WRegExp α κ), WNFA₃ α r.states κ
| weight w => WNFA₃.empty w
| char a => WNFA₃.char a
| P + Q => P.toWNFA + Q.toWNFA
| P * Q => P.toWNFA * Q.toWNFA

theorem accepts_toWNFA (r : WRegExp α κ) :
    r.toWNFA.accepts = r.matches' := by
  induction r with
  | weight w => simp [WNFA₃.accepts_empty]
  | char a => simp [WNFA₃.accepts_char]
  | plus P Q ihp ihq => simp [WNFA₃.accepts_hadd, ihp, ihq]
  | comp P Q ihp ihq => simp [WNFA₃.accepts_hmul, ihp, ihq]

end toWNFA

end WRegExp
