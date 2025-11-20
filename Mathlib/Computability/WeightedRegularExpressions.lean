/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
import Mathlib.Computability.WeightedLanguage

/-!
# Weighted Regular Expressions

This file contains the formal definition for *semiring-weighted* regular expressions and basic
lemmas.

TODO: more explanation
-/

open List

universe u k

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
        | .inl _, .inr _ => isFalse (by rintro ⟨⟩)
        | .inr _, .inl _ => isFalse (by rintro ⟨⟩)

instance instDeciableEqStates {r : WRegExp α κ} : DecidableEq r.states := r.statesDecEq

end toWNFA

end WRegExp
